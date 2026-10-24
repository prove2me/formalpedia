-- Prove2me | Definitions.Def_PricingWithTips3DM_b27b057a2325e62412e51b11
-- name    : PricingWithTips3DM_b27b057a2325e62412e51b11
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:36:29.464167+00:00
-- url     : https://prove2.me/theorems/d853c6b7-2a52-4e42-8471-ee8ee2e08202
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Logic.Sat.Encoding
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_PricingWithTips3DM_0ce3e5e1c7f27e9a1020a44d
import Definitions.Def_PricingWithTips3DM_ddcced5313ed447b67330e23
import Definitions.Def_PricingWithTips3DM_43f9b6655ad25b0a26cba9b7
import Definitions.Def_PricingWithTips3DM_6b7a275bb9cec4f884d54bad
import Definitions.Def_PricingWithTips3DM_700c4ea915bd5ddbfce98a0b
import Definitions.Def_PricingWithTips3DM_d3fa2b92541a58df50ce1d93
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete encoding of SAT instances

A concrete SAT instance is a list of clauses; a clause is a list of literals
`(variable label, polarity)`. Every input is well-formed, so decoding is
total: variables are their `ℕ` labels.

One encoding serves the whole `Logic/` family: 3SAT and its bounded-occurrence
version are `Problem.restrict`ions of SAT over the *same* instance type, so
they decode with the same `decodeSat` and differ only in the side condition
conjoined into the predicate. The decoded formula is `x` with its literal
pairs read as `Literal ℕ`, which is what `decodeSat_φ` records; concrete
gadget outputs are related to the tagged formulas built in the mathematical
layer by `CNF.relabel` along an injective naming map.
-/

namespace Hardness
namespace Cert

/-- Concrete SAT instances: a formula is a list of clauses; a clause is a list
of literals `(variable label, polarity)`. Every input is well-formed. -/
abbrev SatTy : Ty := .list (.list (.pair .nat .bool))

/-- The concrete literal type: `(variable label, polarity)`. -/
abbrev LitTy : Ty := .pair .nat .bool

/-- The concrete clause type: a list of literals. -/
abbrev ClauseTy : Ty := .list LitTy

/-- Decode a concrete SAT instance: variables are their labels. Total — any
list of lists of labelled literals is a CNF formula over `ℕ`. -/
def decodeSat (x : SatTy.denote) : SatInstance where
  V := ℕ
  φ := x.map (List.map fun p ↦ ⟨p.1, p.2⟩)

/-- Read a concrete literal `(label, polarity)` as a `Literal ℕ`. -/
def litOf (p : LitTy.denote) : Literal ℕ := ⟨p.1, p.2⟩

/-- The decoded formula, as a plain `CNF ℕ`. Definitionally `(decodeSat x).φ`,
but stated over `ℕ` instead of over the instance's variable *field*, which is
what lets the certificate proofs rewrite it: a rewrite under `(decodeSat x).V`
fails the motive check. -/
def decodeCNF (x : SatTy.denote) : CNF ℕ := x.map (List.map litOf)

/-- The decoded formula: the concrete clause list, read literal by literal. -/
theorem decodeSat_φ (x : SatTy.denote) : (decodeSat x).φ = decodeCNF x := rfl

/-- Clause widths are visible on the concrete instance: decoding maps clauses
to clauses of the same length, so any property of the widths transfers. -/
theorem decodeSat_lengths_iff {P : ℕ → Prop} (x : SatTy.denote) :
    (∀ c ∈ decodeCNF x, P c.length) ↔ ∀ c ∈ x, P c.length := by
  constructor
  · intro h c hc
    simpa using h (c.map litOf) (List.mem_map_of_mem hc)
  · intro h c hc
    obtain ⟨d, hd, rfl⟩ :=
      List.mem_map.mp (show c ∈ x.map (List.map litOf) from hc)
    rw [List.length_map]
    exact h d hd

/-- Clause widths are visible on the concrete instance: decoding maps clauses
to clauses of the same length. -/
theorem decodeSat_width_iff {n : ℕ} (x : SatTy.denote) :
    (∀ c ∈ decodeCNF x, c.length ≤ n) ↔ ∀ c ∈ x, c.length ≤ n :=
  decodeSat_lengths_iff (P := (· ≤ n)) x

/-- Polarities are visible on the concrete instance: decoding keeps each
literal's polarity bit, so positivity is read off the concrete clause list. -/
theorem decodeSat_positive_iff (x : SatTy.denote) :
    (decodeCNF x).Positive ↔ ∀ c ∈ x, ∀ p ∈ c, p.2 = true := by
  constructor
  · intro h c hc p hp
    exact h (c.map litOf) (List.mem_map_of_mem hc) (litOf p) (List.mem_map_of_mem hp)
  · intro h c hc l hl
    obtain ⟨d, hd, rfl⟩ :=
      List.mem_map.mp (show c ∈ x.map (List.map litOf) from hc)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    exact h d hd p hp

/-- The decoded formula has one clause per concrete clause. -/
theorem length_decodeCNF (x : SatTy.denote) : (decodeCNF x).length = x.length :=
  List.length_map ..

/-- A clause of the decoded formula is the concrete clause, literal by
literal. -/
theorem getElem_decodeCNF (x : SatTy.denote) (j : ℕ) (hj : j < (decodeCNF x).length) :
    (decodeCNF x)[j] = (x[j]'(by rwa [length_decodeCNF] at hj)).map litOf :=
  List.getElem_map ..

/-- Literal occurrences of the decoded formula are the literals of the
enumerated concrete clauses — the transport a gadget certificate needs to match
a `CNF.Occ` existential against its own loop over `listEnum`. -/
theorem exists_occ_decodeCNF_iff (x : SatTy.denote) (Q : Literal ℕ → ℕ → Prop) :
    (∃ o : (decodeCNF x).Occ, Q ((decodeCNF x).occLit o) o.1.1)
      ↔ ∃ q ∈ x.zipIdx, ∃ p ∈ q.1, Q (litOf p) q.2 := by
  rw [CNF.exists_occ_iff]
  constructor
  · rintro ⟨j, hj, l, hl, hQ⟩
    have hjx : j < x.length := by rwa [length_decodeCNF] at hj
    rw [getElem_decodeCNF x j hj] at hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    exact ⟨(x[j], j), List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hjx),
      p, hp, hQ⟩
  · rintro ⟨q, hq, p, hp, hQ⟩
    rw [List.mem_zipIdx_iff_getElem?] at hq
    obtain ⟨hjx, hqe⟩ := List.getElem?_eq_some_iff.mp hq
    have hj : q.2 < (decodeCNF x).length := by rwa [length_decodeCNF]
    refine ⟨q.2, hj, litOf p, ?_, hQ⟩
    rw [getElem_decodeCNF x q.2 hj]
    exact List.mem_map.mpr ⟨p, by rw [hqe]; exact hp, rfl⟩

/-! ### The label scheme of gadget certificates

Gadget programs on concrete SAT instances need fresh variables that cannot
collide with the input's, however it is labelled: original variables are
*doubled*, and a fresh variable tagged `(i, k)` in the mathematical layer gets
the *odd* label `2 * ⟨i, k⟩ + 1`. Parity separates the two families, and
`Nat.pair` keeps distinct tags apart — injectivity is all a certificate ever
needs of the scheme (`CNF.satisfiable_relabel`). -/

/-- The concrete face of doubling a literal's label, keeping its polarity. -/
def embedLit : Code LitTy LitTy :=
  .pair (.comp (.pair (.const .nat 2) .fst) .natMul) .snd

theorem embedLit_eval (p : LitTy.denote) : embedLit.eval p = (2 * p.1, p.2) := rfl

/-- The odd label realizing the tag `(i, k)`: `2 * ⟨i, k⟩ + 1`. -/
def oddLabel (i k : ℕ) : ℕ := 2 * Nat.pair i k + 1

/-- `oddLabel` as a program. -/
def oddVar : Code (.pair .nat .nat) .nat :=
  .comp (.pair (.comp (.pair (.const .nat 2) Code.natPair) .natMul) (.const .nat 1)) .natAdd

theorem oddVar_eval (i k : ℕ) : oddVar.eval (i, k) = oddLabel i k := by
  have h : oddVar.eval (i, k) = 2 * Code.natPair.eval (i, k) + 1 := rfl
  rw [h, natPair_eval]
  rfl

/-! ### Reading a literal out of a clause

The language has no indexing primitive, so `Code.listNth` filters the
enumeration down to the wanted position and returns the result as a
*one-element list* — empty when the position is out of range. That shape is
not a nuisance, it is the useful one: gadget programs assemble clauses by
concatenation, so a literal already wrapped in a list is ready to be appended,
and appending a default before reading position `0` is how a program takes a
`getD` (clients: `split3Code`, `naeCode`). -/

/-- The `k`-th literal of a clause, embedded (doubled label), as a one-element
list — empty if `k` is out of range. -/
def nthLit : Code (.pair ClauseTy .nat) ClauseTy :=
  .comp Code.listNth (.listMap embedLit)

/-- Reading the literal at an in-range position. -/
theorem nthLit_eval {d : ClauseTy.denote} {k : ℕ} (h : k < d.length) :
    nthLit.eval (d, k) = [embedLit.eval d[k]] := by
  have h1 : nthLit.eval (d, k) = (Code.listNth.eval (d, k)).map embedLit.eval := rfl
  rw [h1, listNth_eval h, List.map_cons, List.map_nil]

/-- Reading nothing at an out-of-range position. -/
theorem nthLit_eval_of_le {d : ClauseTy.denote} {k : ℕ} (h : d.length ≤ k) :
    nthLit.eval (d, k) = [] := by
  have h1 : nthLit.eval (d, k) = (Code.listNth.eval (d, k)).map embedLit.eval := rfl
  rw [h1, listNth_eval_of_le h, List.map_nil]

/-- The `k`-th literal of a clause, doubled, falling back on a fixed default
literal when the clause is shorter — the language's `getD`, built from `nthLit`
and the default. A gadget that pads a narrow clause with a literal it holds
false passes that literal here (`pad3`, in the mathematical layer). -/
def padLit (dflt : LitTy.denote) (k : ℕ) : Code (.pair ClauseTy .nat) ClauseTy :=
  .comp
    (.pair (Code.append (.comp (.pair .fst (.const .nat k)) nthLit)
      (.const ClauseTy [dflt])) (.const .nat 0))
    Code.listNth

/-- The padded literal `padLit` produces. -/
def padOf (dflt : LitTy.denote) (d : ClauseTy.denote) (k : ℕ) : LitTy.denote :=
  (d[k]?.map embedLit.eval).getD dflt

/-- **The padding is the language's `getD`**: appending the default to the
one-element list `nthLit` returns and reading position `0` of the result. -/
theorem padLit_eval (dflt : LitTy.denote) (k : ℕ) (d : ClauseTy.denote) (i : ℕ) :
    (padLit dflt k).eval (d, i) = [padOf dflt d k] := by
  have h : (padLit dflt k).eval (d, i)
      = Code.listNth.eval (nthLit.eval (d, k) ++ [dflt], 0) := rfl
  by_cases hk : k < d.length
  · rw [h, nthLit_eval hk, listNth_eval (by simp)]
    simp [padOf, List.getElem?_eq_getElem hk]
  · have hnone : d[k]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [h, nthLit_eval_of_le (by omega), listNth_eval (by simp)]
    simp [padOf, hnone]

/-! ### The variable list

A gadget with one component per *variable* indexes it by a list of labels. A
certificate need not use `cnfVars`: the abstract constructions are parametric
in the list and ask only that it *name every variable*, which frees the program
to use whatever its own deduplication produces.

Shared by every SAT gadget certificate that is indexed by variables, so it
lives here rather than in any one annex (clients: 3DM, 3-COLORABILITY). -/

/-- The variable labels of the formula, deduplicated. -/
def varsCode : Code SatTy (.list .nat) :=
  .comp (.comp .listJoin (.listMap .fst)) (Code.dedupBy .natEq)

/-- The variable list a certificate uses: the labels occurring anywhere in the
formula, deduplicated. -/
def vsOf (x : SatTy.denote) : List ℕ := (x.flatten.map Prod.fst).dedup

theorem varsCode_eval (x : SatTy.denote) : varsCode.eval x = vsOf x := by
  have h : varsCode.eval x = (Code.dedupBy .natEq).eval (x.flatten.map Prod.fst) := rfl
  rw [h, dedupBy_eval (fun _ _ ↦ rfl)]
  rfl

/-- The variable list has no duplicates — which is what makes a label's
position in it unique, and so `varSlot` a faithful naming. -/
theorem nodup_vsOf (x : SatTy.denote) : (vsOf x).Nodup := List.nodup_dedup _

/-- **The program's variable list is the mathematical layer's**, on the nose
and in the same order. A construction that indexes variables *positionally* —
relabeling into `Fin n` through `varSlot (cnfVars φ)` — needs exactly this:
membership would not be enough, since the certificate must reproduce each
variable's position, not merely its presence. -/
theorem cnfVars_decodeCNF (x : SatTy.denote) : cnfVars (decodeCNF x) = vsOf x := by
  rw [cnfVars_eq_dedup, vsOf, decodeCNF, ← List.map_flatten, List.map_map]
  rfl

/-- The variable list names every variable of the decoded formula — the one
hypothesis the abstract correctness theorems make about it. -/
theorem mem_vsOf (x : SatTy.denote) :
    ∀ c ∈ decodeCNF x, ∀ l : Literal ℕ, l ∈ c → l.var ∈ vsOf x := by
  intro c hc l hl
  have hc' : c ∈ x.map (List.map litOf) := hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
  exact List.mem_dedup.mpr
    (List.mem_map.mpr ⟨p, List.mem_flatten.mpr ⟨d, hd, hp⟩, rfl⟩)

/-! ### The slot of a variable

`varSlot` is the first position of a label in the variable list, or the dummy
slot when it is absent. The language has no `idxOf`: the enumeration is
filtered down to the matching positions, the dummy is appended as a default,
and the head is read off with `Code.listNth` (`listSum` turns the resulting
one-element list back into a number). -/

/-- Keep-or-drop against a wanted label in the environment: an enumerated
variable `(u, k)` contributes its position `k` when `u` is the wanted label. -/
def keepEq : Code (.pair .nat (.pair .nat .nat)) (.list .nat) :=
  .branch (.comp (.pair (.comp .snd .fst) .fst) .natEq)
    (.comp (.comp .snd .snd) .listSingle) (.const (.list .nat) [])

/-- The positions of a label in the variable list, in order. -/
def matchIdxs : Code (.pair (.list .nat) .nat) (.list .nat) :=
  .comp (.pair .snd (.comp .fst .listEnum)) (.comp (.listMapEnv keepEq) .listJoin)

/-- The slot of a variable label: its first position in the variable list, or
the dummy slot `n` when it does not occur there. -/
def slotOfCode : Code (.pair (.list .nat) .nat) .nat :=
  .comp
    (.pair
      (.comp (.pair matchIdxs (.comp (.comp .fst .listLen) .listSingle)) .listAppend)
      (.const .nat 0))
    (.comp Code.listNth .listSum)

theorem matchIdxs_eval (l : List ℕ) (v : ℕ) :
    matchIdxs.eval (l, v) = (l.zipIdx.filter fun q ↦ decide (q.1 = v)).map Prod.snd := by
  have h : matchIdxs.eval (l, v) =
      (l.zipIdx.map fun q ↦ if decide (q.1 = v) = true then [q.2] else []).flatten := rfl
  rw [h, flatten_map_ite_eq_map_filter]

/-- The head of the position list: the first occurrence of the label, or
nothing when it is absent. -/
theorem matchIdxs_head (l : List ℕ) (v : ℕ) : ∀ s : ℕ,
    (((l.zipIdx s).filter fun q ↦ decide (q.1 = v)).map Prod.snd)[0]?
      = if v ∈ l then some (s + l.idxOf v) else none := by
  induction l with
  | nil => intro s; simp
  | cons a t ih =>
    intro s
    rw [List.zipIdx_cons, List.filter_cons]
    by_cases ha : a = v
    · subst ha
      rw [if_pos (by simp), List.map_cons, List.getElem?_cons_zero,
        if_pos (List.mem_cons_self ..), List.idxOf_cons_self, Nat.add_zero]
    · rw [if_neg (by simp [ha]), ih (s + 1), List.idxOf_cons_ne _ ha]
      by_cases hv : v ∈ t
      · rw [if_pos hv, if_pos (List.mem_cons_of_mem _ hv)]
        exact congrArg some (by omega)
      · rw [if_neg hv, if_neg (by simp [hv, Ne.symm ha])]

/-- **The slot lookup is faithful**: the program computes `varSlot`, on the
nose and for every input — including labels absent from the list, which land on
the dummy slot exactly as `varSlot` prescribes. -/
theorem slotOfCode_eval (l : List ℕ) (v : ℕ) : slotOfCode.eval (l, v) = (varSlot l v).1 := by
  have hval : slotOfCode.eval (l, v) =
      (Code.listNth.eval (matchIdxs.eval (l, v) ++ [l.length], 0)).sum := rfl
  have hlen : 0 < (matchIdxs.eval (l, v) ++ [l.length]).length := by
    simp
  have hget : (matchIdxs.eval (l, v) ++ [l.length])[0]? = some (varSlot l v).1 := by
    have hhead := matchIdxs_head l v 0
    rw [← matchIdxs_eval] at hhead
    have hslot : (varSlot l v).1 = min (l.idxOf v) l.length := rfl
    by_cases hv : v ∈ l
    · rw [if_pos hv, Nat.zero_add] at hhead
      obtain ⟨a, t, hat⟩ : ∃ a t, matchIdxs.eval (l, v) = a :: t := by
        match hm : matchIdxs.eval (l, v) with
        | [] => rw [hm] at hhead; simp at hhead
        | a :: t => exact ⟨a, t, rfl⟩
      rw [hat] at hhead ⊢
      rw [List.getElem?_cons_zero] at hhead
      rw [List.cons_append, List.getElem?_cons_zero, hslot,
        Nat.min_eq_left (List.idxOf_lt_length_of_mem hv).le]
      exact hhead
    · rw [if_neg hv] at hhead
      have hnil : matchIdxs.eval (l, v) = [] := by
        match hm : matchIdxs.eval (l, v) with
        | [] => rfl
        | a :: t => rw [hm, List.getElem?_cons_zero] at hhead; exact absurd hhead (by simp)
      rw [hnil, List.nil_append, List.getElem?_cons_zero, hslot,
        List.idxOf_of_notMem hv, Nat.min_self]
  rw [hval, listNth_eval hlen, List.sum_singleton]
  exact Option.some_inj.mp ((List.getElem?_eq_getElem hlen).symm.trans hget)

/-! ### Indexing a flattened list of lists

A gadget indexed by literal *occurrences* names them by their position in the
flattened occurrence list. These two lemmas are what identify that position
with mathlib's `finSigmaFinEquiv`, the canonical bijection out of a sigma of
`Fin`s — and `CNF.Occ` is exactly such a sigma. -/

/-- Position `(∑ lengths before i) + j` of a flattened list of lists holds the
`j`-th element of the `i`-th block. -/
theorem flatten_getElem?_sum_take {α : Type*} :
    ∀ (L : List (List α)) (i : ℕ) (hi : i < L.length) (j : ℕ)
      (hj : j < (L[i]'hi).length),
      L.flatten[((L.map List.length).take i).sum + j]? = some ((L[i]'hi)[j]'hj) := by
  intro L
  induction L with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons c L ih =>
    intro i hi j hj
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hj ⊢
      simp only [List.map_cons, List.take_zero, List.sum_nil, Nat.zero_add,
        List.flatten_cons]
      rw [List.getElem?_append_left hj]
      exact List.getElem?_eq_getElem hj
    | succ i' =>
      simp only [List.getElem_cons_succ] at hj ⊢
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons, List.flatten_cons]
      rw [Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left]
      exact ih i' (Nat.lt_of_succ_lt_succ (by simpa using hi)) j hj

/-- The sum of an initial segment of a list of naturals, as a `Fin` sum (the
shape produced by `finSigmaFinEquiv_apply`). -/
theorem sum_take_eq_sum_fin :
    ∀ (n : ℕ) (l : List ℕ) (hn : n ≤ l.length),
      (l.take n).sum = ∑ k : Fin n, l[k.val]'(Nat.lt_of_lt_of_le k.isLt hn) := by
  intro n
  induction n with
  | zero => intro l _; simp
  | succ n ih =>
    intro l hn
    cases l with
    | nil => simp at hn
    | cons a l =>
      rw [List.take_succ_cons, List.sum_cons, ih l (Nat.le_of_succ_le_succ hn),
        Fin.sum_univ_succ]
      congr 1

/-! ### Occurrences, with their position data

A gadget indexed by literal *occurrences* needs more of each occurrence than
its literal. A *chained* gadget — 3-COLORABILITY, where each clause's
occurrences form a chain — needs to recognize the first and last occurrence of
a clause, and the language has no prefix-sum scan with which to recover a
clause's starting offset. Carrying the position within the clause and the
clause's width makes both tests pure arithmetic (`j = 0`, `j + 1 = width`).

`occPosList_getElem?_finSigma` is the bridge to the mathematical layer:
position `finSigmaFinEquiv o` of the list holds exactly occurrence `o`'s data.
`CNF.Occ` is a sigma of `Fin`s, so mathlib's canonical bijection out of such a
sigma *is* the occurrence numbering — no bespoke mixed-radix arithmetic is
needed, and injectivity comes free with it. -/

/-- A concrete occurrence with its position data:
`((clause index, position in clause), (clause width, literal))`. -/
abbrev OccPosTy : Ty := .pair (.pair .nat .nat) (.pair .nat LitTy)

/-- The occurrences of one enumerated clause `(c, i)`, with position data. -/
def occPosOfClause : Code (.pair ClauseTy .nat) (.list OccPosTy) :=
  .comp (.pair (.pair .snd (.comp .fst .listLen)) (.comp .fst .listEnum))
    (.listMapEnv
      (.pair (.pair (.comp .fst .fst) (.comp .snd .snd))
        (.pair (.comp .fst .snd) (.comp .snd .fst))))

/-- Every occurrence of the formula, clause by clause, with position data. -/
def occPos : Code SatTy (.list OccPosTy) :=
  .comp .listEnum (.comp (.listMap occPosOfClause) .listJoin)

/-- The clause blocks of the occurrence list. -/
def occPosBlocks (x : SatTy.denote) : List (List OccPosTy.denote) :=
  x.zipIdx.map fun p ↦ p.1.zipIdx.map fun q ↦ ((p.2, q.2), (p.1.length, q.1))

/-- The occurrence list `occPos` produces. -/
def occPosList (x : SatTy.denote) : List OccPosTy.denote := (occPosBlocks x).flatten

theorem occPos_eval (x : SatTy.denote) : occPos.eval x = occPosList x := rfl

theorem occPosBlocks_map_length (x : SatTy.denote) :
    (occPosBlocks x).map List.length = x.map List.length := by
  apply List.ext_getElem <;> simp [occPosBlocks]

theorem length_occPosList (x : SatTy.denote) :
    (occPosList x).length = (x.map List.length).sum := by
  rw [occPosList, List.length_flatten, occPosBlocks_map_length]

/-- **The occurrence numbering is faithful**: position `finSigmaFinEquiv o` of
the occurrence list holds occurrence `o`'s clause index, position, clause width
and literal. -/
theorem occPosList_getElem?_finSigma (x : SatTy.denote) (o : (decodeCNF x).Occ) :
    (occPosList x)[(finSigmaFinEquiv o : ℕ)]? =
      some ((o.1.val, o.2.val),
        (((decodeCNF x)[o.1.1]'o.1.isLt).length,
          (((decodeCNF x).occLit o).var, ((decodeCNF x).occLit o).polarity))) := by
  obtain ⟨i, j⟩ := o
  have hix : i.val < x.length := by
    rw [← length_decodeCNF]; exact i.isLt
  have hdec : (decodeCNF x)[i.val]'i.isLt = (x[i.val]'hix).map litOf :=
    getElem_decodeCNF x i.val i.isLt
  have hlen : ((decodeCNF x)[i.val]'i.isLt).length = (x[i.val]'hix).length := by
    rw [hdec, List.length_map]
  have hjx : j.val < (x[i.val]'hix).length := by
    rw [← hlen]; exact j.isLt
  have hLlen : i.val < (occPosBlocks x).length := by
    simpa [occPosBlocks] using hix
  have hblock : (occPosBlocks x)[i.val]'hLlen
      = (x[i.val]'hix).zipIdx.map fun q ↦ ((i.val, q.2), ((x[i.val]'hix).length, q.1)) := by
    simp [occPosBlocks]
  have hj' : j.val < ((occPosBlocks x)[i.val]'hLlen).length := by
    rw [hblock]; simpa using hjx
  have hkey := flatten_getElem?_sum_take (occPosBlocks x) i.val hLlen j.val hj'
  have hidx : (finSigmaFinEquiv (⟨i, j⟩ : (decodeCNF x).Occ) : ℕ)
      = (((occPosBlocks x).map List.length).take i.val).sum + j.val := by
    rw [finSigmaFinEquiv_apply]
    congr 1
    rw [occPosBlocks_map_length,
      sum_take_eq_sum_fin i.val (x.map List.length) (by simpa using hix.le)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [decodeCNF, List.getElem_map, List.length_map]
    exact congrArg List.length (getElem_congr rfl rfl _)
  have hlit : (decodeCNF x).occLit (⟨i, j⟩ : (decodeCNF x).Occ)
      = litOf ((x[i.val]'hix)[j.val]'hjx) := by
    have h : (decodeCNF x).occLit (⟨i, j⟩ : (decodeCNF x).Occ)
        = ((decodeCNF x)[i.val]'i.isLt)[j.val]'j.isLt := rfl
    rw [h]
    simp only [hdec, List.getElem_map]
  rw [hidx, occPosList, hkey, hlit]
  simp [hblock, litOf, hlen]

/-- The number of occurrences, in the `Finset.sum` shape `finSigmaFinEquiv`'s
target carries. -/
theorem length_occPosList_eq_sum (x : SatTy.denote) :
    (occPosList x).length
      = ∑ i : Fin (decodeCNF x).length, ((decodeCNF x)[i.1]'i.isLt).length := by
  have hn : (decodeCNF x).length ≤ (x.map List.length).length := by
    simp [length_decodeCNF]
  have h := sum_take_eq_sum_fin ((decodeCNF x).length) (x.map List.length) hn
  rw [List.take_of_length_le (by simp [length_decodeCNF])] at h
  rw [length_occPosList, h]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [decodeCNF]

namespace Concrete

/-- SAT on concrete instances. -/
def SAT : Problem SatTy.denote := Hardness.SAT.comap decodeSat

/-- 3SAT on concrete instances. Same encoding as `Concrete.SAT` — 3SAT is a
restriction of SAT on the same instance type, not a new instance type. -/
def SAT3 : Problem SatTy.denote := Hardness.SAT3.comap decodeSat

/-- Bounded-occurrence 3SAT on concrete instances. -/
def SAT3_OCC3 : Problem SatTy.denote := Hardness.SAT3_OCC3.comap decodeSat

/-- NAE-SAT on concrete instances. -/
def NAE_SAT : Problem SatTy.denote := Hardness.NAE_SAT.comap decodeSat

/-- NAE3SAT on concrete instances. The same encoding once more: not-all-equal
satisfiability asks a different *question* of a SAT instance, not a different
instance type. -/
def NAE_SAT3 : Problem SatTy.denote := Hardness.NAE_SAT3.comap decodeSat

/-- ONE-IN-THREE 3SAT on concrete instances. The same encoding once more:
exactly-one satisfiability asks a third question of a SAT instance, not a third
instance type. -/
def ONE_IN_THREE_SAT3 : Problem SatTy.denote := Hardness.ONE_IN_THREE_SAT3.comap decodeSat

/-- MONOTONE ONE-IN-THREE 3SAT on concrete instances. -/
def MONOTONE_ONE_IN_THREE_SAT3 : Problem SatTy.denote :=
  Hardness.MONOTONE_ONE_IN_THREE_SAT3.comap decodeSat

/-- Unfolding of `Concrete.SAT`. -/
theorem sat_iff (x : SatTy.denote) : SAT x ↔ (decodeCNF x).Satisfiable := Iff.rfl

/-- Unfolding of `Concrete.SAT3`: satisfiability of the decoded formula
together with the width bound, read off the concrete clause list. -/
theorem sat3_iff (x : SatTy.denote) :
    SAT3 x ↔ (∀ c ∈ x, c.length ≤ 3) ∧ (decodeCNF x).Satisfiable :=
  and_congr_left' (decodeSat_width_iff x)

/-- Unfolding of `Concrete.SAT3_OCC3`: the width window `[2, 3]` read off the
concrete clause list, the occurrence bound and satisfiability on the decoded
formula. -/
theorem sat3occ3_iff (x : SatTy.denote) :
    SAT3_OCC3 x ↔
      ((∀ c ∈ x, 2 ≤ c.length ∧ c.length ≤ 3)
        ∧ ∀ v, (decodeCNF x).varOccs v ≤ 3)
      ∧ (decodeCNF x).Satisfiable :=
  and_congr_left' (and_congr_left'
    (decodeSat_lengths_iff (P := fun m ↦ 2 ≤ m ∧ m ≤ 3) x))

/-- Unfolding of `Concrete.NAE_SAT3`: not-all-equal satisfiability of the
decoded formula together with the width condition, read off the concrete
clause list. -/
theorem nae3Sat_iff (x : SatTy.denote) :
    NAE_SAT3 x ↔ (∀ c ∈ x, c.length = 3) ∧ (decodeCNF x).NaeSatisfiable :=
  and_congr_left' (decodeSat_lengths_iff (P := (· = 3)) x)

/-- Unfolding of `Concrete.ONE_IN_THREE_SAT3`: exactly-one satisfiability of the
decoded formula together with the width condition, read off the concrete clause
list. -/
theorem oneInThree3Sat_iff (x : SatTy.denote) :
    ONE_IN_THREE_SAT3 x ↔ (∀ c ∈ x, c.length = 3) ∧ (decodeCNF x).OneSatisfiable :=
  and_congr_left' (decodeSat_lengths_iff (P := (· = 3)) x)

/-- Unfolding of `Concrete.MONOTONE_ONE_IN_THREE_SAT3`: positivity and the
width condition read off the concrete clause list, exactly-one satisfiability on
the decoded formula. -/
theorem monotoneOneInThree3Sat_iff (x : SatTy.denote) :
    MONOTONE_ONE_IN_THREE_SAT3 x ↔ (∀ c ∈ x, ∀ p ∈ c, p.2 = true)
      ∧ (∀ c ∈ x, c.length = 3) ∧ (decodeCNF x).OneSatisfiable :=
  and_congr (decodeSat_positive_iff x)
    (and_congr_left' (decodeSat_lengths_iff (P := (· = 3)) x))

end Concrete

/-! ### Certified weakening of the width restriction

3SAT is a `Problem.restrict`ion of SAT on the same instance type, so weakening
it is `CertifiedReduction.ofRestrict` with a program deciding the width. It
lives here rather than in any one annex because every reduction *from* 3SAT
composes through it. -/

/-- The width test: no clause of width four or more. -/
def sat3Test : Code SatTy .bool :=
  .comp (.listFilter (.comp (.pair (.const .nat 4) .listLen) .natLe))
    (.comp .listLen (.comp (.pair .id (.const .nat 0)) .natEq))

/-- `sat3Test` decides the width restriction of `Concrete.SAT3`. -/
theorem sat3Test_eval_true (x : SatTy.denote) :
    sat3Test.eval x = true ↔ ∀ c ∈ decodeCNF x, c.length ≤ 3 := by
  have h : sat3Test.eval x
      = decide ((x.filter fun c ↦ decide (4 ≤ c.length)).length = 0) := rfl
  rw [h, decide_eq_true_iff, List.length_eq_zero_iff, List.filter_eq_nil_iff,
    decodeSat_lengths_iff (P := (· ≤ 3))]
  constructor
  · intro hf c hc
    have := hf c hc
    simp only [decide_eq_true_eq] at this
    omega
  · intro hf c hc
    simp only [decide_eq_true_eq]
    have := hf c hc
    omega

/-- 3SAT weakens to SAT, certifiedly: test the width, and send offenders to
the fixed unsatisfiable no-instance `[[]]`. -/
def sat3ToSatCertified : CertifiedReduction Concrete.SAT3 Concrete.SAT :=
  CertifiedReduction.ofRestrict
    (R := fun x ↦ ∀ c ∈ (decodeSat x).φ, c.length ≤ 3)
    sat3Test sat3Test_eval_true [[]]
    (fun h ↦ CNF.not_satisfiable_of_nil_mem (List.mem_singleton_self _) h)

end Cert
end Hardness


