-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Tabulate
-- name    : MIPRE_Foundations_Halting_Tabulate
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:42:17.065233+00:00
-- url     : https://prove2.me/theorems/d2ed562b-6ba6-445e-ac79-f019869fdf33
-- title:
--   Deciding acceptance under a time bound, and tabulating the game a string denotes as a `GameData`
-- statement:
--   Let `runForD pd x k` be the budgeted run of the program encoded by `pd` on `x` within cost `k`, `bitStrsOfLen s` and `bitStrsLE T` the bit strings by length, `toBits` the bits of a vector, `questionEquiv s` the question indexing, and `GameData = (nX, nA, w, acc)` a game description.
--
--   Budgets. `MIPRE.Decider.acceptBudget T k x y a b := T * ((encode (x, y, a, b)).size + 1) ^ k`; `MIPRE.CL.Sampler.queryUnder S T k n q` runs the sampler on `(n, q)` under `T * ((encode q).size + 1) ^ k` via `runForD`.
--
--   Indexing (`MIPRE.Verifier`). `bitsToIdx : BitStr → ℕ` reads a string as a binary number, least significant bit first; by `questionEquiv_symm_val`,
--
--   $$\big((\mathrm{questionEquiv}\ s)^{-1}\, v : \mathbb{N}\big) = \mathrm{bitsToIdx}\,(\mathrm{toBits}\ v) \qquad (v : \mathbb{F}_2^{\,s}).$$
--
--   `tagIdx (p : Bool × (Fin s → 𝔽₂)) : Fin (2 ^ (s + 1))` is `bitsToIdx (p.1 :: toBits p.2)`, and `tagEquiv s : Bool × (Fin s → 𝔽₂) ≃ Fin (2 ^ (s + 1))` is `tagIdx` as a bijection. `weightList s fA fB := (bitStrsOfLen s).map fun z => (fA z, fB z, 1)`; `tuples s T` is the product of two copies each of `bitStrsOfLen s` and `bitStrsLE T`; `accListW s T fA fB acc?` lists `(fA x, fB y, idxOf a, idxOf b)` over the tuples with `acc? x y a b = true`.
--
--   From encoded programs (`MIPRE.Halting`). `dimOf sd B k n` and `margOf sd B k n w z` read the dimension query and the query `marginal w 7 z` under the budget `B * (|q| + 1) ^ k`, as a number and a bit string (defaults $0$, `[]`); `accOf pd n x y a b := decide (runForD pd (encode (n, x, y, a, b)) (acceptBudget (n ^ n) n x y a b) = some (encode true))`; `tabOf sd pd s T B k n : GameData`: `nX = 2 ^ (s + 1) - 1`, `nA = (bitStrsLE T).length - 1`, `w` the `weightList s` of the two marginals with `false` (Alice) and `true` (Bob) prepended, `acc` the `accListW s T` with the same tags and `accOf pd n`.
--
--   Lemmas: `queryUnder_eq`, `queryUnder_dimension`, `primrec_encode_marginal`; `bitsToIdx_nil`/`_cons`/`_ofFn`/`_lt`/`_injOn`/`_cons_toBits_inj`/`_toBits_questionEquiv`, `toBits_injective`, `tagIdx_injective`, `tagEquiv_apply`, `accListW_eq_filterMap`; `Primrec` lemmas for `bitsToIdx`, tagging, `tuples`, `accListW`, `dimOf`, `margOf`, the weight list.
--
--   **Formalization Note**. The two question blocks are disjoint and the diagonal carries no weight. `accOf` keeps the budget $n$-boundedness supplies and uses `decide (… = some …)` rather than `==`. `tabOf` is plain data, not a `Verifier`. `accOf_iff` and `primrec_tabOf` are not in this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Tabulate.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Tabulate.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Theorems.Thm_MIPRE_Cost_Eval_deterministic

/-!
# Deciding acceptance under a time bound

The first half of obligation **O2** (blueprint `rem:compression-abstract`, item 3): the
acceptance table of the tabulated game. Filling it in needs `Decider.Accepts` — a `Σ₁`
statement, `∃ t, prog.Runs …` — to be *decided*, and that is exactly what `n`-boundedness
buys: the bound supplies a budget within which the decider must halt, so one budgeted run
settles the question (`Machine.runForD`).

* `Decider.acceptBudget`: the budget `T · (|d| + 1) ^ k` the bound gives at index `n` on the
  tuple `(x, y, a, b)`, read off the shape of `Decider.TimeBoundAt`.
* `Decider.accepts_iff_runForD`: for a decider obeying that bound, acceptance is one budgeted
  run returning `encode true`.
* `Decider.decidableAccepts` and `Verifier.decidableAccepts`: the resulting decision
  procedures, and `Verifier.accepts_iff_runForD` for the verifier a string denotes, where the
  bound comes from `Verifier.IsBounded`.

The other half of the tabulation is the question distribution, and the rest of this file is
what a `GameData` needs for it. `CL.Sampler.queryUnder` runs one sampler query under the same
kind of budget; `Verifier.bitsToIdx` turns the bit string a query returns into the number a
`GameData` names its questions by, and agrees with `Verifier.questionEquiv`; and
`Verifier.weightList` is the weight list itself — one entry of weight `1` for each point of
`𝔽₂^{s(n)}`, at the index pair its two marginals land on. Its `questionWeight` is then the
number of points landing on a given pair and its `totalWeight` is `2 ^ s(n)`, which is exactly
the quotient `CL.clDist` is: `length_filter_bitStrsOfLen` is the bridge, the bit strings of
length `s` being the vectors of `𝔽₂^s`.

`Verifier.answerEquiv_symm_val` is the same service on the answer side: an answer's index is
its position among the bit strings of length at most `T`, the enumeration `answerList` being
`bitStrsLE` mapped by a truncation that is the identity on them.

`Verifier.accListW` is then the acceptance table: the index tuples of the answer tuples a
predicate accepts, enumerated over the two alphabets, with `mem_accListW_iff` saying exactly
what is in it. It takes the two question indexings `fA`, `fB` as parameters, because the
tabulation tags Alice's question differently from Bob's; `Verifier.accList` is the case
`fA = fB = bitsToIdx` and is the same list definitionally (`accList_eq_accListW`), so nothing
downstream of the old name changed. `bitsToIdx_injOn` is what lets a tuple be read back — the
index of a question determines it, among the strings of a fixed length — and `tagEquiv` is the
tagged alphabet it supports: a tag bit and a point of `𝔽₂^s` packed into one index by
*prepending* the tag, so that `bitsToIdx_lt` and `bitsToIdx_injOn` apply verbatim at `s + 1`.

`MIPRE.Halting.tabOf` at the end assembles all of it: the `GameData` two encoded programs and
five numbers describe, with `primrec_tabOf` its computability. Plain data and not a verifier,
because a `Verifier` is a structure carrying proofs and so is not the sort of thing a `Primrec`
statement can mention; the bridge back to the verifier those parameters came from is in
`Halting/Instantiation.lean`.

Nothing here is efficient and nothing needs to be: the tabulation is a computable map, not a
polynomial-time one. The budget is not one number: the two sampler runs take theirs as the
parameters `B`, `k`, so that a caller can pass the sampler's own time bound, while `accOf`
alone runs at the `n ^ n` that the verifier's `n`-boundedness supplies.
-/

namespace MIPRE

open Cost
open HaltingGameValue (GameData)

namespace Decider

variable (D : Decider)

/-- The budget the time bound `TimeBoundAt n T k` gives on the tuple `(x, y, a, b)`: the
decider's input is `cons (encode n) (encode (x, y, a, b))`, and the bound is `T` times the
`k`-th power of one more than the size of the second component. -/
def acceptBudget (T k : ℕ) (x y a b : BitStr) : ℕ :=
  T * ((encode (x, y, a, b) : Data).size + 1) ^ k

end Decider

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

end Verifier

/-! ## Sampler queries under the budget -/

namespace CL.Sampler

variable {ℓ : ℕ} (S : CL.Sampler ℓ)

/-- One query to the sampler, run under the budget its time bound supplies. The sampler is
required to halt on *every* input of the form `(n, …)`, so this is total wherever the bound
holds. -/
def queryUnder (T k n : ℕ) (q : Query) : Option Data :=
  Machine.runForD (encode S.prog) (encode (n, q)) (T * ((encode q : Data).size + 1) ^ k)

/-- Under the bound, a budgeted query returns exactly what the sampler's correctness clauses
say it returns. -/
theorem queryUnder_eq {n T k : ℕ} (hb : S.TimeBoundAt n T k) {q : Query} {r : Data} {t : ℕ}
    (h : S.prog.Runs (encode (n, q)) r t) : S.queryUnder T k n q = some r := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb (encode q)
  obtain ⟨rfl, -⟩ := h₀.deterministic h
  exact Machine.runForD_eq_some h₀ ht₀

/-- The dimension query. -/
theorem queryUnder_dimension {n T k : ℕ} (hb : S.TimeBoundAt n T k) :
    S.queryUnder T k n Query.dimension = some (encode (S.dim n)) :=
  let ⟨_, h⟩ := S.runs_dimension n; S.queryUnder_eq hb h

/-- A marginal query with the player and the level fixed is a primitive recursive function of
the point queried: a query is its tuple, encoded, and `marginal w j z` is `(1, w, j, z, [])`,
so with `w` and `j` literal only `encode z` varies. -/
theorem primrec_encode_marginal (w : Player) (j : ℕ) :
    Primrec fun z : BitStr => (encode (Query.marginal w j z) : Data) := by
  have h : ∀ z : BitStr, (encode (Query.marginal w j z) : Data)
      = Data.cons (encode (1 : ℕ)) (Data.cons (encode w)
          (Data.cons (encode j) (Data.cons (encode z) (encode ([] : BitStr))))) := fun _ => rfl
  refine (Data.primrec_cons.comp (Primrec.const _)
    (Data.primrec_cons.comp (Primrec.const _)
      (Data.primrec_cons.comp (Primrec.const _)
        (Data.primrec_cons.comp Cost.primrec_encode_bitStr (Primrec.const _))))).of_eq
    fun z => (h z).symm

end CL.Sampler

/-! ## Questions as numbers -/

namespace Verifier

/-- The index of a bit string: the number whose binary digits it is, least significant first.
This is the `ℕ`-level form of `Verifier.questionEquiv`, and it is what the tabulation can
actually compute with — the question alphabet of a `GameData` is `Fin (nX + 1)`, so every
question reached by a sampler query has to be turned into a number. -/
def bitsToIdx : BitStr → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * bitsToIdx l

@[simp] theorem bitsToIdx_nil : bitsToIdx [] = 0 := rfl

@[simp] theorem bitsToIdx_cons (b : Bool) (l : BitStr) :
    bitsToIdx (b :: l) = (if b then 1 else 0) + 2 * bitsToIdx l := rfl

theorem bitsToIdx_ofFn {s : ℕ} (f : Fin s → Bool) :
    bitsToIdx (List.ofFn f) = ∑ i : Fin s, (if f i then 1 else 0) * 2 ^ (i : ℕ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [List.ofFn_succ, bitsToIdx_cons, ih, Fin.sum_univ_succ, Finset.mul_sum]
    refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun i _ => ?_)
    rw [Fin.val_succ, pow_succ]
    ring

/-- The `Fin 2` form, where `finFunctionFinEquiv` is literally applicable: `CL.𝔽₂` is `ZMod 2`,
which reduces to `Fin 2` but does not unify with it at the transparency `rw` uses. -/
theorem bitsToIdx_ofFn_fin2 {s : ℕ} (w : Fin s → Fin 2) :
    bitsToIdx (List.ofFn fun i => decide (w i = 1)) = (finFunctionFinEquiv w : ℕ) := by
  rw [bitsToIdx_ofFn, finFunctionFinEquiv_apply]
  refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ rfl
  revert i
  suffices h : ∀ a : Fin 2, (if decide (a = 1) then 1 else 0) = (a : ℕ) from fun i _ => h (w i)
  decide

/-- **The index of a question is the number its bit string denotes.** This is what lets the
tabulation name questions by numbers while the value agreement is read along
`questionEquiv`. -/
@[simp] theorem questionEquiv_symm_val {s : ℕ} (v : Fin s → CL.𝔽₂) :
    (((questionEquiv s).symm v : Fin (2 ^ s)) : ℕ) = bitsToIdx (CL.toBits v) :=
  (bitsToIdx_ofFn_fin2 v).symm

@[simp] theorem bitsToIdx_toBits_questionEquiv {s : ℕ} (i : Fin (2 ^ s)) :
    bitsToIdx (CL.toBits (questionEquiv s i)) = (i : ℕ) := by
  rw [← questionEquiv_symm_val, Equiv.symm_apply_apply]

/-! ## The question weights -/

/-- The index of a bit string is below `2 ^ its length`. -/
theorem bitsToIdx_lt (l : BitStr) : bitsToIdx l < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih => rw [bitsToIdx_cons, List.length_cons, pow_succ]; split <;> omega

theorem primrec_bitsToIdx : Primrec bitsToIdx := by
  have key : ∀ l : BitStr, bitsToIdx l = l.foldr (fun b m => (if b then 1 else 0) + 2 * m) 0 := by
    intro l; induction l with
    | nil => rfl
    | cons b l ih => rw [bitsToIdx_cons, ih, List.foldr_cons]
  have h1 : Primrec fun q : BitStr × (Bool × ℕ) => (if q.2.1 then 1 else 0) + 2 * q.2.2 :=
    Primrec.nat_add.comp
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) h1.to₂).of_eq fun l => (key l).symm

/-- **The weight list of a tabulation**: one entry of weight `1` for each point of `𝔽₂^s`, at
the index pair its two marginals land on. -/
def weightList (s : ℕ) (fA fB : BitStr → ℕ) : List (ℕ × ℕ × ℕ) :=
  (Data.bitStrsOfLen s).map fun z => (fA z, fB z, 1)

/-! ## Answers as numbers -/

/-! ## The acceptance table -/

/-- `bitsToIdx` is injective on the bit strings of a fixed length: it is the binary expansion,
read through `questionEquiv`. -/
theorem bitsToIdx_injOn {s : ℕ} {x y : BitStr} (hx : x.length = s) (hy : y.length = s)
    (h : bitsToIdx x = bitsToIdx y) : x = y := by
  have hx' : CL.toBits (CL.ofBits s x) = x := CL.toBits_ofBits hx
  have hy' : CL.toBits (CL.ofBits s y) = y := CL.toBits_ofBits hy
  have := h
  rw [← hx', ← hy', ← questionEquiv_symm_val, ← questionEquiv_symm_val] at this
  rw [← hx', ← hy', (questionEquiv s).symm.injective (Fin.ext this)]

/-! ## The doubled question alphabet, indexed

A question of the doubled game is a tag bit and a point of `𝔽₂^s`. It is packed into one
number by **prepending the tag bit to the point's bit string**: the index of `(b, v)` is
`bitsToIdx (b :: CL.toBits v)`. Three things this packing buys, and they are the reason for
it:

* the packed index is `bitsToIdx` of a bit string of length `s + 1`, so `bitsToIdx_lt` bounds
  it by `2 ^ (s + 1)` and `bitsToIdx_injOn` — injectivity on strings of a *fixed length* —
  reads it back, both verbatim at `s + 1`;
* Alice's indices are even and Bob's odd, so the two copies are automatically disjoint;
* nothing else in the tabulation changes: the weight list still enumerates `𝔽₂^s`.
-/

/-- `CL.toBits` is injective: it is the binary expansion read by `questionEquiv`. -/
theorem toBits_injective (s : ℕ) :
    Function.Injective (CL.toBits (s := s)) := by
  intro v w h
  refine (questionEquiv s).symm.injective (Fin.ext ?_)
  rw [questionEquiv_symm_val, questionEquiv_symm_val, h]

/-- **The packing is injective, componentwise.** This is `bitsToIdx_injOn` at length `s + 1`,
which is why the tag is *prepended* rather than appended or added as an offset. -/
theorem bitsToIdx_cons_toBits_inj {s : ℕ} {b c : Bool} {v w : Fin s → CL.𝔽₂}
    (h : bitsToIdx (b :: CL.toBits v) = bitsToIdx (c :: CL.toBits w)) : b = c ∧ v = w := by
  have hlen : ∀ (d : Bool) (u : Fin s → CL.𝔽₂), (d :: CL.toBits u).length = s + 1 := by
    intro d u; simp
  obtain ⟨hb, hv⟩ := List.cons_eq_cons.mp (bitsToIdx_injOn (hlen b v) (hlen c w) h)
  exact ⟨hb, toBits_injective s hv⟩

/-- The packed index of a tagged question. -/
def tagIdx {s : ℕ} (p : Bool × (Fin s → CL.𝔽₂)) : Fin (2 ^ (s + 1)) :=
  ⟨bitsToIdx (p.1 :: CL.toBits p.2), by simpa using bitsToIdx_lt (p.1 :: CL.toBits p.2)⟩

theorem tagIdx_injective (s : ℕ) : Function.Injective (tagIdx (s := s)) := by
  rintro ⟨b, v⟩ ⟨c, w⟩ h
  obtain ⟨hb, hv⟩ := bitsToIdx_cons_toBits_inj (congrArg Fin.val h)
  exact Prod.ext hb hv

/-- **The doubled question alphabet.** -/
noncomputable def tagEquiv (s : ℕ) : Bool × (Fin s → CL.𝔽₂) ≃ Fin (2 ^ (s + 1)) :=
  Equiv.ofBijective tagIdx
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨tagIdx_injective s, by
      simp [Fintype.card_prod, pow_succ, mul_comm]⟩)

@[simp] theorem tagEquiv_apply (s : ℕ) (p : Bool × (Fin s → CL.𝔽₂)) :
    ((tagEquiv s p : Fin (2 ^ (s + 1))) : ℕ) = bitsToIdx (p.1 :: CL.toBits p.2) := rfl

/-! ## The acceptance table is primitive recursive

Written as four nested `Primrec.list_flatMap` the proof diverges at `whnf`: each body carries
the accumulated parameter tuple and unification grows with it. Flattening the product *first*
makes every `flatMap` body a bare tuple constructor, and the table is then one `filterMap` over
the flat list (`accList_eq_filterMap`) — with `Verifier.accList` itself unchanged.
-/

/-- The four-fold product of the two enumerations, as one flat list. -/
def tuples (s T : ℕ) : List (BitStr × BitStr × BitStr × BitStr) :=
  (Data.bitStrsOfLen s).flatMap fun x =>
    (Data.bitStrsOfLen s).flatMap fun y =>
      (Data.bitStrsLE T).flatMap fun a =>
        (Data.bitStrsLE T).map fun b => (x, y, a, b)

theorem primrec_tuples : Primrec₂ tuples := by
  have h4 : Primrec fun q : ((((ℕ × ℕ) × BitStr) × BitStr) × BitStr) =>
      (Data.bitStrsLE q.1.1.1.2).map fun b => (q.1.1.2, q.1.2, q.2, b) := by
    refine Primrec.list_map
      (Data.primrec_bitStrsLE.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      ?_
    have hx : Primrec fun r : ((((ℕ × ℕ) × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.1.1.2 := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hy : Primrec fun r : ((((ℕ × ℕ) × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have ha : Primrec fun r : ((((ℕ × ℕ) × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.2 := Primrec.snd.comp Primrec.fst
    exact (hx.pair (hy.pair (ha.pair Primrec.snd))).to₂
  have h3 : Primrec fun q : (((ℕ × ℕ) × BitStr) × BitStr) =>
      (Data.bitStrsLE q.1.1.2).flatMap fun a =>
        (Data.bitStrsLE q.1.1.2).map fun b => (q.1.2, q.2, a, b) :=
    Primrec.list_flatMap
      (Data.primrec_bitStrsLE.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) h4.to₂
  have h2 : Primrec fun q : ((ℕ × ℕ) × BitStr) =>
      (Data.bitStrsOfLen q.1.1).flatMap fun y =>
        (Data.bitStrsLE q.1.2).flatMap fun a =>
          (Data.bitStrsLE q.1.2).map fun b => (q.2, y, a, b) :=
    Primrec.list_flatMap (Data.primrec_bitStrsOfLen.comp (Primrec.fst.comp Primrec.fst)) h3.to₂
  exact (Primrec.list_flatMap (Data.primrec_bitStrsOfLen.comp Primrec.fst) h2.to₂).to₂

def accListW (s T : ℕ) (fA fB : BitStr → ℕ)
    (acc? : BitStr → BitStr → BitStr → BitStr → Bool) : List (ℕ × ℕ × ℕ × ℕ) :=
  (Data.bitStrsOfLen s).flatMap fun x =>
    (Data.bitStrsOfLen s).flatMap fun y =>
      (Data.bitStrsLE T).flatMap fun a =>
        (Data.bitStrsLE T).filterMap fun b =>
          if acc? x y a b then
            some (fA x, fB y, (Data.bitStrsLE T).idxOf a, (Data.bitStrsLE T).idxOf b)
          else none

theorem accListW_eq_filterMap (s T : ℕ) (fA fB : BitStr → ℕ)
    (acc? : BitStr → BitStr → BitStr → BitStr → Bool) :
    accListW s T fA fB acc? = (tuples s T).filterMap fun q =>
      if acc? q.1 q.2.1 q.2.2.1 q.2.2.2 then
        some (fA q.1, fB q.2.1,
          (Data.bitStrsLE T).idxOf q.2.2.1, (Data.bitStrsLE T).idxOf q.2.2.2)
      else none := by
  simp only [accListW, tuples, List.filterMap_flatMap, List.filterMap_map, Function.comp_def]

theorem primrec_accListW {α : Type*} [Primcodable α] {s T : α → ℕ} {fA fB : BitStr → ℕ}
    {acc? : α → BitStr → BitStr → BitStr → BitStr → Bool}
    (hs : Primrec s) (hT : Primrec T) (hfA : Primrec fA) (hfB : Primrec fB)
    (hacc : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      acc? q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :
    Primrec fun a => Verifier.accListW (s a) (T a) fA fB (acc? a) := by
  have hbl : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Data.bitStrsLE (T q.1) := Data.primrec_bitStrsLE.comp (hT.comp Primrec.fst)
  have hbody : Primrec₂ fun (a : α) (q : BitStr × BitStr × BitStr × BitStr) =>
      (if acc? a q.1 q.2.1 q.2.2.1 q.2.2.2 then
        some (fA q.1, fB q.2.1,
          (Data.bitStrsLE (T a)).idxOf q.2.2.1, (Data.bitStrsLE (T a)).idxOf q.2.2.2)
        else none) := by
    refine Primrec.ite ⟨inferInstance, hacc.of_eq fun q => by
        cases h : acc? q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 <;> simp [h]⟩ ?_ (Primrec.const none)
    refine Primrec.option_some.comp
      ((hfA.comp (Primrec.fst.comp Primrec.snd)).pair
        ((hfB.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
          ((Cost.primrec_idxOf_bitStr.comp
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hbl).pair
            (Cost.primrec_idxOf_bitStr.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hbl))))
  exact (Primrec.listFilterMap (primrec_tuples.comp hs hT) hbody).of_eq fun a =>
    (accListW_eq_filterMap (s a) (T a) fA fB (acc? a)).symm

/-- Prepending a fixed tag bit is primitive recursive. -/
theorem primrec_tagIdxOf (b : Bool) : Primrec fun z : BitStr => bitsToIdx (b :: z) :=
  primrec_bitsToIdx.comp (Primrec.list_cons.comp (Primrec.const b) Primrec.id)

end Verifier

/-! ## The tabulation on parameters alone

`tabOf sd pd s T B k n` is the `GameData` seven parameters describe: `sd` the encoded sampler
program, `pd` the encoded decider program, `s` the sampler's dimension at level `n`, `T` the
answer-length cut, `B` and `k` the coefficient and the degree of the budget the two sampler
runs get, and `n` the level itself. Nothing here mentions a `Verifier`, and that is
the point — a `Verifier` is a structure carrying proofs, so a function of one is not data,
while `Primrec` needs its input to be. The bridge back, that these parameters compute the
verifier's own sampler and decider, is `MIPRE.Halting.dimOf_eq`, `margOf_eq` and `accOf_iff`
in `Halting/Instantiation.lean` — the first two at every string and every level, the third on
an `n`-bounded verifier.

The three components each run one program under a budget, and the budgets differ: `dimOf` and
`margOf` one sampler query each (`CL.Sampler.queryUnder` at the `B * (|q| + 1) ^ k` passed in,
which the caller takes from the sampler's own time bound), `accOf` one decider run
(`Decider.acceptBudget` at `T = n ^ n`, `k = n`, the budget `n`-boundedness supplies — see
`accOf`, which cannot be re-budgeted and says why). Each defaults — to `0`, `[]`, `false` — when
the budget is missed or the answer does not decode, which is what makes them total; where the
budget is the right one the default is never taken.

The questions are *doubled*: Alice's index is her marginal's bit string with a `false` tag
prepended, Bob's with a `true` tag, so `nX + 1 = 2 ^ (s + 1)` and the acceptance table is
`Verifier.accListW` at those two indexings rather than `accList`. The packing is the section
"The doubled question alphabet, indexed" above; why the doubling is needed at all is in
`Foundations/GameDouble.lean`.
-/

namespace Halting

def dimOf (sd : Data) (B k n : ℕ) : ℕ :=
  ((Machine.runForD sd (encode (n, CL.Sampler.Query.dimension))
      (B * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ k)).bind
    fun d => (SizedEncoding.decode d : Option ℕ)).getD 0

/-- Player `w`'s marginal question at the point `z`, under the budget `B * (|q| + 1) ^ k`. -/
def margOf (sd : Data) (B k n : ℕ) (w : Player) (z : BitStr) : BitStr :=
  ((Machine.runForD sd (encode (n, CL.Sampler.Query.marginal w 7 z))
      (B * ((encode (CL.Sampler.Query.marginal w 7 z) : Data).size + 1) ^ k)).bind
    fun d => (SizedEncoding.decode d : Option BitStr)).getD []

/-- Acceptance, from the encoded decider program alone. Unlike the two sampler runs this one
cannot be re-budgeted off `GapCompression.sampler_time`: the decider of the verifier a string
denotes is the string's *own*, wrapped, and nothing bounds it unconditionally. So `accOf` keeps
the budget `n`-boundedness supplies, and `MIPRE.Halting.accOf_iff` keeps its hypothesis.

`decide (… = some …)` rather than `… == some …`: the `BEq` a `==` elaborates to here is not the
one `Primrec.eq` is stated at, and reconciling them is a long detour for no gain. -/
def accOf (pd : Data) (n : ℕ) (x y a b : BitStr) : Bool :=
  decide (Machine.runForD pd (encode (n, x, y, a, b))
    (Decider.acceptBudget (n ^ n) n x y a b) = some (encode true))

/-- **The tabulation**, doubled and re-budgeted.  Alice's question index is her marginal's bit
string with a `false` tag prepended, Bob's with a `true` tag: the two blocks are disjoint and
the diagonal carries no weight.  The weight list still enumerates `𝔽₂^s` once, so the total
weight is still `2 ^ s`. -/
def tabOf (sd pd : Data) (s T B k n : ℕ) : GameData where
  nX := 2 ^ (s + 1) - 1
  nA := (Data.bitStrsLE T).length - 1
  w := Verifier.weightList s
        (fun z => Verifier.bitsToIdx (false :: margOf sd B k n .alice z))
        (fun z => Verifier.bitsToIdx (true :: margOf sd B k n .bob z))
  acc := Verifier.accListW s T (fun u => Verifier.bitsToIdx (false :: u))
          (fun v => Verifier.bitsToIdx (true :: v)) (accOf pd n)

theorem primrec_dimOf {α : Type*} [Primcodable α] {sd : α → Data} {B lvl : α → ℕ} (k : ℕ)
    (hsd : Primrec sd) (hB : Primrec B) (hlvl : Primrec lvl) :
    Primrec fun a : α => dimOf (sd a) (B a) k (lvl a) := by
  have hbudget : Primrec fun a : α =>
      B a * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ k :=
    Primrec.nat_mul.comp hB (primrec_nat_pow.comp (Primrec.const _) (Primrec.const k))
  have hinput : Primrec fun a : α => (encode (lvl a, CL.Sampler.Query.dimension) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp hlvl)
      (Primrec.const (encode CL.Sampler.Query.dimension : Data))
  exact Primrec.option_getD.comp
    (Primrec.option_bind (Machine.primrec_runForD.comp ((hsd.pair hinput).pair hbudget))
      (Data.primrec_decode_nat.comp Primrec.snd).to₂)
    (Primrec.const 0)

theorem primrec_margOf {α : Type*} [Primcodable α] {sd : α → Data} {B lvl : α → ℕ} (k : ℕ)
    (hsd : Primrec sd) (hB : Primrec B) (hlvl : Primrec lvl) (w : Player) :
    Primrec fun q : α × BitStr => margOf (sd q.1) (B q.1) k (lvl q.1) w q.2 := by
  have hq : Primrec fun q : α × BitStr =>
      (encode (CL.Sampler.Query.marginal w 7 q.2) : Data) :=
    (CL.Sampler.primrec_encode_marginal w 7).comp Primrec.snd
  have hinput : Primrec fun q : α × BitStr =>
      (encode (lvl q.1, CL.Sampler.Query.marginal w 7 q.2) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp (hlvl.comp Primrec.fst)) hq
  have hbudget : Primrec fun q : α × BitStr =>
      B q.1 * ((encode (CL.Sampler.Query.marginal w 7 q.2) : Data).size + 1) ^ k :=
    Primrec.nat_mul.comp (hB.comp Primrec.fst)
      (primrec_nat_pow.comp (Primrec.succ.comp (Data.primrec_size.comp hq)) (Primrec.const k))
  exact Primrec.option_getD.comp
    (Primrec.option_bind
      (Machine.primrec_runForD.comp (((hsd.comp Primrec.fst).pair hinput).pair hbudget))
      (Data.primrec_decode_bitStr.comp Primrec.snd).to₂)
    (Primrec.const [])

/-- The weight list of the doubled, re-budgeted tabulation.  `Verifier.weightList` itself is
untouched: only the two index maps it is applied to have changed. -/
theorem primrec_weightList {α : Type*} [Primcodable α] {sd : α → Data} {s B lvl : α → ℕ}
    (k : ℕ) (hsd : Primrec sd) (hs : Primrec s) (hB : Primrec B) (hlvl : Primrec lvl) :
    Primrec fun a : α =>
      Verifier.weightList (s a)
        (fun z => Verifier.bitsToIdx (false :: margOf (sd a) (B a) k (lvl a) .alice z))
        (fun z => Verifier.bitsToIdx (true :: margOf (sd a) (B a) k (lvl a) .bob z)) := by
  refine Primrec.list_map (Data.primrec_bitStrsOfLen.comp hs) ?_
  exact (((Verifier.primrec_tagIdxOf false).comp
      (primrec_margOf k hsd hB hlvl Player.alice)).pair
    (((Verifier.primrec_tagIdxOf true).comp
      (primrec_margOf k hsd hB hlvl Player.bob)).pair (Primrec.const 1))).to₂

end Halting

end MIPRE


