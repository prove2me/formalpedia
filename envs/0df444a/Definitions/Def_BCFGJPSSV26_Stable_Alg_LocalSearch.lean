-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
-- name    : BCFGJPSSV26_Stable_Alg_LocalSearch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:57:38.417731+00:00
-- url     : https://prove2.me/theorems/82f790c7-b712-4c05-93de-2cc0c4310d61
-- title:
--   BCFGJPSSV26.Stable.Alg.LocalSearch — The local search
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.LocalSearch` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The deterministic local search of [BCFGJPSSV26b, Section 3] with swaps of size `p = 24 N` and the
--   approximate stopping rule of [BCFGJPSSV26b, Theorem 3.6] (`BCFGJPSSV26.Stable.localSearch`): start
--   from the facilities `0, …, k - 1`; as long as some swap of at most `p` facilities lowers the exact
--   cost below `(1 - 1/(N k)) cost`, apply the first one found. A swap is a list of `p` numbers
--   `x < k m`, each replacing the facility at position `x / m` by `x % m` unless that facility is
--   already open (`BCFGJPSSV26.Stable.lsApply`); the swaps are the `p`-tuples of
--   `Tuples.tuples`, cut at the budget `B`, and at most `B` swaps are applied.
--
--   **Specification** (`BCFGJPSSV26.Stable.isALO_localSearch`): for a valid instance with `k ≤ m`, if
--   `B ≥ (k m)^p` (all swaps are tried, `BCFGJPSSV26.Stable.exists_lsApply_eq`) and
--   `B ≥ 2 N k |enc I| + 2` (enough improvements, `BCFGJPSSV26.Stable.lsStep_iterate_fixed`: for the
--   product `Q` of the denominators of the table, `Q cost` is a nonnegative integer, at most
--   `2^|enc I|` at the start since `Q (1 + Σ |d(a, b)|) ≤ 2^|enc I|`, and drops by a factor
--   `1 - 1/(N k)` with every improvement, so that `B` improvements would bring it below `1` and then
--   below `0`), the output is an approximate local optimum, a list of `k` distinct facilities
--   (`BCFGJPSSV26.Stable.localSearch_spec`). With `BCFGJPSSV26.Stable.costF_le_three_add` it costs at
--   most `(3 + 100/N) opt k ≤ 4 opt k` for `N ≥ 201` (`BCFGJPSSV26.Stable.costF_localSearch_le`).
--   The specification holds for every `N ≥ 1`, the cost bound for every `N ≥ 201`, in particular for a
--   fixed `N` and a budget polynomial in `|enc I|`, as Part I uses them.
--
--   **Contents.** The module is published as a whole: 38 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.costF_localSearch_le`, `BCFGJPSSV26.Stable.isALO_localSearch` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/LocalSearch.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Params
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BuhaiPapers_Background_Tuples

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.LocalSearch` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The local search

The deterministic local search of [BCFGJPSSV26b, Section 3] with swaps of size `p = 24 N` and the
approximate stopping rule of [BCFGJPSSV26b, Theorem 3.6] (`BCFGJPSSV26.Stable.localSearch`): start
from the facilities `0, …, k - 1`; as long as some swap of at most `p` facilities lowers the exact
cost below `(1 - 1/(N k)) cost`, apply the first one found. A swap is a list of `p` numbers
`x < k m`, each replacing the facility at position `x / m` by `x % m` unless that facility is
already open (`BCFGJPSSV26.Stable.lsApply`); the swaps are the `p`-tuples of
`Tuples.tuples`, cut at the budget `B`, and at most `B` swaps are applied.

**Specification** (`BCFGJPSSV26.Stable.isALO_localSearch`): for a valid instance with `k ≤ m`, if
`B ≥ (k m)^p` (all swaps are tried, `BCFGJPSSV26.Stable.exists_lsApply_eq`) and
`B ≥ 2 N k |enc I| + 2` (enough improvements, `BCFGJPSSV26.Stable.lsStep_iterate_fixed`: for the
product `Q` of the denominators of the table, `Q cost` is a nonnegative integer, at most
`2^|enc I|` at the start since `Q (1 + Σ |d(a, b)|) ≤ 2^|enc I|`, and drops by a factor
`1 - 1/(N k)` with every improvement, so that `B` improvements would bring it below `1` and then
below `0`), the output is an approximate local optimum, a list of `k` distinct facilities
(`BCFGJPSSV26.Stable.localSearch_spec`). With `BCFGJPSSV26.Stable.costF_le_three_add` it costs at
most `(3 + 100/N) opt k ≤ 4 opt k` for `N ≥ 201` (`BCFGJPSSV26.Stable.costF_localSearch_le`).
The specification holds for every `N ≥ 1`, the cost bound for every `N ≥ 201`, in particular for a
fixed `N` and a budget polynomial in `|enc I|`, as Part I uses them.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Tuples Encoding

/-- **Apply a swap** `w` to the list `S`: each `x ∈ w` puts facility `x % m` at position `x / m`,
unless it is already in the list. -/
def lsApply (m : ℕ) (w S : List ℕ) : List ℕ :=
  w.foldl (fun S x ↦ if x % m ∈ S then S else S.set (x / m) (x % m)) S

/-- Whether `T` is an improvement over `S`: `cost T < (1 - 1/(N k)) cost S`, exactly. -/
def lsImproves (N : ℕ) (x : Raw) (S T : List ℕ) : Bool :=
  decide (x.cost T < (1 - 1 / ((N : ℚ) * x.k)) * x.cost S)

/-- One step of the local search: the first improving swap among the `p`-tuples cut at `B`, if
there is one. -/
def lsStep (N : ℕ) (x : Raw) (B : ℕ) (S : List ℕ) : List ℕ :=
  match (tuples B (x.k * x.m) (Par.p N)).find? (fun w ↦ lsImproves N x S (lsApply x.m w S)) with
  | some w => lsApply x.m w S
  | none => S

/-- **The local search**: at most `B` steps from the facilities `0, …, k - 1`. -/
def localSearch (N : ℕ) (x : Raw) (B : ℕ) : List ℕ := (lsStep N x B)^[B] (List.range x.k)

/-! ### Swaps keep `k` distinct facilities -/

/-- A list of `k` distinct facilities among `m`. -/
private def LSInv (m k : ℕ) (S : List ℕ) : Prop := S.Nodup ∧ S.length = k ∧ ∀ i ∈ S, i < m

private theorem lsApply_cons (m x : ℕ) (w S : List ℕ) :
    lsApply m (x :: w) S = lsApply m w (if x % m ∈ S then S else S.set (x / m) (x % m)) := rfl

private theorem lsApply_append (m : ℕ) (w w' S : List ℕ) :
    lsApply m (w ++ w') S = lsApply m w' (lsApply m w S) := List.foldl_append

private theorem lsInv_step {m k x : ℕ} {S : List ℕ} (h : LSInv m k S) :
    LSInv m k (if x % m ∈ S then S else S.set (x / m) (x % m)) := by
  split_ifs with hx
  · exact h
  obtain ⟨hnd, hlen, hm⟩ := h
  refine ⟨hnd.set hx, by rw [List.length_set, hlen], fun i hi ↦ ?_⟩
  rcases List.mem_or_eq_of_mem_set hi with hi | rfl
  · exact hm i hi
  · rcases S with _ | ⟨a, S⟩
    · simp at hi
    · exact Nat.mod_lt _ ((Nat.zero_le a).trans_lt (hm a (by simp)))

private theorem lsInv_lsApply {m k : ℕ} (w : List ℕ) {S : List ℕ} (h : LSInv m k S) :
    LSInv m k (lsApply m w S) := by
  induction w generalizing S with
  | nil => exact h
  | cons x w ih => rw [lsApply_cons]; exact ih (lsInv_step h)

/-- Applying a no-op `y` (with `y % m ∈ S`) any number of times leaves `S`. -/
private theorem lsApply_replicate {m y : ℕ} {S : List ℕ} (hy : y % m ∈ S) (j : ℕ) :
    lsApply m (List.replicate j y) S = S := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, lsApply_cons, if_pos hy]; exact ih

/-- In a list without duplicates, setting the position of `S[p]` to `a` replaces `S[p]` by
`a`. -/
private theorem mem_set_iff_of_nodup {S : List ℕ} (hnd : S.Nodup) {p : ℕ} (hp : p < S.length)
    (a i : ℕ) : i ∈ S.set p a ↔ i = a ∨ (i ∈ S ∧ i ≠ S[p]) := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
    rw [List.getElem_set]
    split_ifs with hpj
    · exact .inl rfl
    · rw [List.length_set] at hj
      refine .inr ⟨List.getElem_mem hj, fun h ↦ hpj ?_⟩
      exact ((hnd.getElem_inj_iff).1 h).symm
  · rintro (rfl | ⟨hi, hne⟩)
    · exact List.mem_iff_getElem.2 ⟨p, by rw [List.length_set]; exact hp,
        List.getElem_set_self _⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hi
      have hpj : p ≠ j := fun h ↦ hne (by subst h; rfl)
      exact List.mem_iff_getElem.2 ⟨j, by rw [List.length_set]; exact hj,
        List.getElem_set_ne hpj _⟩

/-! ### Number theory of the table -/

/-- The product of the denominators of a list of rationals. -/
private def denProd (E : List ℚ) : ℕ := (E.map Rat.den).prod

private theorem denProd_pos (E : List ℚ) : 0 < denProd E :=
  List.prod_pos fun a ha ↦ by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 ha
    exact q.pos

/-- Every element of `E` times the product of the denominators is an integer. -/
private theorem exists_int_of_mem {E : List ℚ} {q : ℚ} (hq : q ∈ E) :
    ∃ z : ℤ, (denProd E : ℚ) * q = z := by
  obtain ⟨c, hc⟩ := List.dvd_prod (List.mem_map_of_mem (f := Rat.den) hq)
  refine ⟨c * q.num, ?_⟩
  rw [denProd, hc]
  push_cast
  rw [mul_comm (q.den : ℚ), mul_assoc, Rat.den_mul_eq_num]

private theorem exists_int_sum {Q : ℚ} {l : List ℚ} (h : ∀ v ∈ l, ∃ z : ℤ, Q * v = z) :
    ∃ z : ℤ, Q * l.sum = z := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons v l ih =>
    obtain ⟨a, ha⟩ := h v List.mem_cons_self
    obtain ⟨b, hb⟩ := ih fun u hu ↦ h u (List.mem_cons_of_mem _ hu)
    exact ⟨a + b, by rw [List.sum_cons, mul_add, ha, hb]; push_cast; ring⟩

/-- The length of an encoded rational. -/
private theorem length_encRat (q : ℚ) :
    (encRat q).length = 2 * (q.num.natAbs.size + 1) + 1 + q.den.size := by
  change (frame (decide (q.num < 0) :: Nat.bits q.num.natAbs) ++ Nat.bits q.den).length = _
  simp only [List.length_append, frame, List.length_flatMap, List.length_cons, List.length_nil,
    List.map_const', List.sum_replicate, smul_eq_mul, Nat.size_eq_bits_len]
  ring

/-- A rational `q` with its denominator: `den (1 + |q|) = den + |num| ≤ 2^|enc q|`. -/
private theorem den_mul_le (q : ℚ) : (q.den : ℚ) * (1 + |q|) ≤ 2 ^ (encRat q).length := by
  have h1 : (q.den : ℚ) * |q| = q.num.natAbs := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.den_mul_eq_num, abs_mul, Nat.abs_cast]
  have h2 : q.den + q.num.natAbs ≤ 2 ^ (encRat q).length := by
    have ha := Nat.lt_size_self q.den
    have hb := Nat.lt_size_self q.num.natAbs
    have hle : 2 ^ q.den.size + 2 ^ q.num.natAbs.size ≤ 2 ^ (encRat q).length := by
      rw [length_encRat]
      have h3 : 2 ^ q.den.size ≤ 2 ^ (q.den.size + q.num.natAbs.size) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : 2 ^ q.num.natAbs.size ≤ 2 ^ (q.den.size + q.num.natAbs.size) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 ^ q.den.size + 2 ^ q.num.natAbs.size ≤ 2 ^ (q.den.size + q.num.natAbs.size + 1) :=
            by rw [pow_succ]; omega
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [mul_add, mul_one, h1]
  exact_mod_cast h2

/-- **The denominators and the entries are bounded by the encoding**:
`Π den (1 + Σ |q|) ≤ 2^(Σ |enc q|)`. -/
private theorem denProd_mul_le (E : List ℚ) :
    (denProd E : ℚ) * (1 + (E.map (|·|)).sum) ≤ 2 ^ (E.map fun q ↦ (encRat q).length).sum := by
  induction E with
  | nil => simp [denProd]
  | cons q E ih =>
    have key : ∀ d P a s A B : ℚ, 0 ≤ d → 0 ≤ P → 0 ≤ a → 0 ≤ s → d * (1 + a) ≤ A →
        P * (1 + s) ≤ B → d * P * (1 + (a + s)) ≤ A * B := by
      intro d P a s A B hd hP ha hs hA hB
      calc d * P * (1 + (a + s)) ≤ d * P * ((1 + a) * (1 + s)) :=
            mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg hd hP)
        _ = (d * (1 + a)) * (P * (1 + s)) := by ring
        _ ≤ A * B :=
            mul_le_mul hA hB (by positivity) ((by positivity : (0 : ℚ) ≤ d * (1 + a)).trans hA)
    have hs : (0 : ℚ) ≤ (E.map (|·|)).sum := List.sum_nonneg fun a ha ↦ by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      exact abs_nonneg b
    have h := key q.den (denProd E) |q| _ (2 ^ (encRat q).length) _ (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (abs_nonneg q) hs (den_mul_le q) ih
    simpa only [denProd, List.map_cons, List.prod_cons, List.sum_cons, pow_add, Nat.cast_mul]
      using h

/-! ### The cost of a list of facilities, as entries of the table -/

private theorem getD_eq_getElem' {α : Type*} (l : List α) (d : α) {i : ℕ} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

private theorem getD_eq_default' {α : Type*} (l : List α) (d : α) {i : ℕ} (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

private theorem getD_eq_zero_or_mem (l : List ℚ) (i : ℕ) : l.getD i 0 = 0 ∨ l.getD i 0 ∈ l := by
  by_cases h : i < l.length
  · exact .inr (by rw [getD_eq_getElem' _ _ h]; exact List.getElem_mem h)
  · exact .inl (getD_eq_default' _ _ (by omega))

private theorem getD_row_subset (T : List (List ℚ)) (j : ℕ) {q : ℚ} (hq : q ∈ T.getD j []) :
    q ∈ T.flatten := by
  by_cases h : j < T.length
  · rw [getD_eq_getElem' _ _ h] at hq
    exact List.mem_flatten.2 ⟨_, List.getElem_mem h, hq⟩
  · rw [getD_eq_default' _ _ (by omega)] at hq
    simp at hq

/-- The term of client `j` in the cost: `0` or an entry of row `j`. -/
private theorem minQ_eq_zero_or_mem (n : ℕ) (T : List (List ℚ)) (S : List ℕ) (j : ℕ) :
    Combine.minQ (S.map fun i ↦ (T.getD j []).getD (n + i) 0) = 0 ∨
      Combine.minQ (S.map fun i ↦ (T.getD j []).getD (n + i) 0) ∈ T.getD j [] := by
  by_cases hS : S = []
  · subst hS
    exact .inl rfl
  · have hl : (S.map fun i ↦ (T.getD j []).getD (n + i) 0) ≠ [] := by simpa using hS
    obtain ⟨i, -, hi⟩ := List.mem_map.1 (Combine.minQ_spec hl).1
    rw [← hi]
    exact getD_eq_zero_or_mem _ _

/-- **The cost times the product of the denominators is an integer.** -/
private theorem exists_int_costQ (n : ℕ) (T : List (List ℚ)) (S : List ℕ) :
    ∃ z : ℤ, (denProd T.flatten : ℚ) * Combine.costQ n T S = z := by
  refine exists_int_sum fun v hv ↦ ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hv
  rcases minQ_eq_zero_or_mem n T S j with h | h
  · exact ⟨0, by rw [h, mul_zero, Int.cast_zero]⟩
  · exact exists_int_of_mem (getD_row_subset T j h)

private theorem map_range_getD {β : Type*} (T : List (List ℚ)) (f : List ℚ → β) :
    (List.range T.length).map (fun j ↦ f (T.getD j [])) = T.map f := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [getD_eq_getElem' _ _ (by simpa using h₂)]

/-- **The cost is at most the sum of the absolute values of the table.** -/
private theorem costQ_le (n : ℕ) (T : List (List ℚ)) (S : List ℕ) :
    Combine.costQ n T S ≤ (T.flatten.map (|·|)).sum := by
  set h : ℕ → ℚ := fun j ↦ ((T.getD j []).map (|·|)).sum
  have hh : ∀ j, 0 ≤ h j := fun j ↦ List.sum_nonneg fun a ha ↦ by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact abs_nonneg b
  have h1 : Combine.costQ n T S ≤ ((List.range (min T.length n)).map h).sum := by
    refine List.sum_le_sum fun j _ ↦ ?_
    rcases minQ_eq_zero_or_mem n T S j with hz | hz
    · rw [hz]
      exact hh j
    · refine (le_abs_self _).trans (List.single_le_sum (fun a ha ↦ ?_) _
        (List.mem_map_of_mem hz))
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      exact abs_nonneg b
  have h2 : ((List.range (min T.length n)).map h).sum ≤ ((List.range T.length).map h).sum :=
    ((List.range_sublist.2 (min_le_left _ _)).map h).sum_le_sum fun a ha ↦ by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      exact hh b
  have h3 : ((List.range T.length).map h).sum = (T.flatten.map (|·|)).sum := by
    rw [map_range_getD T (fun r ↦ (r.map (|·|)).sum), List.map_flatten, List.sum_flatten,
      List.map_map]
    rfl
  exact h1.trans (h2.trans h3.le)

/-- The encoded entries of the table are no longer than the encoded table. -/
private theorem sum_length_encRat_le (T : List (List ℚ)) :
    (T.flatten.map fun q ↦ (encRat q).length).sum ≤ (encList (encList encRat) T).length := by
  rw [List.map_flatten, List.sum_flatten, List.map_map]
  refine le_trans ?_ (Turing.MultiTapeTM.sum_length_le_length_encList (encList encRat) T)
  exact List.sum_le_sum fun r _ ↦ Turing.MultiTapeTM.sum_length_le_length_encList encRat r

/-- **Termination by an integral potential**: if every step that moves lowers a nonnegative cost
`c` by a factor `1 - δ`, `Q c` is always an integer and `(1 - δ)^B Q c(a₀) < 1`, then `f` is fixed
after `B` steps. -/
private theorem iterate_fixed {α : Type*} (f : α → α) (c : α → ℚ) (P : α → Prop)
    (hP : ∀ a, P a → P (f a)) {δ : ℚ} (hδ : δ ≤ 1) (hc : ∀ a, P a → 0 ≤ c a) {Q : ℚ}
    (hQ : 0 < Q) (hint : ∀ a, P a → ∃ z : ℤ, Q * c a = z)
    (hdec : ∀ a, P a → f a ≠ a → c (f a) < (1 - δ) * c a) {a₀ : α} (h₀ : P a₀) {B : ℕ}
    (hB : (1 - δ) ^ B * (Q * c a₀) < 1) : f (f^[B] a₀) = f^[B] a₀ := by
  by_contra hne
  have hall : ∀ t ≤ B, f (f^[t] a₀) ≠ f^[t] a₀ := by
    intro t ht heq
    apply hne
    have h : ∀ u, f^[t + u] a₀ = f^[t] a₀ := by
      intro u
      induction u with
      | zero => rfl
      | succ u ih => rw [← add_assoc, Function.iterate_succ_apply', ih, heq]
    have h' := h (B - t)
    rw [Nat.add_sub_cancel' ht] at h'
    rw [h', heq]
  have hPt : ∀ t, P (f^[t] a₀) := by
    intro t
    induction t with
    | zero => exact h₀
    | succ t ih => rw [Function.iterate_succ_apply']; exact hP _ ih
  have hbound : ∀ t ≤ B, c (f^[t] a₀) ≤ (1 - δ) ^ t * c a₀ := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply', pow_succ]
      calc c (f (f^[t] a₀)) ≤ (1 - δ) * c (f^[t] a₀) := (hdec _ (hPt t) (hall t (by omega))).le
        _ ≤ (1 - δ) * ((1 - δ) ^ t * c a₀) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
        _ = _ := by ring
  obtain ⟨z, hz⟩ := hint _ (hPt B)
  have hz0 : (0 : ℚ) ≤ z := hz ▸ mul_nonneg hQ.le (hc _ (hPt B))
  have hz1 : (z : ℚ) < 1 := by
    rw [← hz]
    calc Q * c (f^[B] a₀) ≤ Q * ((1 - δ) ^ B * c a₀) :=
          mul_le_mul_of_nonneg_left (hbound B le_rfl) hQ.le
      _ = (1 - δ) ^ B * (Q * c a₀) := by ring
      _ < 1 := hB
  have hz' : z = 0 := by
    have h0 : (0 : ℤ) ≤ z := by exact_mod_cast hz0
    have h1 : z < 1 := by exact_mod_cast hz1
    omega
  have hcB : c (f^[B] a₀) = 0 := by
    rw [hz', Int.cast_zero] at hz
    exact (mul_eq_zero.1 hz).resolve_left hQ.ne'
  have h := hdec _ (hPt B) hne
  rw [hcB, mul_zero] at h
  exact absurd h (not_lt.2 (hc _ (hP _ (hPt B))))

/-- `(1 - 1/M)^M ≤ 1/2`. -/
private theorem one_sub_inv_pow_le {M : ℕ} (hM : 1 ≤ M) : (1 - 1 / (M : ℚ)) ^ M ≤ 1 / 2 := by
  have hM' : (1 : ℚ) ≤ M := by exact_mod_cast hM
  have hinv : 0 < 1 / (M : ℚ) := by positivity
  have hinv1 : 1 / (M : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM'
  have h1 : 2 ≤ (1 + 1 / (M : ℚ)) ^ M := by
    have := one_add_mul_le_pow (a := 1 / (M : ℚ)) (by linarith) M
    rw [mul_one_div_cancel (by linarith)] at this
    linarith
  have h2 : ((1 - 1 / (M : ℚ)) * (1 + 1 / (M : ℚ))) ^ M ≤ 1 :=
    pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) (by nlinarith)
  rw [mul_pow] at h2
  have h3 : 0 ≤ (1 - 1 / (M : ℚ)) ^ M := pow_nonneg (by linarith) _
  nlinarith

private theorem lsInv_lsStep {N : ℕ} {x : Raw} {B : ℕ} {S : List ℕ} (h : LSInv x.m x.k S) :
    LSInv x.m x.k (lsStep N x B S) := by
  unfold lsStep
  split
  · exact lsInv_lsApply _ h
  · exact h

private theorem lsInv_iterate {N : ℕ} {x : Raw} {B : ℕ} (t : ℕ) {S : List ℕ} (h : LSInv x.m x.k S) :
    LSInv x.m x.k ((lsStep N x B)^[t] S) := by
  induction t with
  | zero => exact h
  | succ t ih => rw [Function.iterate_succ_apply']; exact lsInv_lsStep ih

/-- A step that moves is an improvement. -/
private theorem lsStep_improves {N : ℕ} {x : Raw} {B : ℕ} {S : List ℕ} (h : lsStep N x B S ≠ S) :
    x.cost (lsStep N x B S) < (1 - 1 / ((N : ℚ) * x.k)) * x.cost S := by
  cases hf : (tuples B (x.k * x.m) (Par.p N)).find? (fun w ↦ lsImproves N x S (lsApply x.m w S))
    with
  | none => exact absurd (by unfold lsStep; rw [hf]) h
  | some w =>
    have hw := List.find?_some hf
    unfold lsStep
    rw [hf]
    exact of_decide_eq_true hw

variable {I : Instance}

/-- **The output is a list of `k` distinct facilities.** -/
theorem localSearch_spec (hk : I.k ≤ I.m) (N B : ℕ) :
    (localSearch N (toRaw I) B).Nodup ∧ (localSearch N (toRaw I) B).length = I.k ∧
      ∀ i ∈ localSearch N (toRaw I) B, i < I.m :=
  lsInv_iterate (x := toRaw I) B ⟨List.nodup_range, List.length_range,
    fun _ hi ↦ (List.mem_range.1 hi).trans_le hk⟩

/-- Every set of `k` facilities `r` swaps away from `S` is reached by a list of `r` swaps. -/
private theorem exists_swaps (r : ℕ) : ∀ {S : List ℕ}, LSInv I.m I.k S → ∀ {T : Finset (Fin I.m)},
    T.card = I.k → (I.centers S \ T).card = r →
    ∃ w : List ℕ, w.length = r ∧ (∀ x ∈ w, x < I.k * I.m) ∧ I.centers (lsApply I.m w S) = T := by
  classical
  induction r with
  | zero =>
    intro S hS T hT hr
    refine ⟨[], rfl, by simp, ?_⟩
    change I.centers S = T
    have hsub : I.centers S ⊆ T := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hr)
    exact Finset.eq_of_subset_of_card_le hsub
      (by rw [hT, Instance.card_centers hS.1 hS.2.2, hS.2.1])
  | succ r ih =>
    intro S hS T hT hr
    have hcS : (I.centers S).card = I.k := by rw [Instance.card_centers hS.1 hS.2.2, hS.2.1]
    obtain ⟨d, hd⟩ : (I.centers S \ T).Nonempty := Finset.card_pos.1 (by omega)
    have hcard : (T \ I.centers S).card = r + 1 := by
      rw [← Finset.card_sdiff_comm (by rw [hT, hcS])]
      exact hr
    obtain ⟨a, ha⟩ : (T \ I.centers S).Nonempty := Finset.card_pos.1 (by omega)
    have hdT := (Finset.mem_sdiff.1 hd).2
    have haT := (Finset.mem_sdiff.1 ha).1
    have hdS : d.1 ∈ S := Instance.mem_centers.1 (Finset.mem_sdiff.1 hd).1
    have haS : a.1 ∉ S := fun h ↦ (Finset.mem_sdiff.1 ha).2 (Instance.mem_centers.2 h)
    have hpos : S.idxOf d.1 < S.length := List.idxOf_lt_length_of_mem hdS
    have hSpos : S[S.idxOf d.1] = d.1 := List.getElem_idxOf hpos
    have hm0 : 0 < I.m := (Nat.zero_le _).trans_lt a.2
    have hxmod : (I.m * S.idxOf d.1 + a.1) % I.m = a.1 := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt a.2]
    have hxdiv : (I.m * S.idxOf d.1 + a.1) / I.m = S.idxOf d.1 := by
      rw [Nat.mul_add_div hm0, Nat.div_eq_of_lt a.2, add_zero]
    have hxlt : I.m * S.idxOf d.1 + a.1 < I.k * I.m := by
      have h1 : S.idxOf d.1 + 1 ≤ I.k := by rw [← hS.2.1]; omega
      calc I.m * S.idxOf d.1 + a.1 < I.m * S.idxOf d.1 + I.m := by have := a.2; omega
        _ = I.m * (S.idxOf d.1 + 1) := by ring
        _ ≤ I.m * I.k := Nat.mul_le_mul_left _ h1
        _ = I.k * I.m := mul_comm _ _
    have hstep : (if (I.m * S.idxOf d.1 + a.1) % I.m ∈ S then S else
        S.set ((I.m * S.idxOf d.1 + a.1) / I.m) ((I.m * S.idxOf d.1 + a.1) % I.m)) =
        S.set (S.idxOf d.1) a.1 := by
      rw [hxmod, hxdiv, if_neg haS]
    have hS' : LSInv I.m I.k (S.set (S.idxOf d.1) a.1) := hstep ▸ lsInv_step hS
    have hcS' : I.centers (S.set (S.idxOf d.1) a.1) = insert a ((I.centers S).erase d) := by
      ext i
      rw [Instance.mem_centers, mem_set_iff_of_nodup hS.1 hpos, hSpos, Finset.mem_insert,
        Finset.mem_erase, Instance.mem_centers]
      simp only [Fin.ext_iff, Ne]
      tauto
    have hr' : (I.centers (S.set (S.idxOf d.1) a.1) \ T).card = r := by
      have : insert a ((I.centers S).erase d) \ T = (I.centers S \ T).erase d := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h | ⟨h1, h2⟩, h3⟩
          · exact absurd (h ▸ haT) h3
          · exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨.inr ⟨h1, h2⟩, h3⟩
      rw [hcS', this, Finset.card_erase_of_mem hd, hr, Nat.add_sub_cancel]
    obtain ⟨w, hwl, hwx, hwT⟩ := ih hS' hT hr'
    refine ⟨(I.m * S.idxOf d.1 + a.1) :: w, by simp [hwl], ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hxlt
      · exact hwx y hy
    · rw [lsApply_cons, hstep]
      exact hwT

/-- Every set of `k` facilities within `p` swaps of `S` is reached by some swap of the
enumeration, when it is complete (`(k m)^p ≤ B`). With `k ≥ 1`, as the swaps of `p` positions
are padded by no-ops `S[0]`, which do not exist for `k = 0` (there are no tuples then). -/
theorem exists_lsApply_eq (hk : 1 ≤ I.k) {N B : ℕ} (hB : (I.k * I.m) ^ Par.p N ≤ B)
    {S : List ℕ} (hS : S.Nodup) (hSk : S.length = I.k) (hSm : ∀ i ∈ S, i < I.m)
    {T : Finset (Fin I.m)} (hT : T.card = I.k) (hST : (I.centers S \ T).card ≤ Par.p N) :
    ∃ w ∈ tuples B (I.k * I.m) (Par.p N), I.centers (lsApply I.m w S) = T := by
  obtain ⟨w, hwl, hwx, hwT⟩ := exists_swaps _ ⟨hS, hSk, hSm⟩ hT rfl
  have h0 : 0 < S.length := by omega
  have hy : S[0] < I.m := hSm _ (List.getElem_mem h0)
  refine ⟨List.replicate (Par.p N - (I.centers S \ T).card) S[0] ++ w,
    (mem_tuples hB).2 ⟨?_, ?_⟩, ?_⟩
  · simp only [List.length_append, List.length_replicate, hwl]
    omega
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · rw [List.eq_of_mem_replicate hz]
      exact hy.trans_le (Nat.le_mul_of_pos_left _ hk)
    · exact hwx z hz
  · rw [lsApply_append, lsApply_replicate (by rw [Nat.mod_eq_of_lt hy]; exact List.getElem_mem h0)]
    exact hwT

private theorem cost_nonneg_of_lsInv (hv : I.Valid) {S : List ℕ} (h : LSInv I.m I.k S) :
    0 ≤ (toRaw I).cost S := by
  have hS : S ≠ [] := by
    intro h'
    have := h.2.1
    rw [h', List.length_nil] at this
    have := hv.one_le_k
    omega
  have h1 := Raw.cost_toRaw hS h.2.2
  have h2 := Instance.costF_nonneg hv (I.centers S)
  rw [← h1] at h2
  exact_mod_cast h2

private theorem one_le_length_encInstance (I : Instance) : 1 ≤ (encInstance I).length := by
  rw [Combine.length_encInstance]
  omega

/-- **Termination**: the local search makes fewer than `2 N k |enc I| + 2` improvements, since
`Q cost` is a nonnegative integer for the product `Q` of the denominators of the table, at most
`2^|enc I|` at the start, and drops by a factor `1 - 1/(N k)` with every improvement. -/
theorem lsStep_iterate_fixed (hv : I.Valid) (hk : I.k ≤ I.m) {N B : ℕ} (hN : 1 ≤ N)
    (hB : 2 * N * I.k * (encInstance I).length + 2 ≤ B) :
    lsStep N (toRaw I) B (localSearch N (toRaw I) B) = localSearch N (toRaw I) B := by
  have hk1 := hv.one_le_k
  have hM : 1 ≤ N * I.k := Nat.mul_pos hN hk1
  have hδ : (1 : ℚ) / ((N : ℚ) * I.k) = 1 / ((N * I.k : ℕ) : ℚ) := by push_cast; rfl
  have hδ1 : (1 : ℚ) / ((N : ℚ) * I.k) ≤ 1 := by
    rw [hδ, div_le_one (by exact_mod_cast hM)]
    exact_mod_cast hM
  have hδ0 : 0 ≤ 1 - (1 : ℚ) / ((N : ℚ) * I.k) := by linarith
  have h0 : LSInv I.m I.k (List.range I.k) :=
    ⟨List.nodup_range, List.length_range, fun _ hi ↦ (List.mem_range.1 hi).trans_le hk⟩
  have hQ : (0 : ℚ) < denProd (distTable I).flatten := by exact_mod_cast denProd_pos _
  refine iterate_fixed (lsStep N (toRaw I) B) (toRaw I).cost (LSInv I.m I.k)
    (fun _ h ↦ lsInv_lsStep h) hδ1 (fun _ h ↦ cost_nonneg_of_lsInv hv h) hQ
    (fun S _ ↦ exists_int_costQ I.n (distTable I) S) (fun _ _ h ↦ lsStep_improves h) h0 ?_
  -- the potential at the start is at most `2^|enc I|`
  have hc₀ : (denProd (distTable I).flatten : ℚ) * (toRaw I).cost (List.range I.k) ≤
      2 ^ (encInstance I).length := by
    have h1 := costQ_le I.n (distTable I) (List.range I.k)
    have h2 := denProd_mul_le (distTable I).flatten
    have h3 := sum_length_encRat_le (distTable I)
    have h4 : (encList (encList encRat) (distTable I)).length ≤ (encInstance I).length := by
      rw [Combine.length_encInstance]
      omega
    calc (denProd (distTable I).flatten : ℚ) * (toRaw I).cost (List.range I.k) ≤
        denProd (distTable I).flatten * (1 + ((distTable I).flatten.map (|·|)).sum) :=
          mul_le_mul_of_nonneg_left (by change Combine.costQ I.n (distTable I) _ ≤ _; linarith)
            (Nat.cast_nonneg _)
      _ ≤ 2 ^ _ := h2
      _ ≤ 2 ^ (encInstance I).length := pow_le_pow_right₀ (by norm_num) (h3.trans h4)
  -- `B` steps divide it by `4^|enc I|`
  have hpow : (1 - (1 : ℚ) / ((N : ℚ) * I.k)) ^ B ≤ (1 / 2) ^ (2 * (encInstance I).length) := by
    have hle : N * I.k * (2 * (encInstance I).length) ≤ B := by
      have : N * I.k * (2 * (encInstance I).length) = 2 * N * I.k * (encInstance I).length := by
        ring
      omega
    calc _ ≤ (1 - (1 : ℚ) / ((N : ℚ) * I.k)) ^ (N * I.k * (2 * (encInstance I).length)) :=
          pow_le_pow_of_le_one hδ0 (by
            have : (0 : ℚ) ≤ 1 / ((N : ℚ) * I.k) := by positivity
            linarith) hle
      _ = ((1 - 1 / ((N * I.k : ℕ) : ℚ)) ^ (N * I.k)) ^ (2 * (encInstance I).length) := by
          rw [hδ, pow_mul]
      _ ≤ (1 / 2) ^ (2 * (encInstance I).length) :=
          pow_le_pow_left₀ (pow_nonneg (hδ ▸ hδ0) _) (one_sub_inv_pow_le hM) _
  have hℓ := one_le_length_encInstance I
  calc (1 - 1 / ((N : ℚ) * I.k)) ^ B *
        ((denProd (distTable I).flatten : ℚ) * (toRaw I).cost (List.range I.k)) ≤
      (1 / 2) ^ (2 * (encInstance I).length) * 2 ^ (encInstance I).length :=
        mul_le_mul hpow hc₀ (mul_nonneg hQ.le (cost_nonneg_of_lsInv hv h0)) (by positivity)
    _ = (1 / 2) ^ (encInstance I).length := by
        rw [two_mul, pow_add, mul_assoc, ← mul_pow]
        norm_num
    _ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

end BCFGJPSSV26.Stable


