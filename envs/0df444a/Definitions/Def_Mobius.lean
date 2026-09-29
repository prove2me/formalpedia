-- Prove2me | Definitions.Def_Mobius
-- name    : Mobius
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-05-06T20:42:01.144697+00:00
-- url     : https://prove2.me/theorems/6baebd52-de4d-4fd5-b381-887df25512b4
-- statement:
--   **Möbius helpers for Boolean functions on the cube.**
--
--   Bundles the auxiliary definitions and lemmas used by the
--   `polyDegree_alternating_sum_witness` proof and other Möbius-style
--   arguments on $\{0,1\}^n$:
--
--   - $\mathrm{realOf}(b) = \mathbf{1}[b]$ (Bool $\to \{0,1\} \subset \mathbb{R}$).
--   - $\mathrm{signR}(k) = (-1)^k$ as a real.
--   - $\mathrm{altSum}(f, S) = \sum_{T \subseteq S} (-1)^{|S|-|T|} \cdot \mathrm{realOf}(f(\chi_T))$ — the Möbius alternating sum.
--   - $\mathrm{boolOfFinset}(T)\,i = \mathbf{1}[i \in T]$, $\mathrm{trueSet}(x) = \{i : x(i) = \mathrm{true}\}$, $\mathrm{realVertex}(T) = \mathbf{1}_T$.
--
--   Foundational lemmas:
--   - $\mathrm{signR}\,k = (-1)^k$ in $\mathbb{R}$.
--   - $\mathrm{signR}\,(a+b) = \mathrm{signR}\,a \cdot \mathrm{signR}\,b$, $\mathrm{signR}\,(a-b) = \mathrm{signR}\,a \cdot \mathrm{signR}\,b$ (when $b \le a$).
--   - $\sum_{T' \subseteq X} \mathrm{signR}\,|T'| = [X = \emptyset]$.
--   - *Inner-sum collapse*: for $T \subseteq X$, $\sum_{T \subseteq S \subseteq X} \mathrm{signR}\,(|S| - |T|) = [T = X]$ (and the dual `signR (|X| - |S|)` form).
--   - **Möbius inversion on the cube**: $\mathrm{realOf}(f(x)) = \sum_{S \subseteq \mathrm{trueSet}(x)} \mathrm{altSum}(f, S)$.
--
--   Reusable across any Boolean-cube argument that involves alternating sums on the subset lattice.

import Definitions.Def_BoolFunc
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Möbius helpers for Boolean functions

Definitions and basic lemmas for the Möbius/alt-sum machinery used to
connect `polyDegree f` to the alternating sum
`∑ T ⊆ S, (-1)^(|S|-|T|) · realOf(f(1_T))`.

This file is project-private support for the Gotsman–Linial chain
(specifically the leaf proof of `polyDegree_alternating_sum_witness`).
The definitions and lemmas here are not platform-uploaded; they exist
only to keep the proof file readable.
-/

namespace Mobius

variable {n : ℕ}

/-- Real-valued cube indicator: `realOf b = 1` if `b = true`, else `0`. -/
noncomputable def realOf (b : Bool) : ℝ := if b then 1 else 0

/-- Signed `(-1)^k` as a real number. -/
noncomputable def signR (k : ℕ) : ℝ := if k % 2 = 0 then 1 else -1

/-- Cube vertex (Bool-valued) corresponding to a Finset of true coordinates. -/
def boolOfFinset (T : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ T)

/-- True-set of a cube vertex. -/
def trueSet (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i)

/-- The Möbius alternating sum of `f` over the index set `S`. -/
noncomputable def altSum (f : BoolFunc n) (S : Finset (Fin n)) : ℝ :=
  ∑ T ∈ S.powerset, signR (S.card - T.card) * realOf (f (boolOfFinset T))

/-- Real cube indicator from a Finset. -/
noncomputable def realVertex (T : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ T then 1 else 0

@[simp] lemma realOf_true : realOf true = (1 : ℝ) := by simp [realOf]

@[simp] lemma realOf_false : realOf false = (0 : ℝ) := by simp [realOf]

@[simp] lemma mem_trueSet (x : Fin n → Bool) (i : Fin n) :
    i ∈ trueSet x ↔ x i = true := by
  simp [trueSet]

@[simp] lemma boolOfFinset_apply (T : Finset (Fin n)) (i : Fin n) :
    boolOfFinset T i = decide (i ∈ T) := rfl

@[simp] lemma boolOfFinset_trueSet (x : Fin n → Bool) :
    boolOfFinset (trueSet x) = x := by
  funext i
  simp only [boolOfFinset_apply, mem_trueSet]
  cases h : x i <;> simp

@[simp] lemma realVertex_mem (T : Finset (Fin n)) (i : Fin n) (h : i ∈ T) :
    realVertex T i = 1 := by simp [realVertex, h]

@[simp] lemma realVertex_not_mem (T : Finset (Fin n)) (i : Fin n) (h : i ∉ T) :
    realVertex T i = 0 := by simp [realVertex, h]

/-- `signR k = (-1)^k`. -/
lemma signR_eq_neg_one_pow (k : ℕ) : signR k = (-1 : ℝ) ^ k := by
  unfold signR
  by_cases h : k % 2 = 0
  · rw [if_pos h, (Nat.even_iff.mpr h).neg_one_pow]
  · rw [if_neg h]
    have h1 : k % 2 = 1 := by omega
    rw [(Nat.odd_iff.mpr h1).neg_one_pow]

/-- `signR (a + b) = signR a · signR b`. -/
lemma signR_add (a b : ℕ) : signR (a + b) = signR a * signR b := by
  rw [signR_eq_neg_one_pow, signR_eq_neg_one_pow, signR_eq_neg_one_pow, pow_add]

/-- `(-1)^k · (-1)^k = 1`. -/
lemma neg_one_pow_sq (k : ℕ) : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by
  rw [← pow_add, show k + k = 2 * k from (two_mul k).symm, pow_mul]
  simp

/-- For `b ≤ a`, `signR (a − b) = signR a · signR b`. -/
lemma signR_sub_of_le {a b : ℕ} (h : b ≤ a) :
    signR (a - b) = signR a * signR b := by
  have key : signR a = signR (a - b) * signR b := by
    conv_lhs => rw [show a = (a - b) + b from (Nat.sub_add_cancel h).symm]
    exact signR_add (a - b) b
  rw [key, mul_assoc]
  simp_rw [signR_eq_neg_one_pow]
  rw [neg_one_pow_sq, mul_one]

/-- The alternating sum `∑_{T' ⊆ X} (-1)^|T'|` over a Finset `X` is
    `1` iff `X = ∅`, else `0`. -/
lemma sum_powerset_signR (X : Finset (Fin n)) :
    (∑ T' ∈ X.powerset, signR T'.card) = if X = ∅ then 1 else 0 := by
  classical
  have h_int :
      (∑ T' ∈ X.powerset, ((-1 : ℤ) ^ T'.card)) = if X = ∅ then 1 else 0 :=
    Finset.sum_powerset_neg_one_pow_card
  rcases eq_or_ne X ∅ with rfl | hX
  · simp [signR]
  · rw [if_neg hX] at h_int ⊢
    -- Convert signR to (-1 : ℝ)^k inside the sum.
    have h_step :
        (∑ T' ∈ X.powerset, signR T'.card) =
        (((∑ T' ∈ X.powerset, ((-1 : ℤ) ^ T'.card)) : ℤ) : ℝ) := by
      rw [Finset.sum_congr rfl (fun T' _ => signR_eq_neg_one_pow T'.card)]
      push_cast
      rfl
    rw [h_step, h_int]
    norm_num

/-- Inner sum: for `T ⊆ X`, the alternating sum
    `∑_{T ⊆ S ⊆ X} signR(|S|-|T|)` collapses to `[T = X]`. -/
lemma inner_sum_collapse {X : Finset (Fin n)} (T : Finset (Fin n)) (hT : T ⊆ X) :
    (∑ S ∈ X.powerset.filter (T ⊆ ·), signR (S.card - T.card)) =
      if T = X then 1 else 0 := by
  classical
  -- Reindex via bijection S ↔ S \ T : { S : T ⊆ S ⊆ X } ≃ (X \ T).powerset.
  have h_eq :
      (∑ S ∈ X.powerset.filter (T ⊆ ·), signR (S.card - T.card)) =
      (∑ R ∈ (X \ T).powerset, signR R.card) := by
    refine Finset.sum_bij'
      (fun S _ => S \ T)
      (fun R _ => T ∪ R) ?_ ?_ ?_ ?_ ?_
    · -- S \ T ⊆ X \ T
      intro S hS
      simp only [Finset.mem_powerset, Finset.mem_filter] at hS ⊢
      intro x hx
      simp only [Finset.mem_sdiff] at hx ⊢
      exact ⟨hS.1 hx.1, hx.2⟩
    · -- T ∪ R ∈ X.powerset.filter (T ⊆ ·)
      intro R hR
      simp only [Finset.mem_powerset, Finset.mem_filter] at hR ⊢
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hxT | hxR
        · exact hT hxT
        · exact (Finset.mem_sdiff.mp (hR hxR)).1
      · exact Finset.subset_union_left
    · -- T ∪ (S \ T) = S, given T ⊆ S
      intro S hS
      simp only [Finset.mem_filter] at hS
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (h1 | ⟨h2, _⟩)
        · exact hS.2 h1
        · exact h2
      · intro h1
        by_cases hxT : x ∈ T
        · exact Or.inl hxT
        · exact Or.inr ⟨h1, hxT⟩
    · -- (T ∪ R) \ T = R, given R ⊆ X \ T
      intro R hR
      simp only [Finset.mem_powerset] at hR
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro hxR
        refine ⟨Or.inr hxR, ?_⟩
        intro hxT
        have : x ∈ X \ T := hR hxR
        exact (Finset.mem_sdiff.mp this).2 hxT
    · -- signR(|S| - |T|) = signR(|S \ T|), using S.card - T.card = (S \ T).card.
      intro S hS
      simp only [Finset.mem_filter] at hS
      rw [Finset.card_sdiff_of_subset hS.2]
  rw [h_eq, sum_powerset_signR]
  by_cases h : X \ T = ∅
  · have h_eq_X : T = X := by
      rw [Finset.sdiff_eq_empty_iff_subset] at h
      exact Finset.Subset.antisymm hT h
    rw [h_eq_X]
    simp
  · rw [if_neg h]
    have h_ne : T ≠ X := by
      intro heq
      apply h
      rw [heq, Finset.sdiff_self]
    rw [if_neg h_ne]

/-- Inner sum with sign `signR (X.card - S.card)`: collapses to `[T = X]`.
    This is the "ambient minus bound" form, dual to `inner_sum_collapse`'s
    "bound minus param" form. -/
lemma inner_sum_collapse_compl {X : Finset (Fin n)} (T : Finset (Fin n)) (hT : T ⊆ X) :
    (∑ S ∈ X.powerset.filter (T ⊆ ·), signR (X.card - S.card)) =
      if T = X then 1 else 0 := by
  classical
  -- Step 1: bijection S ↔ R := S \ T.
  have h_bij :
      (∑ S ∈ X.powerset.filter (T ⊆ ·), signR (X.card - S.card)) =
      (∑ R ∈ (X \ T).powerset, signR ((X \ T).card - R.card)) := by
    refine Finset.sum_bij'
      (fun S _ => S \ T)
      (fun R _ => T ∪ R) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_powerset, Finset.mem_filter] at hS ⊢
      intro x hx
      simp only [Finset.mem_sdiff] at hx ⊢
      exact ⟨hS.1 hx.1, hx.2⟩
    · intro R hR
      simp only [Finset.mem_powerset, Finset.mem_filter] at hR ⊢
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hxT | hxR
        · exact hT hxT
        · exact (Finset.mem_sdiff.mp (hR hxR)).1
      · exact Finset.subset_union_left
    · intro S hS
      simp only [Finset.mem_filter] at hS
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (h1 | ⟨h2, _⟩)
        · exact hS.2 h1
        · exact h2
      · intro h1
        by_cases hxT : x ∈ T
        · exact Or.inl hxT
        · exact Or.inr ⟨h1, hxT⟩
    · intro R hR
      simp only [Finset.mem_powerset] at hR
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro hxR
        refine ⟨Or.inr hxR, ?_⟩
        intro hxT
        exact (Finset.mem_sdiff.mp (hR hxR)).2 hxT
    · -- contribution match: signR(X.card - S.card) = signR((X \ T).card - (S \ T).card)
      intro S hS
      simp only [Finset.mem_powerset, Finset.mem_filter] at hS
      have hSX : S ⊆ X := hS.1
      have hTS : T ⊆ S := hS.2
      have hT_le_X : T.card ≤ X.card := Finset.card_le_card hT
      have hT_le_S : T.card ≤ S.card := Finset.card_le_card hTS
      have hS_le_X : S.card ≤ X.card := Finset.card_le_card hSX
      have h_card : X.card - S.card = (X \ T).card - (S \ T).card := by
        rw [Finset.card_sdiff_of_subset hT, Finset.card_sdiff_of_subset hTS]
        omega
      rw [h_card]
  rw [h_bij]
  -- Step 2: pull out signR((X \ T).card) factor.
  rw [show (∑ R ∈ (X \ T).powerset, signR ((X \ T).card - R.card))
        = signR (X \ T).card * (∑ R ∈ (X \ T).powerset, signR R.card) from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    simp only [Finset.mem_powerset] at hR
    have hR_le : R.card ≤ (X \ T).card := Finset.card_le_card hR
    rw [signR_sub_of_le hR_le]]
  rw [sum_powerset_signR]
  by_cases h : X \ T = ∅
  · have h_eq_X : T = X := by
      rw [Finset.sdiff_eq_empty_iff_subset] at h
      exact Finset.Subset.antisymm hT h
    rw [if_pos h, if_pos h_eq_X, mul_one]
    rw [h]
    simp [signR]
  · rw [if_neg h]
    have h_ne : T ≠ X := by
      intro heq
      apply h
      rw [heq, Finset.sdiff_self]
    rw [if_neg h_ne, mul_zero]

/-- Möbius inversion identity: for `f : BoolFunc n` and any cube vertex `v`,
    `realOf(f v) = ∑ S ⊆ trueSet v, altSum f S`. -/
lemma mobius_inversion (f : BoolFunc n) (v : Fin n → Bool) :
    realOf (f v) = ∑ S ∈ (trueSet v).powerset, altSum f S := by
  classical
  -- Substitute altSum and swap the double sum.
  unfold altSum
  rw [show (∑ S ∈ (trueSet v).powerset,
            ∑ T ∈ S.powerset,
              signR (S.card - T.card) * realOf (f (boolOfFinset T)))
        = ∑ T ∈ (trueSet v).powerset,
            ∑ S ∈ (trueSet v).powerset.filter (T ⊆ ·),
              signR (S.card - T.card) * realOf (f (boolOfFinset T)) from by
    apply Finset.sum_comm'
    intro S T
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · rintro ⟨hSV, hTS⟩
      exact ⟨⟨hSV, hTS⟩, hTS.trans hSV⟩
    · rintro ⟨⟨hSV, hTS⟩, _⟩
      exact ⟨hSV, hTS⟩]
  -- Pull realOf(f(boolOfFinset T)) out of inner sum.
  rw [show (∑ T ∈ (trueSet v).powerset,
            ∑ S ∈ (trueSet v).powerset.filter (T ⊆ ·),
              signR (S.card - T.card) * realOf (f (boolOfFinset T)))
        = ∑ T ∈ (trueSet v).powerset,
            realOf (f (boolOfFinset T)) *
              (∑ S ∈ (trueSet v).powerset.filter (T ⊆ ·), signR (S.card - T.card)) from by
    apply Finset.sum_congr rfl
    intro T _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring]
  -- Apply inner_sum_collapse on the inner sum.
  rw [show (∑ T ∈ (trueSet v).powerset,
            realOf (f (boolOfFinset T)) *
              (∑ S ∈ (trueSet v).powerset.filter (T ⊆ ·), signR (S.card - T.card)))
        = ∑ T ∈ (trueSet v).powerset,
            realOf (f (boolOfFinset T)) * (if T = trueSet v then (1 : ℝ) else 0) from by
    apply Finset.sum_congr rfl
    intro T hT
    rw [inner_sum_collapse T (Finset.mem_powerset.mp hT)]]
  -- Only T = trueSet v contributes.
  rw [Finset.sum_eq_single (trueSet v)]
  · simp [boolOfFinset_trueSet]
  · intro T _ hT_ne
    rw [if_neg hT_ne, mul_zero]
  · intro h_not
    exfalso
    apply h_not
    simp [Finset.mem_powerset]

end Mobius


