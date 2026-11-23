-- Prove2me | Definitions.Def_MegiddoLP_ConstructiveApproachI
-- name    : MegiddoLP_ConstructiveApproachI
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-23T06:30:55.076116+00:00
-- url     : https://prove2.me/theorems/abb41886-f15d-4aa2-8531-16439d539568
-- title:
--   Comparison identities and pruning counts for Megiddo’s Approach I
-- statement:
--   The sign of a rescaled comparison determines the original ordering in the one-dimensional search. The arithmetic lemmas control the number of residual comparisons and the cost of repeatedly discarding a fixed fraction.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §2 and §5. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Constructive Approach I Hyperplane Pruning and Pair Decoding

Pure constructive algebra and combinatorics for Megiddo's Approach I (§3.2, pp. 118–121)
without `Classical.choose`:
1. `settle1D`: given a 1D splitter `c` with `2 * #{t_i < c} ≤ N` and `2 * #{c < t_i} ≤ N`,
   one oracle answer `σ` for `x_0` vs `c` explicitly settles at least `N / 2` hyperplanes.
2. `decodePair`: explicit algebraic rule settling either `ℓ` or `γ` from the signs of
   `W1 = ah ℓ - ah γ` and `W2 = β • ah ℓ + α • ah γ` (`α = c - ρ ℓ > 0`, `β = ρ γ - c > 0`).
3. Counting and recurrence lemmas: `zero_plus_div_ge`, `approachI_div_step`, `linear_pruning_bound`.
-/

namespace MegiddoLP.ConstructiveApproachI

/-! ## Ordering Algebra Helpers -/

theorem cmp_sub_zero (A B : ℝ) : compare A B = compare (A - B) 0 := by
  rcases lt_trichotomy A B with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (by linarith)]
  · subst h; simp
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (by linarith)]

theorem cmp_mul_pos {t : ℝ} (ht : 0 < t) (A : ℝ) : compare (t * A) 0 = compare A 0 := by
  rcases lt_trichotomy A 0 with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (mul_neg_of_pos_of_neg ht h)]
  · subst h; simp
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (mul_pos ht h)]

theorem cmp_neg_zero (A : ℝ) : compare (-A) 0 = (compare A 0).swap := by
  rcases lt_trichotomy A 0 with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr (by linarith)]; rfl
  · subst h; simp
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr (by linarith)]; rfl

/-- Scale `compare A 0` by a nonzero scalar `p`: returns `compare (p * A) 0`. -/
noncomputable def scaleOrd (p : ℝ) (o : Ordering) : Ordering :=
  if 0 < p then o else o.swap

theorem scaleOrd_spec {p : ℝ} (hp : p ≠ 0) (A : ℝ) :
    scaleOrd p (compare A 0) = compare (p * A) 0 := by
  unfold scaleOrd
  split_ifs with hpos
  · exact (cmp_mul_pos hpos A).symm
  · have hneg : 0 < -p := by
      have : p < 0 := lt_of_le_of_ne (not_lt.mp hpos) hp
      linarith
    have heq : p * A = -((-p) * A) := by ring
    rw [heq, cmp_neg_zero, cmp_mul_pos hneg]

theorem cmp_tri (z : ℝ) :
    (z < 0 ∧ compare z 0 = .lt) ∨ (z = 0 ∧ compare z 0 = .eq) ∨ (0 < z ∧ compare z 0 = .gt) := by
  rcases lt_trichotomy z 0 with h | h | h
  · exact Or.inl ⟨h, compare_lt_iff_lt.mpr h⟩
  · exact Or.inr (Or.inl ⟨h, compare_eq_iff_eq.mpr h⟩)
  · exact Or.inr (Or.inr ⟨h, compare_gt_iff_gt.mpr h⟩)

/-! ## 1D Median Settling Rule -/

/-- Given `compare x0 c = σ`, return `some (compare (h * x0) β)` whenever settled by `c`. -/
noncomputable def settle1D (c : ℝ) (σ : Ordering) (h β : ℝ) : Option Ordering :=
  match σ with
  | .lt => if c ≤ β / h then some (scaleOrd h .lt) else none
  | .gt => if β / h ≤ c then some (scaleOrd h .gt) else none
  | .eq => some (compare (h * c) β)

theorem settle1D_sound {c x0 h β : ℝ} (hh : h ≠ 0) {σ o : Ordering}
    (hσ : compare x0 c = σ) (hset : settle1D c σ h β = some o) :
    compare (h * x0) β = o := by
  have hrel : h * x0 - β = h * (x0 - β / h) := by field_simp [hh]
  cases σ
  · have hx : x0 < c := compare_lt_iff_lt.mp hσ
    simp only [settle1D] at hset
    split_ifs at hset with hle
    cases hset
    have hlt : x0 - β / h < 0 := by linarith
    rw [cmp_sub_zero, hrel, ← scaleOrd_spec hh, compare_lt_iff_lt.mpr hlt]
  · have hx : x0 = c := compare_eq_iff_eq.mp hσ
    simp only [settle1D, Option.some.injEq] at hset
    rw [hx, hset]
  · have hx : c < x0 := compare_gt_iff_gt.mp hσ
    simp only [settle1D] at hset
    split_ifs at hset with hle
    cases hset
    have hgt : 0 < x0 - β / h := by linarith
    rw [cmp_sub_zero, hrel, ← scaleOrd_spec hh, compare_gt_iff_gt.mpr hgt]

theorem settle1D_count {N : ℕ} (h β : Fin N → ℝ) (c : ℝ) (σ : Ordering)
    (hcL : 2 * (Finset.univ.filter fun i => β i / h i < c).card ≤ N)
    (hcG : 2 * (Finset.univ.filter fun i => c < β i / h i).card ≤ N) :
    N / 2 ≤ (Finset.univ.filter fun i => (settle1D c σ (h i) (β i)).isSome).card := by
  cases σ
  · have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (fun i => β i / h i < c)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have heq : (Finset.univ.filter fun i => (settle1D c .lt (h i) (β i)).isSome) =
        Finset.univ.filter fun i => ¬ (β i / h i < c) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, settle1D, not_lt]
      by_cases hle : c ≤ β i / h i <;> simp [hle]
    rw [heq]; omega
  · have heq : (Finset.univ.filter fun i => (settle1D c .eq (h i) (β i)).isSome) = Finset.univ := by
      ext i; simp [settle1D]
    rw [heq, Finset.card_univ, Fintype.card_fin]
    exact Nat.div_le_self N 2
  · have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (fun i => c < β i / h i)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have heq : (Finset.univ.filter fun i => (settle1D c .gt (h i) (β i)).isSome) =
        Finset.univ.filter fun i => ¬ (c < β i / h i) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, settle1D, not_lt]
      by_cases hle : β i / h i ≤ c <;> simp [hle]
    rw [heq]; omega

/-! ## Explicit 2D Planar Pair Decoding Rule -/

/-- Given `σ1 = compare (u - v) 0` and `σ2 = compare (β * u + α * v) 0` with `0 < α`, `0 < β`:
returns `(true, compare (pL * u) 0)` when `σ1 = σ2`, and `(false, compare (pG * v) 0)` otherwise. -/
noncomputable def decodePair (pL pG : ℝ) (σ1 σ2 : Ordering) : Bool × Ordering :=
  if σ1 = σ2 then
    (true, scaleOrd pL σ1)
  else
    (false, scaleOrd pG (if σ2 = .eq then σ1.swap else σ2))

theorem decodePair_sound {α β u v pL pG : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hpL : pL ≠ 0) (hpG : pG ≠ 0) {σ1 σ2 : Ordering}
    (hσ1 : compare (u - v) 0 = σ1)
    (hσ2 : compare (β * u + α * v) 0 = σ2) :
    ((decodePair pL pG σ1 σ2).1 = true → compare (pL * u) 0 = (decodePair pL pG σ1 σ2).2) ∧
    ((decodePair pL pG σ1 σ2).1 = false → compare (pG * v) 0 = (decodePair pL pG σ1 σ2).2) := by
  subst hσ1; subst hσ2
  by_cases heq : compare (u - v) 0 = compare (β * u + α * v) 0
  · simp only [decodePair, if_pos heq]
    refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    have hu : compare u 0 = compare (u - v) 0 := by
      rcases lt_trichotomy (u - v) 0 with h1 | h1 | h1
      · rw [compare_lt_iff_lt.mpr h1] at heq ⊢
        have h2 := compare_lt_iff_lt.mp heq.symm
        exact compare_lt_iff_lt.mpr (by nlinarith)
      · rw [compare_eq_iff_eq.mpr h1] at heq ⊢
        have h2 := compare_eq_iff_eq.mp heq.symm
        exact compare_eq_iff_eq.mpr (by nlinarith)
      · rw [compare_gt_iff_gt.mpr h1] at heq ⊢
        have h2 := compare_gt_iff_gt.mp heq.symm
        exact compare_gt_iff_gt.mpr (by nlinarith)
    rw [← scaleOrd_spec hpL u, hu]
  · simp only [decodePair, if_neg heq]
    refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
    set τ := if compare (β * u + α * v) 0 = .eq then (compare (u - v) 0).swap
             else compare (β * u + α * v) 0
    have hv : compare v 0 = τ := by
      dsimp only [τ]
      rcases cmp_tri (u - v) with ⟨h1, e1⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
      rcases cmp_tri (β * u + α * v) with ⟨h2, e2⟩ | ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
      simp only [e1, e2, not_true_eq_false, reduceCtorEq, if_true, if_false,
        Ordering.swap] at heq ⊢
      · exact compare_gt_iff_gt.mpr (by nlinarith)
      · exact compare_gt_iff_gt.mpr (by nlinarith)
      · exact compare_lt_iff_lt.mpr (by nlinarith)
      · exact compare_gt_iff_gt.mpr (by nlinarith)
      · exact compare_lt_iff_lt.mpr (by nlinarith)
      · exact compare_lt_iff_lt.mpr (by nlinarith)
    rw [← scaleOrd_spec hpG v, hv]

/-! ## Natural Arithmetic Lemmas for Pruning Counts and Recurrences -/

theorem zero_plus_div_ge (z nz K : ℕ) (hK : 1 ≤ K) :
    (z + nz) / K ≤ z + nz / K := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp
  · have hmod := Nat.div_add_mod nz K
    have hlt : nz % K < K := Nat.mod_lt nz hK
    have hkz : z ≤ K * z := le_mul_of_one_le_left (Nat.zero_le z) hK
    have h1 : z + nz < (z + nz / K + 1) * K := by
      calc z + nz = z + (K * (nz / K) + nz % K) := by rw [hmod]
        _ ≤ K * z + K * (nz / K) + nz % K := by omega
        _ < K * z + K * (nz / K) + K := by omega
        _ = (z + nz / K + 1) * K := by ring
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hK).mpr h1)

theorem approachI_div_step (d N : ℕ) :
    let K := 2 ^ (2 ^ (d + 1) - 1)
    ((N / 2) / K) / K = N / 2 ^ (2 ^ (d + 2) - 1) := by
  intro K
  have he : 2 ^ (2 ^ (d + 2) - 1) = 2 * K * K := by
    dsimp only [K]
    rw [← pow_succ', ← pow_add]
    congr 1
    have : 2 ^ (d + 2) = 2 * 2 ^ (d + 1) := by rw [pow_succ]; ring
    have : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
    omega
  rw [he, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]

/-- Linear recurrence solution for Megiddo pruning: if for `r > 4 * K` (`1 ≤ K`),
`T r ≤ T r' + A * (r + 1)` for some `r' ≤ r - r / (2 * K)` and for `r ≤ 4 * K`, `T r ≤ B`,
then `T r ≤ (B + 8 * K * A) * (r + 1)`. -/
theorem linear_pruning_bound (K A B : ℕ) (hK : 1 ≤ K)
    (T : ℕ → ℕ)
    (hBase : ∀ r ≤ 4 * K, T r ≤ B)
    (hStep : ∀ r, 4 * K < r → ∃ r', r' ≤ r - r / (2 * K) ∧
      ((∀ s ≤ r', T s ≤ (B + 8 * K * A) * (s + 1)) →
      T r ≤ T r' + A * (r + 1))) :
    ∀ r, T r ≤ (B + 8 * K * A) * (r + 1) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r ≤ 4 * K
    · calc T r ≤ B := hBase r hr
        _ ≤ B * 1 := by omega
        _ ≤ (B + 8 * K * A) * (r + 1) := Nat.mul_le_mul (by omega) (by omega)
    · push Not at hr
      set C := B + 8 * K * A
      have hdiv_pos : 2 ≤ r / (2 * K) := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
      have hdiv_le : r / (2 * K) ≤ r := Nat.div_le_self r (2 * K)
      obtain ⟨r', hr'le, hrec⟩ := hStep r hr
      have hr'_lt : r' < r := by omega
      have hstep := hrec (fun s hs => ih s (lt_of_le_of_lt hs hr'_lt))
      have hir' := ih r' hr'_lt
      have hdrop : r + 1 ≤ 8 * K * (r / (2 * K)) := by
        have hmod := Nat.div_add_mod r (2 * K)
        have hlt : r % (2 * K) < 2 * K := Nat.mod_lt r (by omega)
        nlinarith
      have hCA : A * (r + 1) ≤ C * (r - r') := by
        have hrr' : r / (2 * K) ≤ r - r' := by omega
        calc A * (r + 1) ≤ A * (8 * K * (r / (2 * K))) := Nat.mul_le_mul_left A hdrop
          _ = (8 * K * A) * (r / (2 * K)) := by ring
          _ ≤ C * (r / (2 * K)) := Nat.mul_le_mul_right _ (by dsimp [C]; omega)
          _ ≤ C * (r - r') := Nat.mul_le_mul_left C hrr'
      calc T r ≤ T r' + A * (r + 1) := hstep
        _ ≤ C * (r' + 1) + C * (r - r') := Nat.add_le_add hir' hCA
        _ = C * (r + 1) := by
            have : (r' + 1) + (r - r') = r + 1 := by omega
            rw [← Nat.mul_add, this]

/-- If `z + l + e + g = M`, `2 * l ≤ l + e + g`, and `2 * g ≤ l + e + g`, then
`M / 2 ≤ z + e + min l g` and `z + e + min l g ≤ M`. -/
theorem median_split_pair_count {z l e g M : ℕ}
    (hM : z + l + e + g = M)
    (hl : 2 * l ≤ l + e + g)
    (hg : 2 * g ≤ l + e + g) :
    M / 2 ≤ z + e + min l g ∧ z + e + min l g ≤ M := by
  omega

end MegiddoLP.ConstructiveApproachI


