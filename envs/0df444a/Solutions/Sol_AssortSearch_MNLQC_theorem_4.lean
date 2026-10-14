-- Prove2me | solution 1 for AssortSearch.MNLQC.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:51:28.282973+00:00
-- url     : https://prove2.me/submissions/7b929f33-4f36-44ab-844c-b883164d5d12

import Mathlib
import Definitions.Def_AssortSearch_MNLQC_Model

open AssortSearch.MNLQC RetailVariety.Structure

namespace TwentyAnalysis.MNL

variable {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
  (S : Finset (Fin n)) (j : Fin n)

lemma total_pos (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) : 0 < prefTotal v v0 S := by
  unfold prefTotal
  have hs : 0 ≤ ∑ i ∈ S, v i := Finset.sum_nonneg fun i _ => (hv i).le
  linarith

lemma pref_lt (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) {i : Fin n} (hi : i ∈ S) :
    v i < prefTotal v v0 S := by
  have hs : v i ≤ ∑ k ∈ S, v k := Finset.single_le_sum (fun k _ => (hv k).le) hi
  unfold prefTotal
  linarith

lemma demand_formula (hj : j ∉ S) (x : ℝ) (i : Fin n) :
    demandAdded v v0 S j x i = (if i = j then x else v i) / (x + prefTotal v v0 S) := by
  have hs : ∑ k ∈ S, Function.update v j x k = ∑ k ∈ S, v k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact Function.update_of_ne (by intro h; apply hj; simpa [h] using hk) _ _
  unfold demandAdded share
  rw [Finset.sum_insert hj, hs]
  simp only [Function.update_self]
  rw [show x + ∑ k ∈ S, v k + v0 = x + prefTotal v v0 S by unfold prefTotal; ring]
  by_cases hi : i = j <;> simp [hi, Function.update_of_ne]

lemma canonical (hj : j ∉ S) (x : ℝ) : hm m c v v0 S j x =
    (m j * (x / (x + prefTotal v v0 S)) - c (x / (x + prefTotal v v0 S))) +
    ∑ i ∈ S, (m i * (v i / (x + prefTotal v v0 S)) - c (v i / (x + prefTotal v v0 S))) -
    ∑ i ∈ S, profitS m c v v0 S i := by
  unfold hm lossL profitAdded
  rw [demand_formula v v0 S j hj x j]
  simp only [ite_true]
  have hs : (∑ i ∈ S, (m i * demandAdded v v0 S j x i - c (demandAdded v v0 S j x i))) =
      ∑ i ∈ S, (m i * (v i / (x + prefTotal v v0 S)) - c (v i / (x + prefTotal v v0 S))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [demand_formula v v0 S j hj x i, if_neg (by intro h; apply hj; simpa [h] using hi)]
  rw [hs]
  ring

lemma ratio_domain (V : ℝ) (hV : 0 < V) (x : ℝ) (hx : 0 ≤ x) : x / (x + V) ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg hx (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

lemma ratio_strict (V : ℝ) (hV : 0 < V) (x : ℝ) (hx : 0 < x) : x / (x + V) ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨div_pos hx (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

lemma old_ratio_domain (V w : ℝ) (hV : 0 < V) (hw : 0 < w) (hwV : w < V)
    (x : ℝ) (hx : 0 ≤ x) : w / (x + V) ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨div_pos hw (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

lemma profit_concave_cost (hc : ConcaveOn ℝ (Set.Icc 0 1) c) (margin p q u w : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    margin * (p * u + q * w) - c (p * u + q * w) ≤
      p * (margin * u - c u) + q * (margin * w - c w) := by
  have h := hc.2 hu hw hp hq hpq
  simp only [smul_eq_mul] at h
  nlinarith

lemma quasiconvex (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (hc : ConcaveOn ℝ (Set.Icc 0 1) c) (hj : j ∉ S) :
    QuasiconvexOn ℝ (Set.Ici 0) (hm m c v v0 S j) := by
  rw [quasiconvexOn_iff_le_max]
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  simp only [smul_eq_mul]
  let V := prefTotal v v0 S
  have hV : 0 < V := total_pos v v0 S hv hv0
  let z := a * x + b * y
  have hz : 0 ≤ z := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hDx : 0 < x + V := by linarith
  have hDy : 0 < y + V := by linarith
  have hDz : 0 < z + V := by linarith
  let p := a * (x + V) / (z + V)
  let q := b * (y + V) / (z + V)
  have hp : 0 ≤ p := div_nonneg (mul_nonneg ha hDx.le) hDz.le
  have hq : 0 ≤ q := div_nonneg (mul_nonneg hb hDy.le) hDz.le
  have hpq : p + q = 1 := by
    dsimp [p, q, z]
    rw [← add_div]
    apply (div_eq_one_iff_eq (ne_of_gt hDz)).2
    nlinarith
  have hjratio : z / (z + V) = p * (x / (x + V)) + q * (y / (y + V)) := by
    dsimp [p, q, z]
    field_simp [ne_of_gt hDx, ne_of_gt hDy, ne_of_gt hDz]
    <;> ring
  have hiratio (w : ℝ) : w / (z + V) = p * (w / (x + V)) + q * (w / (y + V)) := by
    dsimp [p, q]
    field_simp [ne_of_gt hDx, ne_of_gt hDy, ne_of_gt hDz]
    nlinarith [congrArg (fun t : ℝ => w * t) hab]
  have hjp := profit_concave_cost c hc (m j) p q _ _ hp hq hpq
    (ratio_domain V hV x hx) (ratio_domain V hV y hy)
  rw [← hjratio] at hjp
  have hip : ∀ i ∈ S, m i * (v i / (z + V)) - c (v i / (z + V)) ≤
      p * (m i * (v i / (x + V)) - c (v i / (x + V))) +
      q * (m i * (v i / (y + V)) - c (v i / (y + V))) := by
    intro i hi
    have hix := old_ratio_domain V (v i) hV (hv i) (pref_lt v v0 S hv hv0 hi) x hx
    have hiy := old_ratio_domain V (v i) hV (hv i) (pref_lt v v0 S hv hv0 hi) y hy
    simpa only [← hiratio (v i)] using profit_concave_cost c hc (m i) p q _ _ hp hq hpq
      (Set.Ioo_subset_Icc_self hix) (Set.Ioo_subset_Icc_self hiy)
  have hs := Finset.sum_le_sum hip
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hhm : hm m c v v0 S j z ≤ p * hm m c v v0 S j x + q * hm m c v v0 S j y := by
    rw [canonical m c v v0 S j hj z, canonical m c v v0 S j hj x, canonical m c v v0 S j hj y]
    change _ ≤ _
    dsimp [V] at hjp hs
    nlinarith [congrArg (fun t : ℝ => t * (∑ i ∈ S, profitS m c v v0 S i)) hpq]
  have hmax := add_le_add (mul_le_mul_of_nonneg_left (le_max_left (hm m c v v0 S j x) (hm m c v v0 S j y)) hp)
    (mul_le_mul_of_nonneg_left (le_max_right (hm m c v v0 S j x) (hm m c v v0 S j y)) hq)
  have heq : p * max (hm m c v v0 S j x) (hm m c v v0 S j y) + q * max (hm m c v v0 S j x) (hm m c v v0 S j y) =
      max (hm m c v v0 S j x) (hm m c v v0 S j y) := by rw [← add_mul, hpq, one_mul]
  exact hhm.trans (heq ▸ hmax)

end TwentyAnalysis.MNL

theorem solution
    {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (hc_concave : ConcaveOn ℝ (Set.Icc 0 1) c) (hc_mono : MonotoneOn c (Set.Icc 0 1))
    (hj : j ∉ S) :
    QuasiconvexOn ℝ (Set.Ici 0) (hm m c v v0 S j) := by
  exact TwentyAnalysis.MNL.quasiconvex m c v v0 S j hv hv0 hc_concave hj
