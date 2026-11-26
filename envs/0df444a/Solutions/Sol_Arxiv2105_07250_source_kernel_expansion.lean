-- Prove2me | solution 1 for Arxiv2105_07250.source_kernel_expansion
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T03:02:51.8544+00:00
-- url     : https://prove2.me/submissions/7aa46ebd-d2bf-4deb-9700-f168b0acb394

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace S76SE

lemma ib {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (hF : Measurable F) (hb : ∀ r, |F r| ≤ 1) : Integrable F P :=
  (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
    (Eventually.of_forall fun r => by simpa [Real.norm_eq_abs] using hb r)

lemma b2 (x y : ℝ) (f g : ℝ → ℝ) (hf : ∀ z, |f z| ≤ 1) (hg : ∀ z, |g z| ≤ 1) :
    |f x * g y| ≤ 1 := by
  rw [abs_mul]; exact mul_le_one₀ (hf x) (abs_nonneg _) (hg y)

end S76SE

open Arxiv2105_07250 S76SE in
theorem solution {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (w a : ι → ℝ) (hw : Function.Injective w)
    (θ : ι → Ω → ℝ) (hθ : ∀ i, Measurable (θ i)) (t' t'' : ℝ) :
    ∫ r, sourceSignature w a (fun i => θ i r) t' * sourceSignature w a (fun i => θ i r) t'' ∂P =
      (∑ i, a i ^ 2 *
          (Real.cos (w i * t') * Real.cos (w i * t'') * ∫ r, Real.cos (θ i r) ^ 2 ∂P
            - Real.sin (w i * (t' + t'')) * ∫ r, Real.cos (θ i r) * Real.sin (θ i r) ∂P
            + Real.sin (w i * t') * Real.sin (w i * t'') * ∫ r, Real.sin (θ i r) ^ 2 ∂P)) +
      ∑ i, ∑ j ∈ Finset.univ.erase i, a i * a j *
          (Real.cos (w i * t') * Real.cos (w j * t'') * ∫ r, Real.cos (θ i r) * Real.cos (θ j r) ∂P
            - Real.cos (w i * t') * Real.sin (w j * t'') *
                ∫ r, Real.cos (θ i r) * Real.sin (θ j r) ∂P
            - Real.sin (w i * t') * Real.cos (w j * t'') *
                ∫ r, Real.sin (θ i r) * Real.cos (θ j r) ∂P
            + Real.sin (w i * t') * Real.sin (w j * t'') *
                ∫ r, Real.sin (θ i r) * Real.sin (θ j r) ∂P) := by
  have hc := Real.abs_cos_le_one
  have hs := Real.abs_sin_le_one
  have hcc : ∀ i j, Integrable (fun r => Real.cos (θ i r) * Real.cos (θ j r)) P := fun i j =>
    ib P _ (((hθ i).cos).mul ((hθ j).cos)) (fun r => b2 _ _ _ _ hc hc)
  have hcs : ∀ i j, Integrable (fun r => Real.cos (θ i r) * Real.sin (θ j r)) P := fun i j =>
    ib P _ (((hθ i).cos).mul ((hθ j).sin)) (fun r => b2 _ _ _ _ hc hs)
  have hsc : ∀ i j, Integrable (fun r => Real.sin (θ i r) * Real.cos (θ j r)) P := fun i j =>
    ib P _ (((hθ i).sin).mul ((hθ j).cos)) (fun r => b2 _ _ _ _ hs hc)
  have hss : ∀ i j, Integrable (fun r => Real.sin (θ i r) * Real.sin (θ j r)) P := fun i j =>
    ib P _ (((hθ i).sin).mul ((hθ j).sin)) (fun r => b2 _ _ _ _ hs hs)
  set T : ι → ι → Ω → ℝ := fun i j r => a i * a j *
    (Real.cos (w i * t') * Real.cos (w j * t'') * (Real.cos (θ i r) * Real.cos (θ j r))
      - Real.cos (w i * t') * Real.sin (w j * t'') * (Real.cos (θ i r) * Real.sin (θ j r))
      - Real.sin (w i * t') * Real.cos (w j * t'') * (Real.sin (θ i r) * Real.cos (θ j r))
      + Real.sin (w i * t') * Real.sin (w j * t'') * (Real.sin (θ i r) * Real.sin (θ j r)))
    with hT
  have hTi : ∀ i j, Integrable (T i j) P := fun i j =>
    ((((hcc i j).const_mul _).sub ((hcs i j).const_mul _)).sub ((hsc i j).const_mul _)
      |>.add ((hss i j).const_mul _)).const_mul _
  have hTint : ∀ i j, ∫ r, T i j r ∂P = a i * a j *
      (Real.cos (w i * t') * Real.cos (w j * t'') * ∫ r, Real.cos (θ i r) * Real.cos (θ j r) ∂P
        - Real.cos (w i * t') * Real.sin (w j * t'') * ∫ r, Real.cos (θ i r) * Real.sin (θ j r) ∂P
        - Real.sin (w i * t') * Real.cos (w j * t'') * ∫ r, Real.sin (θ i r) * Real.cos (θ j r) ∂P
        + Real.sin (w i * t') * Real.sin (w j * t'') *
            ∫ r, Real.sin (θ i r) * Real.sin (θ j r) ∂P) := by
    intro i j
    simp only [hT]
    rw [integral_const_mul, integral_add, integral_sub, integral_sub, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul]
    all_goals first
      | exact (hcc i j).const_mul _
      | exact (hcs i j).const_mul _
      | exact (hsc i j).const_mul _
      | exact (hss i j).const_mul _
      | exact ((hcc i j).const_mul _).sub ((hcs i j).const_mul _)
      | exact (((hcc i j).const_mul _).sub ((hcs i j).const_mul _)).sub ((hsc i j).const_mul _)
  have hpt : ∀ r, sourceSignature w a (fun i => θ i r) t' * sourceSignature w a (fun i => θ i r) t''
      = ∑ i, ∑ j, T i j r := by
    intro r
    unfold sourceSignature
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    simp only [hT, Real.cos_add]; ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hTi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hTi _ j), hTint]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  have e1 : ∫ r, Real.cos (θ i r) * Real.cos (θ i r) ∂P = ∫ r, Real.cos (θ i r) ^ 2 ∂P := by
    congr 1; funext r; ring
  have e2 : ∫ r, Real.sin (θ i r) * Real.sin (θ i r) ∂P = ∫ r, Real.sin (θ i r) ^ 2 ∂P := by
    congr 1; funext r; ring
  have e3 : ∫ r, Real.sin (θ i r) * Real.cos (θ i r) ∂P =
      ∫ r, Real.cos (θ i r) * Real.sin (θ i r) ∂P := by
    congr 1; funext r; ring
  rw [e1, e2, e3, show w i * (t' + t'') = w i * t' + w i * t'' by ring, Real.sin_add]
  ring
