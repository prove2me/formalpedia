-- Prove2me | Definitions.Def_CK_GeneralCK_FourMomentLowerBound
-- name    : CK_GeneralCK_FourMomentLowerBound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:32:35.351774+00:00
-- url     : https://prove2.me/theorems/16293f24-d8ae-4c53-951e-69668bb4da34
-- title:
--   Courtade–Kumar proof module `GeneralCK.FourMomentLowerBound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FourMomentLowerBound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FourMomentLowerBound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FourMomentLowerBound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FourMomentLowerBound.lean)

import Definitions.Def_CK_GeneralCK_FourMomentDefs
import Definitions.Def_CK_GeneralCK_RadialConvexity

namespace GeneralCK.InteriorLaw
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem abs_mean_difference_le (μ : InteriorLaw ι) :
    |μ.a-μ.b| ≤ μ.avg (fun i => |μ.left i-μ.right i|) := by
  change |μ.avg μ.left-μ.avg μ.right| ≤ _
  rw [← μ.avg_sub]
  have hh := Finset.abs_sum_le_sum_abs (fun i => μ.weight i*(μ.left i-μ.right i)) Finset.univ
  simpa only [avg, abs_mul, abs_of_nonneg (μ.weight_nonneg _)] using hh

theorem F_moments_le_avg (μ : InteriorLaw ι) :
    F |μ.a-μ.b| ((μ.e+μ.f)/2) ≤
      μ.avg (fun i => F |μ.left i-μ.right i| ((H (μ.left i)+H (μ.right i))/2)) := by
  have hent : μ.avg (fun i => (H (μ.left i)+H (μ.right i))/2) = (μ.e+μ.f)/2 := by
    simp only [avg, e, f, Function.comp_apply, div_eq_mul_inv, ← mul_assoc, mul_add]
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
  have hh := F_sum_le Finset.univ μ.weight (fun i => |μ.left i-μ.right i|)
    (fun i => (H (μ.left i)+H (μ.right i))/2)
    (fun i _ => μ.weight_nonneg i) μ.weight_sum (fun i _ => abs_nonneg _) (by
      intro i _
      have hleft := H_pos (μ.left_interior i).1 (μ.left_interior i).2
      have hright := H_pos (μ.right_interior i).1 (μ.right_interior i).2
      positivity)
  change F (μ.avg (fun i => |μ.left i-μ.right i|))
    (μ.avg (fun i => (H (μ.left i)+H (μ.right i))/2)) ≤ _ at hh
  rw [hent] at hh
  exact (F_mono_radius (abs_nonneg _) μ.abs_mean_difference_le
    (by have := μ.e_pos; have := μ.f_pos; positivity)).trans hh

/-- Finite-law LB1 assembly. Atom reflection and entropy-correction convexity
are explicit unresolved premises, not asserted upstream theorems. -/
theorem fourMomentLowerBound_le_cost (μ : InteriorLaw ι)
    (hreflect : ∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
      entropyCorrection (H u) (H v) ≤ atomCorrection u v)
    (hconvex : ConvexOn ℝ (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1)
      (fun p : ℝ × ℝ => entropyCorrection p.1 p.2)) :
    fourMomentLowerBound μ.a μ.b μ.e μ.f ≤ μ.cost := by
  have hj := hconvex.map_sum_le (t := Finset.univ) (w := μ.weight)
    (p := fun i => (H (μ.left i), H (μ.right i)))
    (fun i _ => μ.weight_nonneg i) μ.weight_sum (by
      intro i _
      exact ⟨⟨H_pos (μ.left_interior i).1 (μ.left_interior i).2, H_le_one _⟩,
        ⟨H_pos (μ.right_interior i).1 (μ.right_interior i).2, H_le_one _⟩⟩)
  have hg : entropyCorrection μ.e μ.f ≤
      μ.avg (fun i => entropyCorrection (H (μ.left i)) (H (μ.right i))) := by
    simpa only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, e, f, avg, Function.comp_apply] using hj
  have hr := μ.avg_mono (fun i => hreflect (μ.left i) (μ.right i)
    (μ.left_interior i).1 (μ.left_interior i).2 (μ.right_interior i).1 (μ.right_interior i).2)
  have he : μ.avg (fun i => atomCorrection (μ.left i) (μ.right i)) =
      μ.cost-μ.avg (fun i => F |μ.left i-μ.right i| ((H (μ.left i)+H (μ.right i))/2)) := by
    unfold atomCorrection
    rw [μ.avg_sub]
    rfl
  rw [he] at hr
  have hF := μ.F_moments_le_avg
  unfold fourMomentLowerBound
  linarith

theorem phi_gap_le_cost_of_fourMoment (μ : InteriorLaw ι)
    (hreflect : ∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
      entropyCorrection (H u) (H v) ≤ atomCorrection u v)
    (hconvex : ConvexOn ℝ (Ioc (0:ℝ) 1 ×ˢ Ioc (0:ℝ) 1)
      (fun p : ℝ × ℝ => entropyCorrection p.1 p.2))
    (hgap : 0 ≤ pureGap μ.a μ.b μ.e μ.f) :
    candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  have hh := μ.fourMomentLowerBound_le_cost hreflect hconvex
  unfold pureGap at hgap
  linarith

end GeneralCK.InteriorLaw


