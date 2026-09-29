-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionRatioGlobalBridge
-- name    : CK_GeneralCK_CorrectionRatioGlobalBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:14:33.949893+00:00
-- url     : https://prove2.me/theorems/8945a9b8-a992-459e-89cd-0589cb689cc8
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionRatioGlobalBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionRatioGlobalBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionRatioGlobalBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionRatioGlobalBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionRatioGlobalBridge.lean)

import Definitions.Def_CK_GeneralCK_CorrectionInteriorRatioBridge
import Definitions.Def_CK_GeneralCK_CorrectionConvexityCriterion

namespace GeneralCK.Correction

/-- The probability coordinates used by the correction certificates parametrize
every point of the open entropy triangle. -/
theorem orderedTriangle_probability_ratio {e f : ℝ}
    (htri : (e, f) ∈ orderedTriangle) :
    let u := entropyInverse e
    let w := entropyInverse f
    let rho := (w-u)/(1/2-u)
    0 < u ∧ u < 1/2 ∧ 0 < rho ∧ rho < 1 ∧
      u+rho*(1/2-u)=w ∧ H u=e ∧ H w=f := by
  rcases htri with ⟨he, hef, hf⟩
  have he1 : e < 1 := hef.trans hf
  have hu : 0 < entropyInverse e := entropyInverse_pos he he1.le
  have huhalf : entropyInverse e < 1/2 := entropyInverse_lt_half he.le he1
  have hw : 0 < entropyInverse f := entropyInverse_pos (he.trans hef) hf.le
  have hwhalf : entropyInverse f < 1/2 :=
    entropyInverse_lt_half (he.trans hef).le hf
  have huw : entropyInverse e < entropyInverse f :=
    entropyInverse_strictMonoOn ⟨he.le, he1.le⟩ ⟨(he.trans hef).le, hf.le⟩ hef
  have hden : 0 < (1/2:ℝ)-entropyInverse e := sub_pos.mpr huhalf
  have hr : 0 < (entropyInverse f-entropyInverse e) /
      ((1/2:ℝ)-entropyInverse e) := div_pos (sub_pos.mpr huw) hden
  have hr1 : (entropyInverse f-entropyInverse e) /
      ((1/2:ℝ)-entropyInverse e) < 1 :=
    (div_lt_one hden).2 (by linarith)
  have hreconstruct : entropyInverse e+
      ((entropyInverse f-entropyInverse e)/((1/2:ℝ)-entropyInverse e))*
        ((1/2:ℝ)-entropyInverse e)=entropyInverse f := by
    rw [div_mul_cancel₀ _ hden.ne']
    ring
  have hHe := (entropyInverse_spec he.le he1.le).2.2
  have hHf := (entropyInverse_spec (he.trans hef).le hf.le).2.2
  exact ⟨hu, huhalf, hr, hr1, hreconstruct, hHe, hHf⟩

/-- A certificate covering all interior probability-ratio coordinates supplies
exactly the two global Hessian sign hypotheses used by correction convexity.
The determinant certificate may be non-strict, matching the analytic criterion. -/
theorem orderedTriangle_signs_of_ratio_kernel
    (hkernel : ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Natural.m11 u (u+rho*(1/2-u)) ∧
      0 ≤ Natural.kdet u (u+rho*(1/2-u))) :
    (∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2) ∧
      (∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) := by
  have hpoint : ∀ e f : ℝ, (e, f) ∈ orderedTriangle →
      0 < Mleft e f ∧ 0 ≤ Mdet e f := by
    intro e f htri
    let u := entropyInverse e
    let w := entropyInverse f
    let rho := (w-u)/(1/2-u)
    have hc := orderedTriangle_probability_ratio htri
    change 0 < u ∧ u < 1/2 ∧ 0 < rho ∧ rho < 1 ∧
      u+rho*(1/2-u)=w ∧ H u=e ∧ H w=f at hc
    rcases hc with ⟨hu, huhalf, hr, hr1, huw, hHu, hHw⟩
    have hk := hkernel u rho hu huhalf hr hr1
    have heq := Natural.kernel_eq_actual_ratio hu (sub_pos.mpr huhalf) hr hr1
    rw [heq.1, heq.2, huw, hHu, hHw] at hk
    have hf0 : 0 < f := htri.1.trans htri.2.1
    have hf1 : f < 1 := htri.2.2
    exact ⟨hk.1, (Mdet_nonneg_iff_Kfactored_nonneg hf0 hf1).2 hk.2⟩
  constructor
  · rintro ⟨e, f⟩ htri
    exact (hpoint e f htri).1
  · rintro ⟨e, f⟩ htri
    exact (hpoint e f htri).2

/-- Strictly positive numerical determinant certificates can be fed directly
to the non-strict global correction criterion. -/
theorem orderedTriangle_signs_of_strict_ratio_kernel
    (hkernel : ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Natural.m11 u (u+rho*(1/2-u)) ∧
      0 < Natural.kdet u (u+rho*(1/2-u))) :
    (∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2) ∧
      (∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) := by
  apply orderedTriangle_signs_of_ratio_kernel
  intro u rho hu huhalf hr hr1
  exact ⟨(hkernel u rho hu huhalf hr hr1).1,
    (hkernel u rho hu huhalf hr hr1).2.le⟩

/-- Coordinate-level family theorems generated by the correction pipeline
already state positivity of the actual Hessian minors.  A family covering the
whole open probability-ratio rectangle therefore supplies the global signs
without replaying the natural-kernel equalities. -/
theorem orderedTriangle_signs_of_actual_ratio_family
    (hfamily : ∀ u rho : ℝ, 0 < u → u < 1/2 → 0 < rho → rho < 1 →
      0 < Mleft (H u) (H (u+rho*(1/2-u))) ∧
      0 < Mdet (H u) (H (u+rho*(1/2-u)))) :
    (∀ p ∈ orderedTriangle, 0 < Mleft p.1 p.2) ∧
      (∀ p ∈ orderedTriangle, 0 ≤ Mdet p.1 p.2) := by
  have hpoint : ∀ e f : ℝ, (e, f) ∈ orderedTriangle →
      0 < Mleft e f ∧ 0 ≤ Mdet e f := by
    intro e f htri
    let u := entropyInverse e
    let w := entropyInverse f
    let rho := (w-u)/(1/2-u)
    have hc := orderedTriangle_probability_ratio htri
    change 0 < u ∧ u < 1/2 ∧ 0 < rho ∧ rho < 1 ∧
      u+rho*(1/2-u)=w ∧ H u=e ∧ H w=f at hc
    rcases hc with ⟨hu, huhalf, hr, hr1, huw, hHu, hHw⟩
    have hs := hfamily u rho hu huhalf hr hr1
    rw [huw, hHu, hHw] at hs
    exact ⟨hs.1, hs.2.le⟩
  constructor
  · rintro ⟨e, f⟩ htri
    exact (hpoint e f htri).1
  · rintro ⟨e, f⟩ htri
    exact (hpoint e f htri).2

#print axioms orderedTriangle_probability_ratio
#print axioms orderedTriangle_signs_of_ratio_kernel
#print axioms orderedTriangle_signs_of_strict_ratio_kernel
#print axioms orderedTriangle_signs_of_actual_ratio_family

end GeneralCK.Correction


