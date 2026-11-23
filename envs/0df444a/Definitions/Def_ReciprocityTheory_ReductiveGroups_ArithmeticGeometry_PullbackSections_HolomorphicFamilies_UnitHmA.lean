-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_UnitHmA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_UnitHmA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:13.962847+00:00
-- url     : https://prove2.me/theorems/df5a4ec9-d87e-4b00-825c-b06198ef3318
-- title:
--   Unit Hm A
-- statement:
--   Definitions and structural lemmas for Unit Hm A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/UnitHmA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {g : ℕ}
theorem hermForm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]
theorem hermForm_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm, smul_dotProduct]
theorem hermForm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
theorem hermForm_rsmul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = c * hermForm Hm z w := by
  simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul]
def imForm (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun z z' w => by rw [hermForm_add_left, Complex.add_im])
    (fun c z w => by
      rw [show (c • z : Fin g → ℂ) = (c : ℂ) • z from by funext i; simp [Complex.real_smul],
        hermForm_smul_left, smul_eq_mul, Complex.im_ofReal_mul])
    (fun z w w' => by rw [hermForm_add_right, Complex.add_im])
    (fun c z w => by rw [hermForm_rsmul_right, smul_eq_mul]; simp)
end ReciprocityTheory.ChartRestriction.G.PullbackSections.UH


