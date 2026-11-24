-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:46.158237+00:00
-- url     : https://prove2.me/submissions/f1c70ca2-abb2-459f-b748-d382c9a37dc2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_FunctorialResolution_Blowup_comap_ker_comp_of_isOpenImmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.solution {Y Y' : Scheme.{u}} (g : Y ⟶ Y') [IsIso g]
    (I : Y'.IdealSheafData) :
    ∃ m : (I.comap g).subscheme ⟶ I.subscheme,
      IsIso m ∧ m ≫ I.subschemeι = (I.comap g).subschemeι ≫ g := by
  have : QuasiCompact (I.comap g).subschemeι := inferInstance
  have : QuasiCompact ((I.comap g).subschemeι ≫ g) := inferInstance
  have hq := FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (I.comap g).subschemeι g
  rw [Scheme.IdealSheafData.ker_subschemeι] at hq
  have e1 : ∀ J : Y'.IdealSheafData, (J.comap g).comap (inv g) = J := by
    intro J
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  have hkk : ((I.comap g).subschemeι ≫ g).ker = I.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι,
      ← e1 (((I.comap g).subschemeι ≫ g).ker), hq, e1]
  refine ⟨IsClosedImmersion.lift I.subschemeι ((I.comap g).subschemeι ≫ g)
      (le_of_eq hkk.symm), ?_, IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq ((I.comap g).subschemeι ≫ g) I.subschemeι _
    (IsClosedImmersion.lift_fac _ _ _) hkk
end AlgebraicGeometry.Scheme.IdealSheafData
