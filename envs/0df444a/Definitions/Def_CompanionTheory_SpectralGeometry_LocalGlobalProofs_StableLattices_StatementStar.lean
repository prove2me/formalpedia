-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementStar
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementStar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:12.070866+00:00
-- url     : https://prove2.me/theorems/f24543be-94b5-4a38-966e-a52b2f5b1ad6
-- title:
--   Statement Star
-- statement:
--   Definitions and structural lemmas for Statement Star, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/StatementStar.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_SmallPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open scoped InnerProductSpace
namespace GlobalTheory.CompanionTheory.RgFl.StarPf
section
variable {A V : Type} [Ring A] [Algebra ℂ A]
def restrictAlg [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) : A →ₐ[ℂ] Module.End ℂ W where
  toFun h := (ρ h).restrict (hW h)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp
  commutes' c := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]
end
end GlobalTheory.CompanionTheory.RgFl.StarPf


