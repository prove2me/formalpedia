-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/53f76680-dfbc-5273-b441-8e2ab709b048

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom Hom.image_preimage_eq_opensRange_inf restrictFunctor Modules Opens Opens.opensRange_ι"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback Hom restrictFunctor restrictFunctorIsoPullback Hom.isIso_iff_isIso_app Hom.isIso_of_isIso_app_of_iSup_eq_top"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

lemma restrictFunctor_map_app' {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (W : (U : Scheme.{u}).Opens) :
    ((restrictFunctor U.ι).map φ).app W = φ.app (U.ι ''ᵁ W) := rfl

lemma isIso_app_of_isIso_pullback_ι_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (hU : IsIso ((Scheme.Modules.pullback U.ι).map φ)) (W : X.Opens) (hWU : W ≤ U) :
    IsIso (φ.app W) := by
  have h1 : IsIso ((restrictFunctor U.ι).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback U.ι) φ).2 hU
  have h2 := Hom.isIso_iff_isIso_app.1 h1 (U.ι ⁻¹ᵁ W)
  rw [restrictFunctor_map_app'] at h2
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.2 hWU]
  rw [← e]
  exact h2

theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map.solution {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map φ)) :
    IsIso φ := by
  choose U hxU hU using h
  refine Hom.isIso_of_isIso_app_of_iSup_eq_top φ U ?_ (fun x V hV => ?_)
  · exact top_le_iff.mp fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩
  · exact isIso_app_of_isIso_pullback_ι_map φ (U x) (hU x) V hV

#print axioms solution

end AlgebraicGeometry.Scheme.Modules

end S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map (solution)
