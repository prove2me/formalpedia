-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5c674a83-e111-5676-b964-e80d1097b461

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (K' : Type u) [Field K'] [Algebra K K']
    (h : ∀ i : ℕ, Subsingleton ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap K K'))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap K K'))).obj M)).HSucc
        (𝒰.baseChange π K') i))
    (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules π M).HSucc 𝒰 i) := by
  obtain ⟨-, hflat⟩ := AlgebraicGeometry.OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial π 𝒰 M htriv K'
  obtain ⟨-, hsucc⟩ := hflat inferInstance
  obtain ⟨e⟩ := hsucc i
  haveI : Subsingleton (K' ⊗[K] (OModulePresheaf.ofModules π M).HSucc 𝒰 i) :=
    e.symm.toEquiv.subsingleton_congr.mpr (h i)
  haveI : Module.FaithfullyFlat K K' := inferInstance
  exact Module.FaithfullyFlat.lTensor_reflects_triviality K K' ((OModulePresheaf.ofModules π M).HSucc 𝒰 i)

end S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field (solution)
