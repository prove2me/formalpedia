-- Prove2me | solution 1 for AlgebraicCurve.essFiniteType_functionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a244506c-8ef8-5569-ba26-634e720efe49

import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_essFiniteType_functionField

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [LocallyOfFiniteType c] :
    letI := (baseToFunctionField c).toAlgebra
    Algebra.EssFiniteType K C.functionField := by
  letI algKF : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have e : V ≤ c ⁻¹ᵁ ⊤ := le_top

  let eK : Γ(Spec (CommRingCat.of K), ⊤) ≃+* K :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have hft : ((c.appLE ⊤ V e).hom.comp eK.symm.toRingHom).FiniteType :=
    (c.finiteType_appLE (isAffineOpen_top _) hV e).comp
      (RingHom.FiniteType.of_surjective _ eK.symm.surjective)
  letI algKA : Algebra K Γ(C, V) := ((c.appLE ⊤ V e).hom.comp eK.symm.toRingHom).toAlgebra
  haveI : Algebra.FiniteType K Γ(C, V) := hft

  haveI : IsFractionRing Γ(C, V) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C V hV
  haveI : IsScalarTower K Γ(C, V) C.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change baseToFunctionField c k =
      (C.germToFunctionField V).hom ((c.appLE ⊤ V e).hom (eK.symm k))
    simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE,
      Scheme.germToFunctionField, CommRingCat.hom_comp]
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  haveI : Algebra.EssFiniteType Γ(C, V) C.functionField :=
    Algebra.EssFiniteType.of_isLocalization C.functionField (nonZeroDivisors Γ(C, V))
  exact Algebra.EssFiniteType.comp K Γ(C, V) C.functionField

end S_AlgebraicCurve_essFiniteType_functionField
end P2MW
export P2MW.S_AlgebraicCurve_essFiniteType_functionField (solution)
