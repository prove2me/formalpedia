-- Prove2me | solution 1 for AlgebraicCurve.finiteAlong_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1cec7d76-7714-5e49-a491-5054cbcabf98

import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finiteAlong_of_isIntegral

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    FiniteAlong K φ := by
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Algebra.EssFiniteType F F' := Algebra.EssFiniteType.of_comp K F F'
  obtain ⟨s, hs⟩ := IntermediateField.fg_top F F'
  have hfin : FiniteDimensional F (IntermediateField.adjoin F (s : Set F')) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [hs] at hfin
  show Module.Finite F F'
  exact (IntermediateField.topEquiv (F := F) (E := F')).toLinearEquiv.finiteDimensional

end S_AlgebraicCurve_finiteAlong_of_isIntegral
end P2MW
export P2MW.S_AlgebraicCurve_finiteAlong_of_isIntegral (solution)
