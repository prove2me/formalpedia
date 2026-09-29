-- Prove2me | solution 1 for AlgebraicCurve.existsUnique_hasSimpleResidue_of_hasSimplePoleAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/65d86db0-9756-5a89-b25b-1841edf6d7f1

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt

set_option autoImplicit false

open AlgebraicCurve

namespace ResEx

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem main [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (v : Place K F) (ω : Ω[F⁄K]) (hω : v.HasSimplePoleAt ω) :
    ∃! a : K, v.HasSimpleResidue ω a := by
  obtain ⟨f, hπf, hωf⟩ := hω

  haveI : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring ⟨v.uniformizer * f, hπf⟩)
  have hval : v.HasValue (v.uniformizer * f) a := ⟨hπf, ha.symm⟩
  refine ⟨a, ⟨f, hωf, hval⟩, ?_⟩

  intro b hb
  obtain ⟨f', hωf', hval'⟩ := hb
  haveI : v.DCoordGenerates := dCoordGenerates_of_isCurveOver v
  have hff : f' = f := by
    rw [← v.differentialCoeff_unique hωf', v.differentialCoeff_unique hωf]
  rw [hff] at hval'
  exact hval'.unique hval

end ResEx

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) (hω : v.HasSimplePoleAt ω) :
    ∃! a : K, v.HasSimpleResidue ω a :=
  ResEx.main v ω hω

#print axioms solution

end S_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt
end P2MW
export P2MW.S_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt (solution)
