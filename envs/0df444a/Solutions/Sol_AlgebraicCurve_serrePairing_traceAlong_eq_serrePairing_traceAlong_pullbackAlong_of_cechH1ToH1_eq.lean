-- Prove2me | solution 1 for AlgebraicCurve.serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/90f09a66-ce4a-52c6-aa96-995bd60d2e55

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import Theorems.Thm_AlgebraicCurve_serrePairing_pullbackAlong_eq_serrePairing_traceAlong
import Theorems.Thm_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_pullbackAlong
import Theorems.Thm_AlgebraicCurve_serrePairing_eq_of_cechH1ToH1_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq

open KaehlerDifferential

open AlgebraicCurve

theorem solution
    {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] [Nontrivial Ω[F'⁄K]] [IsCurveOver K F']
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (hRT : ResidueTheorem K F) (hRT' : ResidueTheorem K F')
    (φα φβ : F →ₐ[K] F') (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral)
    (htrα : TraceIntegralAlong φα hφα) (hsepβ : SeparableAlong K φβ)
    (hfibα : FibreResidueIdentityAlong φα hφα) (hfibβ : FibreResidueIdentityAlong φβ hφβ)
    {S₀ S₁ T₀ T₁ : Set (Place K F)} (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (ω : ↥(regularDifferentials K F))
    (hωα : Differential.pullbackAlong φα (ω : Ω[F⁄K]) ∈ regularDifferentials K F')
    (hωβα : Differential.traceAlong φβ (Differential.pullbackAlong φα (ω : Ω[F⁄K])) ∈ regularDifferentials K F)
    (y : cechH1 T₀ T₁ (0 : Divisor K F))
    (x' : cechH1 ((Place.restrictAlong φα hφα) ⁻¹' S₀) ((Place.restrictAlong φα hφα) ⁻¹' S₁) (0 : Divisor K F'))
    (hx' : cechH1ToH1 (preimage_restrictAlong_union_eq_univ φα hφα hS) 0 x' =
      cechH1ToH1 (preimage_restrictAlong_union_eq_univ φβ hφβ hT) 0 (cechH1.pullbackAlong φβ hφβ T₀ T₁ y)) :
    serrePairing hRT hS ω (cechH1.traceAlong φα hφα htrα S₀ S₁ x')
      = serrePairing hRT hT
          ⟨Differential.traceAlong φβ (Differential.pullbackAlong φα (ω : Ω[F⁄K])), hωβα⟩ y := by
  rw [← serrePairing_pullbackAlong_eq_serrePairing_traceAlong hRT hRT' φα hφα htrα hfibα hS ω hωα x',
    serrePairing_eq_of_cechH1ToH1_eq hRT' _ _ ⟨_, hωα⟩ x' _ hx',
    ← serrePairing_traceAlong_eq_serrePairing_pullbackAlong hRT hRT' φβ hφβ hsepβ hfibβ hT ⟨_, hωα⟩ hωβα y]

end S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq
end P2MW
export P2MW.S_AlgebraicCurve_serrePairing_traceAlong_eq_serrePairing_traceAlong_pullbackAlong_of_cechH1ToH1_eq (solution)
