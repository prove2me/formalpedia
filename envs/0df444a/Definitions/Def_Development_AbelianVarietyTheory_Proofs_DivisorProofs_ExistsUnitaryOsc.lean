-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryOsc
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryOsc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:35.197519+00:00
-- url     : https://prove2.me/theorems/65368bc1-5e1b-4685-bf85-dc202d3fe3a3
-- title:
--   Exists Unitary Osc
-- statement:
--   Definitions and structural lemmas for Exists Unitary Osc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryOsc.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_add
import Theorems.Thm_GlobalTheory_RealWeil_Osc_sm_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix MeasureTheory Complex GlobalTheory.RealWeil GlobalTheory.RealWeil.UnitaryOsc
open scoped InnerProductSpace
namespace GlobalTheory.FockRep
section Abstract
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → H →L[ℂ] H}
def smSub (ρ : V → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {f | Sm ρ f}
  zero_mem' := by
    change Sm ρ 0
    unfold Sm
    simp only [map_zero]
    exact contDiff_const
  add_mem' := fun hf hf' => Osc.sm_add hf hf'
  smul_mem' := fun a _ hf => Osc.sm_smul a hf
end Abstract
end GlobalTheory.FockRep


