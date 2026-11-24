-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
-- name    : Development_AutomorphicArithmetic_WeightCongruences_ProdCmTypeEqNormAndWeightCongruenceOne
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:43.575858+00:00
-- url     : https://prove2.me/theorems/50b448ac-8dcf-44e6-98bd-72e48a12c353
-- title:
--   Prod Cm Type Eq Norm And Weight Congruence One
-- statement:
--   Definitions and structural lemmas for Prod Cm Type Eq Norm And Weight Congruence One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdCmTypeEqNormAndWeightCongruenceOne.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_mem_Psi_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostAx_galE_mem_Psi_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions
theorem fixK {R : Ranks} (H : Host R) (σ : H.E ≃ₐ[ℚ] H.E) (hσ : σ H.sqd = H.sqd) (x : H.K) :
    σ (x : H.E) = x := by
  have hint : IsAlgebraic ℚ H.sqd := (Algebra.IsIntegral.isIntegral (R := ℚ) H.sqd).isAlgebraic
  have hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqd} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint]
    exact x.2
  have hle : Algebra.adjoin ℚ {H.sqd} ≤
      AlgHom.equalizer (σ : H.E →ₐ[ℚ] H.E) (AlgHom.id ℚ H.E) := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact hσ
  exact hle hx
theorem sigma_sqd {R : Ranks} (H : Host R) (g : R.Psi) : H.sigmaOf (g : R.GG) H.sqd = H.sqd := by
  rw [← Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx]
  simpa [Formalism.BasicNotions.Host.sigmaOf, Formalism.HC.HostRaw.galE] using g.2
noncomputable def galK {R : Ranks} (H : Host R) (g : R.Psi) : H.E ≃ₐ[H.K] H.E :=
  AlgEquiv.ofRingEquiv (f := (H.sigmaOf (g : R.GG)).toRingEquiv) (fun y => fixK H _ (sigma_sqd H g) y)


