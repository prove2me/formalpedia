-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SecondLevelOfNormHolds
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SecondLevelOfNormHolds
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:15.421551+00:00
-- url     : https://prove2.me/theorems/25563dee-4762-4cd8-8e4d-2f9f667a684d
-- title:
--   Second Level Of Norm Holds
-- statement:
--   Definitions and structural lemmas for Second Level Of Norm Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SecondLevelOfNormHolds.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog)
namespace BrC
section Alg
variable {K : Type} [Field K]
end Alg
section Cont
variable {K : Type} [Field K]
end Cont
section Normed
variable {K : Type} [NormedField K] [IsUltrametricDist K]
def Osub (σ : K →+* K) : Subring K :=
  Formalism.G.unitBall K ⊓ (σ.comp σ).eqLocus (RingHom.id K)
theorem mem_Osub {σ : K →+* K} {a : K} : a ∈ Osub σ ↔ ‖a‖ ≤ 1 ∧ σ (σ a) = a := by
  simp only [Osub, Subring.mem_inf, RingHom.mem_eqLocus, RingHom.comp_apply, RingHom.id_apply]
  exact Iff.rfl
@[reducible] def starO {σ : K →+* K} (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) : StarRing (Osub σ) where
  star a := ⟨σ a.1, mem_Osub.2 ⟨hσ _ a.2.1, congrArg σ a.2.2⟩⟩
  star_involutive a := Subtype.ext a.2.2
  star_mul a b := Subtype.ext (by
    show σ (a.1 * b.1) = σ b.1 * σ a.1
    rw [map_mul, mul_comm])
  star_add a b := Subtype.ext (map_add σ a.1 b.1)
theorem ne_zero_of_norm {a : K} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h
  rw [h, norm_zero] at ha
  exact zero_ne_one ha
def unitO {σ : K →+* K} {a : K} (ha : ‖a‖ = 1) (hs : σ (σ a) = a) : (Osub σ)ˣ where
  val := ⟨a, mem_Osub.2 ⟨ha.le, hs⟩⟩
  inv := ⟨a⁻¹, mem_Osub.2 ⟨by rw [norm_inv, ha, inv_one], by rw [map_inv₀, map_inv₀, hs]⟩⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ (ne_zero_of_norm ha))
  inv_val := Subtype.ext (inv_mul_cancel₀ (ne_zero_of_norm ha))
variable [CharZero K]
end Normed
end BrC
end Formalism.L2.Th1.D


