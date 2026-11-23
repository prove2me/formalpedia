-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:19.513506+00:00
-- url     : https://prove2.me/theorems/87b27064-68cc-4d60-a7fb-5fe3846f4ce5
-- title:
--   Cas Ps B
-- statement:
--   Definitions and structural lemmas for Cas Ps B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CasPsB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace CasPsB
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
def FY (T : KType ε Λ) (μ : Fin n → ℤ) (Y x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) : T.V →L[ℂ] T.V :=
  fderiv ℂ (Ps1.PhiP μ) (Matrix.of.symm (toMK k⁻¹ * x * toMK k))
    (Matrix.of.symm (toMK k⁻¹ * Y * x * toMK k)) • (T.op k * projW T * T.op k⁻¹)
def FY' (T : KType ε Λ) (μ : Fin n → ℤ) (Y x : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) :
    𝕄 →L[ℂ] (T.V →L[ℂ] T.V) :=
  fderiv ℂ (fun y : 𝕄 => FY T μ Y y k) x
section Lhol
variable [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)}
variable (hU : IsOpen U) (hΩ : ∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n)
  (hfd : ∀ z ∈ U, ∀ H : Matrix (Fin n) (Fin n) ℂ, fderiv ℂ (psM T μ) z H =
      ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
        ∫ k, fderiv ℂ (PhiM μ) (toMK k⁻¹ * z * toMK k) (toMK k⁻¹ * H * toMK k) •
          (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
include hU hΩ hfd
end Lhol
end CasPsB
end ReciprocityTheory.ChartRestriction.DS.S7


