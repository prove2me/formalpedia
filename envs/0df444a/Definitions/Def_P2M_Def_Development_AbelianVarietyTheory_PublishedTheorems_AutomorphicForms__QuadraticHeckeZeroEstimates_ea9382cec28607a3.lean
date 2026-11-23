-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__QuadraticHeckeZeroEstimates_ea9382cec28607a3
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__QuadraticHeckeZeroEstimates_ea9382cec28607a3
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:30.222089+00:00
-- url     : https://prove2.me/theorems/a78a7558-3e6e-466a-893e-55b30cd74110
-- title:
--   Quadratic Hecke Zero Estimates
-- statement:
--   Definitions and structural lemmas for Quadratic Hecke Zero Estimates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/QuadraticHeckeZeroEstimates.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.An
def QuadraticHeckeZeroEstimates : Prop :=
  ∃ c₂ c₃ CA cS : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < CA ∧ 0 < cS ∧
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 →
    ∀ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ → ∃ (𝒬 β : ℝ) (θ : ℤ) (S : Set (HeightOneSpectrum (𝓞 K))),
      4 * |(discr K : ℝ)| ≤ 𝒬 ∧ 𝒬 ≤ 4 * |(discr K : ℝ)| * (Ideal.absNorm 𝔮 : ℝ) ∧ (θ = 0 ∨ θ = 1) ∧
      (θ = 1 → 1 - 1 / (8 * Real.log 𝒬) < β ∧ cS / (𝒬 ^ 2 * Real.log 𝒬) ≤ 1 - β) ∧
      (∀ v ∈ S, v.asIdeal ∣ 𝔮) ∧
      ∀ X : ℝ, 𝒬 ^ c₂ ≤ X →
        |(rayNo 𝔮 : ℝ) * (((rayPrimes 𝔮 X).ncard : ℝ) + ({v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.ncard : ℝ)) -
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤
          CA * (Real.exp (-c₃ * Real.log X / Real.log 𝒬) + Real.exp (-Real.sqrt (c₃ * Real.log X / 2))) *
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X
end GlobalTheory.Mem.An


