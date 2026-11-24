-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MeasurableHaarKernelTriple
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MeasurableHaarKernelTriple
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:53:31.554603+00:00
-- url     : https://prove2.me/theorems/62abd2fa-9b94-411d-9d65-32b3a019b9d9
-- title:
--   Measurable Haar Kernel Triple
-- statement:
--   Definitions and structural lemmas for Measurable Haar Kernel Triple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MeasurableHaarKernelTriple.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_SphericalFunctionFixedUnitaryEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Base0
def PhiA (k : ℕ) (A : ℝ) (g : Mt k 0) : ℝ≥0∞ := ENNReal.ofReal (gN (Matrix.of g) ^ (-A))
def Gf (k : ℕ) (σ : ℝ) (h g h' : Mt k 0) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt 2)⁻¹ * ‖((Matrix.of h)ᴴ *ᵥ ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0)) (iW k) +
    ((Matrix.of g * Matrix.of h') *ᵥ phiV' k 0 0) (iK k)‖) ^ (-σ)
end ReciprocityTheory.ChartRestriction.DS.Xi


