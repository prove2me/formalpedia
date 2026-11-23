-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_HasFDerivAtIntegralPIter
-- name    : Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_HasFDerivAtIntegralPIter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:15.381149+00:00
-- url     : https://prove2.me/theorems/dd4969a8-5b58-4862-9e2d-e8792bf6776f
-- title:
--   Has FDeriv At Integral PIter
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Integral PIter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/HasFDerivAtIntegralPIter.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
namespace Formalism.IndefR.Tow.SobPf.Avg
variable {m : ℕ} {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
def pIter (Φ : (Fin m → ℝ) → X → E) (j : ℕ) (t : Fin m → ℝ) (k : X) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin m → ℝ) E :=
  iteratedFDeriv ℝ j (fun t => Φ t k) t
end Formalism.IndefR.Tow.SobPf.Avg
end


