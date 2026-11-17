-- Prove2me | Definitions.Def_Kyprianou_ProofPreparation_realPoissonProbability
-- name    : Kyprianou_ProofPreparation_realPoissonProbability
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T23:47:43.363197+00:00
-- url     : https://prove2.me/theorems/ab7eaa06-b507-44f6-8360-84c119b1b14d
-- title:
--   Kyprianou.ProofPreparation.realPoissonProbability
-- statement:
--   Automatically extracted helper definition Kyprianou.ProofPreparation.realPoissonProbability from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
-- source:
--   candidate-decomposition:2004a3aa-1f5c-4edd-8bf7-f67523bab94c:81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
noncomputable section

/-- The real-valued Poisson probability law, using a fixed Borel space. -/
def realPoissonProbability (r : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨(poissonMeasure r).map (Nat.cast : ℕ → ℝ), inferInstance⟩

end
end Kyprianou.ProofPreparation


