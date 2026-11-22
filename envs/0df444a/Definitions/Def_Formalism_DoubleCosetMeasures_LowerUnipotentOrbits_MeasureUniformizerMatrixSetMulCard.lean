-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
-- name    : Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:29.153464+00:00
-- url     : https://prove2.me/theorems/80ef942b-a669-4110-921e-3cc34261355e
-- title:
--   Measure Uniformizer Matrix Set Mul Card
-- statement:
--   Definitions and structural lemmas for Measure Uniformizer Matrix Set Mul Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Matrix
namespace Formalism.DoubleCosetMeasures.P.Vol
section PartA
section Alg
variable {F : Type} [Field F]
def piece (O : Subring F) (ϖ : F) {n a : ℕ} (r : Matrix (Fin n) (Fin a) F) :
    Set (Matrix (Fin n) (Fin a) F) :=
  (fun h => -r + h) ⁻¹' IIset O ϖ
end Alg
end PartA
section PartB
variable {F : Type} [Field F]
end PartB
section PartC
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  [BorelSpace F]
def repM (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) {n a : ℕ} (c : Fin n → Fin a → kF O ϖ hϖ) :
    Matrix (Fin n) (Fin a) F :=
  fun i j => ((Quotient.out (c i j) : O) : F)
end PartC
section PartD
section J
variable {F : Type} [Field F]
variable [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F]
end J
end PartD
end Formalism.DoubleCosetMeasures.P.Vol
namespace Formalism.DoubleCosetMeasures.P
end Formalism.DoubleCosetMeasures.P


