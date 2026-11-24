-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:33.155817+00:00
-- url     : https://prove2.me/theorems/80c45005-4d13-467a-9b40-0341b572a39b
-- title:
--   Matrix Coeff Decay Second Part
-- statement:
--   Definitions and structural lemmas for Matrix Coeff Decay Second Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffDecaySecondPart.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
open scoped FourierTransform ContDiff RealInnerProductSpace Real
noncomputable section
namespace GlobalTheory.RealWeil.CoefQDecay
variable {n : ℕ}
def prodTrans (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => g (x + p) * starRingEnd ℂ (g' x)
def derivBound (g g' : Sch (Fin n)) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i g *
    ‖iteratedFDeriv ℝ (j - i) g' x‖
end GlobalTheory.RealWeil.CoefQDecay


