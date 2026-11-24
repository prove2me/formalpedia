-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMeetNull
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMeetNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:44.41269+00:00
-- url     : https://prove2.me/theorems/2ec749d3-796b-40ec-a89e-8a7f3fec1242
-- title:
--   Statements Cone Meet Null
-- statement:
--   Definitions and structural lemmas for Statements Cone Meet Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeMeetNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
noncomputable section
def ConeMeetNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W W' : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime → W'.IsPrime →
    W ≠ W' → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W') ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0
end
end GroundTheory.Heights₂.Heights


