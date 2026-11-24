-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:15.301568+00:00
-- url     : https://prove2.me/theorems/429412b3-3342-4837-b9cb-894180127158
-- title:
--   Statements Cone Proj Hyperplane Null
-- statement:
--   Definitions and structural lemmas for Statements Cone Proj Hyperplane Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeProjHyperplaneNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetArea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)
def ConeProjHyperplaneNull.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        {z : EuclideanSpace ℂ (Fin n) |
          (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
          Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0} = 0
end GroundTheory.Heights₂.Heights


