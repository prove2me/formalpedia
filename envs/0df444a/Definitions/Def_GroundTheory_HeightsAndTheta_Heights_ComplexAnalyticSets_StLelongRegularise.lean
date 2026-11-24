-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:52.277546+00:00
-- url     : https://prove2.me/theorems/d01020e5-0875-4d3b-8224-c1d18a7d76e3
-- title:
--   St Lelong Regularise
-- statement:
--   Definitions and structural lemmas for St Lelong Regularise, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLelongRegularise.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n : ℕ}
def logReg (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) : ℝ :=
  Real.log (‖linEval u x‖ ^ 2 + ε) / 2
def LelongRegularise.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    ContDiff ℝ ∞ f → HasCompactSupport f → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      Tendsto (fun ε => varInt J (d + 1) (logReg u ε) (vecCons f φ)) (𝓝[>] 0)
        (𝓝 (varInt J (d + 1) (fun x => Real.log ‖linEval u x‖) (vecCons f φ)))
end
end GroundTheory.Heights₂.Heights


