-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:29.208728+00:00
-- url     : https://prove2.me/theorems/f6726eb3-73be-4aa9-98c1-6daaaf3e100d
-- title:
--   St Variety Lelong Mono
-- statement:
--   Definitions and structural lemmas for St Variety Lelong Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarietyLelongMono.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
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
open scoped ENNReal
noncomputable section
def VarietyLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ z ∈ zeroSetEuc J, ∀ r s : ℝ, 0 < r → r ≤ s →
      ENNReal.ofReal (s ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z r) ≤
        ENNReal.ofReal (r ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z s)
end
end GroundTheory.Heights₂.Heights


