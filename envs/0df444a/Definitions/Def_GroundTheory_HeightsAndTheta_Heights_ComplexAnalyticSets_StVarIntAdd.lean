-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:56.658102+00:00
-- url     : https://prove2.me/theorems/56651401-851e-4c42-a746-dac0cee27eb9
-- title:
--   St Var Int Add
-- statement:
--   Definitions and structural lemmas for St Var Int Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarIntAdd.lean

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
def VarIntAdd.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin k → (Fin n → ℂ) → ℝ),
    J.IsPrime → Continuous f → HasCompactSupport f → Continuous g → HasCompactSupport g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      varInt J k (f + g) φ = varInt J k f φ + varInt J k g φ
end
end GroundTheory.Heights₂.Heights


