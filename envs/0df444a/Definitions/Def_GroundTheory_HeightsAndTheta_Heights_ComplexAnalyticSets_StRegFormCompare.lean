-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFormCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFormCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:43.378795+00:00
-- url     : https://prove2.me/theorems/6d1182d2-290e-4348-acd2-231a1a8c81e9
-- title:
--   St Reg Form Compare
-- statement:
--   Definitions and structural lemmas for St Reg Form Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegFormCompare.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
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
def RegFormCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → Continuous f → HasCompactSupport f →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Fin n → ℂ) (ε : ℝ), 0 < ε →
        ∀ v w : (Fin n → ℂ) → ℝ, (∀ x, 0 ≤ w x) → (∀ x ∈ tsupport f, |v x| ≤ w x) →
          ∀ y, chartAbsDens J A (fun x => v x * f x) (vecCons (logReg u ε) φ) y ≤
            C * chartDens J A w (vecCons (logReg u ε) fun _ => euclPot) y
end
end GroundTheory.Heights₂.Heights


