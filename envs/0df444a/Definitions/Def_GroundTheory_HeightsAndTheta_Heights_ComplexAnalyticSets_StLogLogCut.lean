-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:19.755383+00:00
-- url     : https://prove2.me/theorems/cc5b0500-8684-4ca2-ad7a-cf5f76ac5c2f
-- title:
--   St Log Log Cut
-- statement:
--   Definitions and structural lemmas for St Log Log Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLogLogCut.lean

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
open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff
noncomputable section
def cutStep (t : ℝ) : ℝ := Real.smoothTransition (2 - 2 * t)
def cutLevel (k : ℕ) : ℝ := Real.exp (-Real.exp ((k : ℝ) + 1))
def logAbsSq {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  Real.log (‖eval y Q‖ ^ 2)
def logLogCut {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) : ℝ :=
  if ‖eval y Q‖ ^ 2 = 0 then 0
  else if 1 ≤ ‖eval y Q‖ ^ 2 then 1
  else cutStep (Real.log (-logAbsSq Q y) / ((k : ℝ) + 1))
def logLogCutAlong {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (Q : MvPolynomial (Fin m) ℂ) (k : ℕ)
    (x : Fin n → ℂ) : ℝ :=
  logLogCut Q k (A *ᵥ x)
def tubeWeight {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  if logAbsSq Q y ≤ -1 then (logAbsSq Q y ^ 2)⁻¹ else 0
def tubeDens {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Fin (d + 1) → ℂ) → ℝ :=
  chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => tubeWeight P (A *ᵥ x))
    (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) φ)
def CutOffShape.Statement : Prop :=
  ∀ (m : ℕ) (Q : MvPolynomial (Fin m) ℂ),
    (∀ k, ContDiff ℝ ∞ (logLogCut Q k) ∧ (∀ y, logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ y, ‖eval y Q‖ ^ 2 < cutLevel k → logLogCut Q k y = 0) ∧
    ∀ y, eval y Q ≠ 0 → Tendsto (fun k => logLogCut Q k y) atTop (𝓝 1)
end
end GroundTheory.Heights₂.Heights


