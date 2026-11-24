-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:27.468268+00:00
-- url     : https://prove2.me/theorems/bafb6998-6d26-4dc3-9a1b-52896087fab2
-- title:
--   Statements Psh
-- statement:
--   Definitions and structural lemmas for Statements Psh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsPsh.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
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
open Matrix Metric
noncomputable section
def LogDetGramContinuous.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (s : Set X) (g rk : ℕ) (Y : X → Matrix (Fin g) (Fin g) ℝ)
    (F : X → Matrix (Fin g) (Fin rk) ℂ), ContinuousOn Y s → ContinuousOn F s →
    (∀ x ∈ s, (Y x).PosDef) → (∀ x ∈ s, (F x).rank = rk) →
    ContinuousOn (fun x => logDetGram (Y x) (F x)) s
def LogDetGramSubmean.Statement : Prop :=
  ∀ (g rk : ℕ) (Y : ℂ → Matrix (Fin g) (Fin g) ℝ) (F : ℂ → Matrix (Fin g) (Fin rk) ℂ),
    (∀ ζ ∈ closedBall (0 : ℂ) 1, (Y ζ).PosDef) → ContinuousOn Y (closedBall 0 1) →
    (∀ j k, Real.circleAverage (fun ζ => Y ζ j k) 0 1 = Y 0 j k) →
    (∀ j k, AnalyticOnNhd ℂ (fun ζ => F ζ j k) (closedBall 0 1)) →
    (∀ ζ ∈ closedBall (0 : ℂ) 1, (F ζ).rank = rk) →
    CircleIntegrable (fun ζ => logDetGram (Y ζ) (F ζ)) 0 1 ∧
      logDetGram (Y 0) (F 0) ≤ Real.circleAverage (fun ζ => logDetGram (Y ζ) (F ζ)) 0 1
def ChartImagContinuous.Statement : Prop :=
  ∀ D : PeriodChartData, ContinuousOn D.Y D.Ustar
def ChartImagMean.Statement : Prop :=
  ∀ (D : PeriodChartData) (z w : Fin D.n → ℂ), (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ D.Ustar) →
    ∀ j k, Real.circleAverage (fun ζ : ℂ => D.Y (z + ζ • w) j k) 0 1 = D.Y z j k
end
end GroundTheory.Heights₂.Heights


