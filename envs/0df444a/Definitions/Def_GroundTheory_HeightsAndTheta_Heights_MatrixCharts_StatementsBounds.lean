-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:06.215167+00:00
-- url     : https://prove2.me/theorems/f617b434-902f-4be7-a88f-fe4df09d7554
-- title:
--   Statements Bounds
-- statement:
--   Definitions and structural lemmas for Statements Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/StatementsBounds.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
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
open Matrix
noncomputable section
def InvEntryBound.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ), 0 < c →
    (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ∀ j l, |Y⁻¹ j l| ≤ c⁻¹
def InvEntryDeriv.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ)
    (Y : E → Matrix (Fin g) (Fin g) ℝ) (p : E) (c b : ℝ), 0 < c →
    (Y p - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef →
    (∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p ∧ ‖fderiv ℝ (fun q => Y q j l) p‖ ≤ b) →
    ∀ j l, DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p ∧
      ‖fderiv ℝ (fun q => (Y q)⁻¹ j l) p‖ ≤ (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b
def MatrixDetDeriv.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (H : E → Matrix (Fin k) (Fin k) ℂ) (p : E) (A B : ℝ),
    (∀ j l, DifferentiableAt ℝ (fun q => H q j l) p ∧ ‖H p j l‖ ≤ A ∧
      ‖fderiv ℝ (fun q => H q j l) p‖ ≤ B) →
    DifferentiableAt ℝ (fun q => (H q).det) p ∧
      ‖fderiv ℝ (fun q => (H q).det) p‖ ≤ (k.factorial : ℝ) * k * A ^ (k - 1) * B
def GramEntryDeriv.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g k : ℕ)
    (F : E → Matrix (Fin g) (Fin k) ℂ) (Z : E → Matrix (Fin g) (Fin g) ℝ) (p : E) (a e e' : ℝ),
    (∀ j l, DifferentiableAt ℝ (fun q => F q j l) p ∧ ‖F p j l‖ ≤ a ∧
      ‖fderiv ℝ (fun q => F q j l) p‖ ≤ a) →
    (∀ j l, DifferentiableAt ℝ (fun q => Z q j l) p ∧ |Z p j l| ≤ e ∧
      ‖fderiv ℝ (fun q => Z q j l) p‖ ≤ e') →
    ∀ j l, DifferentiableAt ℝ (fun q => ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l) p ∧
      ‖((F p)ᴴ * (Z p).map (fun x : ℝ => (x : ℂ)) * F p) j l‖ ≤ (g : ℝ) ^ 2 * a ^ 2 * e ∧
      ‖fderiv ℝ (fun q => ((F q)ᴴ * (Z q).map (fun x : ℝ => (x : ℂ)) * F q) j l) p‖ ≤
        (g : ℝ) ^ 2 * (2 * a ^ 2 * e + a ^ 2 * e')
def LogDetGramDeriv.Statement : Prop :=
  ∀ g k : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → Matrix (Fin g) (Fin k) ℂ) (Y : E → Matrix (Fin g) (Fin g) ℝ) (p : E) (a b c μ : ℝ),
    0 < c → 0 < μ → 0 ≤ a → 0 ≤ b →
    (∀ j l, DifferentiableAt ℝ (fun q => F q j l) p ∧ ‖F p j l‖ ≤ a ∧
      ‖fderiv ℝ (fun q => F q j l) p‖ ≤ a) →
    (∀ j l, DifferentiableAt ℝ (fun q => Y q j l) p ∧ ‖fderiv ℝ (fun q => Y q j l) p‖ ≤ b) →
    (Y p - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef →
    μ ≤ ((F p)ᴴ * (Y p)⁻¹.map (fun x : ℝ => (x : ℂ)) * F p).det.re →
    DifferentiableAt ℝ (fun q => logDetGram (Y q) (F q)) p ∧
      ‖fderiv ℝ (fun q => logDetGram (Y q) (F q)) p‖ ≤
        K * (1 + a) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + b) / μ
def AnalyticDerivBound.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) (U K : Set E),
    IsOpen U → AnalyticOnNhd ℂ f U → IsCompact K → K ⊆ U →
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ K, DifferentiableAt ℝ f x ∧ ‖f x‖ ≤ A ∧ ‖fderiv ℝ f x‖ ≤ A
def ChartFrameDeriv.Statement : Prop :=
  ∀ D : PeriodChartData, ∃ A : ℝ, 0 < A ∧ ∀ p ∈ D.K, ∀ j l,
    DifferentiableAt ℝ (fun q => D.f q j l) p ∧ ‖D.f p j l‖ ≤ A ∧
      ‖fderiv ℝ (fun q => D.f q j l) p‖ ≤ A
def CuspTimeDeriv.Statement : Prop :=
  ∀ D : PeriodChartData, ∀ z ∈ D.Ustar, ∀ i : Fin D.a,
    DifferentiableAt ℝ (fun w => cuspTime D.a_le w i) z ∧
      ‖fderiv ℝ (fun w => cuspTime D.a_le w i) z‖ ≤ Real.exp (D.radius z / 2)
def ChartImagDeriv.Statement : Prop :=
  ∀ D : PeriodChartData, ∃ A : ℝ, 0 < A ∧ ∀ p ∈ D.K, p.1 ∈ D.Ustar → ∀ j l,
    DifferentiableAt ℝ (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => D.Y q.1 j l) p ∧
      ‖fderiv ℝ (fun q : (Fin D.n → ℂ) × (Fin D.m → ℂ) => D.Y q.1 j l) p‖ ≤
        A * Real.exp (D.radius p.1 / 2)
end
end GroundTheory.Heights₂.Heights


