-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:18.800571+00:00
-- url     : https://prove2.me/theorems/4aabbfbd-da7f-44a3-ab75-0de0f3afae74
-- title:
--   Green St
-- statement:
--   Definitions and structural lemmas for Green St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenSt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.A
open MeasureTheory
open scoped Laplacian
noncomputable section
def ddcDens (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * Δ u z
def ddcCoordDens {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  (2 / Real.pi) * ReciprocityTheory.AnForm.levi u z (Pi.single j 1)
def LeviOneEqLaplacianStatement : Prop :=
  ∀ (u : ℂ → ℝ) (z : ℂ),
    ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => u (w 0)) (fun _ => z) (Pi.single 0 1) =
      Δ u z / 4
def GreenOriginStatement : Prop :=
  ∀ u : ℂ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : ℂ => Real.log ‖z‖ * Δ u z) ∧
      ∫ z : ℂ, Real.log ‖z‖ * Δ u z = 2 * Real.pi * u 0
def GreenDdcOriginStatement : Prop :=
  ∀ u : ℂ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : ℂ => Real.log ‖z‖ * ddcDens u z) ∧
      ∫ z : ℂ, Real.log ‖z‖ * ddcDens u z = u 0
def GreenPointStatement : Prop :=
  ∀ (u : ℂ → ℝ) (a : ℂ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : ℂ => Real.log ‖z - a‖ * Δ u z) ∧
      ∫ z : ℂ, Real.log ‖z - a‖ * Δ u z = 2 * Real.pi * u a
def GreenParamFiberStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u → ∀ p : E,
    Integrable (fun z : ℂ => Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z) ∧
      ∫ z : ℂ, Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z = 2 * Real.pi * u (0, p)
def GreenParamStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1)
        ((volume : Measure ℂ).prod μ) ∧
      ∫ q : ℂ × E, Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1 ∂((volume : Measure ℂ).prod μ)
        = 2 * Real.pi * ∫ p : E, u (0, p) ∂μ
def GreenCoordStatement : Prop :=
  ∀ (D : ℕ) (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) ∧
      ∫ z : Fin (D + 1) → ℂ, Real.log ‖z j‖ * ddcCoordDens j u z =
        ∫ w : Fin D → ℂ, u (Fin.insertNth j 0 w)
def GreenCoordFiberStatement : Prop :=
  ∀ (D : ℕ) (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    ∀ w : Fin D → ℂ,
    Integrable (fun ζ : ℂ => Real.log ‖ζ‖ * ddcCoordDens j u (Fin.insertNth j ζ w)) ∧
      ∫ ζ : ℂ, Real.log ‖ζ‖ * ddcCoordDens j u (Fin.insertNth j ζ w) = u (Fin.insertNth j 0 w)
def GreenCoordZeroStatement : Prop :=
  ∀ (D : ℕ) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z 0‖ * ddcCoordDens 0 u z) ∧
      ∫ z : Fin (D + 1) → ℂ, Real.log ‖z 0‖ * ddcCoordDens 0 u z =
        ∫ w : Fin D → ℂ, u (Fin.cons 0 w)
def GreenMaDensStatement : Prop :=
  ∀ u : (Fin 1 → ℂ) → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : Fin 1 → ℂ => Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z) ∧
      ∫ z : Fin 1 → ℂ, Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z = u 0
def GreenMixedStatement : Prop :=
  ∀ (D : ℕ) (j a b : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    (a, b) ≠ (j, j) →
    Integrable (fun z : Fin (D + 1) → ℂ => (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b) ∧
      ∫ z : Fin (D + 1) → ℂ, (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b = 0
end
end ReciprocityTheory.AnForm.A


