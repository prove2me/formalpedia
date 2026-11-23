-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:18.44654+00:00
-- url     : https://prove2.me/theorems/cce6e431-9364-4396-9545-82fc72e15229
-- title:
--   Holo Weak Statement
-- statement:
--   Definitions and structural lemmas for Holo Weak Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/HoloWeakStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
abbrev V (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)
def IsTest {n : ℕ} (Ω : Set (V n)) (g : V n → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ω
noncomputable def dbarDir {n : ℕ} (g : V n → ℂ) (z v : V n) : ℂ :=
  fderiv ℝ g z (I • v) - I * fderiv ℝ g z v
def WeakHolo {n : ℕ} (Ω : Set (V n)) (u : V n → ℂ) : Prop :=
  LocallyIntegrableOn u Ω volume ∧
    ∀ g : V n → ℂ, IsTest Ω g → ∀ v : V n, ∫ z in Ω, u z * dbarDir g z v = 0
def HoloWeakStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (u : V n → ℂ),
    IsOpen Ω → DifferentiableOn ℂ u Ω → WeakHolo Ω u
def RegStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (u : V n → ℂ),
    IsOpen Ω → WeakHolo Ω u →
      ∃ U : V n → ℂ, DifferentiableOn ℂ U Ω ∧ u =ᵐ[volume.restrict Ω] U
def MVStatement : Prop :=
  ∀ (n : ℕ) (c : V n) (R : ℝ) (u : V n → ℂ) (r : ℝ → ℝ≥0∞),
    DifferentiableOn ℂ u (ball c R) → Measurable r →
      ‖u c‖ₑ ^ 2 * ∫⁻ z in ball c R, r ‖z - c‖ ≤ ∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖
def MVEqStatement : Prop :=
  ∀ (n : ℕ) (c : V n) (R : ℝ) (u : V n → ℂ) (k : ℝ → ℝ),
    DifferentiableOn ℂ u (ball c R) →
    IntegrableOn (fun z => (k ‖z - c‖ : ℂ)) (ball c R) →
    IntegrableOn (fun z => u z * (k ‖z - c‖ : ℂ)) (ball c R) →
      ∫ z in ball c R, u z * (k ‖z - c‖ : ℂ) = u c * ∫ z in ball c R, (k ‖z - c‖ : ℂ)
def MVDivStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    Tendsto (fun δ : ℝ => ∫⁻ z in ball (0 : V n) 1, ENNReal.ofReal ((‖z‖ ^ 2 + δ) ^ (-(n : ℝ))))
      (𝓝[>] 0) (𝓝 ∞)
def MVPowStatement : Prop :=
  ∀ (n : ℕ) (s : ℝ), 0 < n →
    (IntegrableOn (fun z : V n => ‖z‖ ^ (-2 * s)) (ball 0 1) ↔ s < n)
def ExtWeakStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (F u : V n → ℂ),
    IsOpen Ω → DifferentiableOn ℂ F Ω →
    DifferentiableOn ℂ u (Ω \ {z | F z = 0}) →
    IntegrableOn (fun z => ‖u z‖ ^ 2) (Ω \ {z | F z = 0}) →
      WeakHolo Ω ((Ω \ {z | F z = 0}).indicator u)
def ExtStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (F u : V n → ℂ),
    IsOpen Ω → DifferentiableOn ℂ F Ω →
    DifferentiableOn ℂ u (Ω \ {z | F z = 0}) →
    IntegrableOn (fun z => ‖u z‖ ^ 2) (Ω \ {z | F z = 0}) →
      ∃ U : V n → ℂ, DifferentiableOn ℂ U Ω ∧ EqOn U u (Ω \ {z | F z = 0})
def ExtNullStatement : Prop :=
  ∀ (n : ℕ) (c : V n) (R : ℝ) (F : V n → ℂ),
    DifferentiableOn ℂ F (ball c R) → (∃ z ∈ ball c R, F z ≠ 0) →
      volume (ball c R ∩ {z | F z = 0}) = 0
def IdentStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (F : V n → ℂ) (a : V n),
    IsOpen Ω → Convex ℝ Ω → DifferentiableOn ℂ F Ω → a ∈ Ω → F =ᶠ[𝓝 a] 0 → EqOn F 0 Ω
end ReciprocityTheory.L2DbarEstimates.C


