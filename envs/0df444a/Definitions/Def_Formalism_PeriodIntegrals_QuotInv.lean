-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_QuotInv
-- name    : Formalism_PeriodIntegrals_QuotInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:59.738294+00:00
-- url     : https://prove2.me/theorems/623f420d-d9e5-4616-b125-7217658cdfb7
-- title:
--   Quot Inv
-- statement:
--   Definitions and structural lemmas for Quot Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/QuotInv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
namespace PI
abbrev MtM (m : ℕ) := Fin m → Fin m → ℂ
def lmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := a * Matrix.of x
def rmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := Matrix.of x * a
def IsMatGroup {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G ∧ (∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) ∧
    ∀ a ∈ G, a⁻¹ ∈ G ∧ a * a⁻¹ = 1
def IsHaarOnM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulQ s) = μ
def IsRightInvM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  ∀ s ∈ S, μ.map (rmulQ s) = μ
def IsQuotM {m : ℕ} (μG μS ν : Measure (MtM m)) : Prop :=
  ∀ f : MtM m → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν
def QuotientSetting {m : ℕ} (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)) : Prop :=
  IsMatGroup G ∧ IsMatGroup S ∧ S ⊆ G ∧ IsHaarOnM G μG ∧ IsHaarOnM S μS ∧ IsRightInvM G μG ∧ IsRightInvM S μS ∧
    IsQuotM μG μS ν
def QuotInv : Prop :=
  ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)), QuotientSetting G S μG μS ν →
    ∀ F : MtM m → ℝ≥0∞, Measurable F →
      (∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x) →
      ∀ g ∈ G, ∫⁻ x, F (fun i j => (Matrix.of x * g) i j) ∂ν = ∫⁻ x, F x ∂ν
def QuotYoung : Prop :=
  ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)), QuotientSetting G S μG μS ν →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
      (e : Matrix (Fin m) (Fin m) ℂ → ℂ) (Φ : Matrix (Fin m) (Fin m) ℂ → V),
      Integrable (fun x : MtM m => e (Matrix.of x)) μG →
      AEStronglyMeasurable (fun x : MtM m => Φ (Matrix.of x)) μG →
      (∀ s ∈ S, ∀ g ∈ G, ‖Φ (s * g)‖ = ‖Φ g‖) →
      (∃ M : ℝ, ∀ g ∈ G, ‖Φ g‖ ≤ M) →
      (∫⁻ x, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν) < ⊤ →
      (∫⁻ x, (‖∫ g, e (Matrix.of g) • Φ (Matrix.of x * Matrix.of g) ∂μG‖₊ : ℝ≥0∞) ^ 2 ∂ν) < ⊤
end PI
end


