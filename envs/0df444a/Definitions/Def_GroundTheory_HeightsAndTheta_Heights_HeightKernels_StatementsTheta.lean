-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:45.744121+00:00
-- url     : https://prove2.me/theorems/6fa9d316-4e6d-4477-83db-ec9dc23d0f98
-- title:
--   Statements Theta
-- statement:
--   Definitions and structural lemmas for Statements Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsTheta.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
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
open Matrix Real MeasureTheory
noncomputable section
def thetaSummand {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ)
    (k : Fin g → ℤ) : ℂ :=
  Complex.exp (π * Complex.I *
      ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
    2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))
def torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ i, (m i : ℂ) * (u i : ℂ))
def ThetaSummandNorm.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ) (k : Fin g → ℤ), Y.IsSymm →
    ‖thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ *
        exp (-π * qf Y u₁) = exp (-π * qf Y (intVec k + a + u₁))
def ThetaNormMajorant.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ), Y.PosDef →
    thetaNorm X Y a b u₁ u₂ ≤ ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁))
def ThetaCharIntegral.Statement : Prop :=
  ∀ (g : ℕ) (m : Fin g → ℤ),
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, torusChar m u = if m = 0 then 1 else 0
def ThetaCubeParseval.Statement : Prop :=
  ∀ (g : ℕ) (c : (Fin g → ℤ) → ℂ), Summable (fun k => ‖c k‖) →
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, ‖∑' k, c k * torusChar k u‖ ^ 2 = ∑' k, ‖c k‖ ^ 2
def ThetaInnerMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ : Fin g → ℝ), Y.PosDef →
    ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1, thetaNorm X Y a b u₁ u₂ ^ 2 =
      ∑' k : Fin g → ℤ, exp (-(2 * π) * qf Y (intVec k + a + u₁))
def ThetaMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ), Y.PosDef →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ))
def ThetaFirstCoordSplit.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ), Y.PosDef → 0 < ρ →
    Y⁻¹ 0 0 = ρ ^ 2 →
    ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + (a + u₁)))
def ThetaConstants.Statement : Prop :=
  ∀ C₃ : ℝ, 0 < C₃ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) (ρ d : ℝ), 1 ≤ g → 0 < ρ → 0 < d → ρ ^ 2 ≤ 2 * g → d⁻¹ ≤ ρ ^ 2 * (2 * g) ^ (g - 1) →
      (C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g ≤
        ((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) * exp (g * log (1 + 1 / ρ) + C * g * log (2 * g))
example {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) :
    thetaChar X Y a b z = ∑' k, thetaSummand X Y a b z k := rfl
example {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ) :
    thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b
      (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ * exp (-π * qf Y u₁) := rfl
example : (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm := Matrix.isSymm_one
example : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨by ext i j; fin_cases i <;> fin_cases j <;> rfl, fun x hx => ?_⟩
  have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h; push_neg at h; apply hx; ext i; fin_cases i <;> simp [h.1, h.2]
  simp only [dotProduct, mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    star_trivial]
  rcases h with h | h
  · have := pow_pos (abs_pos.mpr h) 2
    nlinarith [sq_nonneg (x 0 + x 1), sq_abs (x 0)]
  · have := pow_pos (abs_pos.mpr h) 2
    nlinarith [sq_nonneg (x 0 + x 1), sq_abs (x 1)]
example : Summable (fun k : Fin 1 → ℤ => ‖(if k = 0 then (1 : ℂ) else 0)‖) :=
  summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp_all)
example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧ (0 : ℝ) < 1 ∧
    (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ 0 0 = 1 ^ 2 :=
  ⟨Matrix.PosDef.one, one_pos, isReducedImaginaryPart_one.first⟩
example : (0 : ℝ) < 1 ∧ 1 ≤ (2 : ℕ) ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 2 ∧
    (1 : ℝ) ^ 2 ≤ 2 * ((2 : ℕ) : ℝ) ∧ (1 / 2 : ℝ)⁻¹ ≤ 1 ^ 2 * (2 * ((2 : ℕ) : ℝ)) ^ (2 - 1) := by
  norm_num
end
end GroundTheory.Heights₂.Heights


