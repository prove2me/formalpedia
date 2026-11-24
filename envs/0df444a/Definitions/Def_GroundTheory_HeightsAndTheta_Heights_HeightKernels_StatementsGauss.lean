-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:00.957731+00:00
-- url     : https://prove2.me/theorems/ffd50c2a-1a79-4787-bbe7-49540db0ce73
-- title:
--   Statements Gauss
-- statement:
--   Definitions and structural lemmas for Statements Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsGauss.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Theorems.Thm_GroundTheory_Global_mem_dualLattice

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
open scoped FourierTransform
noncomputable section
def gaussLattice {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin g)) :=
  Submodule.span ℤ (Set.range fun i : Fin g => WithLp.toLp 2 (B *ᵥ Pi.single i 1))
def gaussShellConst (n : ℕ) : ℝ :=
  3 ^ n * √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π))
def GaussSqrt.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∃ B : Matrix (Fin g) (Fin g) ℝ, Bᵀ * B = Y
def GaussLatticeIsLattice.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    DiscreteTopology (gaussLattice B) ∧ ∀ [DiscreteTopology (gaussLattice B)], IsZLattice ℝ (gaussLattice B)
def GaussLatticeCovolume.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ZLattice.covolume (gaussLattice B) = |B.det|
def GaussLatticeCoords.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    (∀ k : Fin g → ℤ, WithLp.toLp 2 (B *ᵥ intVec k) ∈ gaussLattice B) ∧
    (∀ x ∈ gaussLattice B, ∃ k : Fin g → ℤ, x = WithLp.toLp 2 (B *ᵥ intVec k)) ∧
    Function.Injective fun k : Fin g → ℤ => B *ᵥ intVec k
def GaussFourierSelf.Statement : Prop :=
  ∀ (g : ℕ) (w : EuclideanSpace ℝ (Fin g)),
    𝓕 (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) w =
      ((Real.exp (-π * ‖w‖ ^ 2) : ℝ) : ℂ)
def GaussPoissonBound.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 → ∀ a : Fin g → ℝ,
    Summable (fun k : Fin g → ℤ =>
      Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))) ∧
    Summable (fun μ : GroundTheory.Global.dualLattice (gaussLattice B) =>
      Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)) ∧
    ∑' k : Fin g → ℤ, Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a)))) ≤
      |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
        Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)
def GaussDualMin.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ∀ μ ∈ GroundTheory.Global.dualLattice (gaussLattice B), μ ≠ 0 →
      ∃ l : Fin g → ℤ, l ≠ 0 ∧ qf (Bᵀ * B)⁻¹ (intVec l) ≤ ‖μ‖ ^ 2
def GaussDetFactor.Statement : Prop :=
  ∀ (g : ℕ) (Y B : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → Bᵀ * B = (1 / 2 : ℝ) • Y →
    |B.det|⁻¹ = √2 ^ g * Y.det ^ (-(1 / 2 : ℝ))
def GaussPoissonDual.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) → ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => Real.exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∃ Λ : Submodule ℤ (EuclideanSpace ℝ (Fin g)), (∀ v ∈ Λ, v ≠ 0 → ρ ≤ ‖v‖) ∧
        ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) ≤
          √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)
def GaussPacking.Statement : Prop :=
  ∀ (n : ℕ) (s : Finset (EuclideanSpace ℝ (Fin n))) (δ r : ℝ), 0 < δ → 0 ≤ r →
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) → (∀ x ∈ s, ‖x‖ ≤ r) →
    (s.card : ℝ) ≤ (1 + 2 * r / δ) ^ n
def GaussTermBound.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
    ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2) ≤
      √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ))
def GaussShell.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) → ∀ (F : Finset Λ) (m : ℕ),
      ∑ μ ∈ F.filter (fun μ : Λ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊ = m),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        gaussShellConst n * (1 + 1 / δ) ^ n * Real.exp (-(m : ℝ))
def GaussShellSum.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) →
      Summable (fun μ : Λ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)) ∧
      ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        2 * gaussShellConst n * (1 + 1 / δ) ^ n
def GaussConstant.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → √2 ^ n * (2 * gaussShellConst n) ≤ (72 * Real.exp 4 * n) ^ ((n : ℝ) / 2)
example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≠ 0 :=
  ⟨Matrix.PosDef.one, by simp⟩
example : ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 := by simp
example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧
    ((√2)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᵀ * ((√2)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
      (1 / 2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  refine ⟨Matrix.PosDef.one, ?_⟩
  rw [transpose_smul, transpose_one, smul_mul_smul_comm, mul_one]
  congr 1
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num
abbrev gaussUnit : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (Pi.single 0 1)
theorem gaussUnit_norm : ‖gaussUnit‖ = 1 := by
  simp [gaussUnit]
theorem mem_gaussLattice_one {x : EuclideanSpace ℝ (Fin 1)} :
    x ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ) ↔ ∃ a : ℤ, a • gaussUnit = x := by
  have h : (Set.range fun i : Fin 1 => WithLp.toLp 2 ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
      Pi.single i 1)) = {gaussUnit} := by
    rw [Set.range_unique, Matrix.one_mulVec]
    rfl
  rw [gaussLattice, h, Submodule.mem_span_singleton]
theorem gaussLattice_one_min : ∀ v ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ), v ≠ 0 →
    (1 : ℝ) ≤ ‖v‖ := by
  intro v hv hv0
  obtain ⟨a, rfl⟩ := mem_gaussLattice_one.1 hv
  have ha : a ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
  rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, gaussUnit_norm, mul_one, Real.norm_eq_abs]
  exact_mod_cast Int.one_le_abs ha
example : 1 ≤ 1 ∧ (0 : ℝ) < 1 ∧
    ∀ v ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ), v ≠ 0 → (1 : ℝ) ≤ ‖v‖ :=
  ⟨le_rfl, one_pos, gaussLattice_one_min⟩
example : (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≠ 0 ∧
    gaussUnit ∈ GroundTheory.Global.dualLattice (gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
    gaussUnit ≠ 0 := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [GroundTheory.Global.mem_dualLattice]
    intro x hx
    obtain ⟨a, rfl⟩ := mem_gaussLattice_one.1 hx
    refine ⟨a, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, real_inner_self_eq_norm_sq, gaussUnit_norm]
    simp
  · intro h
    have := gaussUnit_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
example : ∀ x ∈ ({0, gaussUnit} : Finset (EuclideanSpace ℝ (Fin 1))),
    ∀ y ∈ ({0, gaussUnit} : Finset (EuclideanSpace ℝ (Fin 1))), x ≠ y → (1 : ℝ) ≤ ‖x - y‖ := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · simp
  · simp
  · exact absurd rfl hxy
example : ∀ x ∈ ({0, gaussUnit} : Finset (EuclideanSpace ℝ (Fin 1))), ‖x‖ ≤ (1 : ℝ) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp
  · simp
example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧ (0 : ℝ) < 1 ∧
    ∀ l : Fin 1 → ℤ, l ≠ 0 → (1 : ℝ) ^ 2 ≤ qf (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ (intVec l) :=
  ⟨Matrix.PosDef.one, one_pos, isReducedImaginaryPart_one.min⟩
end
end GroundTheory.Heights₂.Heights


