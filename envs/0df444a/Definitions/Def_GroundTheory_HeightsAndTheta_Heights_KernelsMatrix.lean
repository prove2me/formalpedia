-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
-- name    : GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:44.659225+00:00
-- url     : https://prove2.me/theorems/5bc9e811-c209-4fbc-ba72-261108747018
-- title:
--   Kernels Matrix
-- statement:
--   Definitions and structural lemmas for Kernels Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KernelsMatrix.lean

import Mathlib
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
def qf {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (Y *ᵥ v)
def intVec {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)
def SymplecticReduction.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ),
    G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin g ⊕ Fin g → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      ρsq ≤ 2 * g ∧
      ∃ P ∈ symplecticGroup (Fin g) ℤ,
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ) (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ).toBlocks₁₁.det ≤
          ρsq * (2 * g) ^ (g - 1)
def siegelGram {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ (Y⁻¹ * X) (X * Y⁻¹) (Y + X * Y⁻¹ * X)
def SiegelCoordinates.Statement : Prop :=
  ∀ g : ℕ,
    (∀ X Y : Matrix (Fin g) (Fin g) ℝ, X.IsSymm → Y.PosDef →
      siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef) ∧
    ∀ G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ,
      G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
      ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
        XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2
def FirstCoordinateBound.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∀ v : Fin g → ℝ,
    v 0 ^ 2 / Y⁻¹ 0 0 ≤ qf Y v
def GaussianSum.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) →
    ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + u)) ≤
        (C * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g
def periodMatrix {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℂ :=
  X.map (↑) + Complex.I • Y.map (↑)
def thetaChar {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) : ℂ :=
  ∑' k : Fin g → ℤ,
    Complex.exp (π * Complex.I *
        ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
          (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
      2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))
def thetaNorm {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (u₁ u₂ : Fin g → ℝ) : ℝ :=
  ‖thetaChar X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ))‖ *
    exp (-π * qf Y u₁)
structure IsReducedImaginaryPart {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) :
    Prop where
  pos : 0 < ρ
  sq_le : ρ ^ 2 ≤ 2 * g
  first : Y⁻¹ 0 0 = ρ ^ 2
  min : ∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)
  det_le : Y⁻¹.det ≤ ρ ^ 2 * (2 * g) ^ (g - 1)
def ThetaBound.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) [NeZero g] (X Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ)
    (a b : Fin g → ℝ), X.IsSymm → Y.PosDef → IsReducedImaginaryPart Y ρ →
    (∀ i, ∃ m : ℤ, a i = m / 2) → (∀ i, ∃ m : ℤ, b i = m / 2) →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ)) ∧
    ∀ u₁ u₂ : Fin g → ℝ,
      thetaNorm X Y a b u₁ u₂ ≤ ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ)) *
        exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2 +
          (g * log (1 + 1 / ρ) + C * g * log (2 * g)))
def finMean {S : Type*} [Fintype S] (f : S → ℝ) : ℝ := (∑ s, f s) / Fintype.card S
def WeakMatrixArithmetic.Statement : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) [NeZero g] (S : Type) [Fintype S] [Nonempty S] (ρ : S → ℝ) (Φ : ℝ),
      (∀ s, 0 < ρ s ∧ ρ s ≤ √(2 * g)) → 0 ≤ Φ →
      finMean (fun s => π / 96 * (ρ s ^ 2)⁻¹ - (g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g))) ≤ Φ →
      finMean (fun s => (ρ s ^ 2)⁻¹) ≤ C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => g * log (1 + 1 / ρ s) + C₀ * g * log (2 * g)) ≤
        C * (Φ + g ^ 2 * log (2 * g)) ∧
      finMean (fun s => posLog (1 / ρ s)) ≤ 1 / 2 * log (1 + finMean (fun s => (ρ s ^ 2)⁻¹))
def ShortVectors.Statement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L],
    ∃ lam : ℝ, IsLeast {t | ∃ v ∈ L, v ≠ 0 ∧ t = ‖v‖} lam ∧
      (lam / √n) ^ n ≤ ZLattice.covolume L ∧
      ∀ (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ), lam ≤ r →
        {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0}.Finite ∧
        (({v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0}.ncard : ℕ) : ℝ) ≤
          (3 * r / lam) ^ Module.finrank ℝ U - 1
example : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ) ∈ symplecticGroup (Fin 1) ℝ ∧
    (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ).PosDef :=
  ⟨Submonoid.one_mem _, Matrix.PosDef.one⟩
example : siegelGram (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 ≠ 1 := by
  intro h
  have := congrFun (congrFun h (Sum.inr 0)) (Sum.inr 0)
  simp [siegelGram] at this
theorem isReducedImaginaryPart_one : IsReducedImaginaryPart (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 where
  pos := one_pos
  sq_le := by norm_num
  first := by simp
  min := by
    intro l hl
    have h0 : l 0 ≠ 0 := by
      intro h; apply hl; funext i; fin_cases i; exact h
    have h : (1 : ℝ) ≤ |(l 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    have h2 : (1 : ℝ) ≤ (l 0 : ℝ) * (l 0 : ℝ) := by
      nlinarith [abs_mul_abs_self (l 0 : ℝ), abs_nonneg (l 0 : ℝ)]
    simpa [qf, intVec, dotProduct] using h2
  det_le := by simp
example : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧ (0 : Matrix (Fin 1) (Fin 1) ℝ).IsSymm ∧
    ∀ l : Fin 1 → ℤ, l ≠ 0 → (1 : ℝ) ^ 2 ≤ qf (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ (intVec l) :=
  ⟨Matrix.PosDef.one, Matrix.isSymm_zero, isReducedImaginaryPart_one.min⟩
example : (∀ s : Unit, 0 < (fun _ => (1 : ℝ)) s ∧ (fun _ => (1 : ℝ)) s ≤ √(2 * (1 : ℕ))) ∧
    finMean (fun _ : Unit => π / 96 * ((1 : ℝ) ^ 2)⁻¹ -
      ((1 : ℕ) * log (1 + 1 / 1) + 0 * (1 : ℕ) * log (2 * (1 : ℕ)))) ≤ 1 := by
  refine ⟨fun _ => ⟨one_pos, ?_⟩, ?_⟩
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · simp only [finMean, Finset.univ_unique, Finset.sum_singleton, Fintype.card_unit]
    have h2 : (0 : ℝ) ≤ log 2 := log_nonneg (by norm_num)
    have hp : π / 96 ≤ 1 := by linarith [pi_lt_four]
    norm_num
    linarith
example (n : ℕ) : IsZLattice ℝ
    (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)) := inferInstance
example (n : ℕ) : DiscreteTopology
    (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)) := inferInstance
end
end GroundTheory.Heights₂.Heights


