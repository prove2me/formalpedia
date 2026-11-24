-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsSiegelReducedCoordinates
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsSiegelReducedCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:29.519954+00:00
-- url     : https://prove2.me/theorems/a423271c-2715-49d6-87c1-cfc8c04cdaec
-- title:
--   Is Siegel Reduced Coordinates
-- statement:
--   Definitions and structural lemmas for Is Siegel Reduced Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/IsSiegelReducedCoordinates.lean

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open Matrix MeasureTheory
noncomputable section
def qf {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (Y *ᵥ v)
def intVec {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)
def firstMinSq {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) : ℝ :=
  ⨅ v : {v : ι → ℤ // v ≠ 0}, qf G (intVec v.1)
def siegelGram {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ (Y⁻¹ * X) (X * Y⁻¹) (Y + X * Y⁻¹ * X)
def S1.Statement : Prop :=
  ∀ (g : ℕ) (hg : 0 < g) (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ),
    G ∈ symplecticGroup (Fin g) ℝ → G.PosDef →
    firstMinSq G ≤ 2 * g ∧
    ∃ M ∈ symplecticGroup (Fin g) ℤ,
      let G' := (M.map (Int.cast : ℤ → ℝ))ᵀ * G * M.map (Int.cast : ℤ → ℝ)
      G' (Sum.inl ⟨0, hg⟩) (Sum.inl ⟨0, hg⟩) = firstMinSq G ∧
      G'.toBlocks₁₁.det ≤ firstMinSq G * (2 * g) ^ (g - 1) ∧
      ∃ X Y : Matrix (Fin g) (Fin g) ℝ, X.IsSymm ∧ Y.PosDef ∧ G' = siegelGram X Y
def S2.Statement : Prop :=
  ∀ (g : ℕ) (hg : 0 < g) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∀ v : Fin g → ℝ,
    v ⟨0, hg⟩ ^ 2 / Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩ ≤ qf Y v
def S3.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) → ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => Real.exp (-(Real.pi / 2) * qf Y (intVec k + u))) ∧
      ∑' k : Fin g → ℤ, Real.exp (-(Real.pi / 2) * qf Y (intVec k + u)) ≤
        (C * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g
def tauOf {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℂ :=
  X.map (fun x : ℝ => (x : ℂ)) + Complex.I • Y.map (fun x : ℝ => (x : ℂ))
def cvec {g : ℕ} (v : Fin g → ℝ) : Fin g → ℂ := fun i => (v i : ℂ)
def thetaChar {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ) : ℂ :=
  ∑' k : Fin g → ℤ,
    Complex.exp (Real.pi * Complex.I *
        (cvec (intVec k + a) ⬝ᵥ (tauOf X Y *ᵥ cvec (intVec k + a))) +
      2 * Real.pi * Complex.I * (cvec (intVec k + a) ⬝ᵥ (z + cvec b)))
def thetaN {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (u₁ u₂ : Fin g → ℝ) : ℝ :=
  ‖thetaChar X Y a b (tauOf X Y *ᵥ cvec u₁ + cvec u₂)‖ * Real.exp (-Real.pi * qf Y u₁)
def thetaBeta {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) : ℝ :=
  ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 4 : ℝ))
def distInt (x : ℝ) : ℝ := |x - round x|
def IsHalfIntegral {g : ℕ} (a : Fin g → ℝ) : Prop := ∀ i, ∃ m : ℤ, a i = m / 2
def IsSiegelReducedCoordinates {g : ℕ} (hg : 0 < g) (X Y : Matrix (Fin g) (Fin g) ℝ) : Prop :=
  Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩ = firstMinSq (siegelGram X Y) ∧
    (Y⁻¹).det ≤ firstMinSq (siegelGram X Y) * (2 * g) ^ (g - 1)
def errE (C : ℝ) (g : ℕ) (ρ : ℝ) : ℝ :=
  g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g)
def S4.Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ) (hg : 0 < g) (X Y : Matrix (Fin g) (Fin g) ℝ),
    X.IsSymm → Y.PosDef → IsSiegelReducedCoordinates hg X Y → ∀ a b : Fin g → ℝ,
      IsHalfIntegral a → IsHalfIntegral b →
      (∫ u in Set.Icc (0 : (Fin g → ℝ) × (Fin g → ℝ)) 1, thetaN X Y a b u.1 u.2 ^ 2) =
          thetaBeta Y ^ 2 ∧
      ∀ u₁ u₂ : Fin g → ℝ,
        thetaN X Y a b u₁ u₂ ≤ thetaBeta Y * Real.exp
          (-(Real.pi / (2 * Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩)) * distInt (u₁ ⟨0, hg⟩ + a ⟨0, hg⟩) ^ 2 +
            errE C g (Real.sqrt (Y⁻¹ ⟨0, hg⟩ ⟨0, hg⟩)))
def mean {σ : Type*} [Fintype σ] (f : σ → ℝ) : ℝ := (∑ s, f s) / Fintype.card σ
def S5.Statement : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) (σ : Type) [Fintype σ] [Nonempty σ] (ρ : σ → ℝ) (Φ : ℝ),
      (∀ s, 0 < ρ s ∧ ρ s ≤ Real.sqrt (2 * g)) → 0 ≤ Φ →
      mean (fun s => Real.pi / 96 * (ρ s)⁻¹ ^ 2 - errE C₀ g (ρ s)) ≤ Φ →
      mean (fun s => (ρ s)⁻¹ ^ 2) ≤ C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)) ∧
      mean (fun s => errE C₀ g (ρ s)) ≤ C * (Φ + (g : ℝ) ^ 2 * Real.log (2 * g)) ∧
      mean (fun s => max (Real.log (ρ s)⁻¹) 0) ≤
        1 / 2 * Real.log (1 + mean (fun s => (ρ s)⁻¹ ^ 2))
def firstMinimum {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⨅ v : {v : L // v ≠ 0}, ‖(v.1 : EuclideanSpace ℝ (Fin n))‖
def shortVectorsIn {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {v | v ∈ L ∧ v ∈ V ∧ ‖v‖ ≤ r ∧ v ≠ 0}
def S8.Statement : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L],
    (firstMinimum L / Real.sqrt n) ^ n ≤ ZLattice.covolume L ∧
    ∀ (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℝ), firstMinimum L ≤ r →
      (shortVectorsIn L V r).Finite ∧
      ((shortVectorsIn L V r).ncard : ℝ) ≤ (3 * r / firstMinimum L) ^ Module.finrank ℝ V - 1
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


