-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
-- name    : Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:40.404063+00:00
-- url     : https://prove2.me/theorems/48c5b17e-c469-42bd-bab3-4a19d059f628
-- title:
--   Inverse Norm Le Of Integer Inner
-- statement:
--   Definitions and structural lemmas for Inverse Norm Le Of Integer Inner, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/InverseNormLeOfIntegerInner.lean

import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.LatticeEstimates
open Finset MeasureTheory
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder
def Ms_min : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.RingOfIntegers K), x ≠ 0 →
    (Module.finrank ℚ K : ℝ) ≤ ∑ φ : K →+* ℂ, ‖φ (x : K)‖ ^ 2
def Ms_entry : Prop :=
  ∀ (f : ℕ) (p q : Fin f → ℝ) (z : Fin f → ℂ) (R2 : ℝ), (∀ τ, 0 ≤ p τ) → (∀ τ, 0 ≤ q τ) →
    (∀ τ, ‖z τ‖ ^ 2 ≤ p τ * q τ) → ∑ τ, p τ ≤ R2 → ∑ τ, q τ ≤ R2 → ∑ τ, ‖z τ‖ ^ 2 ≤ R2 ^ 2
def Ms_hadamard : Prop :=
  ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), G.PosSemidef → G.det.re ≤ ∏ c, (G c c).re
def Ms_between : Prop :=
  ∀ (R G : Type) [Ring R] [AddCommGroup G] [Module R G] [Finite G] (r : ℕ),
    Nat.card {H : Submodule R G // ∃ s : Fin r → G, Submodule.span R (Set.range s) = H} ≤ Nat.card G ^ r
def MeanValueInequalityRadial : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (F : E → ℂ), Differentiable ℂ F →
    (∀ θ : ℝ, μ.map (fun w : E => Complex.exp (θ * Complex.I) • w) = μ) →
    Integrable (fun w => ‖F w‖ ^ 2) μ → ‖F 0‖ ^ 2 ≤ ∫ w, ‖F w‖ ^ 2 ∂μ
def WeightedCauchySchwarz : Prop :=
  ∀ (ι : Type) [Fintype ι] (w : ι → ℝ) (q c : ι → ℂ) (O : ℝ), (∀ e, 0 < w e) → 0 < O →
    ‖∑ e, q e * (w e : ℂ) * c e‖ ^ 2 ≤ (∑ e, ‖q e‖ ^ 2 * w e) * O⁻¹ * ∑ e, ‖c e‖ ^ 2 * w e * O
def L1LeSqrtCardOfL2 : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℂ), ∑ e, ‖c e‖ ^ 2 ≤ 1 → ∑ e, ‖c e‖ ≤ Real.sqrt (Fintype.card ι)
def UnitaryMinorNormLeOne : Prop :=
  ∀ (n r : ℕ) (U : Matrix (Fin n) (Fin n) ℂ) (e e' : Fin r → Fin n), U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    ‖(U.submatrix e e').det‖ ≤ 1
def InverseNormLeOfIntegerInner : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x φ : V) (z : ℤ), z ≠ 0 →
    inner ℂ x φ = (z : ℂ) → 1 / ‖x‖ ≤ ‖φ‖
def InterlacingLogSquareBound : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (T c rho : ℝ), Interlace lam nu → 1 ≤ T →
    c ≠ 0 → |c| ≤ (Wnum lam : ℝ) ^ (n * ∑ i, (min (len lam i) (B0 lam nu)).toNat) →
    0 < rho → rho ^ 2 ≤ T ^ (-(degZ lam nu)) * weylDim lam →
    Real.log ((c * rho) ^ 2) ≤ MeanSquareTwistBound lam nu (Real.log T)
def MuMaxBoundOfAntitoneWeight : Prop :=
  ∀ (κ : ℕ) (lam : Fin (κ + 1) → ℤ) (muMax dmin cc : ℝ), Antitone lam →
    0 < cc → 0 < dmin → (((κ : ℝ) + 1) ^ (wt (plus lam)).toNat)⁻¹ ≤ dmin →
    cc ≤ ((plus lam 0 : ℝ) + κ + 1) ^ ((κ + 1) ^ 2) → muMax ≤ -Real.log dmin + Real.log cc →
    muMax ≤ MeanSquareWeightBound lam
def AntitoneWeightLogBoundExists : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C : ℝ, ∀ (κ : ℕ) (lam : Fin (κ + 1) → ℤ) (v logT logNorm muStd mu : ℝ),
    1 ≤ v → 0 ≤ logT → Antitone lam →
    logNorm ≤ Real.log (C₀ * ((κ : ℝ) + 1) ^ 3 * v ^ 2) → muStd ≤ MeanSquareWeightBound lam →
    mu ≤ (wt (plus lam) : ℝ) * logNorm + muStd - (lam (Fin.last κ) : ℝ) * logT →
    mu ≤ (wt (plus lam) : ℝ) * (C * Real.log (((κ : ℝ) + 1) * v))
        + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus lam 0 : ℝ) + (κ : ℝ) + 1) + |(lam (Fin.last κ) : ℝ)| * logT
def Col_other : Prop :=
  ∀ (κ : ℕ) (lam : Fin (κ + 1) → ℤ) (S : ℤ), (κ : ℤ) + 1 ≤ S → 0 ≤ lam (Fin.last κ) → lam 0 ≤ 3 * S →
    (∀ i, i ≠ 0 → lam i - lam (Fin.last κ) ≤ S + 1) → wt (plus lam) ≤ (κ + 1 + 3) * S
end Formalism.HermitianLattices.LatticeEstimates


