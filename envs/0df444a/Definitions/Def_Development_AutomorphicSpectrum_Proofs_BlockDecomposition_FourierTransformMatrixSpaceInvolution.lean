-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:17.018558+00:00
-- url     : https://prove2.me/theorems/f2e3aaac-41ea-4c86-9bbb-a9d9f12c0f30
-- title:
--   Fourier Transform Matrix Space Involution
-- statement:
--   Definitions and structural lemmas for Fourier Transform Matrix Space Involution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierTransformMatrixSpaceInvolution.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
def kerOp (C : ℂ) (a : ℝ) (R : V ≃ₗᵢ[ℝ] V) (g : V → ℂ) (u : V) : ℂ :=
  C * ∫ v : V, cexp (2 * Real.pi * I * ((a * ⟪u, R v⟫ : ℝ) : ℂ)) * g v
def chirp (k : ℝ) (u : V) : ℂ := cexp (2 * Real.pi * I * (k : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ))
def chirpS (k : ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (chirp k) f
def scaleEquiv (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) : V ≃L[ℝ] V :=
  R.symm.toContinuousLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ V (-a) (neg_ne_zero.2 ha)).toContinuousLinearEquiv
def kerS (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  C • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv a ha R) (𝓕 f)
end GlobalTheory.CompanionTheory.Kloc.Fresnel
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {m n : ℕ}
def matEquiv (m n : ℕ) : (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => WithLp.toLp 2 (fun p => u p.1 p.2)
      invFun := fun x i j => x (i, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
def unitMul (ι : Type) [Fintype ι] (ω : ℂ) (hω : ‖ω‖ = 1) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  ⟨(LinearEquiv.smulOfNeZero ℂ (EuclideanSpace ℂ ι) ω
      (by intro h; simp [h] at hω)).restrictScalars ℝ, fun x => by
    simp [norm_smul, hω]⟩
def opE (C s : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  C * ∫ v : Fin m → Fin n → ℂ, cexp (2 * Real.pi * I *
    ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v
def chE (k : ℝ) (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  cexp (2 * Real.pi * I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u
end GlobalTheory.CompanionTheory.Kloc.Fresnel


