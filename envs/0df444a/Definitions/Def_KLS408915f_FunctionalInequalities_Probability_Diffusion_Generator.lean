-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
-- name    : KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:51:31.752642+00:00
-- url     : https://prove2.me/theorems/0d14e034-fb83-4cff-8549-aea61648ee48
-- title:
--   Coordinate-free diffusion generator and coordinate transport
-- statement:
--   `Probability.Diffusion.diffusionGenerator b σ F x` is the real-valued operator $DF(x)[b(x)] + \frac12\sum_k D^2F(x)[σ(x,k),σ(x,k)]$, for drift `b`, noise columns `σ`, test function `F`, and state `x`; the sum is over `Fin d`. For a finite-dimensional real normed space, `stateEquiv` identifies it continuously linearly with `Fin (Module.finrank ℝ V) → ℝ`, while `transportDrift` and `transportNoise` conjugate the drift and noise through a continuous linear equivalence.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L23-L42 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Fin

noncomputable section
namespace FunctionalInequalities
namespace Probability
namespace Diffusion
/-- `𝓛F(x) = DF(x)[b x] + ½ Σ_k D²F(x)[σ_k x, σ_k x]`. -/
noncomputable def diffusionGenerator {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) : ℝ :=
  fderiv ℝ F x (b x) + (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ F) x (σ x k) (σ x k)
section Adapter
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
/-- Coordinates of a finite-dimensional state space (`N = finrank ℝ V` definitionally). -/
noncomputable def stateEquiv (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
  (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
/-- Transported drift / noise. -/
noncomputable def transportDrift {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    (Φ : V ≃L[ℝ] V') (b : V → V) : V' → V' := fun y => Φ (b (Φ.symm y))
noncomputable def transportNoise {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    {d : ℕ} (Φ : V ≃L[ℝ] V') (σ : V → Fin d → V) : V' → Fin d → V' :=
  fun y k => Φ (σ (Φ.symm y) k)
end Adapter
end Diffusion
end Probability
end FunctionalInequalities


