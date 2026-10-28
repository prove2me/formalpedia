-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator
-- name    : KLSModular_FunctionalInequalities_Probability_Diffusion_Generator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:33:10.99701+00:00
-- url     : https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2
-- title:
--   Coordinate-free diffusion generator and coordinate transport
-- statement:
--   `Probability.Diffusion.diffusionGenerator b σ F x` is the real-valued operator $DF(x)[b(x)] + \frac12\sum_k D^2F(x)[σ(x,k),σ(x,k)]$, for drift `b`, noise columns `σ`, test function `F`, and state `x`; the sum is over `Fin d`. For a finite-dimensional real normed space, `stateEquiv` identifies it continuously linearly with `Fin (Module.finrank ℝ V) → ℝ`, while `transportDrift` and `transportNoise` conjugate the drift and noise through a continuous linear equivalence.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Calculus.FDeriv.Basic
--   import Mathlib.Analysis.Calculus.FDeriv.Comp
--   import Mathlib.Analysis.Calculus.FDeriv.Linear
--   import Mathlib.Analysis.Calculus.FDeriv.Equiv
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   import Mathlib.LinearAlgebra.Basis.Fin
--   import Mathlib.Analysis.Calculus.ContDiff.Basic
--   import Mathlib.Analysis.Calculus.FDeriv.Mul
--   import Mathlib.Analysis.Calculus.ContDiff.Operations
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def diffusionGenerator {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
--       {d : ℕ} (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) : ℝ :=
--     fderiv ℝ F x (b x) + (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ F) x (σ x k) (σ x k)
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`diffusionGenerator_transport`](https://prove2.me/theorems/9a1d8a25-4515-49cd-b4f2-f5f23338d6b2)
--   - [`diffusionGenerator_comp`](https://prove2.me/theorems/04591c87-9e70-47ad-8801-7d7fe84bea55)
--   - [`diffusionGenerator_comp_of_contDiffAt`](https://prove2.me/theorems/83912579-a2cc-45d3-836f-d766607ea3b3)
--   - [`diffusionGenerator_mul`](https://prove2.me/theorems/2d42e13d-4529-4774-b00a-37bb995a10d9)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean) · `FunctionalInequalities.Probability.Diffusion.Generator` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L23-L42 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, definition bundle `KLSModular_FunctionalInequalities_Probability_Diffusion_Generator`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations

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


