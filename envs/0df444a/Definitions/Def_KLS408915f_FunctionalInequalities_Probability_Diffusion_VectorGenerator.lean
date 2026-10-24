-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_VectorGenerator
-- name    : KLS408915f_FunctionalInequalities_Probability_Diffusion_VectorGenerator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:59:24.155675+00:00
-- url     : https://prove2.me/theorems/be50e08d-b494-4195-ad4d-4b656ae60e87
-- title:
--   Vector-valued diffusion generator
-- statement:
--   For real normed spaces $V$ and $W$, a natural number $d$, drift $b:V\to V$, diffusion directions $\sigma:V\to\operatorname{Fin}(d)\to V$, and a function $G:V\to W$, `vectorGenerator b σ G x` defines the $W$-valued expression
--   $$
--   DG(x)[b(x)] + \frac{1}{2}\sum_{k\in\operatorname{Fin}(d)} D^2G(x)[\sigma(x,k),\sigma(x,k)].
--   $$
--   Here the derivatives are formed using Lean's Fréchet derivative operator `fderiv`, and the finite sum is indexed by `Fin d`; no differentiability hypotheses are required by this definition.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/VectorGenerator.lean#L20-L24 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.VectorGenerator`, definition bundle `KLS408915f_FunctionalInequalities_Probability_Diffusion_VectorGenerator`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
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
open scoped Topology
namespace FunctionalInequalities
namespace Probability
namespace Diffusion
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
/-- The vector-valued generator `𝓛G(x) = DG(x)[b x] + ½ Σ_k D²G(x)[σ_k x, σ_k x]` of a `W`-valued function
(the drift of `G(X_t)` in Itô's formula; BKL arXiv:2610.05474v1, (81)–(82)). -/
def vectorGenerator {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : V → V) (σ : V → Fin d → V) (G : V → W) (x : V) : W :=
  fderiv ℝ G x (b x) + (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)
end Diffusion
end Probability
end FunctionalInequalities


