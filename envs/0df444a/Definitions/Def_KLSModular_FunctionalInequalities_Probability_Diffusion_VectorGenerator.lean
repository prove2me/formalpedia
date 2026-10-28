-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_VectorGenerator
-- name    : KLSModular_FunctionalInequalities_Probability_Diffusion_VectorGenerator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:08:50.400311+00:00
-- url     : https://prove2.me/theorems/a27154a7-c41b-4d48-aa0c-9939263debb7
-- title:
--   Vector-valued diffusion generator
-- statement:
--   For real normed spaces $V$ and $W$, a natural number $d$, drift $b:V\to V$, diffusion directions $\sigma:V\to\operatorname{Fin}(d)\to V$, and a function $G:V\to W$, `vectorGenerator b σ G x` defines the $W$-valued expression
--   $$
--   DG(x)[b(x)] + \frac{1}{2}\sum_{k\in\operatorname{Fin}(d)} D^2G(x)[\sigma(x,k),\sigma(x,k)].
--   $$
--   Here the derivatives are formed using Lean's Fréchet derivative operator `fderiv`, and the finite sum is indexed by `Fin d`; no differentiability hypotheses are required by this definition.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   import Mathlib.Analysis.Calculus.ContDiff.Basic
--   import Mathlib.Analysis.Calculus.ContDiff.Operations
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def vectorGenerator {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
--       (b : V → V) (σ : V → Fin d → V) (G : V → W) (x : V) : W :=
--     fderiv ℝ G x (b x) + (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`vectorGenerator_clm_comp`](https://prove2.me/theorems/caa939ed-b8ae-4cc1-9991-797211b242e5)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/VectorGenerator.lean) · `FunctionalInequalities.Probability.Diffusion.VectorGenerator` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/VectorGenerator.lean#L20-L24 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.VectorGenerator`, definition bundle `KLSModular_FunctionalInequalities_Probability_Diffusion_VectorGenerator`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

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


