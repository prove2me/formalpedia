-- Prove2me | Definitions.Def_NonstatNV_Model_Standing
-- name    : NonstatNV_Model_Standing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:33.93298+00:00
-- url     : https://prove2.me/theorems/552443e2-490e-4b21-854e-f4483406e243
-- title:
--   Standing assumptions of the Nonstationary Newsvendor (Assumption 1)
-- statement:
--   A model satisfies the **standing assumptions** if
--
--   1. $\mu_{\min}\le\mu_{\max}$ (the parameter interval of Assumption 1(a));
--   2. $b_{\max}\ge0$ and $h_{\max}\ge0$;
--   3. $Q$ is nonempty and $Q\subseteq[0,Q_{\max}]$ ("a fixed subset of $\mathbb R_+$ bounded above by $Q_{\max}$");
--   4. for every $\mu\in[\mu_{\min},\mu_{\max}]$, $D_\mu$ is integrable with mean $\mathbb E[D_\mu]=\mu$;
--   5. for every $\mu\in[\mu_{\min},\mu_{\max}]$, $D_\mu$ is sub-Gaussian (Assumption 1(b)): it satisfies the tail condition $\mathbb P(|X|>x)\le2e^{-x^2/K^2}$ for some $K>0$, which may depend on $\mu$.
--
--   These are the assumptions stated once in §2 and used by every result of the paper.
--
--   **Formalization Note** Nonemptiness of $Q$ is presupposed by every $\arg\min_{q\in Q}$ of the paper. Assumption 2 (Lipschitz cost), the uniform sub-Gaussian bound on the noise and the argmin selection are separate predicates, added to a statement exactly where the paper uses them.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, §2, pp.9–10: Q (p.9), Assumption 1 and footnote 4 (p.10), mean convention (p.10)

import Definitions.Def_NonstatNV_Model
import Definitions.Def_NonstatNV_IsTailSubGaussian

open MeasureTheory

namespace NonstatNV

/-- The standing assumptions of the model (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, §2, pp.9–10):

1. `μmin ≤ μmax` (the bounded parameter interval of Assumption 1(a));
2. `0 ≤ bmax`, `0 ≤ hmax` (`b_t ∈ [0, bmax]`, `h_t ∈ [0, hmax]`, p.9);
3. `Q` is nonempty and `Q ⊆ [0, Qmax]` ("a fixed subset of ℝ₊ bounded above by Qmax", p.9);
4. for every `μ ∈ [μmin, μmax]`, `D_μ` is integrable with mean `μ` ("our taking μ = E[D_μ]", p.10);
5. for every `μ ∈ [μmin, μmax]`, `D_μ` is sub-Gaussian (Assumption 1(b), footnote 4): its tail
   satisfies `IsTailSubGaussian` with some `K > 0`, which may depend on `μ`.

**Formalization Note** Nonemptiness of `Q` is presupposed by every `argmin_{q∈Q}` of the paper.
Assumption 2 (`Model.LipschitzCost`), the uniform sub-Gaussian bounds (`Model.NoiseMGFBound`) and
the minimizer selection (`Model.IsArgminSelection`, which also asserts that minimizers exist) are
separate predicates, added where used. -/
def Model.Standing (M : Model) : Prop :=
  M.μmin ≤ M.μmax ∧ 0 ≤ M.bmax ∧ 0 ≤ M.hmax ∧ M.Q.Nonempty ∧ M.Q ⊆ Set.Icc 0 M.Qmax ∧
    ∀ μ ∈ Set.Icc M.μmin M.μmax,
      Integrable (fun d : ℝ => d) (M.D μ : Measure ℝ) ∧
      ∫ d, d ∂(M.D μ : Measure ℝ) = μ ∧
      ∃ K : ℝ, 0 < K ∧ IsTailSubGaussian (M.D μ : Measure ℝ) K

end NonstatNV


