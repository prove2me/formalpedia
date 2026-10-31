-- Prove2me | Definitions.Def_SDEConvexOpt_SigmaInfL2
-- name    : SDEConvexOpt_SigmaInfL2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:26.066758+00:00
-- url     : https://prove2.me/theorems/73127aa4-4b0b-4f24-ab00-ee9ae097d832
-- title:
--   Square-integrable noise: $\sigma_\infty\in L^2(\mathbb R_+)$
-- statement:
--   The diffusion term $\sigma$ has square-integrable noise when
--   $$
--   \int_0^\infty\sigma_\infty(t)^2\,dt<+\infty,\qquad \sigma_\infty(t)=\sup_{x\in\mathbb R^d}\|\sigma(t,x)\|_F .
--   $$
--   This is the hypothesis under which the solution of (SDE) converges almost surely to a minimizer.
--
--   **Formalization Note** The integral is a lower Lebesgue integral in $[0,\infty]$ over $t\in[0,\infty)$. Under (H), $t\mapsto\sigma_\infty(t)$ is measurable, because the supremum may be taken over a countable dense set of $x$; so the condition is the paper's, without any integrability side condition.
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, (1.1), p.3; Theorem 3.1, p.9

import Definitions.Def_SDEConvexOpt_sigmaInf

open MeasureTheory
open scoped NNReal ENNReal

namespace SDEConvexOpt

open EthierKurtz

/-- The square-integrable noise condition `σ∞ ∈ L²(ℝ₊)`, i.e. `∫₀^∞ σ∞(t)² dt < +∞`
(Maulen S., Fadili, Attouch, arXiv:2207.02750v1, (1.1), p.3, and Theorem 3.1, p.9).

**Formalization Note** The integral is a lower Lebesgue integral in `ℝ≥0∞` over `t ∈ [0, ∞)`,
with `t` passed to `σ∞` as `t.toNNReal`. Under (H), `t ↦ σ∞(t)` is measurable (a supremum over a
countable dense set of `x`, by the Lipschitz continuity in `x`), so this is the paper's
condition, with no integrability side condition. -/
def SigmaInfL2 {d m : ℕ} (σ : ℝ≥0 × SDEState d → Diffusion d m) : Prop :=
  ∫⁻ t in Set.Ici (0 : ℝ), sigmaInf σ t.toNNReal ^ 2 < ∞

end SDEConvexOpt


