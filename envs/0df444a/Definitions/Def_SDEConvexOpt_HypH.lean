-- Prove2me | Definitions.Def_SDEConvexOpt_HypH
-- name    : SDEConvexOpt_HypH
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:41.400649+00:00
-- url     : https://prove2.me/theorems/1e54d93d-ecc1-4bd5-9b80-b3ad53293de7
-- title:
--   Assumption (H) on the diffusion $\sigma$: measurable, bounded entries, Lipschitz in $x$ uniformly in $t$
-- statement:
--   A diffusion term $\sigma:\mathbb R_+\times\mathbb R^d\to\mathbb R^{d\times m}$ satisfies (H) when it is a measurable matrix-valued function whose entries $\sigma_{ik}$ satisfy
--   $$
--   \sup_{t\ge0,\,x\in\mathbb R^d}|\sigma_{ik}(t,x)|<\infty,\qquad |\sigma_{ik}(t,x')-\sigma_{ik}(t,x)|\le l_0\|x'-x\|,
--   $$
--   for some $l_0>0$ and all $t\ge0$, $x,x'\in\mathbb R^d$.
--
--   The Lipschitz condition gives well-posedness of (SDE); the boundedness controls the noise.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$, and measurability is joint, for the Borel $\sigma$-algebra of $\mathbb R_{\ge0}\times\mathbb R^d$. One common bound $C$ for the finitely many entries is equivalent to one bound per entry.
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, (SDE) and (H), p.2

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SDEConvexOpt_Diffusion

open scoped NNReal

namespace SDEConvexOpt

open EthierKurtz

/-- The assumption (H) on the diffusion term `σ : ℝ₊ × ℝ^d → ℝ^{d×m}`
(Maulen S., Fadili, Attouch, arXiv:2207.02750v1, (SDE) and (H), p.2): `σ` is a measurable
matrix-valued function whose entries satisfy
`sup_{t ≥ 0, x ∈ ℝ^d} |σᵢₖ(t, x)| < ∞` and `|σᵢₖ(t, x') − σᵢₖ(t, x)| ≤ l₀ ‖x' − x‖`
for some `l₀ > 0` and all `t ≥ 0`, `x, x' ∈ ℝ^d`.

**Formalization Note** Time is `ℝ≥0`. The measurability of `σ` (stated on p.2 with (SDE)) is
joint, for the Borel σ-algebra of `ℝ≥0 × ℝ^d`. The paper bounds each of the finitely many entries
separately; one common bound `C` for all entries is equivalent. -/
def HypH {d m : ℕ} (σ : ℝ≥0 × SDEState d → Diffusion d m) : Prop :=
  Measurable σ ∧
    (∃ C : ℝ, ∀ (t : ℝ≥0) (x : SDEState d) (i : Fin d) (k : Fin m), |σ (t, x) (i, k)| ≤ C) ∧
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ (t : ℝ≥0) (x x' : SDEState d) (i : Fin d) (k : Fin m),
      |σ (t, x') (i, k) - σ (t, x) (i, k)| ≤ l₀ * ‖x' - x‖

end SDEConvexOpt


