-- Prove2me | Definitions.Def_EngageInfo_concaveClosure
-- name    : EngageInfo_concaveClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:00.856606+00:00
-- url     : https://prove2.me/theorems/ff7ed4dd-b942-4f23-87ed-9427ba879b85
-- title:
--   Concave closure (8): $V(\alpha)=\sup\{x : (\alpha,x)\in\mathrm{co}(\operatorname{graph} f)\}$
-- statement:
--   For a function $f$ of the belief, let $\operatorname{graph} f=\{(\alpha,f(\alpha)) : \alpha\in[0,1]\}$ and let $\mathrm{co}(f)$ be its convex hull in $\mathbb R^2$. The **concave closure** of $f$ is
--
--   $$V(\alpha)=\sup\{x : (\alpha,x)\in\mathrm{co}(f)\}.$$
--
--   The paper's optimal value function is $V^*$, the concave closure of $v^*$.
--
--   **Formalization Note** The convex hull is Mathlib's `convexHull ℝ` in $\mathbb R\times\mathbb R$ and the supremum is the real `sSup`; for $\alpha\in[0,1]$ and $f$ bounded on $[0,1]$ the set is nonempty and bounded above.
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, §3.2, p.12, (8)

import Mathlib

namespace EngageInfo

/-- **Concave closure (8) of a function of the belief.**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §3.2, p.12, (8):
"V∗(α) ≡ sup{x|(α, x) ∈ co(v∗)}, where co(v∗) is the convex hull of the graph of v∗ (i.e., the set
{(α, x)|x = v∗(α), α ∈ [0, 1]})".

`graphOn01 f` is the graph `{(α, f α) | α ∈ [0, 1]}` of `f` over beliefs, and
`concaveClosure f α = sup {x | (α, x) ∈ co(graph f)}`. The paper's `V∗` is
`concaveClosure (vstar M)`.

**Formalization Note** `co` is Mathlib's `convexHull ℝ` in `ℝ × ℝ`, and the supremum is the real
`sSup`. For `α ∈ [0, 1]` and `f` bounded on `[0, 1]` (as `v∗` is), the set is nonempty and bounded
above, so `sSup` is the true supremum. -/
def graphOn01 (f : ℝ → ℝ) : Set (ℝ × ℝ) := {q | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 = f q.1}

/-- The concave closure `V(α) = sup {x | (α, x) ∈ co(graph f)}` of (8). -/
noncomputable def concaveClosure (f : ℝ → ℝ) (α : ℝ) : ℝ :=
  sSup {x | (α, x) ∈ convexHull ℝ (graphOn01 f)}

end EngageInfo


