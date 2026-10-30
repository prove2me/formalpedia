-- Prove2me | Definitions.Def_DDROCS_ImpliesGuarantee
-- name    : DDROCS_ImpliesGuarantee
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:28:58.646174+00:00
-- url     : https://prove2.me/theorems/69e7dcc0-90eb-4b16-8b86-1284b20d113c
-- title:
--   A set implies a probabilistic guarantee at level $\epsilon$
-- statement:
--   Let $\mathbb P$ be a measure on $\mathbb R^d$ (the law of the uncertain parameter $\tilde u$), $\mathcal U \subseteq \mathbb R^d$ and $\epsilon \in \mathbb R$. The set $\mathcal U$ **implies a probabilistic guarantee for $\mathbb P$ at level $\epsilon$** if for every concave function $g : \mathbb R^d \to \mathbb R$,
--
--   $$
--   g(u) \le 0 \ \text{ for all } u \in \mathcal U \quad\Longrightarrow\quad \mathbb P\bigl(g(\tilde u) \le 0\bigr) \ge 1-\epsilon .
--   $$
--
--   In the paper this is property (P2): for every decision $x^*$ and every constraint function $f(u,x)$ concave in $u$, robust feasibility $f(u,x^*) \le 0$ for all $u\in\mathcal U$ implies that the uncertain constraint $f(\tilde u, x^*) \le 0$ holds with probability at least $1-\epsilon$.
--
--   **Formalization Note** Because $x^*$ is fixed in (2), only $g = f(\cdot, x^*)$ matters; it ranges over all real-valued concave functions on $\mathbb R^d$, and every such $g$ arises as $f(\cdot,x^*)$ for $f(u,x) := g(u)$. A real-valued concave function on $\mathbb R^d$ is continuous, so the event $\{g \le 0\}$ is closed.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, p. 2, property (P2) and implication (2)

import Mathlib
open MeasureTheory

namespace DDROCS

/-- **A set implies a probabilistic guarantee at level `ε`**, property (P2) and implication (2).
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, p. 2, (P2) and (2):
"The set `U_ϵ` implies a probabilistic guarantee for `P∗` at level `ϵ`, that is, for any
`x∗ ∈ ℝ^k` and for every function `f(u,x)` concave in `u` for all `x`, we have the implication:
If `f(u,x∗) ≤ 0 ∀u ∈ U_ϵ`, then `P∗(f(ũ,x∗) ≤ 0) ≥ 1 − ϵ`."

`ImpliesGuarantee U P ε` says: for every concave `g : ℝ^d → ℝ` with `g ≤ 0` on `U`,
`P{u : g u ≤ 0} ≥ 1 − ε`.

**Formalization Note.** Since `x∗` is fixed in (2), only `g = f(·, x∗)` matters; it is an
arbitrary real-valued function concave on `ℝ^d`, and conversely every such `g` arises as
`f(·, x∗)` for `f(u, x) := g(u)`. So quantifying over all concave `g` is the same property as
quantifying over all `x∗` and all `f` concave in `u`. A real-valued concave function on `ℝ^d` is
continuous, so the event `{g ≤ 0}` is closed and measurable. The law `P` is a parameter (the
paper uses `P∗` and, in Theorem 1, any `P`). -/
def ImpliesGuarantee {d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d)))
    (P : Measure (EuclideanSpace ℝ (Fin d))) (ε : ℝ) : Prop :=
  ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ConcaveOn ℝ Set.univ g → (∀ u ∈ U, g u ≤ 0) →
    1 - ε ≤ (P {u | g u ≤ 0}).toReal

end DDROCS


