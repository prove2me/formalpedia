-- Prove2me | Definitions.Def_DDROFB_marginal
-- name    : DDROFB_marginal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:04:16.093843+00:00
-- url     : https://prove2.me/theorems/b95b3bd2-d87b-4599-b88f-9a132b7a2379
-- title:
--   Marginal law $\mathbb P_i$ of the $i$-th component
-- statement:
--   Let $\mathbb P$ be a measure on $\mathbb R^d$, the law of a random vector $\tilde u$, and let $i \in \{1,\dots,d\}$. The **marginal** $\mathbb P_i$ is the law of the component $\tilde u_i$:
--
--   $$
--   \mathbb P_i(A) \;=\; \mathbb P\bigl(\{u \in \mathbb R^d : u_i \in A\}\bigr), \qquad A \subseteq \mathbb R \text{ Borel}.
--   $$
--
--   The forward–backward confidence region is described entirely through the marginals $\mathbb P_1,\dots,\mathbb P_d$ and their means and deviations.
--
--   **Formalization Note** The marginal is the push-forward of $\mathbb P$ under the coordinate map of `EuclideanSpace ℝ (Fin d)`, which is continuous, hence measurable.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 1.1, p. 6 (unnumbered: "P_i denotes the marginal measure of ũ_i")

import Mathlib
open MeasureTheory

namespace DDROFB

/-- **Marginal law** `P_i` of the `i`-th component.
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Sec. 1.1, p. 6
(unnumbered): "`P_i` denotes the marginal measure of `ũ_i`."

`marginal P i` is the push-forward of `P` under the coordinate map `u ↦ u_i`.

**Formalization Note.** The coordinate map `EuclideanSpace ℝ (Fin d) → ℝ` is continuous, hence
measurable, so `Measure.map` is the true image measure (never Lean's zero measure for a
non-measurable map). -/
noncomputable def marginal {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) (i : Fin d) :
    Measure ℝ :=
  P.map (fun u => u i)

end DDROFB


