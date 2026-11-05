-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_IsUtilityFunction
-- name    : BauerleRiederMDP_NoArbitrage_IsUtilityFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:50.786201+00:00
-- url     : https://prove2.me/theorems/057a5270-b710-47b7-a565-1c804a635cb0
-- title:
--   Utility function (Definition 3.4.1)
-- statement:
--   A function $U:\operatorname{dom}U\to\mathbb R$ is a **utility function** if $U$ is strictly increasing, strictly concave and continuous on $\operatorname{dom}U$. When $\operatorname{dom}U=[0,\infty)$, $U$ is required to be right-continuous in $0$.
--
--   Examples are $U(x)=\log x$ on $(0,\infty)$ and $U(x)=x^\gamma/\gamma$ on $[0,\infty)$ for $0<\gamma<1$.
--
--   **Formalization Note** $U$ is a function $\mathbb R\to\mathbb R$ and $\operatorname{dom}U$ a subset of $\mathbb R$; only the values of $U$ on $\operatorname{dom}U$ matter. Continuity on $\operatorname{dom}U$ in the subspace topology includes the right-continuity in $0$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 3.4.1, p.70 (PDF 84), and p.71 (PDF 85)

import Mathlib

namespace BauerleRiederMDP.NoArbitrage

/-- Definition 3.4.1 (Bäuerle & Rieder 2011, p.70, PDF 84): a function `U : dom U → ℝ` is a
utility function if `U` is strictly increasing, strictly concave and continuous on `dom U`. When
`dom U = [0, ∞)` the book supposes that `U` is also right-continuous in `0` (p.71, PDF 85).

**Formalization Note** `U` is a function `ℝ → ℝ` and `dom U ⊆ ℝ` a set; only the values on
`dom U` matter. `ContinuousOn U dom` is continuity of the restriction to `dom U`, which for
`dom U = [0, ∞)` includes the right-continuity in `0`. `StrictConcaveOn` includes the convexity
of `dom U` (an interval). -/
structure IsUtilityFunction (dom : Set ℝ) (U : ℝ → ℝ) : Prop where
  strictMonoOn : StrictMonoOn U dom
  strictConcaveOn : StrictConcaveOn ℝ dom U
  continuousOn : ContinuousOn U dom

end BauerleRiederMDP.NoArbitrage


