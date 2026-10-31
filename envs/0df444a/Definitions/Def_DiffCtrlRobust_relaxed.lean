-- Prove2me | Definitions.Def_DiffCtrlRobust_relaxed
-- name    : DiffCtrlRobust_relaxed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:14.191993+00:00
-- url     : https://prove2.me/theorems/8afbf7ec-0e2b-4c4e-b23a-eddbe4cbdb10
-- title:
--   Relaxed extension $b(x,v)$, $c(x,v)$ of a coefficient to $\mathcal P(\mathbb U)$
-- statement:
--   Let $\mathbb U$ be a compact metric space and $\mathrm V=\mathcal P(\mathbb U)$ the space of probability measures on $\mathbb U$. A coefficient $f(x,\zeta)$, such as the drift or the running cost, is extended to $\mathrm V$ by integration:
--
--   $$
--   f(x,\mathrm v)=\int_{\mathbb U} f(x,\zeta)\,\mathrm v(\mathrm d\zeta),\qquad \mathrm v\in\mathrm V.
--   $$
--
--   This is the relaxed-control convention: a control action is a probability measure on $\mathbb U$, and an ordinary action $\zeta$ is the Dirac mass at $\zeta$.
--
--   **Formalization Note** One definition serves the vector-valued drift and the real-valued cost. The integral is a Bochner integral.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2, p.5 (extension of b) and §2.1, p.6 (extension of c)

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- The relaxed extension of a coefficient to a probability measure on the control space:
`b(x, v) = ∫_U b(x, ζ) v(dζ)` and `c(x, v) := ∫_U c(x, ζ) v(dζ)`
(arXiv:2205.05894v2, §2, p.5, and §2.1, p.6).

**Formalization Note.** One definition serves the drift (`E = ℝ^d`) and the cost (`E = ℝ`).
V = P(U) is `ProbabilityMeasure U`. The integral is a Bochner integral, which is a genuine integral
for the coefficients of this mission: they are continuous on the compact set `{x} × U`. -/
noncomputable def relaxed {X U E : Type*} [MeasurableSpace U] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : X → U → E) (x : X) (μ : ProbabilityMeasure U) : E :=
  ∫ ζ, f x ζ ∂(μ : Measure U)

end DiffCtrlRobust


