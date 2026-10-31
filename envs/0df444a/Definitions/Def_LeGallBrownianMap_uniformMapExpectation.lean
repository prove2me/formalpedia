-- Prove2me | Definitions.Def_LeGallBrownianMap_uniformMapExpectation
-- name    : LeGallBrownianMap_uniformMapExpectation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:58.453511+00:00
-- url     : https://prove2.me/theorems/c28bcd51-c151-4aa6-b2f9-b35b20ad335a
-- title:
--   Expectation under the uniform law on $A^q_n$
-- statement:
--   For a bounded continuous function $f:\mathbb K\to\mathbb R$, a scale $c$ and $M_n$ uniformly distributed over $A^q_n$,
--
--   $$
--   \mathbb E\big[f(m_n, c\, d_{gr})\big] = \frac{1}{\# A^q_n}\sum_{M\in A^q_n} f\big(m(M), c\, d_{gr}\big).
--   $$
--
--   Convergence in distribution in $\mathbb K$ of the rescaled maps is expressed by the convergence of these expectations for every bounded continuous $f$.
--
--   **Formalization Note** When $A^q_n$ is empty ($q=3$, $n$ odd) the value is $0$; these $n$ are excluded in the theorems.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §1, p.2 (M_n uniform over A^q_n)

import Mathlib
import Definitions.Def_LeGallBrownianMap_QAngulation
import Definitions.Def_LeGallBrownianMap_mapGH
import Definitions.Def_LeGallBrownianMap_ghMeasurableSpace

open GromovHausdorff
open scoped BoundedContinuousFunction

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §1, p.2:
"we consider a random planar map M_n that is uniformly distributed over A^q_n."

`uniformMapExpectation q n c f = E[f(m_n, c d_gr)]` for `M_n` uniform on `A^q_n`: the average of
`f (mapGH c M)` over all rooted planar q-angulations `M` with `n` faces.

**Formalization Note.** The law of the random map is the uniform law on the finite set
`QAngulation q n`, so its expectations are finite averages; convergence in distribution in K is
stated through these expectations for all bounded continuous `f : K → ℝ`. When `A^q_n` is empty
(q = 3, n odd) the value is `0`; the mission's statements never use those `n`. -/
noncomputable def uniformMapExpectation (q n : ℕ) (c : ℝ) (f : GHSpace →ᵇ ℝ) : ℝ :=
  (Fintype.card (QAngulation q n) : ℝ)⁻¹ * ∑ M : QAngulation q n, f (mapGH c M.1)

end LeGallBrownianMap


