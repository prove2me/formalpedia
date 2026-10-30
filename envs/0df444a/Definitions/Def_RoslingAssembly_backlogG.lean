-- Prove2me | Definitions.Def_RoslingAssembly_backlogG
-- name    : RoslingAssembly_backlogG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:38:31.28447+00:00
-- url     : https://prove2.me/theorems/6305082d-9918-4fbf-97ea-6c2e6bd91711
-- title:
--   Expected backlog function $\int_y^\infty(\xi-y)\varphi^{m+1}(\xi)\,d\xi$
-- statement:
--   Let $\varphi$ be the density of the one-period demand and $\varphi^{m+1}$ its $(m+1)$-fold convolution, the density of the total demand of $m+1$ periods. The **expected backlog function** is
--   $$G_m(y)=\int_y^\infty(\xi-y)\,\varphi^{m+1}(\xi)\,d\xi=\mathbb E\big[(\xi_1+\dots+\xi_{m+1}-y)^+\big],$$
--   the expected amount by which the demand of $m+1$ periods exceeds $y$.
--
--   In problem P it is used with $m=l_1$ and $y=Y_{1t}$: it gives the expected backlog of the end item at the time the period-$t$ order arrives.
--
--   **Formalization Note** The convolution enters only through this integral, written as an expectation under the product measure `Measure.pi` over $m+1$ coordinates.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 567, (1)–(2)

import Mathlib
open MeasureTheory

namespace RoslingAssembly

/-- **Expected backlog function** (p. 567, (1)–(2)). Rosling, *Optimal Inventory Policies for
Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 567: the backlog term
"∫_{Y_1t}^∞ (ξ − Y_1t) φ_1^{l_1+1}(ξ) dξ" of (1) and (2), "where φ_1^{l_1+1}(·) is the
convolution of φ(·) over (l_1 + 1) periods".

For a one-period demand law `μ` and `m : ℕ`,
$$G_m(y)=\int (\xi_1+\dots+\xi_{m+1}-y)^+\,d\mu^{\otimes(m+1)}=\int_y^\infty(\xi-y)\,\varphi^{m+1}(\xi)\,d\xi,$$
the expected amount by which the total demand of `m + 1` periods exceeds `y`. The paper uses it
with `m = l_1`, the end item's lead time.

**Formalization Note.** The `(m+1)`-fold convolution enters only through this integral, which
is written as an expectation under the product measure `Measure.pi` over `Fin (m + 1)`. When
`μ` has a finite mean (assumed wherever it is used) the integrand is integrable. -/
noncomputable def backlogG (μ : Measure ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  ∫ x, max 0 (∑ j, x j - y) ∂(Measure.pi fun _ : Fin (m + 1) => μ)

end RoslingAssembly


