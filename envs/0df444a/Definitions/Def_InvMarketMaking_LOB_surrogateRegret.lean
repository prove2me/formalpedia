-- Prove2me | Definitions.Def_InvMarketMaking_LOB_surrogateRegret
-- name    : InvMarketMaking_LOB_surrogateRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:29.480405+00:00
-- url     : https://prove2.me/theorems/0bb5aece-92e5-4f0f-8047-44cabda9a42c
-- title:
--   Surrogate regret $R^J_t=t\,J^*-\sum_{\tau\le t}r_\tau$ and virtual regret $R^\circ_t=t\,J(b^\circ,a^\circ)-\sum_{\tau\le t}r_\tau$
-- statement:
--   For a sequence of rewards $r_1,r_2,\dots$ the **surrogate regret** and the **virtual regret** against a pair $(b^\circ,a^\circ)$ at time $t$ are
--   $$
--   R^J_t=t\cdot J^*-\sum_{\tau=1}^t r_\tau,\qquad R^\circ_t=t\cdot J(b^\circ,a^\circ)-\sum_{\tau=1}^t r_\tau .
--   $$
--   $R^J_t$ compares the revenue of the learner with $t$ rounds of the surrogate optimum $J^*$; $R^\circ_t$ compares it with the best pair on a grid.
--
--   **Formalization Note** The paper writes Eq. (5) at the horizon $T$; Proposition 6.17 and Theorem 6.18 use the same expression at every $t\le T$.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Eq. (5), p. 17, and Definition 4.5, p. 20

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_J

namespace InvMarketMaking.LOB

open MeasureTheory

/-- The surrogate cumulative regret at time `t` of a reward sequence `r`:
`R^J_t = t · J* − Σ_{τ=1}^t r_τ` (Maran, Restelli, Stradi, arXiv:2610.24562v1, Eq. (5), p. 17).

**Formalization Note** Eq. (5) writes `R^J_T`; Proposition 6.17 and Theorem 6.18 (p. 47) use the
same quantity at every `t ≤ T`, with `t · J*` (the `2(t/N)` term of Proposition 6.17 fixes this
normalization). -/
noncomputable def surrogateRegret (V : Measure (ℝ × ℝ)) (r : ℕ → ℝ) (t : ℕ) : ℝ :=
  t * Jstar V - ∑ τ ∈ Finset.Icc 1 t, r τ

/-- The virtual regret at time `t` against the pair `(b°, a°)`:
`R°_t = t · J(b°, a°) − Σ_{τ=1}^t r_τ` (arXiv:2610.24562v1, Definition 4.5, p. 20, at time `t`). -/
noncomputable def virtualRegret (V : Measure (ℝ × ℝ)) (bo ao : ℝ) (r : ℕ → ℝ) (t : ℕ) : ℝ :=
  t * J V bo ao - ∑ τ ∈ Finset.Icc 1 t, r τ

end InvMarketMaking.LOB


