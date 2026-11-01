-- Prove2me | Definitions.Def_LocalDOvS_SUS_typeIUpdate
-- name    : LocalDOvS_SUS_typeIUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:49.059607+00:00
-- url     : https://prove2.me/theorems/8887eff8-86cf-412d-9ae4-637dfad48614
-- title:
--   Type-I Operation (with corrected bounds)
-- statement:
--   The **Type-I Operation** on a pair $x,y$ of active points (after the test found $\hat F(x)+h\le\hat F(y)-h$):
--
--   1. if $x<y$, remove every $z\in S$ with $z\ge y$, and set $x_U:=y$;
--   2. otherwise, remove every $z\in S$ with $z\le y$, and set $x_L:=y$.
--
--   The iteration index increases by one; the step size is unchanged.
--
--   **Formalization Note** The pair is given by its positions $j,l$ in $S$. The paper sets $x_{U,k+1}:=y-d_k$ and $x_{L,k+1}:=y+d_k$ (p.ec14); these exclude the integers strictly between grid points, and with them the second induction event of the proof of Theorem 2 can fail ($f=(9,6,3,2.5,3.2,6,9)$, $S=\{1,3,5,7\}$, $d=2$, $x=3$, $y=5$ gives $x_U=3$ and excludes the minimizer $4$). The bounds are corrected to $y$.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, lines 11–16, p.15; p.ec14 (bounds corrected)

import Mathlib
import Definitions.Def_LocalDOvS_SUS_SUSState

namespace LocalDOvS.SUS

/-- The Type-I Operation for the pair `x = x0 + j·s`, `y = x0 + l·s` of the active set
(Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2, lines 11–16, p.15, and the bounds of
p.ec14, corrected):

* if `x < y` (`j < l`), remove every `z ∈ S` with `z ≥ y`, and set `x_U := y`;
* otherwise, remove every `z ∈ S` with `z ≤ y`, and set `x_L := y`.

**Formalization Note (correction of p.ec14).** The paper sets `x_{U,k+1} := y − d_k` and
`x_{L,k+1} := y + d_k`, which exclude the integers strictly between grid points; with that
definition the second induction event of the proof of Theorem 2 can fail (`f = (9, 6, 3, 2.5,
3.2, 6, 9)`, `S = {1, 3, 5, 7}`, `d = 2`, `x = 3`, `y = 5`: then `x_U = 3` excludes the
minimizer `4`). The corrected bounds are `y`. The algorithm itself does not use `x_L`, `x_U`. -/
def typeIUpdate (st : SUSState) (j l : ℕ) : SUSState :=
  if j < l then
    { st with k := st.k + 1, M := l, xU := st.x0 + l * st.s }
  else
    { st with k := st.k + 1, x0 := st.x0 + (l + 1) * st.s, M := st.M - (l + 1),
              xL := st.x0 + l * st.s }

end LocalDOvS.SUS


