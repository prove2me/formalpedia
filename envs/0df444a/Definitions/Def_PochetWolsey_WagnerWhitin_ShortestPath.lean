-- Prove2me | Definitions.Def_PochetWolsey_WagnerWhitin_ShortestPath
-- name    : PochetWolsey_WagnerWhitin_ShortestPath
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:25.939295+00:00
-- url     : https://prove2.me/theorems/9575af3f-004f-40bb-a68a-0157bcf96f47
-- title:
--   Regeneration-interval shortest-path formulation
-- statement:
--   For $n$ periods, introduce one nonnegative flow $\varphi_{ut}$ for every interval $1\le u\le t\le n$. Regard this as an arc from node $u$ to node $t+1$. The set $Q^{SP-U}$ consists of real production $x$, setup variables $0\le y_t\le1$, and these flows, subject to one unit of net outflow at node $1$, one unit of net inflow at node $n+1$, and flow conservation at intermediate nodes. The remaining constraints are
--   $$\sum_{\tau=t:d_{t\tau}>0}^n\varphi_{t\tau}\le y_t,\qquad x_t=\sum_{\tau=t}^n d_{t\tau}\varphi_{t\tau}.$$
--   Its $(x,y)$ projection is defined by existentially eliminating $\varphi$.
--
--   This is the formulation used in Theorems 7.8 and 7.9. Zero-demand intervals do not require setups, and idle setups remain allowed.
--
--   **Formalization Note** Only triangular interval arcs are present; there are no unused flow coordinates. Nodes use `Fin (n+1)` and periods use `Fin n`. At $n=0$ the coinciding source and sink contributions cancel, but both theorems require $n>0$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, pp. 222–223 (PDF 236–237), Eqs. (7.22)–(7.27)

import Mathlib
import Definitions.Def_PochetWolsey_WagnerWhitin_LotSizing

open scoped BigOperators

namespace PochetWolsey.WagnerWhitin

/-- An arc (u,t) represents printed regeneration interval [u+1,t+1]. -/
abbrev IntervalArc (n : ℕ) := {a : Fin n × Fin n // a.1 ≤ a.2}

def spFeasible {n : ℕ} (d : Fin n → ℝ) :
    Set (((Fin n → ℝ) × (Fin n → ℝ)) × (IntervalArc n → ℝ)) := by
  classical
  exact {z | (∀ t, 0 ≤ z.1.2 t ∧ z.1.2 t ≤ 1) ∧
    (∀ a, 0 ≤ z.2 a) ∧
    (∀ v : Fin (n + 1),
      (∑ a : IntervalArc n, if a.1.1.castSucc = v then z.2 a else 0) -
      (∑ a : IntervalArc n, if a.1.2.succ = v then z.2 a else 0) =
      (if v = 0 then 1 else 0) - (if v = Fin.last n then 1 else 0)) ∧
    (∀ t, (∑ a : IntervalArc n,
      if a.1.1 = t ∧ 0 < demandSum d a.1.1 a.1.2 then z.2 a else 0) ≤ z.1.2 t) ∧
    (∀ t, z.1.1 t = ∑ a : IntervalArc n,
      if a.1.1 = t then demandSum d a.1.1 a.1.2 * z.2 a else 0)}

def spProject {n : ℕ} (d : Fin n → ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | ∃ φ : IntervalArc n → ℝ, (z, φ) ∈ spFeasible d}

end PochetWolsey.WagnerWhitin


