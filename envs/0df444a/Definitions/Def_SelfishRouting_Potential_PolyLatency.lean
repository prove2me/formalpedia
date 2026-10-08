-- Prove2me | Definitions.Def_SelfishRouting_Potential_PolyLatency
-- name    : SelfishRouting_Potential_PolyLatency
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:16.000962+00:00
-- url     : https://prove2.me/theorems/d867391e-3b50-402e-9913-ec3d2bd75469
-- title:
--   Polynomial latency functions $\ell_e(x)=\sum_{i=0}^{p}a_{e,i}x^i$
-- statement:
--   Fix a natural number $p$ and, for every edge $e$ and every $i$, a real coefficient $a_{e,i}$. The **polynomial latency of degree at most $p$** on edge $e$ is
--   $$\ell_e(x)=\sum_{i=0}^{p}a_{e,i}\,x^i .$$
--
--   This is the class of latency functions in Corollary 2.8 of Roughgarden and Tardos (p. 11). Every edge uses the same bound $p$ on the degree; the leading coefficient $a_{e,p}$ may vanish, so edges of lower degree are included.
--
--   **Formalization Note** The coefficients form a function $a$ of the edge and of $i\in\mathbb N$; only the values with $i\le p$ enter the sum.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 11, Corollary 2.8

import Mathlib

namespace SelfishRouting.Potential

/-- Polynomial latency functions of degree at most `p` (Corollary 2.8, p. 11):
`ℓ_e(t) = ∑_{i=0}^{p} a_{e,i} tⁱ`, with coefficient `a j i` of `tⁱ` on edge `j`. -/
noncomputable def polyLatency {J : ℕ} (p : ℕ) (a : Fin J → ℕ → ℝ) (j : Fin J) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1), a j i * t ^ i

end SelfishRouting.Potential


