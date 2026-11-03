-- Prove2me | Definitions.Def_WeightedCongestionBR_costPoly
-- name    : WeightedCongestionBR_costPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:57.969093+00:00
-- url     : https://prove2.me/theorems/6da845c7-daad-4659-8f68-d98e1bb27500
-- title:
--   Cost polynomial of a resource
-- statement:
--   For a resource $e$ with cost function $c_e(x)=\sum_{\nu=0}^d a_{e,\nu}x^\nu$, the polynomial with coefficients $a_{e,\nu}$. The potential $\phi_e$ of (5) is built from these coefficients.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. The cost is a function of the load $x\ge0$. If it agrees with a real polynomial on $[0,\infty)$, that polynomial is unique, and it is returned; this holds for every polynomial game. Otherwise the value is the zero polynomial, which no statement uses.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §4.1, p.11

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

open Classical in
/-- The coefficients `a_{e,ν}` of the cost function `c_e(x) = ∑_ν a_{e,ν} x^ν` of resource `e`
(Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §4.1, p.11), as a real polynomial.

**Formalization Note** `Game.cost` is a function on loads `x ≥ 0`. When it agrees with a real
polynomial on `[0, ∞)`, that polynomial is unique (two polynomials agreeing on infinitely many
points are equal), and `costPoly` returns it; this is the case for every game satisfying
`CongestionApproxPNE.IsPolyGame d`. Otherwise it returns `0`, a junk value no statement uses. -/
noncomputable def costPoly {n r : ℕ} (G : Game n r) (e : Fin r) : Polynomial ℝ :=
  if h : ∃ P : Polynomial ℝ, ∀ x : ℝ≥0, G.cost e x = P.eval (x : ℝ) then Classical.choose h else 0

end WeightedCongestionBR


