-- Prove2me | Definitions.Def_OnlineCAP_FracOnlineAlg
-- name    : OnlineCAP_FracOnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:32.052649+00:00
-- url     : https://prove2.me/theorems/87dfe68e-6035-42cd-8f0b-7758ffa782f1
-- title:
--   Online fractional algorithm
-- statement:
--   An **online fractional algorithm** maintains, after the requests $s=(r_1,\dots,r_t)$ have been revealed, a vector $x^t=x(s)\in\mathbb R^U$ with
--
--   $$x^t_e\ge 0\qquad\text{and}\qquad x^t_e\ge x^{t-1}_e\qquad\text{for every } e .$$
--
--   It is deterministic and online: $x(s)$ depends only on the revealed prefix. Feasibility (every revealed request is fractionally covered) and the competitive bound are imposed by `IsFracCompetitive`.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2.2, p.10

import Mathlib

namespace OnlineCAP

/-- **Online fractional algorithm.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2.2, "Fractional Hitting Set and LP Formulation",
p.10 (PDF p.10): "In the fractional relaxation of the problem, we must maintain a monotone
fractional solution xt ∈ R^U_{≥0} over time."

`x s e` is the fractional value `x^t_e` of the element `e` after the requests `s` (of length `t`)
have been revealed. It is nonnegative and nondecreasing in time (`xt_e ≥ xt−1_e`).

**Formalization Note.** Deterministic, and online because `x s` depends only on the revealed
prefix. Feasibility and competitiveness are imposed by `IsFracCompetitive`. -/
structure FracOnlineAlg (U Req : Type) where
  /-- the fractional solution after the revealed prefix -/
  x : List Req → U → ℝ
  /-- `x^t_e ≥ 0` -/
  nonneg : ∀ s e, 0 ≤ x s e
  /-- `x^t_e ≥ x^{t−1}_e` -/
  mono : ∀ s r e, x s e ≤ x (s ++ [r]) e

end OnlineCAP


