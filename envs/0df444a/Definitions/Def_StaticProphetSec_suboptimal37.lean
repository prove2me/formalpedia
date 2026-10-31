-- Prove2me | Definitions.Def_StaticProphetSec_suboptimal37
-- name    : StaticProphetSec_suboptimal37
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:22.010597+00:00
-- url     : https://prove2.me/theorems/9ed9f7b5-04d9-464b-9084-b337a2bd1b85
-- title:
--   Problem (37): objective, feasibility and suboptimality
-- statement:
--   Problem (37) is
--
--   $$\min\ B_0+B_1(p_1+p_2)+B_2p_1p_2\quad\text{s.t.}\quad A_0+A_1(p_1+p_2)+A_2p_1p_2=\phi,\quad(p_1,p_2)\in[0,1]^2.$$
--
--   A point $(p_1,p_2)$ is **suboptimal** when some feasible point has a strictly smaller objective value.
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, (37), p.34; Lemma 12, p.34

import Mathlib

namespace StaticProphetSec

/-- The objective `B0 + B1 (p1 + p2) + B2 p1 p2` of problem (37) (Arnosti & Ma,
arXiv:2108.12893v2, (37), p.34). -/
def objective37 (B0 B1 B2 p1 p2 : ℝ) : ℝ :=
  B0 + B1 * (p1 + p2) + B2 * (p1 * p2)

/-- Feasibility in problem (37): `A0 + A1 (p1 + p2) + A2 p1 p2 = φ` and `(p1, p2) ∈ [0, 1]²`
(Arnosti & Ma, arXiv:2108.12893v2, (37), p.34). -/
def feasible37 (A0 A1 A2 φ p1 p2 : ℝ) : Prop :=
  A0 + A1 * (p1 + p2) + A2 * (p1 * p2) = φ ∧ 0 ≤ p1 ∧ p1 ≤ 1 ∧ 0 ≤ p2 ∧ p2 ≤ 1

/-- A point `(p1, p2)` is suboptimal for problem (37) when some feasible point has a strictly
smaller objective value (Arnosti & Ma, arXiv:2108.12893v2, Lemma 12, p.34). -/
def suboptimal37 (A0 A1 A2 B0 B1 B2 φ p1 p2 : ℝ) : Prop :=
  ∃ p1' p2' : ℝ, feasible37 A0 A1 A2 φ p1' p2' ∧
    objective37 B0 B1 B2 p1' p2' < objective37 B0 B1 B2 p1 p2

end StaticProphetSec


