-- Prove2me | Definitions.Def_PhiDivRobust_Barrier_logBarrier
-- name    : PhiDivRobust_Barrier_logBarrier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:54:02.58231+00:00
-- url     : https://prove2.me/theorems/5802f71c-346a-44ce-9ad8-847cf2387e89
-- title:
--   The logarithmic barrier φ_B(s, y, z) = −ln(z − y f(s/y)) − ln s − ln y and its domain, Eqs. (34)–(35)
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ and let $g(s,y)=y f(s/y)$ be its perspective. The constraint set (34) of the paper is
--
--   $$\{(s,y,z):\ y f(s/y)\le z,\ s\ge 0,\ y\ge 0\}.$$
--
--   Its **logarithmic barrier** (35) is
--
--   $$\varphi_B(s,y,z)\;=\;-\ln\bigl(z-y f(s/y)\bigr)-\ln s-\ln y,$$
--
--   which is finite exactly on the **barrier domain**
--
--   $$F_f\;=\;\{(s,y,z)\in\mathbb R^3:\ s>0,\ y>0,\ y f(s/y)<z\},$$
--
--   the interior of (34) when $f$ is continuous on $(0,\infty)$. Two objects are defined: the set $F_f$ and the function $\varphi_B$.
--
--   The barrier is the function an interior-point method minimises, penalised, to keep iterates inside (34); its self-concordance on $F_f$ is the subject of the mission.
--
--   **Formalization Note** Points are triples $(s,y,z)\in\mathbb R\times\mathbb R\times\mathbb R$ in this order. `Real.log` returns $0$ at non-positive arguments, so $\varphi_B$ has junk values outside $F_f$; since $F_f$ is open, the differentials of $\varphi_B$ at points of $F_f$ never see them.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 350, Theorem 2, Eqs. (34) and (35)

import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective

namespace PhiDivRobust.Barrier

/-- The interior of the set (34) `{y f(s/y) ≤ z, s ≥ 0, y ≥ 0}` on which the barrier (35) is finite:
the points `(s, y, z)` with `s > 0`, `y > 0` and `y f(s/y) < z`. -/
def barrierDomain (f : ℝ → ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2.1 ∧ perspective f (p.1, p.2.1) < p.2.2}

/-- The logarithmic barrier (35): `φ_B(s, y, z) = -ln(z - y f(s/y)) - ln s - ln y`. -/
noncomputable def logBarrier (f : ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  -Real.log (p.2.2 - perspective f (p.1, p.2.1)) - Real.log p.1 - Real.log p.2.1

end PhiDivRobust.Barrier


