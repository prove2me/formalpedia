-- Prove2me | Definitions.Def_LiquidWelfareFPA_lambertW
-- name    : LiquidWelfareFPA_lambertW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:52.592108+00:00
-- url     : https://prove2.me/theorems/94e5be3d-23ee-47e9-b2a6-d30244dfb773
-- title:
--   Principal branch of the Lambert $W$ function
-- statement:
--   For $x\ge-1/e$, $W(x)$ is the unique $y\ge-1$ with
--
--   $$y\,e^{y}=x .$$
--
--   The map $y\mapsto ye^y$ is strictly increasing on $[-1,\infty)$ with range $[-1/e,\infty)$, so $W$ is well defined there, increasing, $W(xe^x)=x$ for $x\ge-1$, and $W(x)\in(-1,0)$ for $x\in(-1/e,0)$.
--
--   **Formalization Note** Mathlib has no Lambert $W$. For $x<-1/e$ the definition returns the placeholder value $0$; no statement of the mission evaluates it there.
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, footnote 3, p.10 and Appendix A, p.21

import Mathlib

namespace LiquidWelfareFPA

open Classical in
/-- **The principal branch of the Lambert W function.**
Fikioris & Tardos, arXiv:2210.07502v4, footnote 3, p.10: "The Lambert W function W(x) is the
solution to the equation ye^y = x"; Appendix A, p.21: "W(x) is an increasing function in x and …
W(x) ∈ (−1, 0) when x ∈ (−1/e, 0)", "W(xe^x) = x, by definition for x ≥ −1".

For `x ≥ −1/e`, `lambertW x` is the unique `y ≥ −1` with `y · e^y = x` (the map `y ↦ y e^y` is
strictly increasing on `[−1, ∞)` with range `[−1/e, ∞)`, so the chosen `y` is unique).

**Formalization Note** Mathlib has no Lambert W. For `x < −1/e` there is no such `y` and the
definition returns the junk value `0`; no statement evaluates it there. -/
noncomputable def lambertW (x : ℝ) : ℝ :=
  if h : ∃ y : ℝ, -1 ≤ y ∧ y * Real.exp y = x then Classical.choose h else 0

end LiquidWelfareFPA


