-- Prove2me | Definitions.Def_FracColorLocal_KrFree_Shearer
-- name    : FracColorLocal_KrFree_Shearer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:11:37.738822+00:00
-- url     : https://prove2.me/theorems/8cb351aa-0a44-4cd9-9cb8-e60f9d011180
-- title:
--   Shearer's function f, defined piecewise at 0 and 1
-- statement:
--   **Shearer's function** $f:[0,\infty)\to\mathbb R$ is
--
--   $$f(d)=\frac{d\log d-d+1}{(d-1)^2}\quad(d>0,\ d\neq 1),\qquad f(0)=1,\qquad f(1)=\tfrac12,$$
--
--   with $\log$ the natural logarithm. It is continuous, positive, strictly decreasing and strictly convex on $[0,\infty)$, with $f(d)\sim\log d/d$ as $d\to\infty$; Shearer's bound $\alpha(G)\ge n f(d)$ for triangle-free graphs of average degree $d$ is stated with it.
--
--   **Formalization Note** `shearerF : ℝ → ℝ` is defined by the three cases above; at negative arguments it returns an unused value (the formula with `Real.log` of a negative number). Only arguments in $[0,\infty)$ occur in this mission (weighted degrees are nonnegative), and its derivative $f'$ is `deriv shearerF`, evaluated only at $d>0$.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 1 (PDF 2), (1.1)

import Mathlib

namespace FracColorLocal.KrFree

/-- Shearer's function `f` of (1.1): `f(d) = (d log d - d + 1)/(d - 1)^2` for `d > 0`, `d ≠ 1`,
with `f(0) = 1` and `f(1) = 1/2`. Only its values on `[0, ∞)` are used. -/
noncomputable def shearerF (d : ℝ) : ℝ :=
  if d = 0 then 1
  else if d = 1 then 1 / 2
  else (d * Real.log d - d + 1) / (d - 1) ^ 2

end FracColorLocal.KrFree


