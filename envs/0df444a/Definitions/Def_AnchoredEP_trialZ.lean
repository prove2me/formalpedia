-- Prove2me | Definitions.Def_AnchoredEP_trialZ
-- name    : AnchoredEP_trialZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:42.792197+00:00
-- url     : https://prove2.me/theorems/bba5f7dd-5c47-4075-bb40-f391ae9bee8f
-- title:
--   Trial point $z_{k+1}(a)$
-- statement:
--   Given an exact subproblem solver, the trial point of the step $a$ at the state $(z_k,v_k,A_k)$ is the solution $z_{k+1}(a)$ of
--   $$
--   0\in a\,P_{k,a}(z_{k+1}(a))+aH(z_{k+1}(a))+z_{k+1}(a)-\Big(\frac{a}{A_k+a}z_0+\frac{A_k}{A_k+a}z_k\Big),
--   $$
--   where $P_{k,a}=\mathbb T^{(p-1)}_{L_p}(\cdot\,;z_{k+\frac12}(a))$; it is the solver's output for the center $z_{k+\frac12}(a)$ and the anchored point.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, Eq. (87), p.37

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_trialAnchor
import Definitions.Def_AnchoredEP_trialMid

namespace AnchoredEP

/-- **The trial point `z_{k+1}(a)`.** Jiang–Yoon, arXiv:2609.30212, Appendix G.2, Eq. (87), p.37:
`z_{k+1}(a)` is the solution of
`0 ∈ a P_{k,a}(z_{k+1}(a)) + a H(z_{k+1}(a)) + z_{k+1}(a) − (a/(A_k + a) z₀ + A_k/(A_k + a) z_k)`,
with `P_{k,a} = 𝕋_λ^{(p−1)}(·; z_{k+½}(a))`.

`trialZ F sol z0 s a` is the point returned by the subproblem solver `sol`
(see `IsSubSolver`) for step `a`, Taylor center `z_{k+½}(a)` and anchored point
`a/(A_k + a) z₀ + A_k/(A_k + a) z_k`.

**Formalization Note.** The solver specification `IsSubSolver F H p L sol` ties `sol` to the
model `𝕋_L^{(p−1)}`. -/
noncomputable def trialZ {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (a : ℝ) : EuclideanSpace ℝ (Fin d) :=
  sol a (trialMid F z0 s a) (trialAnchor z0 s a)

end AnchoredEP


