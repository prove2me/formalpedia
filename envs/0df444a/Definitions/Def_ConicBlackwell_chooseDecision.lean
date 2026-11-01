-- Prove2me | Definitions.Def_ConicBlackwell_chooseDecision
-- name    : ConicBlackwell_chooseDecision
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:16.675413+00:00
-- url     : https://prove2.me/theorems/9216916f-b9b6-489a-b1e3-e63af09920f3
-- title:
--   CHOOSEDECISION$_{\mathrm{CBA}^+}(u)=(\kappa/\tilde u)\hat u$
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be the decision set, $\kappa=\max_{x\in\mathcal X}\|x\|_2$, and $x_0\in\mathcal X$ a fixed point. For an aggregate payoff vector $u=(\tilde u,\hat u)\in\mathbb R\times\mathbb R^n$,
--
--   $$
--   \mathrm{CHOOSEDECISION}_{\mathrm{CBA}^+}(u)=\begin{cases}(\kappa/\tilde u)\,\hat u, & \tilde u\neq0,\\ x_0, & \tilde u=0.\end{cases}
--   $$
--
--   When $u$ lies in the cone $\mathcal C=\operatorname{cone}(\{\kappa\}\times\mathcal X)$, say $u=\alpha(\kappa,x)$ with $\alpha>0$, this returns $x\in\mathcal X$.
--
--   **Formalization Note** $\kappa$ is `kappa X`, the supremum of the norms over $\mathcal X$ (the maximum on a nonempty compact set); the arbitrary point $x_0$ is a parameter.
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), §3.1, p.5

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_ConicBlackwell_tail
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **CHOOSEDECISION_{CBA+}.**  For `u = (ũ, û) ∈ ℝ × ℝⁿ`,
`CHOOSEDECISION_{CBA+}(u) = (κ/ũ) û`, and `= x₀` (a fixed point of `X`) when `ũ = 0`.
Grand-Clément & Kroer, *Solving Optimization Problems with Blackwell Approachability*, arXiv:2202.12277v1, §3.1, p.5.

Formalization Note: `κ = kappa X` (the supremum of `‖x‖₂` over `X`, which is the paper's max on a
nonempty compact `X`); `ũ = u 0`, `û = tail u`.  The arbitrary point `x₀` is a parameter. -/
noncomputable def chooseDecision {n : ℕ} (X : Set (E n)) (x₀ : E n) (u : E (n + 1)) : E n :=
  if u 0 = 0 then x₀ else (kappa X / u 0) • tail u

end ConicBlackwell


