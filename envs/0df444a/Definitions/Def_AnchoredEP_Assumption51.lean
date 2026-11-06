-- Prove2me | Definitions.Def_AnchoredEP_Assumption51
-- name    : AnchoredEP_Assumption51
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:56.266426+00:00
-- url     : https://prove2.me/theorems/84ddb4f7-de7d-4573-a61a-afc2c58b912c
-- title:
--   Assumption 5.1: $D^{p-1}F$ is $L_p$-Lipschitz
-- statement:
--   Let $p\ge 1$ and $L_p\in\mathbb R$. An operator $F:\mathbb R^d\to\mathbb R^d$ satisfies **Assumption 5.1** if it is $p-1$ times continuously differentiable and its $(p-1)$th derivative is $L_p$-Lipschitz:
--   $$
--   \|D^{p-1}F(z)-D^{p-1}F(z')\|_{\mathrm{op}}\le L_p\|z-z'\|\qquad\text{for all } z,z'\in\mathbb R^d,
--   $$
--   where $\|\cdot\|_{\mathrm{op}}$ is the induced norm of a multilinear map.
--
--   This is the smoothness assumption of the $p$th-order method.
--
--   **Formalization Note** The derivative is Mathlib's `iteratedFDeriv`, whose norm is the induced multilinear operator norm. Since `iteratedFDeriv` is $0$ where $F$ is not differentiable, the existence of $D^{p-1}F$ presupposed by the source is stated as `ContDiff ℝ (p - 1) F`; a Lipschitz $(p-1)$th derivative is continuous, so this adds no condition.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Assumption 5.1, p.11

import Mathlib

namespace AnchoredEP

/-- **Assumption 5.1 (Lipschitz `(p−1)`th derivative).** Jiang–Yoon, arXiv:2609.30212,
Assumption 5.1, p.11: "The `(p − 1)`th derivative of `F` is `L_p`-Lipschitz continuous, i.e., we
have `‖D^{p−1}F(z) − D^{p−1}F(z′)‖_op ≤ L_p‖z − z′‖` for all `z, z′ ∈ ℝ^d`, where `‖·‖_op` denotes
the induced multilinear operator norm."

**Formalization Note.** `D^{p−1}F` is `iteratedFDeriv ℝ (p - 1) F`, a continuous multilinear map
whose Mathlib norm is the induced multilinear operator norm. Since `iteratedFDeriv` is `0` at
points where `F` is not differentiable, the existence of `D^{p−1}F` that the assumption
presupposes is made explicit as `ContDiff ℝ (p - 1) F`; a Lipschitz `(p−1)`th derivative is in
particular continuous, so this adds no condition. -/
def Assumption51 {d : ℕ} (p : ℕ) (L : ℝ)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ContDiff ℝ (p - 1 : ℕ) F ∧
    ∀ z z' : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ (p - 1) F z - iteratedFDeriv ℝ (p - 1) F z'‖ ≤ L * ‖z - z'‖

end AnchoredEP


