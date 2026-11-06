-- Prove2me | Definitions.Def_AnchoredEP_regTaylor
-- name    : AnchoredEP_regTaylor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:42.773802+00:00
-- url     : https://prove2.me/theorems/7df9a0b7-de90-4bdd-b7c6-d5b4ad196a0c
-- title:
--   Regularized Taylor model $\mathbb T^{(p-1)}_\lambda(z;y)$
-- statement:
--   For $\lambda\in\mathbb R$, the **regularized Taylor model** of $F$ with center $y$ is
--   $$
--   \mathbb T^{(p-1)}_\lambda(z;y)=\mathbb T^{(p-1)}(z;y)+\frac{\lambda}{(p-1)!}\|z-y\|^{p-1}(z-y).
--   $$
--   With $\lambda=L_p$ and center $y=z_{k+\frac12}$ this is the surrogate operator $P_k$ of Eq. (26). The regularization makes the model maximal monotone when $\lambda\ge L_p$ (Lemma G.1), so that each subproblem has a unique solution.
--
--   **Formalization Note** `regTaylor F p lam y z` is $\mathbb T^{(p-1)}_{\mathrm{lam}}(z;y)$ (center first).
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Lemma G.1, p.36, and Eq. (26), p.11

import Mathlib
import Definitions.Def_AnchoredEP_taylorOp

namespace AnchoredEP

/-- **The regularized Taylor model `𝕋_λ^{(p−1)}`.** Jiang–Yoon, arXiv:2609.30212, Lemma G.1,
p.36: "define `𝕋_λ^{(p−1)}(z′; z) := 𝕋^{(p−1)}(z′; z) + λ/(p − 1)! ‖z′ − z‖^{p−1}(z′ − z)`"; with
`λ = L_p` it is the surrogate operator `P_k` of Eq. (26), p.11.

`regTaylor F p lam y z` is `𝕋_lam^{(p−1)}(z; y)`: center `y`, evaluated at `z`.

**Formalization Note.** `(p − 1)!` is `Nat.factorial (p - 1)` cast to `ℝ`; the power
`‖z − y‖^{p−1}` is a natural-number power. -/
noncomputable def regTaylor {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (lam : ℝ) (y z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  taylorOp F p y z + (lam / ((p - 1).factorial : ℝ) * ‖z - y‖ ^ (p - 1)) • (z - y)

end AnchoredEP


