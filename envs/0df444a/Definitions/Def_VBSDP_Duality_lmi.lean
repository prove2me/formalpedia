-- Prove2me | Definitions.Def_VBSDP_Duality_lmi
-- name    : VBSDP_Duality_lmi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:29.55007+00:00
-- url     : https://prove2.me/theorems/c4de8b44-ff01-42d3-9b96-fb25c1f9826a
-- title:
--   (1), p. 49 — the affine matrix function $F(x)=F_0+\sum_i x_iF_i$ of the linear matrix inequality
-- statement:
--   Let $m,n$ be natural numbers. Given a matrix $F_0\in\mathbb R^{n\times n}$, matrices $F_1,\ldots,F_m\in\mathbb R^{n\times n}$ and a vector $x\in\mathbb R^m$, the affine matrix function of Vandenberghe and Boyd is
--
--   $$F(x)=F_0+\sum_{i=1}^{m}x_iF_i.$$
--
--   The constraint $F(x)\ge 0$, meaning that $F(x)$ is positive semidefinite, is a **linear matrix inequality**, and minimizing a linear function $c^Tx$ subject to it is the semidefinite program (1). This one definition is shared by both missions of the series: the duality theory of §3 (Theorem 3.1) and the potential-reduction analysis of §§4–5 (Theorem 5.1).
--
--   **Formalization Note** The paper's $F_1,\ldots,F_m$ are indexed in Lean by `Fin m`, so $F_i$ is `F (i-1)`, and $F_0$ is the separate argument `F₀`. The definition itself does not require the data to be symmetric; the paper's standing assumption that $F_0,\ldots,F_m$ are symmetric is stated as a hypothesis by the theorems whose content depends on it. Because Mathlib's positive semidefiniteness over $\mathbb R$ includes symmetry, the constraint $F(x)\ge 0$ always forces $F(x)$ to be symmetric.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 49 (PDF p. 1), (1), definition of F(x), https://doi.org/10.1137/1038003

import Mathlib

namespace VBSDP.Duality

def lmi {m n : ℕ} (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  F₀ + ∑ i, x i • F i

end VBSDP.Duality


