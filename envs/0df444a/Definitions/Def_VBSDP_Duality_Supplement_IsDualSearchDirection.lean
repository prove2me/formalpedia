-- Prove2me | Definitions.Def_VBSDP_Duality_Supplement_IsDualSearchDirection
-- name    : VBSDP_Duality_Supplement_IsDualSearchDirection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:01:03.722817+00:00
-- url     : https://prove2.me/theorems/676a1c3b-774e-4b94-b7b5-e18f496ae905
-- title:
--   (66), p. 79 — the dual search directions δxᵈ, δZᵈ of potential reduction method 2*
-- statement:
--   Let $F_0,F_1,\dots,F_m$ be symmetric $n\times n$ real matrices, $c\in\mathbb R^m$, and let $F(x)=F_0+\sum_{i=1}^m x_iF_i$. Fix a parameter $\nu$ and a current pair $(x,Z)$, write $F=F(x)$ and
--
--   $$\rho=\frac{n+\nu\sqrt n}{c^Tx+\operatorname{Tr}F_0Z}.$$
--
--   A pair $(\delta x^d,\delta Z^d)$ with $\delta x^d\in\mathbb R^m$ and $\delta Z^d$ a symmetric $n\times n$ matrix is a **dual search direction** at $(x,Z)$ when it solves the linear system (66):
--
--   $$Z^{-1}\,\delta Z^d\,Z^{-1}+\sum_{i=1}^m\delta x^d_iF_i=-\rho F+Z^{-1},\qquad \operatorname{Tr}F_j\,\delta Z^d=0\quad(j=1,\dots,m).$$
--
--   These are the search directions of potential reduction method 2*: $\delta Z^d$ minimizes a second-order approximation of the potential in the dual variable over dual feasible directions, and $\delta x^d$ is the accompanying multiplier, used as the primal direction.
--
--   **Formalization Note** The definition is the bare linear system; it contains no decrease condition. Symmetry of $\delta Z^d$ (the constraint $V=V^T$ of (65), and the definition of a dual feasible direction on p. 77) is part of the predicate. $Z^{-1}$ is Mathlib's matrix inverse, which is the true inverse whenever $Z$ is positive definite, as it is at every strictly feasible pair. The indices of $F_1,\dots,F_m$ are zero-based (`Fin m`) and $F_0$ is a separate argument; $\sqrt n$ is `Real.sqrt n` for the matrix size $n$.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 79 (PDF p. 31), (65)–(66); ρ defined on p. 78 (PDF p. 30), after (63); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi

namespace VBSDP.Duality.Supplement

/-- The dual search directions (66), p. 79: at the current pair `(x, Z)`, with
`F = F(x)` and `ρ = (n + ν√n) / (cᵀx + Tr F₀Z)`, the pair `(δx, δZ)` satisfies
`Z⁻¹ δZ Z⁻¹ + Σᵢ δxᵢ Fᵢ = −ρF + Z⁻¹` and `Tr Fⱼ δZ = 0` for every `j`,
with `δZ` symmetric. -/
noncomputable def IsDualSearchDirection {m n : ℕ} (ν : ℝ) (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (δx : Fin m → ℝ) (δZ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  δZ.IsHermitian ∧
  Z⁻¹ * δZ * Z⁻¹ + ∑ i, δx i • F i =
    -(((n : ℝ) + ν * Real.sqrt n) / (c ⬝ᵥ x + (F₀ * Z).trace)) •
      VBSDP.Duality.lmi F₀ F x + Z⁻¹ ∧
  ∀ j, (F j * δZ).trace = 0

end VBSDP.Duality.Supplement


