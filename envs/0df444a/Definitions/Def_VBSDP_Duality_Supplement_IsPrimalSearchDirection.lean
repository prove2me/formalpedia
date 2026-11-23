-- Prove2me | Definitions.Def_VBSDP_Duality_Supplement_IsPrimalSearchDirection
-- name    : VBSDP_Duality_Supplement_IsPrimalSearchDirection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:01:41.167407+00:00
-- url     : https://prove2.me/theorems/94420ab4-032a-44de-a695-aadab91b60b4
-- title:
--   (64), p. 79 — the primal search directions δxᵖ, δZᵖ of potential reduction methods 1 and 2
-- statement:
--   Let $F_0,F_1,\dots,F_m$ be symmetric $n\times n$ real matrices, $c\in\mathbb R^m$, and let $F(x)=F_0+\sum_{i=1}^m x_iF_i$. Fix a parameter $\nu$ and a current pair $(x,Z)$, write $F=F(x)$ and
--
--   $$\rho=\frac{n+\nu\sqrt n}{c^Tx+\operatorname{Tr}F_0Z}.$$
--
--   A pair $(\delta x^p,\delta Z^p)$ with $\delta x^p\in\mathbb R^m$ and $\delta Z^p$ a symmetric $n\times n$ matrix is a **primal search direction** at $(x,Z)$ when it solves the linear system (64):
--
--   $$F\,\delta Z^p\,F+\sum_{i=1}^m\delta x^p_iF_i=-\rho FZF+F,\qquad \operatorname{Tr}F_j\,\delta Z^p=0\quad(j=1,\dots,m).$$
--
--   Here $\delta x^p$ minimizes the local quadratic approximation (63) of the potential in $x$, and $\delta Z^p$ is the accompanying dual feasible direction. Method 1 uses $\delta x^p$ (with $\delta Z^d$ from (66)); method 2 uses the pair $\delta x^p,\delta Z^p$.
--
--   **Formalization Note** The definition is the bare linear system; it contains no decrease condition. Symmetry of $\delta Z^p$ (the constraint $V=V^T$ of (59) and the definition of a dual feasible direction on p. 77) is part of the predicate. The indices of $F_1,\dots,F_m$ are zero-based (`Fin m`) and $F_0$ is a separate argument; $\sqrt n$ is `Real.sqrt n` for the matrix size $n$.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 79 (PDF p. 31), (63)–(64); ρ defined on p. 78 (PDF p. 30); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi

namespace VBSDP.Duality.Supplement

/-- The primal search directions (64), p. 79: at the current pair `(x, Z)`, with
`F = F(x)` and `ρ = (n + ν√n) / (cᵀx + Tr F₀Z)`, the pair `(δx, δZ)` satisfies
`F δZ F + Σᵢ δxᵢ Fᵢ = −ρ F Z F + F` and `Tr Fⱼ δZ = 0` for every `j`,
with `δZ` symmetric. -/
noncomputable def IsPrimalSearchDirection {m n : ℕ} (ν : ℝ) (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (δx : Fin m → ℝ) (δZ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  δZ.IsHermitian ∧
  VBSDP.Duality.lmi F₀ F x * δZ * VBSDP.Duality.lmi F₀ F x + ∑ i, δx i • F i =
    -(((n : ℝ) + ν * Real.sqrt n) / (c ⬝ᵥ x + (F₀ * Z).trace)) •
      (VBSDP.Duality.lmi F₀ F x * Z * VBSDP.Duality.lmi F₀ F x) +
      VBSDP.Duality.lmi F₀ F x ∧
  ∀ j, (F j * δZ).trace = 0

end VBSDP.Duality.Supplement


