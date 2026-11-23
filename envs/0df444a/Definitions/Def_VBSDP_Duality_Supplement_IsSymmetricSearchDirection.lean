-- Prove2me | Definitions.Def_VBSDP_Duality_Supplement_IsSymmetricSearchDirection
-- name    : VBSDP_Duality_Supplement_IsSymmetricSearchDirection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:02:23.327083+00:00
-- url     : https://prove2.me/theorems/b897722a-53ca-4126-8648-735477247302
-- title:
--   §5.4, p. 80 — the symmetric (Nesterov–Todd) search directions δxˢʸᵐ, δZˢʸᵐ of potential reduction method 3
-- statement:
--   Let $F_0,F_1,\dots,F_m$ be symmetric $n\times n$ real matrices, $c\in\mathbb R^m$, and let $F(x)=F_0+\sum_{i=1}^m x_iF_i$. Fix a parameter $\nu$ and a current pair $(x,Z)$, write $F=F(x)$ and
--
--   $$\rho=\frac{n+\nu\sqrt n}{c^Tx+\operatorname{Tr}F_0Z}.$$
--
--   Let $F\succ0$ and $Z\succ0$. A pair $(\delta x^{\rm sym},\delta Z^{\rm sym})$ with $\delta Z^{\rm sym}$ symmetric is a **symmetric search direction** at $(x,Z)$ when
--
--   $$RR^T\,\delta Z^{\rm sym}\,RR^T+\sum_{i=1}^m\delta x^{\rm sym}_iF_i=-\rho F+Z^{-1},\qquad\operatorname{Tr}F_j\,\delta Z^{\rm sym}=0\quad(j=1,\dots,m),$$
--
--   where $R$ satisfies $R^TF^{-1}R=\Lambda^{-1/2}$ and $R^TZR=\Lambda^{1/2}$; it can be constructed as $R=F^{1/2}U\Lambda^{-1/4}$ from the eigenvalue decomposition $F^{1/2}ZF^{1/2}=U\Lambda U^T$.
--
--   **Formalization Note** Only the product $W=RR^T$ enters the system. The two relations for $R$ give $F=R\Lambda^{1/2}R^T=RR^T\,Z\,RR^T$, so $W$ is a positive definite solution of $WZW=F$, and this equation has exactly one positive definite solution, $W=F^{1/2}(F^{1/2}ZF^{1/2})^{-1/2}F^{1/2}$. The predicate therefore asks for a positive definite $W$ with $WZW=F$ in place of $RR^T$; it is the same system. Symmetry of $\delta Z^{\rm sym}$ is part of the predicate. $Z^{-1}$ is Mathlib's matrix inverse, the true inverse at positive definite $Z$. Indices are zero-based; $\sqrt n$ is `Real.sqrt n`.
-- source:
--   Vandenberghe and Boyd, Semidefinite Programming, SIAM Rev. 38 (1996), p. 80 (PDF p. 32), §5.4; ρ defined on p. 78 (PDF p. 30); https://doi.org/10.1137/1038003

import Mathlib
import Definitions.Def_VBSDP_Duality_lmi

namespace VBSDP.Duality.Supplement

/-- The symmetric (Nesterov–Todd) search directions of §5.4, p. 80: with `F = F(x)` and
`ρ = (n + ν√n) / (cᵀx + Tr F₀Z)`, the pair `(δx, δZ)` satisfies
`R Rᵀ δZ R Rᵀ + Σᵢ δxᵢ Fᵢ = −ρ F + Z⁻¹` and `Tr Fⱼ δZ = 0` for every `j`, with `δZ`
symmetric. The scaling `W = R Rᵀ` is given by its characterization: `W` is positive
definite and `W Z W = F` (which `R Rᵀ` satisfies for the page's `R`, and which has exactly
one positive definite solution). -/
noncomputable def IsSymmetricSearchDirection {m n : ℕ} (ν : ℝ) (c : Fin m → ℝ)
    (F₀ : Matrix (Fin n) (Fin n) ℝ) (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (δx : Fin m → ℝ) (δZ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  δZ.IsHermitian ∧
  (∃ W : Matrix (Fin n) (Fin n) ℝ, W.PosDef ∧ W * Z * W = VBSDP.Duality.lmi F₀ F x ∧
    W * δZ * W + ∑ i, δx i • F i =
      -(((n : ℝ) + ν * Real.sqrt n) / (c ⬝ᵥ x + (F₀ * Z).trace)) •
        VBSDP.Duality.lmi F₀ F x + Z⁻¹) ∧
  ∀ j, (F j * δZ).trace = 0

end VBSDP.Duality.Supplement


