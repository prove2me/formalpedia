-- Prove2me | Definitions.Def_CubicHolant_Dichotomy_Tractable
-- name    : CubicHolant_Dichotomy_Tractable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:36:44.119569+00:00
-- url     : https://prove2.me/theorems/a0785500-65f6-4814-846b-9ebc7ea0de7f
-- title:
--   The tractable family $\mathcal T$: rank one, generalized equalities, and scalings, cube-root diagonal twists and reversals of six affine signatures
-- statement:
--   A **symmetric Boolean ternary signature** $f=[f_0,f_1,f_2,f_3]$ is a vector of four complex numbers; it stands for the function $f(i,j,k)=f_{i+j+k}$ on bits $i,j,k\in\{0,1\}$.
--
--   1. $f$ is **rank one** (the paper also says *degenerate*, p. 11) if $f=\lambda[u_0^3,u_0^2u_1,u_0u_1^2,u_1^3]$ for some constants $\lambda,u_0,u_1$. This includes the zero signature.
--   2. $f$ is a **generalized equality** if $f=[x,0,0,y]$, i.e. $f_1=f_2=0$.
--   3. For $\omega$ with $\omega^3=1$ the **diagonal transformation** is $\Gamma_\omega[f_0,f_1,f_2,f_3]=[f_0,\omega f_1,\omega^2f_2,f_3]$, and the **reversal** is $f^{\mathrm{rev}}=[f_3,f_2,f_1,f_0]$.
--   4. The six **affine representatives** are
--   $$[1,0,1,0],\quad[1,0,-1,0],\quad[1,1,-1,-1],\quad[1,-1,-1,1],\quad[1,i,1,i],\quad[1,-i,1,-i].$$
--   5. The **tractable family** $\mathcal T$ consists of the rank-one signatures, the generalized equalities, and all signatures $c\,\Gamma_\omega h$ and $c\,(\Gamma_\omega h)^{\mathrm{rev}}$ with $c\neq0$, $\omega^3=1$ and $h$ one of the six representatives.
--
--   Item 5 is the closure of the six representatives under nonzero scaling, $\Gamma_\omega$ and reversal: $\Gamma_\omega\Gamma_{\omega'}=\Gamma_{\omega\omega'}$ and $(\Gamma_\omega h)^{\mathrm{rev}}=\Gamma_{\omega^{-1}}(h^{\mathrm{rev}})$ (p. 6), so no further composition adds a signature. The family is not normalized: $[0,1,0,1]=[1,0,1,0]^{\mathrm{rev}}$ belongs to it.
--
--   **Formalization Note** A signature is `f : Fin 4 → ℂ` with `f 0 = f₀`, …, `f 3 = f₃`. The constants of a rank-one representation are arbitrary complex numbers. The paper asks for algebraic ones, but every statement applies `InT` to an algebraic `f`, and an algebraic rank-one `f` always has an algebraic representation ($\lambda=f_0$, $u=(1,f_1/f_0)$ when $f_0\neq0$, and $[0,0,0,\lambda]$ otherwise).
-- source:
--   Yin Liu, A Dichotomy for Cubic Bipartite Holant Problems with Complex Algebraic Weights, STOC 2027 submission (manuscript sha256 f70906c3…), p. 4, §1.2; p. 11 (degenerate = rank one)

import Mathlib

set_option autoImplicit false

namespace CubicHolant.Dichotomy

/-! # The tractable family `𝒯`

Yin Liu, *A Dichotomy for Cubic Bipartite Holant Problems with Complex Algebraic Weights*, STOC 2027
submission (manuscript sha256 f70906c3…), §1.2, p. 4; "degenerate means rank one", p. 11.

A symmetric Boolean ternary signature `[f₀, f₁, f₂, f₃]` is a vector `f : Fin 4 → ℂ`. -/

/-- `f` is **rank one** (degenerate): `f = λ[u₀³, u₀²u₁, u₀u₁², u₁³]` for some constants
`λ, u₀, u₁`; this includes the zero signature (p. 4). -/
def IsRankOne (f : Fin 4 → ℂ) : Prop :=
  ∃ l u₀ u₁ : ℂ, f = ![l * u₀ ^ 3, l * (u₀ ^ 2 * u₁), l * (u₀ * u₁ ^ 2), l * u₁ ^ 3]

/-- `f` is a **generalized equality** `[x, 0, 0, y]` (p. 4). -/
def IsGenEq (f : Fin 4 → ℂ) : Prop :=
  f 1 = 0 ∧ f 2 = 0

/-- The diagonal transformation `Γ_ω[f₀, f₁, f₂, f₃] = [f₀, ωf₁, ω²f₂, f₃]` (p. 4; used with
`ω³ = 1`). -/
def gammaT (ω : ℂ) (f : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![f 0, ω * f 1, ω ^ 2 * f 2, f 3]

/-- Reversal `f^rev = [f₃, f₂, f₁, f₀]` (p. 4). -/
def revT (f : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![f 3, f 2, f 1, f 0]

/-- The six affine representatives of p. 4, in the printed order:
`[1, 0, 1, 0]`, `[1, 0, −1, 0]`, `[1, 1, −1, −1]`, `[1, −1, −1, 1]`, `[1, i, 1, i]`,
`[1, −i, 1, −i]`. -/
def affineRep : Fin 6 → Fin 4 → ℂ :=
  ![![1, 0, 1, 0], ![1, 0, -1, 0], ![1, 1, -1, -1], ![1, -1, -1, 1],
    ![1, Complex.I, 1, Complex.I], ![1, -Complex.I, 1, -Complex.I]]

/-- The tractable family `𝒯` (p. 4): the rank-one signatures, the generalized equalities, and all
nonzero scalar multiples of the transformations `Γ_ω` (`ω³ = 1`) and reversals of the six affine
representatives, i.e. `c · Γ_ω h` and `c · (Γ_ω h)^rev` with `c ≠ 0`, `ω³ = 1` and `h` one of the
six (the closure of the six under these operations, since `Γ_ω Γ_ω' = Γ_{ωω'}` and
`(Γ_ω h)^rev = Γ_{ω⁻¹}(h^rev)`, p. 6). -/
def InT (f : Fin 4 → ℂ) : Prop :=
  IsRankOne f ∨ IsGenEq f ∨
    ∃ (c ω : ℂ) (k : Fin 6), c ≠ 0 ∧ ω ^ 3 = 1 ∧
      (f = c • gammaT ω (affineRep k) ∨ f = c • revT (gammaT ω (affineRep k)))

end CubicHolant.Dichotomy


