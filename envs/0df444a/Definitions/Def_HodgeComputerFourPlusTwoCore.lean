-- Prove2me | Definitions.Def_HodgeComputerFourPlusTwoCore
-- name    : HodgeComputerFourPlusTwoCore
-- status  : Definition
-- author  : @xuanji
-- created : 2026-11-10T05:25:20.455804+00:00
-- url     : https://prove2.me/theorems/85cd56fc-ecf1-4928-8c0f-75b19b944ecb
-- title:
--   Four-variable core of four-plus-two-residual
-- statement:
--   Let $x=(x_0,x_1,x_2,x_3)$ be coordinates on $\mathbb{C}^4$. This file defines the data of the *four-variable core* of the Hodge Computer instance `four-plus-two-residual`.
--
--   1. The **core sextic** is
--   $$H = x_0^6 + \tfrac57 x_0^5x_1 + \tfrac57 x_0^3x_1x_2x_3 + \tfrac{10}{7}x_0x_1^5 + \tfrac{10}{7}x_0x_1x_2^3x_3 + x_1^6 + x_2^6 + \tfrac57 x_2^5x_3 + \tfrac{15}{7}x_2x_3^5 + x_3^6 .$$
--   It is the part of the instance polynomial $F = H(X_0,X_1,Y_0,Y_1) + B(X_2,Y_2)$ that involves the first two $X$ and first two $Y$ variables, with $(x_0,x_1,x_2,x_3)=(X_0,X_1,Y_0,Y_1)$.
--
--   2. The **core source** is $A = x_0^3x_2^3$ (the instance source $X_0^3Y_0^3$).
--
--   3. A pair $(D,N)$, with $D\in\mathbb{C}[x]$ and $N=(N_0,\dots,N_3)\in\mathbb{C}[x]^4$, is a **core certificate** if $D\neq 0$, there is $k\ge 0$ such that $D$ is homogeneous of degree $k+1$ and every $N_i$ is homogeneous of degree $k+2$, and
--   $$2\,A\,D^2 \;-\; 2\,D\sum_{i=0}^{3}\frac{\partial H}{\partial x_i}N_i \;+\; 3\,H\Big(D\sum_{i=0}^{3}\frac{\partial N_i}{\partial x_i}-\sum_{i=0}^{3}\frac{\partial D}{\partial x_i}N_i\Big)=0 .$$
--
--   Equivalently, the rational vector field $v=\sum_i (N_i/D)\,\partial_{x_i}$, homogeneous of degree one, satisfies the strict twisted equation
--   $$v(H)-\tfrac32\,H\,\operatorname{div}v = A ,$$
--   which says that $A\,H^{-5/3}\,dx_0\wedge dx_1\wedge dx_2\wedge dx_3 = d\big(-\tfrac32 H^{-2/3}\,\iota_v\,dx_0\wedge\dots\wedge dx_3\big)$. No coprimality between $D$ and $H$ is required.
--
--   The role of this definition is to isolate the four-variable content of the six-variable Diamond certificate problem for `four-plus-two-residual`: a core certificate lifts to a full certificate by an explicit formula.
--
--   **Formalization Note.** `core` and `coreSource` are elements of `MvPolynomial (Fin 4) ℂ`; `CoreCertificate D N` is the proposition in item 3.
-- source:
--   Derived from the instance four-plus-two-residual of https://hodge.computer (github.com/hodge-computer/sextics, data/four-plus-two-residual/instance.rec) and the prove2.me definition HodgeComputerFourPlusTwoResidual; the reduction to four variables is proved in the sketch submitted for HodgeComputer.FourPlusTwoResidual.certificate.

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.FourPlusTwoResidual
open MvPolynomial
open scoped BigOperators

/-- The four-variable core `H(x₀,x₁,y₀,y₁)` of the four-plus-two sextic
`F = H(X₀,X₁,Y₀,Y₁) + B(X₂,Y₂)`. Variables `0,1,2,3` stand for `X₀,X₁,Y₀,Y₁`. -/
def core : MvPolynomial (Fin 4) ℂ :=
  X 0 ^ 6 + C (5 / 7 : ℂ) * X 0 ^ 5 * X 1 + C (5 / 7 : ℂ) * X 0 ^ 3 * X 1 * X 2 * X 3
    + C (10 / 7 : ℂ) * X 0 * X 1 ^ 5 + C (10 / 7 : ℂ) * X 0 * X 1 * X 2 ^ 3 * X 3 + X 1 ^ 6
    + X 2 ^ 6 + C (5 / 7 : ℂ) * X 2 ^ 5 * X 3 + C (15 / 7 : ℂ) * X 2 * X 3 ^ 5 + X 3 ^ 6

/-- The source `x₀³·y₀³` in the core variables. -/
def coreSource : MvPolynomial (Fin 4) ℂ := X 0 ^ 3 * X 2 ^ 3

/-- A strict twisted certificate on the core: a nonconstant homogeneous denominator `D`
and numerators `N` of one degree more such that the rational field `v = N / D` satisfies
`v(H) - (3/2)·H·div(v) = A`, written after clearing `D²` and the factor `2`. -/
def CoreCertificate (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ) : Prop :=
  D ≠ 0 ∧ (∃ k : ℕ, D.IsHomogeneous (k + 1) ∧ ∀ i, (N i).IsHomogeneous (k + 2)) ∧
    2 * coreSource * D ^ 2 - 2 * D * (∑ i, pderiv i core * N i)
      + 3 * core * (D * (∑ i, pderiv i (N i)) - ∑ i, pderiv i D * N i) = 0

end HodgeComputer.FourPlusTwoResidual


