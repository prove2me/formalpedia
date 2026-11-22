-- Prove2me | Definitions.Def_HodgeComputerFourPlusTwoSourceAlgebra
-- name    : HodgeComputerFourPlusTwoSourceAlgebra
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T13:53:14.579518+00:00
-- url     : https://prove2.me/theorems/8991740f-fa0e-4246-8578-dcbda2ecd5c7
-- title:
--   Generalized variable-source core certificate algebra, polynomial-exact baseline, and coprime linear system
-- statement:
--   This module extends the four-variable core definitions of `four-plus-two-residual` to arbitrary homogeneous sextic sources $S \in \mathbb{C}[x_0, x_1, y_0, y_1]$, providing the algebraic primitives needed to assemble multi-divisor bundle certificates and audit candidate denominators via their source images $W_D / E$.
--
--   1. `coreResidual S D N`: the cleared four-variable residual
--
--   $$
--   F_H(S, D, N) = 2 S D^2 - 2 D \sum_{i=0}^3 (\partial_i H) N_i + 3 H \Bigl(D \sum_{i=0}^3 \partial_i N_i - \sum_{i=0}^3 (\partial_i D) N_i\Bigr).
--   $$
--
--   2. `CoreCertificateFor S D N`: a nonzero denominator $D$ homogeneous of degree $d \ge 0$ and numerators $N_i$ homogeneous of degree $d + 1$ satisfying `coreResidual S D N = 0`. Allowing $d = 0$ includes the polynomial-exact baseline $D = 1$ with linear vector fields $\deg N_i = 1$.
--
--   3. `PolyExactCoreSource S`: a source representable at $D = 1$ as $S = L \cdot \nabla H - \frac{3}{2} H \operatorname{div}(L)$ for a homogeneous linear vector field $L$ ($\deg L_i = 1$).
--
--   4. `CoprimeLinearCoreSystem S D N T`: the lower-degree linear pair $\sum_i (\partial_i D) N_i = D T$ (degree $2d$) and $2 S D - 2 \sum_i (\partial_i H) N_i + 3 H (\sum_i \partial_i N_i - T) = 0$ (degree $d + 6$).
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry

set_option autoImplicit false
noncomputable section

namespace HodgeComputer.FourPlusTwoResidual

open MvPolynomial
open scoped BigOperators

/-- Cleared four-variable core residual `F_H(S, D, N)` for an arbitrary sextic source `S`:
`2 S D² - 2 D (N · ∇H) + 3 H (D div(N) - N · ∇D)`. -/
def coreResidual (S D : MvPolynomial (Fin 4) ℂ)
    (N : Fin 4 → MvPolynomial (Fin 4) ℂ) : MvPolynomial (Fin 4) ℂ :=
  2 * S * D ^ 2 - 2 * D * (∑ i, pderiv i core * N i) +
    3 * core * (D * (∑ i, pderiv i (N i)) - ∑ i, pderiv i D * N i)

/-- Generalized core certificate for an arbitrary source `S`, allowing `deg D = d ≥ 0`
(including `D = 1` with linear numerators `deg Nᵢ = 1`). -/
def CoreCertificateFor (S D : MvPolynomial (Fin 4) ℂ)
    (N : Fin 4 → MvPolynomial (Fin 4) ℂ) : Prop :=
  D ≠ 0 ∧ (∃ d : ℕ, D.IsHomogeneous d ∧ ∀ i, (N i).IsHomogeneous (d + 1)) ∧
    coreResidual S D N = 0

/-- A sextic source `S` is polynomial-exact on the core if `S = L · ∇H - (3/2) H div(L)`
for a homogeneous linear vector field `L` (`deg Lᵢ = 1`), i.e. the `D = 1` baseline. -/
def PolyExactCoreSource (S : MvPolynomial (Fin 4) ℂ) : Prop :=
  ∃ L : Fin 4 → MvPolynomial (Fin 4) ℂ,
    (∀ i, (L i).IsHomogeneous 1) ∧
      2 * S = 2 * (∑ i, pderiv i core * L i) - 3 * core * (∑ i, pderiv i (L i))

/-- Lower-degree linear pair `(N, T)` equivalent to `CoreCertificateFor S D N` when `H ∤ D`,
with equations of degrees `2d` and `d + 6` instead of `2d + 6`. -/
def CoprimeLinearCoreSystem (S D : MvPolynomial (Fin 4) ℂ)
    (N : Fin 4 → MvPolynomial (Fin 4) ℂ) (T : MvPolynomial (Fin 4) ℂ) : Prop :=
  (∑ i, pderiv i D * N i = D * T) ∧
    (2 * S * D - 2 * (∑ i, pderiv i core * N i) +
      3 * core * ((∑ i, pderiv i (N i)) - T) = 0)

end HodgeComputer.FourPlusTwoResidual


