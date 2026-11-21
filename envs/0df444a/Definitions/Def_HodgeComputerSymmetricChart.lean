-- Prove2me | Definitions.Def_HodgeComputerSymmetricChart
-- name    : HodgeComputerSymmetricChart
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:17.015808+00:00
-- url     : https://prove2.me/theorems/5ab56686-5301-4e2d-9cd5-cc30c7598706
-- title:
--   Reflection-chart cubic equation and canonical trace source for symmetric-sextic-residual
-- statement:
--   This module defines the explicit weighted cubic equation $f_{\mathrm{sym}}(\lambda, b, c, d, u)$, descended quadratic source $P_{\mathrm{sym}}(\lambda, b, c, d, u)$, and cleared canonical linear trace source for the open frontier target `symmetric-sextic-residual` (`Permutation symmetry · residual sector`).
--
--   Under the reflection chart $(X_0, X_1, X_2, Y_0, Y_1, Y_2) = (1 + v, 1 - v, b, c + \lambda v, c - \lambda v, d)$ with $u = v^2$, the quadrics $Q_X = X_0 X_1 + X_0 X_2 + X_1 X_2$ and $Q_Y = Y_0 Y_1 + Y_0 Y_2 + Y_1 Y_2$ pull back to
--
--   $$
--   L_{\mathrm{sym}} = 1 + 2 b - u, \qquad R_{\mathrm{sym}} = c^2 + 2 c d - \lambda^2 u,
--   $$
--
--   the sextic $F$ pulls back to $f_{\mathrm{sym}}(\lambda, b, c, d, v^2) = \ell_{\mathrm{sym}} v^6 + B_{\mathrm{sym}} v^4 + C_{\mathrm{sym}} v^2 + D_{\mathrm{sym}}$, and the residual source $A = X_0 X_1 X_2 Y_0 Y_1 Y_2$ pulls back to $P_{\mathrm{sym}}(\lambda, b, c, d, v^2)$ where
--
--   $$
--   P_{\mathrm{sym}}(\lambda, b, c, d, u) = b d (1 - u)(c^2 - \lambda^2 u).
--   $$
--
--   The definition also packages the explicit cubic coefficients $(\ell_{\mathrm{sym}}, B_{\mathrm{sym}}, C_{\mathrm{sym}}, D_{\mathrm{sym}})$ and the resulting linear-in-$u$ canonical trace polynomial `symCanonicalSource`.
--
--   These data bind the mission target `HodgeComputer.SymmetricSexticResidual.certificate` to the reusable reflection-chart transport and canonical trace reductions.
--
--   **Formalization Note** Built on `HodgeComputerSymmetricSexticResidual` and `HodgeComputerReflectionChart` using variable order $(\lambda, b, c, d, u)$ on `Fin 5`.
-- source:
--   Hodge.computer Atlas instance `symmetric-sextic-residual`, `data/symmetric-sextic-residual/instance.rec` and GitHub Discussion #117 (`fqlx`, `benediamond`, `kmehltretter82`), https://github.com/hodge-computer/sextics/discussions/117

import Definitions.Def_HodgeComputerSymmetricSexticResidual
import Definitions.Def_HodgeComputerReflectionChart

set_option autoImplicit false
noncomputable section

namespace HodgeComputer.SymmetricSexticResidual
open MvPolynomial HodgeComputer.ReflectionChart

/-- Left quadric factor `1 + 2 b - u` on the reflection chart `(λ, b, c, d, u)`. -/
def leftQuadric : ChartPoly := 1 + C 2 * X 1 - X 4

/-- Right quadric factor `c² + 2 c d - λ² u` on the reflection chart `(λ, b, c, d, u)`. -/
def rightQuadric : ChartPoly := X 2 ^ 2 + C 2 * X 2 * X 3 - X 0 ^ 2 * X 4

/-- Weighted cubic equation `f_sym(λ, b, c, d, u)` of `symmetric-sextic-residual`
on the reflection chart `(1 + v, 1 - v, b, c + λ v, c - λ v, d)`, `u = v²`. -/
def symWeighted : ChartPoly :=
  C 2 + X 1 ^ 6 + C 2 * X 2 ^ 6 + X 3 ^ 6 +
    C 30 * X 4 + C 30 * X 4 ^ 2 + C 2 * X 4 ^ 3 +
    C 30 * X 0 ^ 2 * X 2 ^ 4 * X 4 +
    C 30 * X 0 ^ 4 * X 2 ^ 2 * X 4 ^ 2 + C 2 * X 0 ^ 6 * X 4 ^ 3 +
    C (5 / 7 : ℂ) * leftQuadric ^ 2 * rightQuadric +
    C (10 / 7 : ℂ) * leftQuadric * rightQuadric ^ 2

/-- Descended quadratic source `P_sym(λ, b, c, d, u) = b d (1 - u) (c² - λ² u)`
of `symmetric-sextic-residual` on the reflection chart. -/
def symSource : ChartPoly :=
  X 1 * X 3 * (1 - X 4) * (X 2 ^ 2 - X 0 ^ 2 * X 4)

/-- Leading `u³` coefficient `ℓ_sym(λ)` of `symWeighted`. -/
def symEll : ChartPoly :=
  C 2 + C 2 * X 0 ^ 6 - C (5 / 7 : ℂ) * X 0 ^ 2 - C (10 / 7 : ℂ) * X 0 ^ 4

/-- Quadratic `u²` coefficient `B_sym(λ, b, c, d)` of `symWeighted`. -/
def symB : ChartPoly :=
  let L0 : ChartPoly := 1 + C 2 * X 1
  let R0 : ChartPoly := X 2 ^ 2 + C 2 * X 2 * X 3
  C 30 + C 30 * X 0 ^ 4 * X 2 ^ 2 +
    C (5 / 7 : ℂ) * (R0 + C 2 * X 0 ^ 2 * L0) +
    C (10 / 7 : ℂ) * (X 0 ^ 4 * L0 + C 2 * X 0 ^ 2 * R0)

/-- Linear `u` coefficient `C_sym(λ, b, c, d)` of `symWeighted`. -/
def symC : ChartPoly :=
  let L0 : ChartPoly := 1 + C 2 * X 1
  let R0 : ChartPoly := X 2 ^ 2 + C 2 * X 2 * X 3
  C 30 + C 30 * X 0 ^ 2 * X 2 ^ 4 +
    C (5 / 7 : ℂ) * (-X 0 ^ 2 * L0 ^ 2 - C 2 * L0 * R0) +
    C (10 / 7 : ℂ) * (-C 2 * X 0 ^ 2 * L0 * R0 - R0 ^ 2)

/-- Constant coefficient `D_sym(b, c, d)` of `symWeighted`. -/
def symD : ChartPoly :=
  let L0 : ChartPoly := 1 + C 2 * X 1
  let R0 : ChartPoly := X 2 ^ 2 + C 2 * X 2 * X 3
  C 2 + X 1 ^ 6 + C 2 * X 2 ^ 6 + X 3 ^ 6 +
    C (5 / 7 : ℂ) * L0 ^ 2 * R0 + C (10 / 7 : ℂ) * L0 * R0 ^ 2

/-- Cleared canonical linear-in-`u` trace source `K₀ + K₁ u` of `symmetric-sextic-residual`. -/
def symCanonicalSource : ChartPoly :=
  cubicTraceK0 symEll symB symC symD
    (X 1 * X 3 * X 2 ^ 2) (X 1 * X 3 * X 0 ^ 2) 0 +
  cubicTraceK1 symEll symB
    (-X 1 * X 3 * (X 2 ^ 2 + X 0 ^ 2)) (X 1 * X 3 * X 0 ^ 2) 0 * X 4

end HodgeComputer.SymmetricSexticResidual


