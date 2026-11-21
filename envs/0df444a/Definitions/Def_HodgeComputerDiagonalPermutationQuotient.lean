-- Prove2me | Definitions.Def_HodgeComputerDiagonalPermutationQuotient
-- name    : HodgeComputerDiagonalPermutationQuotient
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:24.328974+00:00
-- url     : https://prove2.me/theorems/fa3ae37c-9cbe-44af-9e92-a9ec62573c91
-- title:
--   Transposition-invariant source and reflection-chart cubic for diagonal-permutation
-- statement:
--   This module defines the $(01)$-transposition-invariant source $B_2$, the descended $(01)$-reflection cubic $f_{\mathrm{diag}}(\lambda, b, c, d, u)$, the cubic source $P_{\mathrm{diag}}(\lambda, b, c, d, u)$, and its cleared canonical linear-in-$u$ trace representative for the open target `diagonal-permutation` (`Simultaneous permutations · standard sector`).
--
--   The protected sextic $F$ is invariant under the diagonal $S_3$ action permuting $(X_0, X_1, X_2)$ and $(Y_0, Y_1, Y_2)$ simultaneously, while its target source $A = X_0^3 Y_0^3 - X_1^3 Y_1^3$ spans the two-dimensional standard representation. Introducing the $(01)$-transposition-invariant polynomial
--
--   $$
--   B_2 = X_0^3 Y_0^3 + X_1^3 Y_1^3 - 2 X_2^3 Y_2^3,
--   $$
--
--   its $S_3$-iterates $B_0 = \sigma_{02}(B_2)$ and $B_1 = \sigma_{12}(B_2)$ satisfy $A = \frac{1}{3}(B_1 - B_0)$. On the reflection chart $(1 + v, 1 - v, b, c + \lambda v, c - \lambda v, d)$ with $u = v^2$, $F$ pulls back to $f_{\mathrm{diag}}(\lambda, b, c, d, u) = \ell u^3 + B u^2 + C u + D$ with $\ell(\lambda) = 2 + \frac{10}{7}\lambda^2 + 2\lambda^6$, and $B_2$ pulls back to the degree-$3$ polynomial
--
--   $$
--   P_{\mathrm{diag}}(\lambda, b, c, d, u) = 2 \lambda^3 u^3 + (6 \lambda c^2 + 18 \lambda^2 c + 6 \lambda^3) u^2 + (6 c^3 + 18 \lambda c^2 + 6 \lambda^2 c) u + (2 c^3 - 2 b^3 d^3).
--   $$
--
--   The polynomial `diagCanonicalSource` records the cleared linear-in-$u$ trace representative $K_0 + K_1 u$ obtained after cancelling both the $u^3$ first-order pole and the $u^2$ branch trace modulo $f_{\mathrm{diag}}$.
--
--   These definitions support the multi-stage reduction of `HodgeComputer.DiagonalPermutation.certificate` to a linear-source relative primitive on the weighted threefold $f_{\mathrm{diag}} = 0$.
--
--   **Formalization Note** Built on `HodgeComputerDiagonalPermutation` and `HodgeComputerReflectionChart`.
-- source:
--   Hodge.computer Atlas instance `diagonal-permutation`, `data/diagonal-permutation/instance.rec`, `why.md`, and GitHub Discussion #177 (`benediamond`, `kejace`), https://github.com/hodge-computer/sextics/discussions/177

import Definitions.Def_HodgeComputerDiagonalPermutation
import Definitions.Def_HodgeComputerReflectionChart

set_option autoImplicit false
noncomputable section

namespace HodgeComputer.DiagonalPermutation
open MvPolynomial HodgeComputer.ReflectionChart

/-- The `(01)`-transposition-invariant degree-six source
`B₂ = X₀³ Y₀³ + X₁³ Y₁³ - 2 X₂³ Y₂³` (`benediamond`, Discussion #177). -/
def transpositionSource : HodgeComputer.AmbientPoly 5 :=
  X 0 ^ 3 * X 3 ^ 3 + X 1 ^ 3 * X 4 ^ 3 - C 2 * X 2 ^ 3 * X 5 ^ 3

/-- Leading coefficient `ℓ(λ) = 2 + (10/7) λ² + 2 λ⁶` of the `(01)`-reflection cubic. -/
def diagEll : ChartPoly :=
  C 2 + C (10 / 7 : ℂ) * X 0 ^ 2 + C 2 * X 0 ^ 6

/-- Quadratic coefficient `B(λ, b, c, d)` of the `(01)`-reflection cubic. -/
def diagB : ChartPoly :=
  C 30 - C (10 / 11 : ℂ) * X 3 ^ 2 - C (10 / 7 : ℂ) * X 2 ^ 2 +
    C (10 / 7 : ℂ) * X 0 * X 1 * X 3 - C (20 / 11 : ℂ) * X 0 * X 1 * X 2 +
    C (30 / 13 : ℂ) * X 0 ^ 2 * X 2 * X 3 + C (30 / 11 : ℂ) * X 0 ^ 2 * X 1 -
    C (20 / 13 : ℂ) * X 0 ^ 3 * X 3 + C 30 * X 0 ^ 4 * X 2 ^ 2 -
    C (10 / 13 : ℂ) * X 0 ^ 4 * X 1 ^ 2

/-- Linear coefficient `C(λ, b, c, d)` of the `(01)`-reflection cubic. -/
def diagC : ChartPoly :=
  C 30 + C (10 / 13 : ℂ) * X 2 * X 3 ^ 3 + C (10 / 13 : ℂ) * X 2 ^ 3 * X 3 +
    C (30 / 7 : ℂ) * X 1 * X 2 * X 3 + C (30 / 11 : ℂ) * X 1 * X 2 ^ 2 -
    C (20 / 13 : ℂ) * X 0 * X 3 ^ 3 - C (60 / 13 : ℂ) * X 0 * X 2 ^ 2 * X 3 +
    C (30 / 7 : ℂ) * X 0 * X 1 * X 3 - C (60 / 11 : ℂ) * X 0 * X 1 * X 2 +
    C (10 / 7 : ℂ) * X 0 * X 1 ^ 3 * X 3 - C (20 / 11 : ℂ) * X 0 * X 1 ^ 3 * X 2 -
    C (10 / 7 : ℂ) * X 0 ^ 2 + C (30 / 13 : ℂ) * X 0 ^ 2 * X 2 * X 3 +
    C 30 * X 0 ^ 2 * X 2 ^ 4 + C (10 / 11 : ℂ) * X 0 ^ 2 * X 1 +
    C (10 / 11 : ℂ) * X 0 ^ 2 * X 1 ^ 3

/-- Constant coefficient `D(b, c, d)` of the `(01)`-reflection cubic. -/
def diagD : ChartPoly :=
  C 2 + C (10 / 11 : ℂ) * X 3 ^ 2 + X 3 ^ 6 + C (10 / 13 : ℂ) * X 2 * X 3 ^ 3 +
    C (10 / 7 : ℂ) * X 2 ^ 2 + C (10 / 13 : ℂ) * X 2 ^ 3 * X 3 + C 2 * X 2 ^ 6 +
    C (10 / 7 : ℂ) * X 1 * X 2 * X 3 + C (10 / 11 : ℂ) * X 1 * X 2 ^ 2 +
    C (10 / 13 : ℂ) * X 1 ^ 2 * X 2 ^ 4 + C (10 / 7 : ℂ) * X 1 ^ 3 * X 2 * X 3 +
    C (10 / 11 : ℂ) * X 1 ^ 3 * X 2 ^ 2 + X 1 ^ 6

/-- The weighted cubic equation `f_diag(λ, b, c, d, u) = ℓ u³ + B u² + C u + D`
of `diagonal-permutation` on the `(01)`-reflection chart. -/
def diagWeighted : ChartPoly :=
  diagEll * X 4 ^ 3 + diagB * X 4 ^ 2 + diagC * X 4 + diagD

/-- The descended cubic source `P_diag(λ, b, c, d, u)` of `transpositionSource`
on the `(01)`-reflection chart. -/
def diagSource : ChartPoly :=
  C 2 * X 0 ^ 3 * X 4 ^ 3 +
    (C 6 * X 0 * X 2 ^ 2 + C 18 * X 0 ^ 2 * X 2 + C 6 * X 0 ^ 3) * X 4 ^ 2 +
    (C 6 * X 2 ^ 3 + C 18 * X 0 * X 2 ^ 2 + C 6 * X 0 ^ 2 * X 2) * X 4 +
    (C 2 * X 2 ^ 3 - C 2 * X 1 ^ 3 * X 3 ^ 3)

/-- Cleared canonical linear-in-`u` trace source `K₀ + K₁ u` of `diagonal-permutation`,
obtained after subtracting the first-order pole `p₃ / ℓ` and quadratic branch trace modulo `f_diag`. -/
def diagCanonicalSource : ChartPoly :=
  cubicTraceK0 diagEll diagB diagC diagD
    (C 2 * X 2 ^ 3 - C 2 * X 1 ^ 3 * X 3 ^ 3)
    (C 6 * X 0 * X 2 ^ 2 + C 18 * X 0 ^ 2 * X 2 + C 6 * X 0 ^ 3)
    (C 2 * X 0 ^ 3) +
  cubicTraceK1 diagEll diagB
    (C 6 * X 2 ^ 3 + C 18 * X 0 * X 2 ^ 2 + C 6 * X 0 ^ 2 * X 2)
    (C 6 * X 0 * X 2 ^ 2 + C 18 * X 0 ^ 2 * X 2 + C 6 * X 0 ^ 3)
    (C 2 * X 0 ^ 3) * X 4

end HodgeComputer.DiagonalPermutation


