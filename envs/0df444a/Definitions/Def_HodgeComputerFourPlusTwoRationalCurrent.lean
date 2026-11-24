-- Prove2me | Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
-- name    : HodgeComputerFourPlusTwoRationalCurrent
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-24T07:28:51.221121+00:00
-- url     : https://prove2.me/theorems/c78ca94a-cec1-4324-b3da-187584e0622b
-- title:
--   Rational vector-field finish line, fixed affine support, pencil Laurent specialization, and nodal seed companion matrices for four-plus-two-residual
-- statement:
--   This definition module packages the rational-field, affine-chart, pencil-specialization, and local cubic-trace operators for `four-plus-two-residual` (`F = H(X_0, X_1, Y_0, Y_1) + B(X_2, Y_2)`, `q = 1`, `A = X_0^3 Y_0^3`):
--
--   1. `CoreRationalEquation δ v`: the single fraction-field equation
--
--   $$
--   \sum_{i=0}^3 v_i\,\delta_i(H) - \frac{3}{2} H \sum_{i=0}^3 \delta_i(v_i) = X_0^3 Y_0^3
--   $$
--
--   in a fraction ring $K$ of $\mathbb{C}[x_0, x_1, y_0, y_1]$.
--
--   2. `affineCore` and `FixedSupportEquation B n N`: on $x_0 = 1$ with $(x, y, z) = (x_1/x_0, y_0/x_0, y_1/x_0)$ and $h(x,y,z) = H(1,x,y,z)$, the cleared numerator system $2 B (N \cdot \nabla h) - 3 h (B \operatorname{div} N - n (N \cdot \nabla B)) = 3 y^3 B^{n+1}$, which is linear in $N_0, N_1, N_2$ for any fixed nonzero polynomial $B$ and exponent $n$.
--
--   3. `chartCurrent δ P q` and `laurentCorrected h q m`: the ratio-chart twisted divergence $(2/3) q(P) - P \operatorname{div}(q)$ and binomial telescoping sum $\sum_{j=0}^m \binom{-2/3}{j} h^j q_j$ specializing a polar Laurent chain along a pencil $P + \varepsilon S$.
--
--   4. `seedMulX k` and `seedAdjugateNumerator k u v`: the $3 \times 3$ companion and adjugate matrices for $x = \alpha^2$ ($x^3 = k$) computing the three-sheet normalized trace at the coupled nodal seed.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoCore
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
noncomputable section

namespace HodgeComputer.FourPlusTwoResidual

open MvPolynomial Matrix
open scoped BigOperators

/-- Rational twisted vector-field equation `v(H) - (3/2)·H·div(v) = x₀³·y₀³`
in a fraction field `K` of `ℂ[x₀,x₁,y₀,y₁]` equipped with coordinate derivations `δ`. -/
def CoreRationalEquation {K : Type*} [Field K]
    [Algebra (MvPolynomial (Fin 4) ℂ) K]
    (δ : Fin 4 → Derivation ℤ K K) (v : Fin 4 → K) : Prop :=
  (∑ i, v i * δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K core)) -
    (3 / 2 : K) * algebraMap (MvPolynomial (Fin 4) ℂ) K core * (∑ i, δ i (v i)) =
    algebraMap (MvPolynomial (Fin 4) ℂ) K coreSource

/-- Dehomogenized four-plus-two core `h(x,y,z) = H(1,x,y,z)` in `ℂ[x,y,z]`
with indices `0, 1, 2` standing for `x = x₁/x₀, y = y₀/x₀, z = y₁/x₀`. -/
def affineCore : MvPolynomial (Fin 3) ℂ :=
  1 + C (5 / 7 : ℂ) * X 0 + C (5 / 7 : ℂ) * X 0 * X 1 * X 2 + C (10 / 7 : ℂ) * X 0 ^ 5 +
  C (10 / 7 : ℂ) * X 0 * X 1 ^ 3 * X 2 + X 0 ^ 6 + X 1 ^ 6 + C (5 / 7 : ℂ) * X 1 ^ 5 * X 2 +
  C (15 / 7 : ℂ) * X 1 * X 2 ^ 5 + X 2 ^ 6

/-- Cleared affine numerator system for `q_i = N_i / B^n` solving
`(2/3)·q(h) - h·div(q) = y³`, linear in `N` for fixed `(B, n)`. -/
def FixedSupportEquation (B : MvPolynomial (Fin 3) ℂ) (n : ℕ)
    (N : Fin 3 → MvPolynomial (Fin 3) ℂ) : Prop :=
  2 * B * (∑ i, N i * pderiv i affineCore) - 3 * affineCore *
    (B * (∑ i, pderiv i (N i)) - (n : MvPolynomial (Fin 3) ℂ) * (∑ i, N i * pderiv i B)) =
    3 * X 1 ^ 3 * B ^ (n + 1)

/-- Directional action `∑ i, v_i · δ_i` of a coordinate vector field. -/
def fieldAction {ι k R : Type*} [Fintype ι] [CommRing k] [CommRing R] [Algebra k R]
    (δ : ι → Derivation k R R) (v : ι → R) : Derivation k R R :=
  ∑ i, v i • δ i

/-- Coordinate divergence `∑ i, δ_i(v_i)` of a vector field. -/
def fieldDivergence {ι k R : Type*} [Fintype ι] [CommRing k] [CommRing R] [Algebra k R]
    (δ : ι → Derivation k R R) (v : ι → R) : R :=
  ∑ i, δ i (v i)

/-- Ratio-chart twisted divergence operator `(2/3)·q(P) - P·div(q)`. -/
def chartCurrent {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    (δ : ι → Derivation ℚ K K) (P : K) (q : ι → K) : K :=
  (2 / 3 : K) * fieldAction δ q P - P * fieldDivergence δ q

/-- Running rational remainder weight in finite Laurent pencil specialization. -/
def laurentD : ℕ → ℚ
  | 0 => 1
  | j + 1 => -(2 / (3 * ((j : ℚ) + 1))) * laurentD j - laurentD j

/-- Binomial weight `binom(-2/3, j)` for the `j`-th polar Laurent coefficient. -/
def laurentC : ℕ → ℚ
  | 0 => 1
  | j + 1 => -(2 / (3 * ((j : ℚ) + 1))) * laurentD j

/-- Specialized current `∑_{j=0}^m c_j · h^j · q_j` cancelling a pole of order `m` along `P + ε S`. -/
def laurentCorrected {ι K : Type*} [Field K] [CharZero K]
    (h : K) (q : ℕ → ι → K) (m : ℕ) : ι → K :=
  ∑ j ∈ Finset.range (m + 1), fun i => algebraMap ℚ K (laurentC j) * h ^ j * q j i

/-- Companion matrix of `x = α²` on `(1, x, x²)` in the cubic algebra `x³ = k`. -/
def seedMulX {K : Type*} [CommRing K] (k : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, k; 1, 0, 0; 0, 1, 0]

/-- Adjugate numerator matrix clearing `(u + v·x)⁻¹` over `u³ + k·v³`. -/
def seedAdjugateNumerator {K : Type*} [CommRing K] (k u v : K) : Matrix (Fin 3) (Fin 3) K :=
  !![u ^ 2, k * v ^ 2, -(k * u * v); -(u * v), u ^ 2, k * v ^ 2; v ^ 2, -(u * v), u ^ 2]

end HodgeComputer.FourPlusTwoResidual


