-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
-- name    : WeierstrassEllipticZeta_DifferentialPolynomials
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T11:18:19.534206+00:00
-- url     : https://prove2.me/theorems/0118f1e3-b200-4d8e-a054-3ca36fdc68ff
-- title:
--   Cleared elliptic monomials and their polynomial differential operator
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$. The following definitions specify its cleared polynomial derivative data. Set
--
--   $$
--   J_v(z)=(z+v,\zeta(v),\wp(v),\wp'(v),\zeta(z),\wp(z),\wp'(z),\wp''(z)),
--   $$
--
--   and let $D$ be the integer polynomial derivation whose values on these eight coordinates are
--
--   $$
--   (1,0,0,0,-X_5,X_6,X_7,12X_5X_6).
--   $$
--
--   For $l_2,l_3\le M$, let $P$ be the explicit polynomial obtained from the multiplied addition identities for
--
--   $$
--   G_v(z)=(z+v)^{l_0}[2(\wp(v)-\wp(z))]^{3M}
--   \wp(z+v)^{l_2}\zeta(z+v)^{l_3}.
--   $$
--
--   The supplied data assert
--
--   $$
--   \deg D^nP\le l_0+5M+n,
--   \qquad G_v^{(n)}(z)=(D^nP)(J_v(z))
--   $$
--
--   whenever $v,z,z+v$ are outside the lattice. The polynomial is fixed before $v,z$ are chosen, and no nonzero-difference hypothesis is imposed on $\wp(v)-\wp(z)$.
--
--   Explicitly, the polynomial $P\in\mathbb Z[X_0,\ldots,X_7]$ is
--
--   $$
--   P=X_0^{l_0}A^{3M-2l_2-l_3}B^{l_2}C^{l_3},
--   $$
--
--   where
--
--   $$
--   A=2(X_2-X_5),\quad
--   B=-4(X_5+X_2)(X_2-X_5)^2+(X_3-X_6)^2,
--   $$
--
--   $$
--   C=2(X_4+X_1)(X_2-X_5)+(X_3-X_6).
--   $$
--
--   The natural-number subtraction is nonnegative under the bounds on $l_2,l_3$. `ClearedAdditionJetData` is the proposition asserting the displayed degree and derivative identities; its definition does not prove them. No coefficient-height bound is included.
-- source:
--   Senthil Kumar K (2026), Lemma 4 equations (7)-(10), with the coordinate monomial from Section 5 Lemma 8 incorporated by the product rule. The differential operator uses the derivative of DLMF 23.3.12, https://dlmf.nist.gov/23.3.E12, and zeta prime equals minus wp. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

namespace WeierstrassEllipticZeta

open MvPolynomial

/-- Coordinates are `z+v`, three fixed values at `v`, and four moving values at `z`. -/
def ellipticJetCoordinates (L : PeriodPair) (v z : ℂ) : Fin 8 → ℂ :=
  ![z + v, weierstrassZeta L v, L.weierstrassP v, L.derivWeierstrassP v,
    weierstrassZeta L z, L.weierstrassP z, L.derivWeierstrassP z,
    deriv L.derivWeierstrassP z]

/-- The polynomial vector field for the elliptic and zeta differential equations. -/
def ellipticJetDerivation :
    Derivation ℤ (MvPolynomial (Fin 8) ℤ) (MvPolynomial (Fin 8) ℤ) :=
  mkDerivation ℤ ![1, 0, 0, 0, -X 5, X 6, X 7, 12 * X 5 * X 6]

/-- The multiplied addition formulas, with an optional coordinate power. -/
def clearedAdditionPolynomial (M l₀ l₂ l₃ : ℕ) : MvPolynomial (Fin 8) ℤ :=
  X 0 ^ l₀ * (2 * (X 2 - X 5)) ^ (3 * M - 2 * l₂ - l₃) *
    (-4 * (X 5 + X 2) * (X 2 - X 5) ^ 2 + (X 3 - X 6) ^ 2) ^ l₂ *
    (2 * (X 4 + X 1) * (X 2 - X 5) + (X 3 - X 6)) ^ l₃

/-- The canonical cleared auxiliary monomial as a total complex function.
Derivative identities below are restricted to regular arguments. -/
def clearedAdditionMonomial (L : PeriodPair) (v : ℂ) (M l₀ l₂ l₃ : ℕ)
    (z : ℂ) : ℂ :=
  (z + v) ^ l₀ * (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) *
    L.weierstrassP (z + v) ^ l₂ * weierstrassZeta L (z + v) ^ l₃

/-- Exact polynomial derivative presentations and their total-degree bounds.
Coefficient-height estimates are separate obligations. -/
def ClearedAdditionJetData (L : PeriodPair) : Prop :=
  ∀ (M l₀ l₂ l₃ : ℕ), l₂ ≤ M → l₃ ≤ M → ∀ n : ℕ,
    (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃)).totalDegree ≤
      l₀ + 5 * M + n ∧
    ∀ v z : ℂ, v ∉ L.lattice → z ∉ L.lattice → z + v ∉ L.lattice →
      iteratedDeriv n (clearedAdditionMonomial L v M l₀ l₂ l₃) z =
        eval₂ (Int.castRingHom ℂ) (ellipticJetCoordinates L v z)
          (ellipticJetDerivation^[n] (clearedAdditionPolynomial M l₀ l₂ l₃))

end WeierstrassEllipticZeta


