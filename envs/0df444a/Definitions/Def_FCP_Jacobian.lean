-- Prove2me | Definitions.Def_FCP_Jacobian
-- name    : FCP_Jacobian
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T19:06:38.663322+00:00
-- url     : https://prove2.me/theorems/26593d23-4f43-40b9-8dd0-de1a65c6b54b
-- title:
--   Polynomial self-maps, their Jacobian matrix, and the Jacobian conjecture predicate
-- statement:
--   A **polynomial self-map** of $k^n$ is an $n$-tuple $F = (F_1, \dots, F_n)$ of polynomials in $n$ variables over a commutative ring $k$. Its **Jacobian matrix** has $(i,j)$ entry $\partial F_i / \partial X_j$, and composition $F \circ G$ is substitution of the coordinates of $G$ into $F$.
--
--   $\mathrm{JC}(k, n)$ is the assertion that every polynomial self-map of $k^n$ whose Jacobian determinant is a unit of the polynomial ring has a two-sided inverse that is again a polynomial self-map.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/JacobianConjecture.lean); https://en.wikipedia.org/wiki/Jacobian_conjecture

import Mathlib

namespace FCP.Jacobian

open MvPolynomial

/-- A polynomial self-map of affine `n`-space over `k`: an `n`-tuple of polynomials in
`n` variables. -/
abbrev PolyMap (k : Type) [CommRing k] (n : ℕ) := Fin n → MvPolynomial (Fin n) k

/-- The Jacobian matrix of a polynomial self-map, with `(i, j)` entry the partial derivative of
the `i`-th coordinate with respect to the `j`-th variable. -/
noncomputable def jacobian {k : Type} [CommRing k] {n : ℕ} (F : PolyMap k n) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) k) :=
  Matrix.of fun i j => pderiv j (F i)

/-- Composition of polynomial self-maps: `comp F G` substitutes the coordinates of `G` into
the polynomials of `F`. -/
noncomputable def comp {k : Type} [CommRing k] {n : ℕ} (F G : PolyMap k n) : PolyMap k n :=
  fun i => aeval G (F i)

/-- The identity polynomial self-map, whose `i`-th coordinate is the variable `X i`. -/
noncomputable def idMap (k : Type) [CommRing k] (n : ℕ) : PolyMap k n := fun i => X i

/-- The Jacobian conjecture for `n` variables over `k`: every polynomial self-map of `kⁿ` whose
Jacobian determinant is a unit admits a two-sided polynomial inverse. -/
def JacobianConjectureProp (k : Type) [CommRing k] (n : ℕ) : Prop :=
  ∀ F : PolyMap k n, IsUnit (jacobian F).det →
    ∃ G : PolyMap k n, comp G F = idMap k n ∧ comp F G = idMap k n

end FCP.Jacobian


