-- Prove2me | Definitions.Def_EllipticCurve_ZeroComponentAt
-- name    : EllipticCurve_ZeroComponentAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/972b2a43-0d9d-5262-8073-36ca10ddb117
-- title:
--   Points in the identity component at a place of Q​
-- statement:
--   The module defines a single predicate, [`WeierstrassCurve.InZeroComponentAt W A P`](../def/EllipticCurve_ZeroComponentAt.html#L13). Its data are: a Weierstrass curve $W$ over $\mathbb{Z}$ (a bare Weierstrass equation, with no minimality or nonsingularity assumption); a valuation subring $A$ of $\overline{\mathbb{Q}}$, i.e. a place of $\overline{\mathbb{Q}}$, with its maximal ideal and residue field $k_A =$ `IsLocalRing.ResidueField A`; and a point $P$ of the affine point type of $W$ base changed along $\mathbb{Z}\to\mathbb{Q}$ and then to $\overline{\mathbb{Q}}$. The predicate is the disjunction of the following cases. Either $P$ is the point at infinity $0$; or $P$ is an affine point `.some x y h` with coordinates $x,y\in\overline{\mathbb{Q}}$ and a proof $h$ that $(x,y)$ is a nonsingular point of the base-changed affine equation, and then one of two further conditions holds: (i) $x\notin A$, i.e. the abscissa is not $A$-integral; or (ii) both $x\in A$ and $y\in A$, and the images $\bar x,\bar y$ of $x,y$ under the residue map $A\to k_A$ form a nonsingular point of the affine curve obtained by reducing the *integral* model $W$ modulo the maximal ideal of $A$ (that is, of $W$ mapped along $\mathbb{Z}\to k_A$).
--
--   Thus the predicate is stated relative to the chosen integral Weierstrass model $W$ and to the chosen place $A$, and it is a bare `Prop`: nothing here asserts that the points satisfying it form a subgroup, nor that $A$-integrality of $x$ forces that of $y$ (condition (ii) demands both). For a model minimal at the residue characteristic of $A$, case (i) describes the kernel of reduction and case (ii) the points reducing into the smooth locus, so that the predicate cuts out the classical subgroup $E_0$ of points reducing to nonsingular points; the group-theoretic and reduction-theoretic properties are proved elsewhere as separate theorems.
--
--   **Relation to Mathlib.** Built entirely from Mathlib notions — `WeierstrassCurve`, its base change and affine points, `Nonsingular`, `ValuationSubring` and `IsLocalRing.ResidueField` with its residue map — but Mathlib has no notion of the identity component or of the reduction of a point at a place, so this predicate is the project's own.
--
--   **Where it is used.** The predicate is used in the local analysis of torsion points on the integral Frey model: at primes of multiplicative reduction and at $p$ one asks whether a point of order $p$ lies on the identity component, and this feeds Mazur's Eisenstein-ideal argument showing that the mod-$p$ representation of the Frey curve has no cofixed line for $p\ge 17$ (including the global input [`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`](../thm.html#WeierstrassCurve.mazurStepThree_not_inZeroComponentAt)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_EllipticCurve_ZeroComponentAt.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace WeierstrassCurve

open scoped WeierstrassCurve.Affine

def InZeroComponentAt (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) : Prop :=
  P = 0 ∨ ∃ (x y : AlgebraicClosure ℚ)
      (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
    P = .some x y h ∧
      (x ∉ A ∨ ∃ (hx : x ∈ A) (hy : y ∈ A),
        (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular
          (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩))

end WeierstrassCurve


