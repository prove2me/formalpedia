-- Prove2me | Definitions.Def_WeierstrassCurve_HasseInvariant
-- name    : WeierstrassCurve_HasseInvariant
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/fd640505-38ce-5fde-ba82-0d2c33ecb34a
-- title:
--   Hasse invariant, Legendre curves, Hasse-supersingular j-invariants
-- statement:
--   Three definitions are made. For a natural number $q$ and a Weierstrass curve $W$ over a commutative ring $R$, [`WeierstrassCurve.hasseInvariant q W`](../def/WeierstrassCurve_HasseInvariant.html#L11) is the coefficient of $x^{q-1}$ in the $\lfloor (q-1)/2\rfloor$-th power of the two-torsion cubic of $W$, i.e. of
--   $$\bigl(4x^{3}+b_2x^{2}+2b_4x+b_6\bigr)^{\lfloor (q-1)/2\rfloor}\in R[x],$$
--   where $b_2,b_4,b_6$ are the usual quantities attached to the coefficients $a_1,\dots ,a_6$ and both $q-1$ and the halving are truncated natural-number operations. Thus the invariant is attached to a chosen Weierstrass model, not to an isomorphism class, and it is taken of the cubic $(2y+a_1x+a_3)^2$ rather than of a monic cubic obtained by completing the square; for $y^2=f(x)$ with $f$ monic this differs from the classical coefficient of $x^{q-1}$ in $f^{(q-1)/2}$ by the unit factor $4^{\lfloor (q-1)/2\rfloor}$ when $4$ is invertible.
--
--   For $t\in R$, [`WeierstrassCurve.legendreCurve t`](../def/WeierstrassCurve_HasseInvariant.html#L14) is the Weierstrass curve with coefficients $a_1=0$, $a_2=-(1+t)$, $a_3=0$, $a_4=t$, $a_6=0$, that is $y^2=x^3-(1+t)x^2+tx=x(x-1)(x-t)$.
--
--   Finally, for a field $K$, [`ModularCurve.ssJSetHasse q K`](../def/WeierstrassCurve_HasseInvariant.html#L21) is the subset of $K$ consisting of those $j$ such that every Weierstrass curve $W$ over $K$ which is elliptic (its discriminant is a unit) and satisfies $W.j=j$ has vanishing Hasse invariant at $q$. The quantification is over all models with the given $j$-invariant, so membership is by definition a condition on every such model; the set is empty of content at elements of $K$ that are not $j$-invariants of any elliptic curve over $K$ only in the vacuous sense.
--
--   **Relation to Mathlib.** Built on Mathlib's `WeierstrassCurve`, its `twoTorsionPolynomial`, `j` and `IsElliptic`; the Hasse invariant, the Legendre family and the Hasse-supersingular set of $j$-invariants are the project's own definitions.
--
--   **Where it is used.** These definitions give the characteristic-$q$ supersingularity condition in the form of the vanishing of a weight $q-1$ invariant of a Weierstrass model, and the Legendre family provides explicit models with prescribed $2$-torsion in which that condition can be computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_HasseInvariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

noncomputable def hasseInvariant (q : ℕ) (W : WeierstrassCurve R) : R :=
  (W.twoTorsionPolynomial.toPoly ^ ((q - 1) / 2)).coeff (q - 1)

def legendreCurve (t : R) : WeierstrassCurve R :=
  ⟨0, -(1 + t), 0, t, 0⟩

end WeierstrassCurve

namespace ModularCurve

def ssJSetHasse (q : ℕ) (K : Type*) [Field K] : Set K :=
  {j | ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j → W.hasseInvariant q = 0}

end ModularCurve


