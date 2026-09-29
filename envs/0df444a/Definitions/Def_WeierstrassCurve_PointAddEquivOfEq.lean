-- Prove2me | Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
-- name    : WeierstrassCurve_PointAddEquivOfEq
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/93e7e779-30aa-5d16-a2cc-e9754d867383
-- title:
--   Transport of affine point groups along an equality of Weierstrass models
-- statement:
--   Over a field $L$, a `WeierstrassCurve L` is a tuple of coefficients $(a_1,a_2,a_3,a_4,a_6)$, and `W.toAffine.Point` is the group of $L$-points of the associated affine Weierstrass curve: a point is either the marked point at infinity or a pair $(x,y)$ together with a proof that $(x,y)$ is a nonsingular solution of the Weierstrass equation, with the usual chord-and-tangent addition. The module provides the transport of this group along an *equality* of coefficient tuples: given Weierstrass curves $W_1, W_2$ over $L$ and a proof $e : W_1 = W_2$, `pointAddEquivOfEq e` is an isomorphism of additive groups $W_1(L) \xrightarrow{\sim} W_2(L)$ obtained by substituting $W_2$ for $W_1$ in the identity isomorphism. So it is not an isomorphism of curves in the geometric sense but a coercion between two notations for literally the same Weierstrass equation, packaged as an `AddEquiv` so that it can be composed with genuine homomorphisms.
--
--   Three further statements record its behaviour. `pointAddEquivOfEq_refl` says that the transport along the reflexivity proof $W = W$ is the identity isomorphism of $W(L)$. `pointAddEquivOfEq_symm` says that the inverse of the transport along $e : W_1 = W_2$ is the transport along the reversed equality $W_2 = W_1$. `pointAddEquivOfEq_some` says that on an affine point, the map acts by the identity on coordinates: for $x, y \in L$ and a proof $h$ that $(x,y)$ is a nonsingular point of $W_1$, the image of the corresponding point is the point of $W_2$ with the same coordinates $x, y$, whose nonsingularity proof is the transport of $h$. In particular the point at infinity goes to the point at infinity, and the isomorphism is the identity on underlying coordinate data.
--
--   **Relation to Mathlib.** `WeierstrassCurve`, the affine point group `Affine.Point` with its additive group structure, and the nonsingularity predicate are Mathlib's; Mathlib has no transport of the point group along an equality of Weierstrass coefficient tuples, and this module supplies that together with its basic rewriting rules.
--
--   **Where it is used.** The device is used where a Weierstrass model arising by construction — for instance by base change or reduction of a chosen model — is proved to be equal to a given model, so that maps into or out of the two point groups may be compared; keeping the transport in one named definition with this small interface lets the statements that use it be free of coercions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_PointAddEquivOfEq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace WeierstrassCurve

variable {L : Type*} [Field L] [DecidableEq L]

def pointAddEquivOfEq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point :=
  e ▸ AddEquiv.refl _

@[simp] theorem pointAddEquivOfEq_refl (W : WeierstrassCurve L) :
    pointAddEquivOfEq (rfl : W = W) = AddEquiv.refl _ := rfl

theorem pointAddEquivOfEq_symm {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) :
    (pointAddEquivOfEq e).symm = pointAddEquivOfEq e.symm := by subst e; rfl

theorem pointAddEquivOfEq_some {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂)
    {x y : L} (h : W₁.toAffine.Nonsingular x y) :
    pointAddEquivOfEq e (.some x y h) = .some x y (e ▸ h) := by subst e; rfl

end WeierstrassCurve


