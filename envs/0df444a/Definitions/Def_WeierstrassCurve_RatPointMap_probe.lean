-- Prove2me | Definitions.Def_WeierstrassCurve_RatPointMap_probe
-- name    : WeierstrassCurve_RatPointMap_probe
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/ce07b20c-8454-54a1-91e9-81335e68ebd8
-- title:
--   Coordinatewise map on affine points along a ring homomorphism
-- statement:
--   Fix fields $F$ and $k$, a ring homomorphism $f : F \to k$, and a Weierstrass curve $W_0$ over $F$, given by its coefficients $a_1,a_2,a_3,a_4,a_6$. Mathlib's base change `WeierstrassCurve.map` produces the Weierstrass curve $W_0.\mathrm{map}\,f$ over $k$ whose coefficients are the images $f(a_i)$. The module defines `ratPointMap`, the map from the set of affine points of $W_0$ (the Mathlib type `W₀.toAffine.Point`, whose elements are either the point at infinity `.zero` or a pair $(x,y)$ of coordinates in $F$ together with a proof that $(x,y)$ is a nonsingular point of the affine equation) to the affine points of $W_0.\mathrm{map}\,f$. It is defined by cases: the point at infinity goes to the point at infinity, and a point with coordinates $(x,y)$ goes to the point with coordinates $(f(x), f(y))$. That the image pair is again a nonsingular solution of the transported equation is supplied by Mathlib's `WeierstrassCurve.Affine.map_nonsingular`, applied with the injectivity of $f$ (automatic for a ring homomorphism out of a field). The definition is a map of underlying point sets only; no group-homomorphism property is asserted here.
--
--   Alongside it, a small auxiliary congruence statement `some_congr` records that for an affine Weierstrass curve $V$ over $k$ and coordinates $x_1,y_1,x_2,y_2$ in $k$ with $x_1 = x_2$ and $y_1 = y_2$, the points `Point.some x₁ y₁ h₁` and `Point.some x₂ y₂ h₂` are equal, for any two nonsingularity proofs $h_1$, $h_2$: the point depends only on its coordinates, the proof component being irrelevant.
--
--   **Relation to Mathlib.** The construction rests on Mathlib's base change `WeierstrassCurve.map` and on `WeierstrassCurve.Affine.map_nonsingular`; `ratPointMap` itself is the project's own name for the resulting map on affine point sets.
--
--   **Where it is used.** The map is used where points of a Weierstrass curve have to be transported along a homomorphism of the base field, for instance when comparing points of a curve with points of its base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_RatPointMap_probe.lean

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine

variable {F k : Type} [Field F] [Field k] (f : F →+* k) {W₀ : WeierstrassCurve F}

private theorem some_congr {V : Affine k} {x₁ y₁ x₂ y₂ : k} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

def ratPointMap : W₀.toAffine.Point → (W₀.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((W₀.toAffine.map_nonsingular f.injective x y).mpr h)

end WeierstrassCurve


