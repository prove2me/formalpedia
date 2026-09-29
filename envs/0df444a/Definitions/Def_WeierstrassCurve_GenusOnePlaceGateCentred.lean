-- Prove2me | Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
-- name    : WeierstrassCurve_GenusOnePlaceGateCentred
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/0a00705d-5ab9-5688-8c10-6b5d796a42fa
-- title:
--   Centring condition for the genus-one place–point gate
-- statement:
--   Let $W$ be an affine Weierstrass curve over a field $F$, equipped with the gate class `GenusOnePlaceGate W`, which carries a bijection `pointEquivPlace` between the point group $W.\mathrm{Point}$ and the places of $W$'s function field over $F$ (all of residue degree one), and write `placeOfPoint` for this bijection. Here a place, in the project's sense, is a valuation subring of the function field that contains the image of $F$, is not the whole field, and is a principal ideal ring, hence a discrete valuation ring.
--
--   The module defines the `Prop`-valued mixin class `GenusOnePlaceGate.IsCentred W`, which adds no data and whose two fields express that the bijection attaches to each affine point a place centred at that point in coordinates. Explicitly: for all $x,y\in F$ and every proof `h` that $(x,y)$ is a nonsingular point of $W$, writing $v$ for the place `placeOfPoint (Point.some x y h)`, the field requires that the image in the function field, under the map from the coordinate ring of $W$, of the class `CoordinateRing.XClass W x` of $X - x$ lies in the non-units of the valuation subring of $v$, and likewise that the image of the class `CoordinateRing.YClass W (Polynomial.C y)` of $Y - y$ lies in the non-units of that valuation subring. Membership in the non-units of a valuation subring means valuation strictly less than $1$, that is, strictly positive order at $v$; so the maximal ideal of $v$ contains $X - x$ and $Y - y$.
--
--   Two lemmas, `algebraMap_XClass_mem_nonunits` and `algebraMap_YClass_mem_nonunits`, restate the two fields as standalone statements with $x$ and $y$ implicit.
--
--   **Relation to Mathlib.** The coordinate ring, the function field, `XClass`/`YClass`, `Nonsingular` and `Point.some` are Mathlib's notions for affine Weierstrass curves; the notion of a place of a function field used here (a valuation subring containing the constants, proper, and a principal ideal ring) and the gate classes relating points to places are the project's own.
--
--   **Where it is used.** The bijection carried by `GenusOnePlaceGate W` is a priori arbitrary, and the companion class `AbelTheorem W` constrains it only up to composition with an automorphism and a translation of the point group; requiring it to be centred at each affine point forces it to be the geometric dictionary, sending a point to the place of the function field it determines. This mixin is therefore assumed in those statements where the maps transported along the Abel–Jacobi identification `genusOnePic0Equiv` interact with coordinates — reduction of points, Frobenius on points, explicit isogeny formulae — rather than with the group structure alone.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_GenusOnePlaceGateCentred.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_GenusOnePic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F]

variable (W : Affine F) in

class GenusOnePlaceGate.IsCentred [GenusOnePlaceGate W] : Prop where

  XClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits

  YClass_mem_nonunits : ∀ (x y : F) (h : W.Nonsingular x y),
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits

namespace GenusOnePlaceGate.IsCentred

variable {W : Affine F} [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W]

theorem algebraMap_XClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  XClass_mem_nonunits x y h

theorem algebraMap_YClass_mem_nonunits {x y : F} (h : W.Nonsingular x y) :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ (placeOfPoint (Point.some x y h)).toValuationSubring.nonunits :=
  YClass_mem_nonunits x y h

end GenusOnePlaceGate.IsCentred

end WeierstrassCurve.Affine


