-- Prove2me | Definitions.Def_MazurTransfer_Order13IntegralBaseAndFieldMaps
-- name    : MazurTransfer_Order13IntegralBaseAndFieldMaps
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:01:09.509021+00:00
-- url     : https://prove2.me/theorems/7985a13d-a633-4d40-8155-ae6ab97c0968
-- title:
--   The integral base ring Z[1/104] and its specified maps to admissible rings
-- statement:
--   Let $B=\mathbb Z[1/104]$. The element $104$ is a unit in $B$. For every commutative ring $K$ in which $104$ is invertible, the specified localization construction gives a ring homomorphism $$B\longrightarrow K.$$ These are the actual integral base and scalar maps used by the order-thirteen Picard family, including its rational and mod-3/mod-5 fibres.
-- source:
--   MazurTheorem Order13CurveOverIntegersWith104Inverted.lean and Order13IntegralCurveRationalAndFiniteFieldFibres.lean, Apache-2.0, Vas and contributors. Exactly three original declarations BaseRing, unit104 and mapToRing are retained with their bodies unchanged, using authoritative complete frontend declaration and namespace ranges. Unneeded curve geometry and separate fibre-existence proofs are omitted. All three original complete closed types and both data construction values are kernel-compared; native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: canonical rational and finite-field scalar maps and the same integral Picard family’s finite fibres.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal smooth integral curve over Z[1/104].
Named downstream consumer: identifying the rational and finite-field fibres
of this actual family for compatible Picard good reduction.
This proves smoothness, flatness and local finite presentation; properness
and fibre compatibility are separate conclusions still to be constructed.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.Order13IntegralBase
open CategoryTheory AlgebraicGeometry

abbrev BaseRing := Localization.Away (104 : ℤ)

theorem unit104 : IsUnit (104 : BaseRing) := by
  simpa only [map_ofNat] using
    (IsLocalization.Away.algebraMap_isUnit (S := BaseRing) (104 : ℤ))




/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: genuine rational and finite-field fibres of the actual
smooth curve over Z[1/104]. Named downstream consumer: the compatible
integral Picard family and torsion specialization at primes three and five.
Integral properness, a Picard family, and torsion injectivity are separate.
-/

def mapToRing (K : Type) [CommRing K] (h : IsUnit (104 : K)) : BaseRing →+* K :=
  IsLocalization.Away.lift (104 : ℤ) (g := Int.castRingHom K) (by simpa only [map_ofNat] using h)

end MazurTransfer.Order13IntegralBase




#print axioms MazurTransfer.Order13IntegralBase.BaseRing
#print axioms MazurTransfer.Order13IntegralBase.unit104
#print axioms MazurTransfer.Order13IntegralBase.mapToRing


