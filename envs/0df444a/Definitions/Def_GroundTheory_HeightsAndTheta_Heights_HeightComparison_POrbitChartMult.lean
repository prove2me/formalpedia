-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:23:36.864828+00:00
-- url     : https://prove2.me/theorems/aa78e37e-1f05-46db-b89d-ad7a857984b0
-- title:
--   POrbit Chart Mult
-- statement:
--   Definitions and structural lemmas for POrbit Chart Mult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
namespace OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
section General
variable {O : Type*} [CommRing O] [IsDomain O]
omit [IsDomain O] in

abbrev fibO (ι : Type) (m : Ideal O) : Ideal (MvPolynomial ι O) := Ideal.map C m
omit [IsDomain O] in
instance fibO_isPrime (ι : Type) (m : Ideal O) [m.IsPrime] : (fibO ι m).IsPrime := by
  have h : fibO ι m = RingHom.ker (map (Ideal.Quotient.mk m) :
      MvPolynomial ι O →+* MvPolynomial ι (O ⧸ m)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [h]
  exact RingHom.ker_isPrime _
omit [IsDomain O] in

abbrev locB (ι : Type) (m : Ideal O) [m.IsPrime] := Localization.AtPrime (fibO ι m)
omit [IsDomain O] in

abbrev betaB (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O) (m : Ideal O) [m.IsPrime] :
    MvPolynomial (Coord n) ℤ →+* locB ι m :=
  (algebraMap (MvPolynomial ι O) (locB ι m)).comp γ
variable {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]
end General
section Abstract
variable {R B : Type*} [CommRing R] [CommRing B]
end Abstract
section General2
variable {O : Type*} [CommRing O] [IsDomain O]
  {Fε : Type*} [FunLike Fε (MvPolynomial (Coord n) ℤ) O]
  [RingHomClass Fε (MvPolynomial (Coord n) ℤ) O] (ε : Fε)
  (γ : MvPolynomial (Coord n) ℤ →+* MvPolynomial ι O)
  (hγ : ∀ {F : MvPolynomial (Coord n) ℤ} {d : ι → ℕ}, IsWeightedHomogeneous (coordDeg n) F d →
    γ F = C (ε F) * ∏ k, X k ^ d k)
  (V : Ideal (MvPolynomial (Coord n) ℤ)) [(V.map ε).IsPrime]
end General2
end OrbitChartMult
end
end GroundTheory.Heights₂.Heights


