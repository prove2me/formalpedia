-- Prove2me | Definitions.Def_RiemannMasullo_LocalAdditiveTamagawaMeasures
-- name    : RiemannMasullo_LocalAdditiveTamagawaMeasures
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T00:51:19.83598+00:00
-- url     : https://prove2.me/theorems/e1f3638b-121c-4d28-aca1-306b1875e207
-- title:
--   Normalized local additive Tamagawa measures
-- statement:
--   At the infinite places, use real Lebesgue measure or twice complex Lebesgue measure. At a finite place, scale additive Haar measure by the inverse square root of the local different norm divided by the Haar mass of the valuation ring.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec3.lean#L120-L151

import Mathlib
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
noncomputable section
namespace RiemannMasullo
open Function MeasureTheory NumberField IsDedekindDomain InfinitePlace.Completion Set
open scoped Classical ENNReal NNReal NumberField.AdeleRing Pointwise

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local instance (v : InfinitePlace F) : MeasurableSpace v.Completion := borel _
local instance (v : Primes(F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Primes(F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F) :=
  RiemannMasullo.locallyCompactSpace_adicCompletion v
local notation "differentExp(" F ", " v ")" =>
  multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))
local notation "differentMass(" F ", " v ")" =>
  Inv.inv (ENNReal.ofReal (Real.sqrt (Nat.cast (Ideal.absNorm (HeightOneSpectrum.asIdeal v)) ^
    differentExp(F, v))))
def infiniteLocalAdditiveTamagawaMeasure (v : InfinitePlace F) : Measure v.Completion :=
  if h : v.IsReal then
    Measure.map (ringEquivRealOfIsReal h).symm (volume : Measure ℝ)
  else
    Measure.map (ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm
      (2 • (volume : Measure ℂ))

def finiteLocalAdditiveTamagawaMeasure (v : Primes(F)) : Measure (v.adicCompletion F) :=
  let μ := Measure.addHaar (G := v.adicCompletion F)
  (differentMass(F, v) / μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) • μ
end RiemannMasullo


