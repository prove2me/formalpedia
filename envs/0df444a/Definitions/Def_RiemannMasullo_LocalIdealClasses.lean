-- Prove2me | Definitions.Def_RiemannMasullo_LocalIdealClasses
-- name    : RiemannMasullo_LocalIdealClasses
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T01:55:15.314568+00:00
-- url     : https://prove2.me/theorems/48099ea5-abd9-4e2a-88c7-302548ab2f41
-- title:
--   Sec1
-- statement:
--   Definitions and structural lemmas for Sec1, from Ryan McCorvie and RiemannMasullo contributors; manuscript by Alessandro Maria Masullo's pinned Masullo formalization: partial supporting library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/1d230a0b2ed5968e8c5134784934df4e8a8521b8/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean

module
public import Mathlib
set_option autoImplicit false
@[expose] public section
@[expose] public section
noncomputable section
namespace RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
section PicardGroups
open scoped Classical
local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (Primes(F))) F
local notation "LocalClass(" F ", " v ")" =>
  (HeightOneSpectrum.adicCompletion F v)ˣ ⧸ Submonoid.units (Submonoid.ofClass (HeightOneSpectrum.adicCompletionIntegers F v))
def sUnitLocalClasses (T D : Finset (Primes(F))) :
    (T : Set (Primes(F))).unit F →* ((v : D) → LocalClass(F, v.val)) :=
  MonoidHom.pi fun v ↦ (QuotientGroup.mk' (v.val.adicCompletionIntegers F).units).comp
    ((Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom).comp
      ((T : Set (Primes(F))).unit F).subtype)
def localIdealClass (v : Primes(F)) (x : (v.adicCompletion F)ˣ) : CommRing.Pic (𝓞 F) :=
  (ClassGroup.equivPic (𝓞 F) (ClassGroup.mk0
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) ^ (-WithZero.log (Valued.v x.val))
end PicardGroups
end RiemannMasullo


