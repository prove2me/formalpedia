-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
-- name    : ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:20.922929+00:00
-- url     : https://prove2.me/theorems/0c87b5da-c7ab-4535-aa23-b7c50e248b02
-- title:
--   Gal Smul As Ideal
-- statement:
--   Definitions and structural lemmas for Gal Smul As Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/SUnitGalois/GalSmulAsIdeal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField.SUnit
abbrev sUnits (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ :=
  (S : Set (HeightOneSpectrum (𝓞 K))).unit K
def unitsToSUnits (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (𝓞 K)ˣ →* sUnits K S :=
  (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).codRestrict (sUnits K S) fun x v _ => by
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuation_of_unit_eq]
    rfl
def valS (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnits K S →* (S → Multiplicative ℤ) :=
  MonoidHom.pi fun v => (HeightOneSpectrum.valuationOfNeZero (K := K) v.1).comp (sUnits K S).subtype
open scoped Pointwise in

instance galSmul (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L] :
    MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  smul σ v :=
    { asIdeal := σ • v.asIdeal
      isPrime := Ideal.IsPrime.smul σ
      ne_bot := by
        rw [Ideal.pointwise_smul_def, ne_eq,
          Ideal.map_eq_bot_iff_of_injective (MulAction.injective σ)]
        exact v.ne_bot }
  one_smul v := HeightOneSpectrum.ext (one_smul _ v.asIdeal)
  mul_smul σ τ v := HeightOneSpectrum.ext (mul_smul σ τ v.asIdeal)
def galUnits {K L : Type*} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L) : Lˣ →* Lˣ :=
  Units.map σ.toRingEquiv.toMonoidHom
end ReciprocityTheory.DiscreteGroups.GlobalClassField.SUnit
end


