-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingIsomorphismTransportsPlaces
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingIsomorphismTransportsPlaces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:34.957847+00:00
-- url     : https://prove2.me/theorems/053a42e6-0628-4377-88f0-7ad90baed83d
-- title:
--   Ring Isomorphism Transports Places
-- statement:
--   Definitions and structural lemmas for Ring Isomorphism Transports Places, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RingIsomorphismTransportsPlaces.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
namespace GlobalTheory.CompanionTheory.PTIso.Places
variable {R S : Type} [CommRing R] [CommRing S]
theorem mem_iff_apply_mem_map (f : R ≃+* S) (I : Ideal R) (x : R) :
    x ∈ I ↔ f x ∈ I.map f := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · exact fun h => ⟨x, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [← f.injective e]
variable [IsDedekindDomain R] [IsDedekindDomain S]
noncomputable def placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) : HeightOneSpectrum S where
  asIdeal := v.asIdeal.map f
  isPrime := by
    haveI := v.isPrime
    exact Ideal.map_isPrime_of_equiv f
  ne_bot := by
    intro h
    apply v.ne_bot
    exact (Ideal.map_eq_bot_iff_of_injective f.injective).1 h
theorem placeMap_asIdeal (f : R ≃+* S) (v : HeightOneSpectrum R) :
    (placeMap f v).asIdeal = v.asIdeal.map f := rfl
theorem placeMap_symm_placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) :
    placeMap f.symm (placeMap f v) = v := by
  apply HeightOneSpectrum.ext
  rw [placeMap_asIdeal, placeMap_asIdeal, Ideal.map_symm]
  ext x
  rw [Ideal.mem_comap]
  exact (mem_iff_apply_mem_map f _ x).symm
noncomputable def placeEquiv (f : R ≃+* S) : HeightOneSpectrum R ≃ HeightOneSpectrum S where
  toFun := placeMap f
  invFun := placeMap f.symm
  left_inv := placeMap_symm_placeMap f
  right_inv := placeMap_symm_placeMap f.symm
end GlobalTheory.CompanionTheory.PTIso.Places


