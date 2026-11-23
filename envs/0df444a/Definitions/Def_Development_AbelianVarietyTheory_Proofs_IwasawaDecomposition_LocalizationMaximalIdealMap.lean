-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationMaximalIdealMap
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationMaximalIdealMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:39.709469+00:00
-- url     : https://prove2.me/theorems/756df4ff-e819-4378-998f-8556b3760e77
-- title:
--   Localization Maximal Ideal Map
-- statement:
--   Definitions and structural lemmas for Localization Maximal Ideal Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationMaximalIdealMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
namespace GlobalTheory
theorem exists_mul_mem_map_maximalIdeal_of_formallyUnramified_quotient
    (B S : Type) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S]
    (J q : Ideal S) [q.IsMaximal]
    (hJ : J ≤ (maximalIdeal B).map (algebraMap B S))
    (hq : (maximalIdeal B).map (algebraMap B S) ≤ q)
    (hU : Algebra.FormallyUnramified B (S ⧸ J)) (hF : Module.Finite B (S ⧸ J))
    (y : S) (hy : y ∈ q) :
    ∃ t : S, t ∉ q ∧ t * y ∈ (maximalIdeal B).map (algebraMap B S) := by
  have hJq : J ≤ q := hJ.trans hq
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ q := by rwa [Ideal.mk_ker]
  let qb : Ideal (S ⧸ J) := q.map (Ideal.Quotient.mk J)
  haveI hqb : qb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : ∀ s : S, Ideal.Quotient.mk J s ∈ qb → s ∈ q := by
    intro s hs
    have : s ∈ qb.comap (Ideal.Quotient.mk J) := hs
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hker] at this
  let D := Localization.AtPrime qb
  haveI : Algebra.FormallyUnramified (S ⧸ J) D := .of_isLocalization qb.primeCompl
  haveI : Algebra.FormallyUnramified B D := .comp B (S ⧸ J) D
  haveI : Algebra.EssFiniteType (S ⧸ J) D := .of_isLocalization D qb.primeCompl
  haveI : Algebra.EssFiniteType B (S ⧸ J) := inferInstance
  haveI : Algebra.EssFiniteType B D := .comp B (S ⧸ J) D
  have hBD : ∀ b : B, algebraMap B D b =
      algebraMap (S ⧸ J) D (Ideal.Quotient.mk J (algebraMap B S b)) := fun b => by
    rw [IsScalarTower.algebraMap_apply B (S ⧸ J) D]; rfl
  have hmem : ∀ b ∈ maximalIdeal B, algebraMap B D b ∈ maximalIdeal D := by
    intro b hb
    rw [hBD, IsLocalization.AtPrime.to_map_mem_maximal_iff D qb]
    exact Ideal.mem_map_of_mem _ (hq (Ideal.mem_map_of_mem _ hb))
  haveI : IsLocalHom (algebraMap B D) := ⟨fun b hb => by
    by_contra hnu
    exact (mem_maximalIdeal _).1 (hmem b ((mem_maximalIdeal _).2 hnu)) hb⟩
  have hmax : (maximalIdeal B).map (algebraMap B D) = maximalIdeal D :=
    Algebra.FormallyUnramified.map_maximalIdeal
  let I := (maximalIdeal B).map (algebraMap B S)
  have hmapD : (maximalIdeal B).map (algebraMap B D) =
      (I.map (Ideal.Quotient.mk J)).map (algebraMap (S ⧸ J) D) := by
    simp only [I, Ideal.map_map]
    congr 1
  have hyD : algebraMap (S ⧸ J) D (Ideal.Quotient.mk J y) ∈
      (I.map (Ideal.Quotient.mk J)).map (algebraMap (S ⧸ J) D) := by
    rw [← hmapD, hmax, IsLocalization.AtPrime.to_map_mem_maximal_iff D qb]
    exact Ideal.mem_map_of_mem _ hy
  obtain ⟨⟨a, s⟩, has⟩ := (IsLocalization.mem_map_algebraMap_iff qb.primeCompl D).1 hyD
  simp only at has
  rw [← map_mul] at has
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists qb.primeCompl D).1 has
  obtain ⟨a', ha', haa⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 a.2
  obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : S ⧸ J)
  obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (c : S ⧸ J)
  refine ⟨c' * s', ?_, ?_⟩
  · intro hmul
    rcases (inferInstance : q.IsPrime).mem_or_mem hmul with h | h
    · exact c.2 (hc' ▸ Ideal.mem_map_of_mem _ h)
    · exact s.2 (hs' ▸ Ideal.mem_map_of_mem _ h)
  · have hdiff : c' * (y * s') - c' * a' ∈ J := by
      rw [← Ideal.Quotient.eq, map_mul, map_mul, map_mul, hc', hs', haa]
      exact hc
    have h1 : c' * s' * y = (c' * (y * s') - c' * a') + c' * a' := by ring
    rw [h1]
    exact I.add_mem (hJ hdiff) (I.mul_mem_left _ ha')
theorem map_maximalIdeal_localization_eq_of_formallyUnramified_quotient
    (B S : Type) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S]
    (J q : Ideal S) [q.IsMaximal]
    (hJ : J ≤ (maximalIdeal B).map (algebraMap B S))
    (hq : (maximalIdeal B).map (algebraMap B S) ≤ q)
    (hU : Algebra.FormallyUnramified B (S ⧸ J)) (hF : Module.Finite B (S ⧸ J)) :
    (maximalIdeal B).map ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S)) =
      maximalIdeal (Localization.AtPrime q) := by
  let C := Localization.AtPrime q
  have hK : (maximalIdeal B).map ((algebraMap S C).comp (algebraMap B S)) =
      ((maximalIdeal B).map (algebraMap B S)).map (algebraMap S C) := by
    rw [Ideal.map_map]
  rw [hK, ← Localization.AtPrime.map_eq_maximalIdeal]
  refine le_antisymm (Ideal.map_mono hq) (Ideal.map_le_iff_le_comap.2 fun y hy => ?_)
  obtain ⟨t, ht, hty⟩ :=
    exists_mul_mem_map_maximalIdeal_of_formallyUnramified_quotient B S J q hJ hq hU hF y hy
  have htu : IsUnit (algebraMap S C t) :=
    IsLocalization.map_units C (⟨t, ht⟩ : q.primeCompl)
  have h2 := Ideal.mem_map_of_mem (algebraMap S C) hty
  rw [map_mul] at h2
  exact (Ideal.unit_mul_mem_iff_mem _ htu).1 h2
example : ∀ (B S : Type) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ (IsLocalRing.maximalIdeal B).map (algebraMap B S) → (IsLocalRing.maximalIdeal B).map (algebraMap B S) ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → (IsLocalRing.maximalIdeal B).map ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S)) = IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
  @map_maximalIdeal_localization_eq_of_formallyUnramified_quotient
end GlobalTheory


