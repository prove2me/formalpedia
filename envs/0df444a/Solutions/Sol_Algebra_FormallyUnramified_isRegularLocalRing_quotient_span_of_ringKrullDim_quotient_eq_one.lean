-- Prove2me | solution 1 for Algebra.FormallyUnramified.isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/922df395-bb6f-531d-84c6-2968c6957d3b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallyUnramified_isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one

set_option autoImplicit false

universe u

open IsLocalRing

namespace OrdRegL67

theorem map_mk_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    haveI := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (maximalIdeal R).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [sup_eq_left.mpr (le_maximalIdeal hI)]

end OrdRegL67

open OrdRegL67 IsLocalRing in
theorem solution
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (ϖ : R) (hR : IsRegularLocalRing (R ⧸ Ideal.span {ϖ})) (hR1 : ringKrullDim (R ⧸ Ideal.span {ϖ}) = 1)
    (hS1 : ringKrullDim (S ⧸ Ideal.span {algebraMap R S ϖ}) = 1) :
    IsRegularLocalRing (S ⧸ Ideal.span {algebraMap R S ϖ}) := by
  classical

  have hIR : Ideal.span {ϖ} ≠ ⊤ := by
    intro h
    haveI : Subsingleton (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.subsingleton_iff.mpr h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hR1
    exact absurd hR1 (by decide)
  have hIS : Ideal.span {algebraMap R S ϖ} ≠ ⊤ := by
    intro h
    haveI : Subsingleton (S ⧸ Ideal.span {algebraMap R S ϖ}) := Ideal.Quotient.subsingleton_iff.mpr h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hS1
    exact absurd hS1 (by decide)
  haveI : Nontrivial (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.nontrivial_iff.mpr hIR
  haveI : Nontrivial (S ⧸ Ideal.span {algebraMap R S ϖ}) := Ideal.Quotient.nontrivial_iff.mpr hIS
  haveI := IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {algebraMap R S ϖ})) Ideal.Quotient.mk_surjective

  haveI := hR
  have hsr : (maximalIdeal (R ⧸ Ideal.span {ϖ})).spanFinrank = 1 := by
    have h := hR.spanFinrank_maximalIdeal
    rw [hR1] at h
    have h' : ((maximalIdeal (R ⧸ Ideal.span {ϖ})).spanFinrank : WithBot ℕ∞) = ((1 : ℕ) : WithBot ℕ∞) := by
      rw [h]; rfl
    exact_mod_cast h'
  obtain ⟨s, hscard, hsspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (R ⧸ Ideal.span {ϖ})))
  rw [hsr, Finset.card_eq_one] at hscard
  obtain ⟨tbar, rfl⟩ := hscard
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective tbar
  rw [Finset.coe_singleton] at hsspan

  have hmR : maximalIdeal R = Ideal.span {ϖ, t} := by
    have hmap := map_mk_maximalIdeal (Ideal.span {ϖ}) hIR
    have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {ϖ}))) hmap
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (le_maximalIdeal hIR)] at hcomap
    rw [hcomap, ← hsspan]
    have hspan : (Submodule.span (R ⧸ Ideal.span {ϖ}) {Ideal.Quotient.mk (Ideal.span {ϖ}) t} : Ideal (R ⧸ Ideal.span {ϖ})) =
        (Ideal.span {t}).map (Ideal.Quotient.mk (Ideal.span {ϖ})) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hspan, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      Set.insert_eq, Ideal.span_union, sup_comm]

  have hmS : maximalIdeal S = Ideal.span {algebraMap R S ϖ, algebraMap R S t} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S), hmR, Ideal.map_span, Set.image_pair]

  have hmQ : maximalIdeal (S ⧸ Ideal.span {algebraMap R S ϖ}) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {algebraMap R S ϖ}) (algebraMap R S t)} := by
    have h0 : Ideal.Quotient.mk (Ideal.span {algebraMap R S ϖ}) (algebraMap R S ϖ) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [← map_mk_maximalIdeal (Ideal.span {algebraMap R S ϖ}) hIS, hmS, Ideal.map_span, Set.image_pair, h0,
      Ideal.span_insert_zero]
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [hS1, hmQ]
  have := Submodule.spanFinrank_span_le_ncard_of_finite (R := S ⧸ Ideal.span {algebraMap R S ϖ})
    (M := S ⧸ Ideal.span {algebraMap R S ϖ}) (Set.finite_singleton (Ideal.Quotient.mk (Ideal.span {algebraMap R S ϖ}) (algebraMap R S t)))
  rw [Set.ncard_singleton] at this
  exact_mod_cast this

end S_Algebra_FormallyUnramified_isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one
end P2MW
export P2MW.S_Algebra_FormallyUnramified_isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one (solution)
