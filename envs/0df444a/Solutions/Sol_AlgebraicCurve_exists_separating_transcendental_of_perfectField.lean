-- Prove2me | solution 1 for AlgebraicCurve.exists_separating_transcendental_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/792d0909-c16c-55f0-97a0-e8101b570ba7

import Mathlib
import Theorems.Thm_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental
import Theorems.Thm_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_separating_transcendental_of_perfectField

open IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "finrank_frobeniusSubfield_eq_of_transcendental"
namespace SeparatingTranscendentalOfPerfectField
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isTranscendenceBasis_of_transcendental {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) : IsTranscendenceBasis K (fun _ : Fin 1 => x) := by
  have hind : AlgebraicIndependent K (fun _ : Fin 1 => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  refine hind.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  have hr : Set.range (fun _ : Fin 1 => x) = ({x} : Set F) := by
    ext y
    simp [eq_comm]
  rw [hr, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  haveI := hfd
  exact Algebra.IsAlgebraic.of_finite K⟮x⟯ F

theorem isAlgebraic_adjoin_of_transcendental {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic K⟮t⟯ F := by
  classical
  have htind : AlgebraicIndepOn K id ({t} : Set F) := by
    refine algebraicIndependent_unique_type_iff.mpr ?_
    simpa using ht
  obtain ⟨s, hts, hbasis⟩ := exists_isTranscendenceBasis_superset htind
  have hcard := hbasis.lift_cardinalMk_eq (isTranscendenceBasis_of_transcendental hx hfd)
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hsub : s.Subsingleton := Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le
  have hseq : s = {t} := hsub.eq_singleton_of_mem (hts rfl)
  subst hseq
  have h := hbasis.isAlgebraic_field
  rwa [Subtype.range_coe] at h

theorem finiteDimensional_adjoin_of_transcendental {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) {t : F} (ht : Transcendental K t) :
    FiniteDimensional K⟮t⟯ F := by
  classical
  haveI := hfd
  have halg : Algebra.IsAlgebraic K⟮t⟯ F := isAlgebraic_adjoin_of_transcendental hx hfd ht

  obtain ⟨s, hs⟩ := Module.finite_def.mp hfd
  set E : IntermediateField K⟮t⟯ F :=
    IntermediateField.adjoin K⟮t⟯ (insert x (↑s : Set F)) with hE
  have hxE : x ∈ E := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)

  have hrange : ∀ r : K⟮x⟯, (r : F) ∈ E := by
    intro r
    have hle : K⟮x⟯ ≤ E.restrictScalars K :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ((IntermediateField.mem_restrictScalars K).mpr hxE)
    exact (IntermediateField.mem_restrictScalars K).mp (hle r.2)

  have hmem : ∀ y : F, y ∈ E := by
    intro y
    have hy : y ∈ Submodule.span K⟮x⟯ (↑s : Set F) := by
      rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction (fun z hz => ?_) ?_ (fun z w _ _ hz hw => ?_)
      (fun r z _ hz => ?_) hy
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hz)
    · exact zero_mem E
    · exact add_mem hz hw
    · rw [Algebra.smul_def]
      exact mul_mem (hrange r) hz
  have htop : E = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hmem y

  haveI : Finite ↥(insert x (↑s : Set F)) :=
    Set.Finite.to_subtype ((s.finite_toSet).insert x)
  have hfdE : FiniteDimensional K⟮t⟯ ↥E := by
    rw [hE]
    exact IntermediateField.finiteDimensional_adjoin
      (fun z _ => (halg.isAlgebraic z).isIntegral)
  rw [htop] at hfdE
  haveI := hfdE
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := K⟮t⟯) (E := F)).toLinearEquiv

theorem transcendental_of_not_mem_fieldRange_frobenius [PerfectField K] (p : ℕ)
    [Fact p.Prime] [CharP K p] [CharP F p] {t : F} (ht : t ∉ (frobenius F p).fieldRange) :
    Transcendental K t := by
  intro halg
  apply ht
  haveI : Algebra.IsAlgebraic K K⟮t⟯ :=
    IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  haveI : PerfectField K⟮t⟯ := Algebra.IsAlgebraic.perfectField (K := K)
  haveI : CharP K⟮t⟯ p := charP_of_injective_algebraMap (algebraMap K K⟮t⟯).injective p
  obtain ⟨s, hs⟩ := surjective_frobenius K⟮t⟯ p ⟨t, mem_adjoin_simple_self K t⟩
  refine RingHom.mem_fieldRange.mpr ⟨(s : F), ?_⟩
  have h := congrArg (fun u : K⟮t⟯ => (u : F)) hs
  simpa [frobenius_def] using h

theorem exists_separating [PerfectField K] {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
  classical
  haveI := hfd
  obtain h0 | ⟨p, hp, hchar⟩ := CharP.exists' K
  ·
    haveI : CharZero K⟮x⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮x⟯).injective
    haveI : Algebra.IsAlgebraic K⟮x⟯ F := Algebra.IsAlgebraic.of_finite K⟮x⟯ F
    exact ⟨x, hx, hfd, Algebra.IsAlgebraic.isSeparable_of_perfectField⟩
  ·
    haveI := hp
    haveI := hchar
    haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p

    have hdeg : Module.finrank (frobenius F p).fieldRange F = p :=
      AlgebraicCurve.finrank_frobeniusSubfield_eq_of_transcendental p x hx

    have hnle : ¬ ((⊤ : Subfield F) ≤ (frobenius F p).fieldRange) := by
      intro hle
      have h1 : Module.finrank (frobenius F p).fieldRange F = 1 := by
        rw [← Subfield.relfinrank_top_right, Subfield.relfinrank_eq_one_iff]
        exact hle
      exact hp.out.one_lt.ne (h1.symm.trans hdeg)
    obtain ⟨t, -, ht⟩ := SetLike.not_le_iff_exists.mp hnle

    have httr : Transcendental K t := transcendental_of_not_mem_fieldRange_frobenius p ht
    have htfd : FiniteDimensional K⟮t⟯ F :=
      finiteDimensional_adjoin_of_transcendental hx hfd httr
    haveI := htfd
    have hsep : Algebra.IsSeparable K⟮t⟯ F :=
      Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq p hdeg
        (⟨t, mem_adjoin_simple_self K t⟩ : K⟮t⟯) ht
    exact ⟨t, httr, htfd, hsep⟩

end AlgebraicCurve.SeparatingTranscendentalOfPerfectField

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
  AlgebraicCurve.SeparatingTranscendentalOfPerfectField.exists_separating htr hfd

end S_AlgebraicCurve_exists_separating_transcendental_of_perfectField
end P2MW
export P2MW.S_AlgebraicCurve_exists_separating_transcendental_of_perfectField (solution)
