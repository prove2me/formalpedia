-- Prove2me | solution 1 for AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/23a7c8de-d2d2-5bde-82cc-79ceb7974abc

import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one

set_option autoImplicit false

universe u v

open IntermediateField

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [Algebra.EssFiniteType K F]
    [Algebra.Transcendental K F] (hΩ : Module.finrank F Ω[F⁄K] = 1) :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
  classical

  obtain ⟨t, ht⟩ : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by
    by_contra h
    push Not at h
    have htop : (⊤ : Submodule F Ω[F⁄K]) = ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
      rintro _ ⟨x, rfl⟩
      exact h x
    have h0 : Module.finrank F Ω[F⁄K] = 0 := by
      rw [← finrank_top, htop, finrank_bot]
    omega

  have hspan : ∀ ω : Ω[F⁄K], ∃ c : F, c • KaehlerDifferential.D K F t = ω :=
    (finrank_eq_one_iff_of_nonzero' _ ht).mp hΩ

  have hDt : KaehlerDifferential.D K⟮t⟯ F t = 0 := by
    have h := (KaehlerDifferential.D K⟮t⟯ F).map_algebraMap (AdjoinSimple.gen K t)
    rwa [AdjoinSimple.algebraMap_gen] at h
  have hsub : Subsingleton Ω[F⁄K⟮t⟯] := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    obtain ⟨ω₀, rfl⟩ := KaehlerDifferential.map_surjective K K⟮t⟯ F ω
    obtain ⟨c, rfl⟩ := hspan ω₀
    rw [map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply, hDt,
      smul_zero]

  haveI : Algebra.FormallyUnramified K⟮t⟯ F := ⟨hsub⟩
  haveI : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  have hsep : Algebra.IsSeparable K⟮t⟯ F := Algebra.FormallyUnramified.isSeparable K⟮t⟯ F
  have hfin : Module.Finite K⟮t⟯ F := Algebra.FormallyUnramified.finite_of_free K⟮t⟯ F

  refine ⟨t, ?_, hfin, hsep⟩
  show ¬IsAlgebraic K t
  intro halg
  haveI : Algebra.IsAlgebraic K K⟮t⟯ := isAlgebraic_adjoin_simple halg.isIntegral
  haveI : Algebra.IsAlgebraic K⟮t⟯ F := Algebra.IsAlgebraic.of_finite K⟮t⟯ F
  have hKF : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.trans (R := K) (S := K⟮t⟯) (A := F)
  exact Algebra.transcendental_iff_not_isAlgebraic.mp ‹Algebra.Transcendental K F› hKF

#print axioms solution

end S_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one (solution)
