-- Prove2me | solution 1 for AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/991be2c4-66a7-5b40-a552-e2b0e95492c5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed

namespace B9

theorem natCard_algHom_eq_finrank (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]
    [Module.Finite K B] [IsReduced B] : Nat.card (B →ₐ[K] K) = Module.finrank K B := by
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _

  have hquot : ∀ I : MaximalSpectrum B, Module.finrank K (B ⧸ I.asIdeal) = 1 := by
    intro I
    letI : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite K (B ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
    haveI : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
    have hbij : Function.Bijective (algebraMap K (B ⧸ I.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ I.asIdeal)
    have e : K ≃ₗ[K] (B ⧸ I.asIdeal) :=
      LinearEquiv.ofBijective (Algebra.linearMap K (B ⧸ I.asIdeal)) hbij
    rw [← e.finrank_eq, Module.finrank_self]

  let e : B ≃ₐ[K] ((I : MaximalSpectrum B) → B ⧸ I.asIdeal) :=
    AlgEquiv.ofRingEquiv (f := IsArtinianRing.equivPi B) (fun r => by
      ext I
      rfl)

  have hfin : Module.finrank K B = Fintype.card (MaximalSpectrum B) := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [hquot]

  have hker_max : ∀ φ : B →ₐ[K] K, (RingHom.ker φ.toRingHom).IsMaximal := fun φ =>
    RingHom.ker_isMaximal_of_surjective φ.toRingHom (fun k => ⟨algebraMap K B k, by simp⟩)
  let kerMap : (B →ₐ[K] K) → MaximalSpectrum B := fun φ => ⟨RingHom.ker φ.toRingHom, hker_max φ⟩
  have hinj : Function.Injective kerMap := by
    intro φ ψ h
    have hk : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom := congrArg MaximalSpectrum.asIdeal h
    apply AlgHom.ext
    intro b

    have h1 : b - algebraMap K B (φ b) ∈ RingHom.ker ψ.toRingHom := by
      rw [← hk, RingHom.mem_ker]
      simp
    rw [RingHom.mem_ker] at h1
    have : ψ b - φ b = 0 := by
      simpa [map_sub, AlgHom.commutes] using h1
    linear_combination -this
  have hsurj : Function.Surjective kerMap := by
    intro I
    letI : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite K (B ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
    haveI : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
    have hbij : Function.Bijective (algebraMap K (B ⧸ I.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ I.asIdeal)

    let eI : K ≃ₐ[K] (B ⧸ I.asIdeal) := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ I.asIdeal)) hbij
    let φ : B →ₐ[K] K := (eI.symm : (B ⧸ I.asIdeal) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K I.asIdeal)
    refine ⟨φ, ?_⟩
    apply MaximalSpectrum.ext
    show RingHom.ker φ.toRingHom = I.asIdeal
    ext b
    rw [RingHom.mem_ker]
    show eI.symm (Ideal.Quotient.mk I.asIdeal b) = 0 ↔ b ∈ I.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_eq_zero_iff _ eI.symm.injective]
  haveI : Fintype (B →ₐ[K] K) := Fintype.ofFinite _
  rw [hfin, Nat.card_eq_fintype_card]
  exact Fintype.card_of_bijective ⟨hinj, hsurj⟩
end B9

theorem solution (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] : Nat.card (B →ₐ[K] K) = Module.finrank K B :=
  B9.natCard_algHom_eq_finrank K B

end S_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed
end P2MW
export P2MW.S_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed (solution)
