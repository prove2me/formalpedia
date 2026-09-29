-- Prove2me | solution 1 for Algebra.FormallySmooth.quotient_span_singleton_of_existsUnique_eq_smul_D
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3e06f629-cf85-5b14-b39d-c4edf7816b33

import Mathlib
import Theorems.Thm_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallySmooth_quotient_span_singleton_of_existsUnique_eq_smul_D

set_option autoImplicit false

open Polynomial

theorem solution
    {A : Type} [CommRing A] {S : Type} [CommRing S] [Algebra A S] [Algebra.FormallySmooth A S]
    (t : S) (hdt : ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    Algebra.FormallySmooth A (S ⧸ Ideal.span ({t} : Set S)) := by
  classical
  set J : Ideal S := Ideal.span ({t} : Set S) with hJ

  have hinst : (algebraMap A S).toAlgebra = ‹Algebra A S› := Algebra.algebra_ext _ _ (fun _ => rfl)
  have hi : (algebraMap A S).FormallySmooth := RingHom.formallySmooth_algebraMap.mpr ‹_›
  have hdt' : letI : Algebra A S := (algebraMap A S).toAlgebra;
      ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • KaehlerDifferential.D A S t := by
    rw [hinst]; exact hdt
  obtain ⟨hfs, -⟩ := RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
    (algebraMap A S) hi t hdt'

  let e : Polynomial A →+* S := Polynomial.eval₂RingHom (algebraMap A S) t
  letI algXS : Algebra (Polynomial A) S := e.toAlgebra
  haveI : IsScalarTower A (Polynomial A) S := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A S a = e (Polynomial.C a)
    simp [e, Polynomial.eval₂RingHom])
  haveI hFS : Algebra.FormallySmooth (Polynomial A) S := hfs
  have heX : algebraMap (Polynomial A) S Polynomial.X = t := by
    show e Polynomial.X = t; simp [e, Polynomial.eval₂RingHom]

  refine Algebra.FormallySmooth.of_comp_surjective ?_
  intro B _ _ I hI g

  letI algXB : Algebra (Polynomial A) B := (Polynomial.aeval (0 : B)).toRingHom.toAlgebra
  haveI : IsScalarTower A (Polynomial A) B := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A B a = (Polynomial.aeval (0 : B)) (Polynomial.C a)
    simp)
  have hXB : algebraMap (Polynomial A) B Polynomial.X = 0 := by
    show (Polynomial.aeval (0 : B)) Polynomial.X = 0; simp

  have hcomm : ∀ p : Polynomial A,
      g (Ideal.Quotient.mk J (algebraMap (Polynomial A) S p)) = Ideal.Quotient.mk I (algebraMap (Polynomial A) B p) := by
    intro p
    have h1 : Ideal.Quotient.mk J (algebraMap (Polynomial A) S p) = algebraMap A (S ⧸ J) (p.coeff 0) := by
      show Ideal.Quotient.mk J (Polynomial.eval₂ (algebraMap A S) t p) = _
      rw [Polynomial.hom_eval₂, show Ideal.Quotient.mk J t = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl), Polynomial.eval₂_at_zero]
      rfl
    have h2 : algebraMap (Polynomial A) B p = algebraMap A B (p.coeff 0) := by
      show (Polynomial.aeval (0 : B)) p = _
      rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    rw [h1, h2, AlgHom.commutes]; rfl
  let g' : S →ₐ[Polynomial A] B ⧸ I :=
    { toRingHom := g.toRingHom.comp (Ideal.Quotient.mk J)
      commutes' := fun p => by
        show g (Ideal.Quotient.mk J (algebraMap (Polynomial A) S p)) = Ideal.Quotient.mk I (algebraMap (Polynomial A) B p)
        exact hcomm p }
  obtain ⟨h, hh⟩ := Algebra.FormallySmooth.comp_surjective (Polynomial A) S I hI g'
  have hht : h t = 0 := by rw [← heX, AlgHom.commutes, hXB]
  have hker : ∀ j ∈ J, (h.restrictScalars A) j = 0 := by
    intro j hj
    rw [hJ, Ideal.mem_span_singleton] at hj
    obtain ⟨s, rfl⟩ := hj
    show h (t * s) = 0
    rw [map_mul, hht, zero_mul]
  let hbar : (S ⧸ J) →ₐ[A] B := Ideal.Quotient.liftₐ J (h.restrictScalars A) hker
  refine ⟨hbar, ?_⟩
  apply AlgHom.ext
  intro x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  show Ideal.Quotient.mk I (hbar (Ideal.Quotient.mk J s)) = g (Ideal.Quotient.mk J s)
  have : hbar (Ideal.Quotient.mk J s) = h s := rfl
  rw [this]
  exact congrArg (fun φ : S →ₐ[Polynomial A] B ⧸ I => φ s) hh

end S_Algebra_FormallySmooth_quotient_span_singleton_of_existsUnique_eq_smul_D
end P2MW
export P2MW.S_Algebra_FormallySmooth_quotient_span_singleton_of_existsUnique_eq_smul_D (solution)
