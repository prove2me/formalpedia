-- Prove2me | solution 1 for Algebra.isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a079d97b-b3dc-5ba2-8ad7-8d859d413fd1

import Mathlib
import Theorems.Thm_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v w

namespace S42D4

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in

theorem formallyUnramified_of_isReduced (k : Type u) [Field k] [PerfectField k]
    (A : Type w) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A] :
    Algebra.FormallyUnramified k A := by
  haveI : IsArtinianRing A := isArtinian_of_tower k (inferInstance : IsArtinian k A)

  let e : A ≃ₐ[k] ((I : MaximalSpectrum A) → A ⧸ I.asIdeal) := (IsArtinianRing.equivPi A).restrictScalars k
  haveI : ∀ I : MaximalSpectrum A, Algebra.FormallyUnramified k (A ⧸ I.asIdeal) := by
    intro I
    haveI : Module.Finite k (A ⧸ I.asIdeal) := inferInstance
    haveI : Algebra.IsAlgebraic k (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite k _
    haveI : Algebra.IsSeparable k (A ⧸ I.asIdeal) := inferInstance
    exact Algebra.FormallyUnramified.of_isSeparable k (A ⧸ I.asIdeal)
  exact Algebra.FormallyUnramified.of_equiv e.symm

theorem isReduced_baseChange (k : Type u) [Field k] [PerfectField k]
    (K : Type v) [Field K] [Algebra k K]
    (A : Type w) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A] :
    IsReduced (K ⊗[k] A) := by
  haveI := formallyUnramified_of_isReduced k A
  haveI : Algebra.FormallyUnramified K (K ⊗[k] A) := inferInstance
  haveI : Algebra.EssFiniteType K (K ⊗[k] A) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[k] A)

theorem natCard_eq_of_isReduced (k : Type u) [Field k] [PerfectField k]
    (K : Type v) [Field K] [Algebra k K] [IsAlgClosed K]
    (A : Type w) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A] :
    Nat.card (A →ₐ[k] K) = Module.finrank k A := by
  haveI := isReduced_baseChange k K A
  rw [Nat.card_congr (AlgHom.liftEquiv k K A K), AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed K (K ⊗[k] A),
    Module.finrank_baseChange]

def liftRed (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]
    (A : Type w) [CommRing A] [Algebra k A] :
    (A →ₐ[k] K) ≃ (A ⧸ nilradical A →ₐ[k] K) where
  toFun f := Ideal.Quotient.liftₐ (nilradical A) f fun a ha => by
    obtain ⟨n, hn⟩ := ha
    exact IsReduced.eq_zero (f a) ⟨n, by rw [← map_pow, hn, map_zero]⟩
  invFun g := g.comp (Ideal.Quotient.mkₐ k (nilradical A))
  left_inv f := by ext a; rfl
  right_inv g := by
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

end S42D4

open S42D4 in
theorem solution
    (k : Type u) [Field k] [PerfectField k]
    (K : Type v) [Field K] [Algebra k K] [IsAlgClosed K]
    (A : Type w) [CommRing A] [Algebra k A] [Module.Finite k A] :
    IsReduced A ↔ Nat.card (A →ₐ[k] K) = Module.finrank k A := by
  constructor
  · intro hA
    exact natCard_eq_of_isReduced k K A
  · intro hcount

    haveI : IsReduced (A ⧸ nilradical A) := (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical (⊥ : Ideal A))
    have h1 : Nat.card (A →ₐ[k] K) = Module.finrank k (A ⧸ nilradical A) := by
      rw [Nat.card_congr (liftRed k K A)]
      exact natCard_eq_of_isReduced k K (A ⧸ nilradical A)

    have h2 : Module.finrank k ((nilradical A).restrictScalars k) = 0 := by
      have := Submodule.finrank_quotient_add_finrank ((nilradical A).restrictScalars k)
      have h3 : Module.finrank k (A ⧸ (nilradical A).restrictScalars k) = Module.finrank k (A ⧸ nilradical A) := rfl
      omega
    rw [← nilradical_eq_bot_iff]
    have h4 : (nilradical A).restrictScalars k = ⊥ := Submodule.finrank_eq_zero.1 h2
    exact (Submodule.restrictScalars_eq_bot_iff k A A).1 h4

end S_Algebra_isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed
end P2MW
export P2MW.S_Algebra_isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed (solution)
