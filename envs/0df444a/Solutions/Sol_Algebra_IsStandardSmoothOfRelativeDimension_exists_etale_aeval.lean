-- Prove2me | solution 1 for Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1328c172-7756-5098-8488-c14db776d3c5

import Mathlib
import Theorems.Thm_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
import Theorems.Thm_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_exists_etale_aeval

set_option autoImplicit false

open MvPolynomial

namespace FrobRankC3

attribute [local instance] Fintype.ofFinite

theorem main {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ x : Fin n → S, (MvPolynomial.aeval x : MvPolynomial (Fin n) R →ₐ[R] S).toRingHom.Etale := by
  classical

  have hA : Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
    have := MvPolynomial.isStandardSmoothOfRelativeDimension_natCard R (Fin n)
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  rcases subsingleton_or_nontrivial S with hS | hS
  · refine ⟨fun _ => 0, ?_⟩
    letI : Algebra (MvPolynomial (Fin n) R) S :=
      (MvPolynomial.aeval (fun _ => (0 : S)) : MvPolynomial (Fin n) R →ₐ[R] S).toRingHom.toAlgebra
    change Algebra.Etale (MvPolynomial (Fin n) R) S
    infer_instance

  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension n R S›
  let τ : Set ι := (Set.range P.map)ᶜ
  have hτ : Fintype.card τ = n := by
    rw [← hP]
    simp only [τ, Fintype.card_compl_set, Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
      Set.card_range_of_injective P.map_inj]
  let e : Fin n ≃ τ := (Fintype.equivFinOfCardEq hτ).symm
  let x : Fin n → S := fun j => P.val (e j : ι)
  refine ⟨x, ?_⟩
  set A := MvPolynomial (Fin n) R with hAdef
  letI : Algebra A S := (MvPolynomial.aeval x : A →ₐ[R] S).toRingHom.toAlgebra
  have halg : ∀ a : A, algebraMap A S a = MvPolynomial.aeval x a := fun _ => rfl
  haveI : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  change Algebra.Etale A S

  have hrange : LinearMap.range (KaehlerDifferential.mapBaseChange R A S) = ⊤ := by
    rw [eq_top_iff, ← P.basisKaehler.span_eq, Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    refine ⟨(1 : S) ⊗ₜ KaehlerDifferential.D R A (X (e.symm t)), ?_⟩
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, halg,
      MvPolynomial.aeval_X, P.basisKaehler_apply]
    simp [x]
  haveI : Algebra.FormallyUnramified A S := by
    refine ⟨⟨fun ω₁ ω₂ => ?_⟩⟩
    have hzero : ∀ ω : Ω[S⁄A], ω = 0 := by
      intro ω
      obtain ⟨η, rfl⟩ := KaehlerDifferential.map_surjective R A S ω
      have hη : η ∈ LinearMap.ker (KaehlerDifferential.map R A S S) := by
        rw [(KaehlerDifferential.exact_mapBaseChange_map R A S).linearMap_ker_eq, hrange]
        trivial
      exact hη
    rw [hzero ω₁, hzero ω₂]
  exact Algebra.Etale.of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (R := R) n

end FrobRankC3

universe u v

theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ x : Fin n → S,
      (MvPolynomial.aeval x : MvPolynomial (Fin n) R →ₐ[R] S).toRingHom.Etale :=
  FrobRankC3.main n

end S_Algebra_IsStandardSmoothOfRelativeDimension_exists_etale_aeval
end P2MW
export P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_exists_etale_aeval (solution)
