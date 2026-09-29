-- Prove2me | solution 1 for Algebra.exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/160f73ca-162f-5dc0-ada6-8839570be8c3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace AlgSpreadDirect

open MvPolynomial

theorem exists_map_eq_of_coeffs_subset {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {n : ℕ} (L : IntermediateField k K) (p : MvPolynomial (Fin n) K)
    (hp : (↑p.coeffs : Set K) ⊆ (L : Set K)) :
    ∃ q : MvPolynomial (Fin n) L, MvPolynomial.map (algebraMap L K) q = p := by
  have : p ∈ Set.range (MvPolynomial.map (algebraMap L K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    exact ⟨⟨c, hp hc⟩, rfl⟩
  exact this

theorem exists_model_of_lifts
    (L₀ K : Type v) [CommRing L₀] [CommRing K] [Algebra L₀ K]
    (A : Type w) [CommRing A] [Algebra K A] [Algebra L₀ A] [IsScalarTower L₀ K A]
    {n : ℕ} (f : MvPolynomial (Fin n) K →ₐ[K] A) (hf : Function.Surjective f)
    (s : Finset (MvPolynomial (Fin n) K)) (hs : Ideal.span (↑s : Set (MvPolynomial (Fin n) K)) = RingHom.ker f)
    (q : ∀ p ∈ s, MvPolynomial (Fin n) L₀) (hq : ∀ p (hp : p ∈ s), MvPolynomial.map (algebraMap L₀ K) (q p hp) = p) :
    ∃ (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra L₀ A₀) (_ : Algebra.FiniteType L₀ A₀),
      Nonempty ((K ⊗[L₀] A₀) ≃ₐ[K] A) := by
  classical
  let I : Ideal (MvPolynomial (Fin n) L₀) := Ideal.span (Set.range fun p : s => q p.1 p.2)
  let A₀ : Type v := MvPolynomial (Fin n) L₀ ⧸ I

  let φ₀ : MvPolynomial (Fin n) L₀ →ₐ[L₀] A := MvPolynomial.aeval fun i => f (X i)
  have hfae : ∀ p : MvPolynomial (Fin n) K, f p = MvPolynomial.aeval (fun i => f (X i)) p := fun p => by
    conv_lhs => rw [show f = MvPolynomial.aeval (fun i => f (X i)) from MvPolynomial.algHom_ext (fun i => by simp)]
  have hφ₀ : ∀ p : MvPolynomial (Fin n) L₀, φ₀ p = f (MvPolynomial.map (algebraMap L₀ K) p) := fun p => by
    rw [hfae, MvPolynomial.aeval_map_algebraMap]
  have hφ₀I : ∀ a ∈ I, φ₀ a = 0 := by
    have hle : I ≤ RingHom.ker (φ₀ : MvPolynomial (Fin n) L₀ →+* A) := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨⟨p, hp⟩, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      show φ₀ (q p hp) = 0
      rw [hφ₀, hq p hp]
      have hpJ : p ∈ RingHom.ker f := hs ▸ Ideal.subset_span hp
      exact RingHom.mem_ker.mp hpJ
    intro a ha
    exact hle ha
  let g : A₀ →ₐ[L₀] A := Ideal.Quotient.liftₐ I φ₀ hφ₀I
  let Φ : K ⊗[L₀] A₀ →ₐ[K] A := AlgHom.liftEquiv L₀ K A₀ A g

  let ψ₀ : MvPolynomial (Fin n) K →ₐ[K] K ⊗[L₀] A₀ :=
    MvPolynomial.aeval fun i => (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (X i) : A₀)
  have hψ₀map : ∀ p : MvPolynomial (Fin n) L₀,
      ψ₀ (MvPolynomial.map (algebraMap L₀ K) p) = (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I p : A₀) := fun p => by
    change (MvPolynomial.aeval fun i => (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (X i) : A₀))
      (MvPolynomial.map (algebraMap L₀ K) p) = _
    rw [MvPolynomial.aeval_map_algebraMap]
    have : (MvPolynomial.aeval (R := L₀) (S₁ := K ⊗[L₀] A₀) fun i => (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (X i) : A₀)) =
        ((Algebra.TensorProduct.includeRight (R := L₀) (A := K) (B := A₀)).comp (Ideal.Quotient.mkₐ L₀ I)) :=
      MvPolynomial.algHom_ext fun i => by
        rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
        rfl
    rw [this]
    rfl
  have hψ₀J : ∀ a ∈ RingHom.ker f, ψ₀ a = 0 := by
    have hle : RingHom.ker f ≤ RingHom.ker (ψ₀ : MvPolynomial (Fin n) K →ₐ[K] K ⊗[L₀] A₀).toRingHom := by
      rw [← hs]
      refine Ideal.span_le.mpr fun p hp => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker]
      show ψ₀ p = 0
      rw [← hq p hp, hψ₀map]
      have : (Ideal.Quotient.mk I (q p hp) : A₀) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨⟨p, hp⟩, rfl⟩)
      rw [this, TensorProduct.tmul_zero]
    intro a ha
    exact hle ha
  let e : (MvPolynomial (Fin n) K ⧸ RingHom.ker f) ≃ₐ[K] A := Ideal.quotientKerAlgEquivOfSurjective hf
  let Ψ : A →ₐ[K] K ⊗[L₀] A₀ := (Ideal.Quotient.liftₐ (RingHom.ker f) ψ₀ hψ₀J).comp (e.symm : A →ₐ[K] _)

  have hΦ : ∀ p : MvPolynomial (Fin n) L₀,
      Φ ((1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I p : A₀)) = f (MvPolynomial.map (algebraMap L₀ K) p) := by
    intro p
    change (AlgHom.liftEquiv L₀ K A₀ A g) ((1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I p : A₀)) = _
    rw [AlgHom.liftEquiv_tmul, one_smul]
    change Ideal.Quotient.liftₐ I φ₀ hφ₀I (Ideal.Quotient.mk I p) = _
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact hφ₀ p
  have hΨ : ∀ p : MvPolynomial (Fin n) K, Ψ (f p) = ψ₀ p := by
    intro p
    change Ideal.Quotient.liftₐ (RingHom.ker f) ψ₀ hψ₀J (e.symm (f p)) = ψ₀ p
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply hf p]
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl

  have h₁ : Φ.comp Ψ = AlgHom.id K A := by
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hf a
    rw [AlgHom.comp_apply, hΨ, AlgHom.id_apply]
    have : (Φ.comp ψ₀) = f := MvPolynomial.algHom_ext fun i => by
      rw [AlgHom.comp_apply]
      change Φ (MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (X i) : A₀)) (X i)) = f (X i)
      rw [MvPolynomial.aeval_X, hΦ, MvPolynomial.map_X]
    exact AlgHom.congr_fun this p
  have h₂ : Ψ.comp Φ = AlgHom.id K (K ⊗[L₀] A₀) := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      change Ψ (Φ ((1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (X i) : A₀))) = (1 : K) ⊗ₜ[L₀] (Ideal.Quotient.mk I (X i) : A₀)
      rw [hΦ, hΨ, hψ₀map]
  haveI : Algebra.FiniteType L₀ A₀ := inferInstance
  exact ⟨A₀, inferInstance, inferInstance, inferInstance, ⟨AlgEquiv.ofAlgHom Φ Ψ h₁ h₂⟩⟩

end AlgSpreadDirect

open AlgSpreadDirect MvPolynomial in
theorem solution
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (A : Type w) [CommRing A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra L A₀) (_ : Algebra.FiniteType L A₀),
      Nonempty ((K ⊗[L] A₀) ≃ₐ[K] A) := by
  classical

  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := K) (S := A)).mp inferInstance
  obtain ⟨s, hs⟩ : (RingHom.ker f).FG := IsNoetherian.noetherian _

  let C : Finset K := s.biUnion fun p => p.coeffs
  let L : IntermediateField k K := IntermediateField.adjoin k (↑C : Set K)
  have hLfd : FiniteDimensional k L := by
    haveI : Finite (↑(↑C : Set K)) := Finite.of_fintype _
    exact IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral

  have hlift : ∀ p ∈ s, ∃ q : MvPolynomial (Fin n) L, MvPolynomial.map (algebraMap L K) q = p := by
    intro p hp
    refine exists_map_eq_of_coeffs_subset L p fun c hc => ?_
    exact IntermediateField.subset_adjoin k _ (Finset.mem_biUnion.mpr ⟨p, hp, hc⟩)
  choose q hq using hlift

  exact ⟨L, hLfd, exists_model_of_lifts L K A f hf s hs q hq⟩

end S_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic
end P2MW
export P2MW.S_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic (solution)
