-- Prove2me | solution 1 for AutomorphicForm.SplitPlace.exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fe1767cb-5d94-5cc5-83f4-711560b4c657

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SplitPlace_exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace SplitDictSol

section PiFactor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ι → Type*} [∀ w, Field (F w)]
  {A : Type*} [Field A]

theorem exists_factor (χ : (Π w, F w) →+* A) :
    ∃ w₀ : ι, χ (Pi.single w₀ 1) = 1 ∧ ∀ y : Π w, F w, χ y = χ (Pi.single w₀ (y w₀)) := by
  classical

  have hidem : ∀ w, χ (Pi.single w 1) = 0 ∨ χ (Pi.single w 1) = 1 := by
    intro w
    have h : χ (Pi.single w 1) * χ (Pi.single w 1) = χ (Pi.single w 1) := by
      rw [← map_mul, ← Pi.single_mul, mul_one]
    by_cases h0 : χ (Pi.single w 1) = 0
    · exact Or.inl h0
    · right
      have := mul_right_cancel₀ h0 (h.trans (one_mul _).symm)
      exact this
  have hsum : ∑ w, χ (Pi.single w (1 : F w)) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun w => (1 : F w))]
    exact map_one χ
  have hex : ∃ w₀, χ (Pi.single w₀ 1) = 1 := by
    by_contra h
    push Not at h
    have : ∑ w, χ (Pi.single w (1 : F w)) = 0 :=
      Finset.sum_eq_zero fun w _ => (hidem w).resolve_right (h w)
    rw [this] at hsum
    exact zero_ne_one hsum
  obtain ⟨w₀, hw₀⟩ := hex
  refine ⟨w₀, hw₀, fun y => ?_⟩
  have horth : ∀ w, w ≠ w₀ → χ (Pi.single w (y w)) = 0 := by
    intro w hw
    have h0 : Pi.single w (y w) * Pi.single w₀ (1 : F w₀) = 0 := by
      ext w'
      simp only [Pi.mul_apply, Pi.zero_apply]
      by_cases h1 : w' = w
      · subst h1
        rw [Pi.single_eq_of_ne (Ne.symm (Ne.symm hw)) , mul_zero]
      · rw [Pi.single_eq_of_ne h1, zero_mul]
    have := congrArg χ h0
    rw [map_mul, hw₀, mul_one, map_zero] at this
    exact this
  calc χ y = χ (∑ w, Pi.single w (y w)) := by rw [Finset.univ_sum_single]
    _ = ∑ w, χ (Pi.single w (y w)) := map_sum χ _ _
    _ = χ (Pi.single w₀ (y w₀)) :=
        Finset.sum_eq_single_of_mem w₀ (Finset.mem_univ _) (fun w _ hw => horth w hw)

def factorHom (χ : (Π w, F w) →+* A) (w₀ : ι) (h1 : χ (Pi.single w₀ 1) = 1) : F w₀ →+* A where
  toFun t := χ (Pi.single w₀ t)
  map_one' := h1
  map_mul' s t := by rw [← map_mul, ← Pi.single_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' s t := by rw [← map_add, ← Pi.single_add]

@[scoped simp] theorem factorHom_apply (χ : (Π w, F w) →+* A) (w₀ : ι) (h1 : χ (Pi.single w₀ 1) = 1) (t : F w₀) :
    factorHom χ w₀ h1 t = χ (Pi.single w₀ t) := rfl

end PiFactor

theorem toNNReal_congr {b₁ b₂ : NNReal} (h : b₁ = b₂) (h₁ : b₁ ≠ 0) (h₂ : b₂ ≠ 0)
    (x : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal h₁ x = WithZeroMulInt.toNNReal h₂ x := by
  subst h
  rfl

end SplitDictSol
p2m_reactivate "P2MW.S_AutomorphicForm_SplitPlace_exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq.SplitDictSol"

open SplitDictSol in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (ι : L →ₐ[K] v.adicCompletion K) :
    ∃ (e : Fin (Module.finrank K L) ≃ v.Extension (𝓞 L))
      (θ : ∀ i : Fin (Module.finrank K L), ((e i).1.adicCompletion L) ≃ₐ[v.adicCompletion K] v.adicCompletion K),
      (∀ (z : L ⊗[K] v.adicCompletion K) (i : Fin (Module.finrank K L)),
        AutomorphicForm.SplitPlace.psi K L (v.adicCompletion K) σ ι z i =
          θ i (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v z (e i))) ∧
      (∀ (i : Fin (Module.finrank K L)) (y : (e i).1.adicCompletion L),
        θ i y ∈ v.adicCompletionIntegers K ↔ y ∈ (e i).1.adicCompletionIntegers L) ∧
      (∀ (i : Fin (Module.finrank K L)) (y : (e i).1.adicCompletion L), ‖θ i y‖ = ‖y‖) := by
  classical
  haveI hfd : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
  letI : Fintype (v.Extension (𝓞 L)) := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v

  let Φ := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
  let ψ := AutomorphicForm.SplitPlace.psi K L (v.adicCompletion K) σ ι
  let χ : Fin (Module.finrank K L) → ((Π w : v.Extension (𝓞 L), w.1.adicCompletion L) →+* (v.adicCompletion K)) := fun i =>
    ((Pi.evalRingHom (fun _ : Fin (Module.finrank K L) => (v.adicCompletion K)) i).comp ψ.toRingHom).comp
      Φ.symm.toRingEquiv.toRingHom
  have hχ : ∀ i z, χ i (Φ z) = ψ z i := by
    intro i z
    simp [χ]
  let c : (v.adicCompletion K) → (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) := fun a w => algebraMap (v.adicCompletion K) _ a
  have hΦc : ∀ a, Φ ((1 : L) ⊗ₜ[K] a) = c a := by
    intro a
    funext w
    show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ((1 : L) ⊗ₜ[K] a) w = _
    rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]
  have hχc : ∀ i a, χ i (c a) = a := by
    intro i a
    rw [← hΦc, hχ]
    show ψ ((1 : L) ⊗ₜ[K] a) i = a
    rw [show ψ ((1 : L) ⊗ₜ[K] a) = fun _ => a from AutomorphicForm.SplitPlace.psi_one_tmul K L (v.adicCompletion K) σ ι a]

  choose w₀ hw₀ using fun i => exists_factor (χ i)
  let θ' : ∀ i, (w₀ i).1.adicCompletion L →+* (v.adicCompletion K) := fun i => factorHom (χ i) (w₀ i) (hw₀ i).1
  have hθ'c : ∀ i a, θ' i (algebraMap (v.adicCompletion K) _ a) = a := by
    intro i a
    show χ i (Pi.single (w₀ i) (c a (w₀ i))) = a
    rw [← (hw₀ i).2 (c a), hχc]
  have hsurj : ∀ i, Function.Surjective (algebraMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L)) := by
    intro i y
    exact ⟨θ' i y, (θ' i).injective (by rw [hθ'c])⟩
  have hθ'surj : ∀ i, Function.Surjective (θ' i) := fun i a => ⟨algebraMap _ _ a, hθ'c i a⟩

  have hχeq : ∀ i j, w₀ j = w₀ i → ∀ y, χ j y = χ i y := by
    intro i j hj y
    obtain ⟨a, ha⟩ := hsurj i (y (w₀ i))
    have key : ∀ k, w₀ k = w₀ i → χ k y = a := by
      intro k hk
      have h2 := (hw₀ k).2 (c a)
      have h3 := (hw₀ k).2 y
      rw [hk] at h2 h3
      rw [h3, ← ha]
      show χ k (Pi.single (w₀ i) (c a (w₀ i))) = a
      rw [← h2, hχc]
    rw [key j hj, key i rfl]

  have hinj : Function.Injective w₀ := by
    intro i j hij
    have hψ : ∀ x : L, ψ (x ⊗ₜ[K] (1 : (v.adicCompletion K))) i = ψ (x ⊗ₜ[K] (1 : (v.adicCompletion K))) j := by
      intro x
      rw [← hχ, ← hχ, hχeq i j hij.symm]
    have hσ' : (σ ^ (i : ℕ)) = σ ^ (j : ℕ) := by
      ext x
      have h := hψ x
      simp only [ψ, AutomorphicForm.SplitPlace.psi_tmul, mul_one] at h
      exact ι.toRingHom.injective h
    exact AutomorphicForm.SplitPlace.pow_injective_fin hprime σ hσ hσ'

  have hrank1 : ∀ i, Module.finrank (v.adicCompletion K) ((w₀ i).1.adicCompletion L) = 1 := by
    intro i
    have e1 : (v.adicCompletion K) ≃ₗ[(v.adicCompletion K)] (w₀ i).1.adicCompletion L :=
      LinearEquiv.ofBijective (Algebra.linearMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L))
        ⟨(algebraMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L)).injective, hsurj i⟩
    rw [← e1.finrank_eq, Module.finrank_self]
  have hcard : Fintype.card (Fin (Module.finrank K L)) = Fintype.card (v.Extension (𝓞 L)) := by
    apply le_antisymm (Fintype.card_le_of_injective w₀ hinj)
    have hsum := Ideal.sum_ramification_inertia_extensions (𝓞 K) K L (𝓞 L) v
    have hle : Fintype.card (v.Extension (𝓞 L)) ≤ Module.finrank K L := by
      calc Fintype.card (v.Extension (𝓞 L)) = ∑ w : v.Extension (𝓞 L), 1 := by
            rw [← Finset.card_univ, Finset.card_eq_sum_ones]
        _ ≤ ∑ w : v.Extension (𝓞 L), v.asIdeal.ramificationIdx' w.1.asIdeal * v.asIdeal.inertiaDeg' w.1.asIdeal := by
            refine Finset.sum_le_sum fun w _ => ?_
            rw [HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w]
            exact Module.finrank_pos
        _ = Module.finrank K L := hsum
    simpa only [Fintype.card_fin] using hle
  have hbij : Function.Bijective w₀ := (Fintype.bijective_iff_injective_and_card w₀).2 ⟨hinj, hcard⟩
  let e : Fin (Module.finrank K L) ≃ v.Extension (𝓞 L) := Equiv.ofBijective w₀ hbij

  let θr : ∀ i, (w₀ i).1.adicCompletion L ≃+* (v.adicCompletion K) := fun i =>
    RingEquiv.ofBijective (θ' i) ⟨(θ' i).injective, hθ'surj i⟩
  let θ : ∀ i, ((e i).1.adicCompletion L) ≃ₐ[(v.adicCompletion K)] (v.adicCompletion K) := fun i =>
    AlgEquiv.ofRingEquiv (f := θr i) (fun a => by
      show θ' i (algebraMap (v.adicCompletion K) _ a) = a
      exact hθ'c i a)
  have hθ : ∀ i (y : (w₀ i).1.adicCompletion L), θ i y = χ i (Pi.single (w₀ i) y) := fun _ _ => rfl

  have hef : ∀ i, v.asIdeal.ramificationIdx' (w₀ i).1.asIdeal = 1 ∧ v.asIdeal.inertiaDeg' (w₀ i).1.asIdeal = 1 := by
    intro i
    have h := HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L (w₀ i)
    rw [hrank1 i] at h
    exact ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩
  refine ⟨e, θ, ?_, ?_, ?_⟩
  ·
    intro z i
    show ψ z i = χ i (Pi.single (w₀ i) ((Φ z) (w₀ i)))
    rw [← (hw₀ i).2, hχ]
  ·
    intro i y
    obtain ⟨a, rfl⟩ := hsurj i y
    show θ' i (algebraMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L) a) ∈ v.adicCompletionIntegers K ↔
      algebraMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L) a ∈ (w₀ i).1.adicCompletionIntegers L
    rw [hθ'c i a,
      HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      show algebraMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L) a =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom K L (w₀ i) a from rfl,
      HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom]
    have hunder : HeightOneSpectrum.under (𝓞 K) (w₀ i).1 = v := (w₀ i).2
    rw [hunder, (hef i).1, pow_one]
  ·
    intro i y
    obtain ⟨a, rfl⟩ := hsurj i y
    show ‖θ' i (algebraMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L) a)‖ = ‖algebraMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L) a‖
    rw [hθ'c i a]
    have hunder : HeightOneSpectrum.under (𝓞 K) (w₀ i).1 = v := (w₀ i).2

    have habs : Ideal.absNorm (w₀ i).1.asIdeal = Ideal.absNorm v.asIdeal := by
      have hLO : (w₀ i).1.asIdeal.LiesOver v.asIdeal := ⟨by simp_rw [← (w₀ i).2]; rfl⟩
      have hf := (hef i).2
      rw [Ideal.inertiaDeg_algebraMap] at hf
      haveI := v.isMaximal
      letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
      haveI : Module.Finite (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ (w₀ i).1.asIdeal) :=
        Module.finite_of_finrank_pos (by rw [hf]; exact one_pos)
      rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply,
        Module.natCard_eq_pow_finrank (K := 𝓞 K ⧸ v.asIdeal) (V := 𝓞 L ⧸ (w₀ i).1.asIdeal), hf, pow_one]
    rw [NumberField.FinitePlace.norm_def v a,
      NumberField.FinitePlace.norm_def (w₀ i).1 (algebraMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L) a),
      show algebraMap (v.adicCompletion K) ((w₀ i).1.adicCompletion L) a =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom K L (w₀ i) a from rfl,
      HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom, hunder, (hef i).1, pow_one]
    congr 1
    exact (toNNReal_congr (by exact_mod_cast habs.symm) _ _ _)

end S_AutomorphicForm_SplitPlace_exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq
end P2MW
export P2MW.S_AutomorphicForm_SplitPlace_exists_equiv_extension_algEquiv_forall_psi_eq_and_mem_adicCompletionIntegers_iff_and_norm_eq (solution)
