-- Prove2me | solution 1 for AutomorphicForm.exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6e33ec31-c555-5375-b6ab-e35c90a244f8

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace KcTorusNormFromCentralizer

open AutomorphicForm

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem card_aut_dvd_finrank : Fintype.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
  have h1 : Module.finrank (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L =
      Nat.card (⊤ : Subgroup (L ≃ₐ[K] L)) :=
    IntermediateField.finrank_fixedField_eq_card ⊤
  have h2 := Module.finrank_mul_finrank K
    (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
  rw [h1, Subgroup.card_top, Nat.card_eq_fintype_card] at h2
  exact Dvd.intro_left _ h2

variable {K L}

theorem orderOf_eq_finrank (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    orderOf σ = Module.finrank K L := by
  have hcard : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rcases (Nat.dvd_prime hdeg).1 (card_aut_dvd_finrank K L) with h | h
    · exfalso
      have : Subsingleton (L ≃ₐ[K] L) := Fintype.card_le_one_iff_subsingleton.1 h.le
      exact hσ (Subsingleton.elim _ _)
    · exact h
  have hdvd : orderOf σ ∣ Module.finrank K L := hcard ▸ orderOf_dvd_card
  rcases (Nat.dvd_prime hdeg).1 hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hσ
  · exact h

theorem pow_finrank_eq_one (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_eq_finrank hdeg σ hσ]
  exact pow_orderOf_eq_one σ

theorem iterate_finrank_apply (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (l : L) : (⇑σ)^[Module.finrank K L] l = l := by
  rw [← AlgEquiv.coe_pow, pow_finrank_eq_one hdeg σ hσ, AlgEquiv.one_apply]

end Galois

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem sigmaTensor_tmul (l : L) (a : A) : sigmaTensor K L A σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [sigmaTensor]

theorem sigmaTensor_includeRight (a : A) :
    sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a := by
  rw [Algebra.TensorProduct.includeRight_apply, sigmaTensor_tmul, map_one]

theorem sigmaTensor_sigmaTensor (τ : L ≃ₐ[K] L) (u : L ⊗[K] A) :
    sigmaTensor K L A σ (sigmaTensor K L A τ u) = sigmaTensor K L A (σ * τ) u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, sigmaTensor_tmul, AlgEquiv.mul_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem sigmaTensor_iterate (r : ℕ) (u : L ⊗[K] A) :
    (sigmaTensor K L A σ)^[r] u = sigmaTensor K L A (σ ^ r) u := by
  induction r generalizing u with
  | zero =>
      rw [Function.iterate_zero, id, pow_zero]
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul l a => rw [sigmaTensor_tmul, AlgEquiv.one_apply]
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, sigmaTensor_sigmaTensor, ← pow_succ']

theorem sigmaTensor_iterate_eq_self {n : ℕ} (hper : ∀ l : L, (⇑σ)^[n] l = l) (u : L ⊗[K] A) :
    (sigmaTensor K L A σ)^[n] u = u := by
  rw [sigmaTensor_iterate]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, AlgEquiv.coe_pow, hper]
  | add x y hx hy => rw [map_add, hx, hy]

theorem val_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    ((sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (sigmaTensor K L A σ) := rfl

theorem val_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) A).map
        (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := rfl

theorem sigmaGL_toTensorGL (g : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A g) = toTensorGL K L A g := by
  apply Units.ext
  rw [val_sigmaGL, val_toTensorGL, Matrix.map_map]
  congr 1
  funext a
  exact sigmaTensor_includeRight K L A σ a

theorem normString_eq_sigmaNormPow (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ =
      LT.TwistedNorm.sigmaNormPow (sigmaGL K L A σ) (Module.finrank K L) δ := by
  rw [LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range]
  rfl

theorem sigmaGL_iterate_eq_self (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g :=
  LT.TwistedNorm.iterate_generalLinearGroup_map_eq_self
    (fun u => sigmaTensor_iterate_eq_self K L A σ hper u) g

theorem sigmaGL_normString (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A σ (normString K L A σ δ) = δ⁻¹ * normString K L A σ δ * δ := by
  rw [normString_eq_sigmaNormPow]
  exact LT.TwistedNorm.map_sigmaNormPow _ _ (sigmaGL_iterate_eq_self K L A σ hper δ)

theorem normString_twistedConj (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
    (δ x : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) = x⁻¹ * normString K L A σ δ * x := by
  rw [normString_eq_sigmaNormPow, normString_eq_sigmaNormPow]
  exact LT.TwistedNorm.sigmaNormPow_sigmaConjElt _ _ (sigmaGL_iterate_eq_self K L A σ hper x) δ

end Twist

section Main

variable (K L : Type) [Field K] [Field L] [Algebra K L]

theorem main (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A]
    (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) :
    ∃ t x : GL (Fin 2) (L ⊗[K] A),
      t ∈ Subgroup.centralizer
          ({AutomorphicForm.toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) ∧
      AutomorphicForm.normString K L A σ t = AutomorphicForm.toTensorGL K L A γ ∧
      t = x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x := by

  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  have hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l := iterate_finrank_apply hdeg σ hσ
  obtain ⟨y, hy⟩ := h

  set t : GL (Fin 2) (L ⊗[K] A) := y⁻¹ * δ * sigmaGL K L A σ y with ht
  have hNt : normString K L A σ t = toTensorGL K L A γ := by
    rw [ht, normString_twistedConj K L A σ hper δ y]
    exact hy.symm
  have hfix := sigmaGL_normString K L A σ hper t
  rw [hNt, sigmaGL_toTensorGL] at hfix

  have hcomm : toTensorGL K L A γ * t = t * toTensorGL K L A γ := by
    calc toTensorGL K L A γ * t = t * (t⁻¹ * toTensorGL K L A γ * t) := by group
      _ = t * toTensorGL K L A γ := by rw [← hfix]
  refine ⟨t, y, ?_, hNt, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  exact hcomm

end Main

end KcTorusNormFromCentralizer

end

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A]
    (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) :
    ∃ t x : GL (Fin 2) (L ⊗[K] A),
      t ∈ Subgroup.centralizer
          ({AutomorphicForm.toTensorGL K L A γ} : Set (GL (Fin 2) (L ⊗[K] A))) ∧
      AutomorphicForm.normString K L A σ t = AutomorphicForm.toTensorGL K L A γ ∧
      t = x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x :=
  KcTorusNormFromCentralizer.main K L hdeg σ hσ A γ δ h

end S_AutomorphicForm_exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_centralizer_normString_eq_toTensorGL_of_isNormOf_of_prime (solution)
