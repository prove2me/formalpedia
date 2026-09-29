-- Prove2me | solution 1 for AutomorphicForm.exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/22f149dd-cbbf-516c-9503-a1755b1c4062

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_normString_apply_eq_one_tmul_norm_apply_of_diagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace LocalNormBridge

open AutomorphicForm

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

section Period

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem iterate_finrank_apply_of_gen (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (l : L) : (⇑σ)^[Module.finrank K L] l = l := by
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hord : orderOf σ = Nat.card (L ≃ₐ[K] L) := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hpow : σ ^ Module.finrank K L = 1 := by
    rw [← hcard, ← hord]; exact pow_orderOf_eq_one σ
  rw [← AlgEquiv.coe_pow, hpow, AlgEquiv.one_apply]

end Period

section Lift

variable (K L : Type) [Field K] [Field L] [Algebra K L]

theorem exists_exact_lift (σ : L ≃ₐ[K] L) (hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l)
    (A : Type) [CommRing A] [Algebra K A]
    (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) :
    ∃ t : GL (Fin 2) (L ⊗[K] A),
      toTensorGL K L A γ * t = t * toTensorGL K L A γ ∧
      AutomorphicForm.normString K L A σ t = AutomorphicForm.toTensorGL K L A γ := by
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
  exact ⟨t, hcomm, hNt⟩

end Lift

section Inj

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem one_tmul_injective : Function.Injective fun a : A => ((1 : L) ⊗ₜ[K] a : L ⊗[K] A) := by

  have hinj : Function.Injective (LinearMap.toSpanSingleton K L (1 : L)) := fun a b h =>
    smul_left_injective K (one_ne_zero : (1 : L) ≠ 0) (by simpa [LinearMap.toSpanSingleton_apply] using h)
  have hker : LinearMap.ker (LinearMap.toSpanSingleton K L (1 : L)) = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg (1 : K)
    simpa [LinearMap.toSpanSingleton_apply] using this
  intro a b hab
  have h := congrArg (fun z : L ⊗[K] A => TensorProduct.lid K A (LinearMap.rTensor A g z)) hab
  simpa [LinearMap.rTensor_tmul, hg1] using h

end Inj

end LocalNormBridge

end

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [CommRing A] [Algebra K A] (x y : Aˣ) (hxy : IsUnit ((x : A) - (y : A))) :
    (∃ δ : GL (Fin 2) (L ⊗[K] A), AutomorphicForm.IsNormOf K L A σ (diagUnits2 x y) δ) ↔
      ((x : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A)) ∧
       (y : A) ∈ Set.range (fun t : (L ⊗[K] A)ˣ => Algebra.norm A (t : L ⊗[K] A))) := by
  classical
  have hper : ∀ l : L, (⇑σ)^[Module.finrank K L] l = l := LocalNormBridge.iterate_finrank_apply_of_gen σ hgen
  set ι : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight with hι

  have hγ : ∀ i j : Fin 2, ((AutomorphicForm.toTensorGL K L A (diagUnits2 x y) : GL (Fin 2) (L ⊗[K] A)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j = (1 : L) ⊗ₜ[K] ((diagUnits2 x y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j :=
    fun i j => rfl
  have hd : ((diagUnits2 x y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(x : A), 0; 0, (y : A)] :=
    LanglandsTunnell.CubicInduction.coe_diagUnits2 x y
  constructor
  · rintro ⟨δ, hδ⟩
    obtain ⟨t, hcomm, hNt⟩ := LocalNormBridge.exists_exact_lift K L σ hper A (diagUnits2 x y) δ hδ

    have hu : IsUnit ((1 : L) ⊗ₜ[K] (x : A) - (1 : L) ⊗ₜ[K] (y : A) : L ⊗[K] A) := by
      have := hxy.map ι
      rwa [map_sub, hι, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply] at this
    have hent : ∀ i j : Fin 2, ((AutomorphicForm.toTensorGL K L A (diagUnits2 x y) * t : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
        ((t * AutomorphicForm.toTensorGL K L A (diagUnits2 x y) : GL (Fin 2) (L ⊗[K] A)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j := fun i j => by rw [hcomm]
    have h01 : ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
      have h := hent 0 1
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hγ, hd] at h
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, TensorProduct.tmul_zero, zero_mul, mul_zero, add_zero, zero_add] at h

      have : ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 *
          ((1 : L) ⊗ₜ[K] (x : A) - (1 : L) ⊗ₜ[K] (y : A)) = 0 := by
        rw [mul_sub, mul_comm _ ((1 : L) ⊗ₜ[K] (x : A)), h, sub_self]
      exact (hu.mul_left_eq_zero.mp this)
    have h10 : ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
      have h := hent 1 0
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hγ, hd] at h
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, TensorProduct.tmul_zero, zero_mul, mul_zero, add_zero, zero_add] at h

      have : ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 *
          ((1 : L) ⊗ₜ[K] (x : A) - (1 : L) ⊗ₜ[K] (y : A)) = 0 := by
        rw [mul_sub, ← h, mul_comm ((1 : L) ⊗ₜ[K] (y : A)), sub_self]
      exact (hu.mul_left_eq_zero.mp this)

    have hdet : IsUnit (((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 *
        ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1) := by
      have h := (Matrix.GeneralLinearGroup.det t).isUnit
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h01, h10, mul_zero, sub_zero] at h
      exact h
    obtain ⟨hα, hβ⟩ := IsUnit.mul_iff.mp hdet

    obtain ⟨-, -, h00, h11⟩ :=
      AutomorphicForm.normString_apply_eq_one_tmul_norm_apply_of_diagonal K L σ hgen A t h10 h01
    rw [hNt, hγ, hd] at h00 h11
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h00 h11
    refine ⟨⟨hα.unit, ?_⟩, ⟨hβ.unit, ?_⟩⟩
    · change Algebra.norm A ((hα.unit : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (x : A)
      rw [IsUnit.unit_spec]
      exact (LocalNormBridge.one_tmul_injective K L A h00).symm
    · change Algebra.norm A ((hβ.unit : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (y : A)
      rw [IsUnit.unit_spec]
      exact (LocalNormBridge.one_tmul_injective K L A h11).symm
  · rintro ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩
    refine ⟨diagUnits2 d₁ d₂, 1, ?_⟩
    unfold AutomorphicForm.IsNormConjugator
    rw [inv_one, one_mul, mul_one]
    obtain ⟨h10, h01, h00, h11⟩ :=
      AutomorphicForm.normString_apply_eq_one_tmul_norm_apply_of_diagonal K L σ hgen A (diagUnits2 d₁ d₂)
        (by rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl)
        (by rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]; rfl)
    have hd₁' : Algebra.norm A ((d₁ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (x : A) := hd₁
    have hd₂' : Algebra.norm A ((d₂ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (y : A) := hd₂
    apply Units.ext
    apply Matrix.ext
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩
    · rw [hγ, hd, h00, LanglandsTunnell.CubicInduction.coe_diagUnits2]; simp [hd₁']
    · rw [hγ, hd, h01]; simp
    · rw [hγ, hd, h10]; simp
    · rw [hγ, hd, h11, LanglandsTunnell.CubicInduction.coe_diagUnits2]; simp [hd₂']

end S_AutomorphicForm_exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub
end P2MW
export P2MW.S_AutomorphicForm_exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub (solution)
