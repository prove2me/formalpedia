-- Prove2me | solution 1 for AutomorphicForm.mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/02b7da9f-9550-52a5-8c12-a8818f9f4af9

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace HW47NS

section Scalars

variable {A B : Type*} [CommRing A] [CommRing B]

theorem map_scalar (f : A →+* B) (c : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : A →* B) c) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Aˣ → GL (Fin 2) A) := by
  intro a b h
  have := congrArg (fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) 0 0) h
  refine Units.ext ?_
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

end Scalars

section Sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

noncomputable abbrev sigmaUnits : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ :=
  Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A)

noncomputable def galNorm (n : ℕ) : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ where
  toFun x := ∏ i ∈ Finset.range n, (sigmaUnits K L A σ)^[i] x
  map_one' := by simp [iterate_map_one]
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => iterate_map_mul _ i x y

theorem galNorm_apply (n : ℕ) (x : (L ⊗[K] A)ˣ) :
    galNorm K L A σ n x = ∏ i ∈ Finset.range n, (sigmaUnits K L A σ)^[i] x := rfl

theorem sigmaTensor_tmul (l : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor]

theorem iterate_sigmaTensor_tmul (i : ℕ) (l : L) (a : A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[i] (l ⊗ₜ[K] a) = (σ ^ i) l ⊗ₜ[K] a := by
  induction i with
  | zero => simp
  | succ i ih => simp only [Function.iterate_succ_apply', ih, sigmaTensor_tmul, pow_succ', AlgEquiv.mul_apply]

theorem coe_iterate_sigmaUnits (i : ℕ) (x : (L ⊗[K] A)ˣ) :
    (((sigmaUnits K L A σ)^[i] x : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (AutomorphicForm.sigmaTensor K L A σ)^[i] (x : L ⊗[K] A) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem coe_galNorm (n : ℕ) (x : (L ⊗[K] A)ˣ) :
    ((galNorm K L A σ n x : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      ∏ i ∈ Finset.range n, (AutomorphicForm.sigmaTensor K L A σ)^[i] (x : L ⊗[K] A) := by
  rw [galNorm_apply, Units.coe_prod]
  exact Finset.prod_congr rfl fun i _ => coe_iterate_sigmaUnits K L A σ i x

theorem iterate_sigmaGL_apply (i : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) (j k : Fin 2) :
    (((AutomorphicForm.sigmaGL K L A σ)^[i] g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) j k =
      (AutomorphicForm.sigmaTensor K L A σ)^[i] ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) j k) := by
  induction i generalizing g with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      congr 1

theorem sigmaGL_toTensorGL (γ : GL (Fin 2) A) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.toTensorGL K L A γ) = AutomorphicForm.toTensorGL K L A γ := by
  apply Units.ext
  ext j k
  change AutomorphicForm.sigmaTensor K L A σ
      ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((γ : Matrix (Fin 2) (Fin 2) A) j k)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((γ : Matrix (Fin 2) (Fin 2) A) j k)
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply, sigmaTensor_tmul, map_one]

theorem prod_range_conj (y δ : GL (Fin 2) (L ⊗[K] A)) (m : ℕ) :
    ((List.range m).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i]
        (y⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ y)).prod =
      y⁻¹ * ((List.range m).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod *
        (⇑(AutomorphicForm.sigmaGL K L A σ))^[m] y := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_append, List.prod_append, ih,
        List.map_singleton, List.map_singleton, List.prod_singleton, List.prod_singleton,
        iterate_map_mul, iterate_map_mul, iterate_map_inv, ← Function.iterate_succ_apply]
      simp only [mul_assoc, mul_inv_cancel_left]

theorem sigmaGL_prod_range (δ : GL (Fin 2) (L ⊗[K] A)) (m : ℕ) :
    AutomorphicForm.sigmaGL K L A σ (((List.range m).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod) =
      δ⁻¹ * ((List.range m).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod *
        (⇑(AutomorphicForm.sigmaGL K L A σ))^[m] δ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.prod_append, map_mul, ih, List.map_singleton, List.prod_singleton,
        ← Function.iterate_succ_apply' (AutomorphicForm.sigmaGL K L A σ) m δ]
      simp only [mul_assoc]

theorem prod_range_diagonal (δ : GL (Fin 2) (L ⊗[K] A))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) (m : ℕ) :
    (((((List.range m).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0) ∧
    (((((List.range m).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0) ∧
    (((((List.range m).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 =
      ∏ i ∈ Finset.range m, (AutomorphicForm.sigmaTensor K L A σ)^[i] ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0)) ∧
    (((((List.range m).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1 =
      ∏ i ∈ Finset.range m, (AutomorphicForm.sigmaTensor K L A σ)^[i] ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      obtain ⟨i10, i01, i00, i11⟩ := ih
      have f10 : (((⇑(AutomorphicForm.sigmaGL K L A σ))^[m] δ : GL (Fin 2) (L ⊗[K] A)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 1 0 = 0 := by
        rw [iterate_sigmaGL_apply, h10, iterate_map_zero]
      have f01 : (((⇑(AutomorphicForm.sigmaGL K L A σ))^[m] δ : GL (Fin 2) (L ⊗[K] A)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 1 = 0 := by
        rw [iterate_sigmaGL_apply, h01, iterate_map_zero]
      have f00 := iterate_sigmaGL_apply K L A σ m δ 0 0
      have f11 := iterate_sigmaGL_apply K L A σ m δ 1 1
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, Units.val_mul]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Matrix.mul_apply, Fin.sum_univ_two, i10, i11, f10, zero_mul, mul_zero, add_zero]
      · rw [Matrix.mul_apply, Fin.sum_univ_two, i00, i01, f01, zero_mul, mul_zero, add_zero]
      · rw [Matrix.mul_apply, Fin.sum_univ_two, i00, i01, f00, zero_mul, add_zero, Finset.prod_range_succ]
      · rw [Matrix.mul_apply, Fin.sum_univ_two, i10, i11, f11, zero_mul, zero_add, Finset.prod_range_succ]

end Sigma

section Order

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem iterate_sigmaTensor_finrank (t : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[Module.finrank K L] t = t := by
  have hσ : σ ^ Module.finrank K L = 1 := by
    rw [← IsGalois.card_aut_eq_finrank K L]
    exact pow_card_eq_one'
  have hcoe : ((AutomorphicForm.sigmaTensor K L A σ)^[Module.finrank K L] : L ⊗[K] A → L ⊗[K] A) =
      ⇑((AutomorphicForm.sigmaTensor K L A σ) ^ Module.finrank K L) := (RingHom.coe_pow _ _).symm
  rw [hcoe]
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul l a => rw [← hcoe, iterate_sigmaTensor_tmul, hσ, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, hx, hy]

theorem iterate_sigmaGL_finrank (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(AutomorphicForm.sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  apply Units.ext
  ext j k
  rw [iterate_sigmaGL_apply]
  exact iterate_sigmaTensor_finrank K L A σ _

end Order

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

theorem mem_range_idelicNorm_of_includeRight_eq_galNorm
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (u : (AdeleRing (𝓞 K) K)ˣ) (e : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hgal : Units.map (Algebra.TensorProduct.includeRight :
        AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom.toMonoidHom u =
      galNorm K L (AdeleRing (𝓞 K) K) σ (Module.finrank K L) e) :
    u ∈ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm := by
  classical
  let iR : (AdeleRing (𝓞 K) K)ˣ →* (L ⊗[K] AdeleRing (𝓞 K) K)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom.toMonoidHom
  let 𝒩 := galNorm K L (AdeleRing (𝓞 K) K) σ (Module.finrank K L)
  let Ering : L ⊗[K] AdeleRing (𝓞 K) K ≃+* AdeleRing (𝓞 L) L :=
    (Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)
  let Eu : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ := Units.map Ering.toRingHom.toMonoidHom
  let D := M4aHerbrand.GenuineDescent.genuineDescentDatum K L
  obtain ⟨hTS1, hTS2, -⟩ := AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D

  have hEσ : ∀ x : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      Eu (sigmaUnits K L (AdeleRing (𝓞 K) K) σ x) = D.unitsAct σ (Eu x) := by
    intro x
    have h1 := hTS1 σ (Matrix.GeneralLinearGroup.scalar (Fin 2) x)
    change Matrix.GeneralLinearGroup.map Ering.toRingHom
        (Matrix.GeneralLinearGroup.map (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) σ)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
      Matrix.GeneralLinearGroup.map (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom
        (Matrix.GeneralLinearGroup.map Ering.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) at h1
    rw [map_scalar, map_scalar, map_scalar, map_scalar] at h1
    have h2 := scalar_injective h1
    refine (Units.ext ?_ : Eu (sigmaUnits K L (AdeleRing (𝓞 K) K) σ x) = _)
    have h3 := congrArg (fun z : (AdeleRing (𝓞 L) L)ˣ => (z : AdeleRing (𝓞 L) L)) h2
    simp at h3
    exact h3

  have hEβ : ∀ a : (AdeleRing (𝓞 K) K)ˣ, Eu (iR a) =
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a := by
    intro a
    have h1 := hTS2 (Matrix.GeneralLinearGroup.scalar (Fin 2) a)
    change Matrix.GeneralLinearGroup.map Ering.toRingHom
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeRight :
            AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom
          (Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = _ at h1
    rw [map_scalar, map_scalar, map_scalar] at h1
    exact scalar_injective h1
  have hEσi : ∀ (i : ℕ) (x : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ),
      Eu ((sigmaUnits K L (AdeleRing (𝓞 K) K) σ)^[i] x) = (D.unitsAct σ)^[i] (Eu x) := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
        intro x
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hEσ, ih]
  have hiter : ∀ (i : ℕ) (w : (AdeleRing (𝓞 L) L)ˣ), (D.unitsAct σ)^[i] w = D.unitsAct (σ ^ i) w := by
    intro i
    induction i with
    | zero => intro w; simp
    | succ i ih =>
        intro w
        rw [Function.iterate_succ_apply', ih, pow_succ', map_mul, MulAut.mul_apply]
  obtain ⟨hβinj, -, -, hprod⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D
  have hEN : Eu (𝒩 e) = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom
      ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (Eu e)) := by
    rw [← hprod, LT.TwistedNorm.prod_algEquiv_eq_prod_range_of_generator hgen]
    change Eu (galNorm K L (AdeleRing (𝓞 K) K) σ (Module.finrank K L) e) = _
    rw [galNorm_apply, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [hEσi, hiter]
  have hfinal : Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom u =
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom
        ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (Eu e)) := by
    rw [← hEN, ← hEβ]
    exact congrArg Eu hgal
  refine ⟨Eu e, ?_⟩
  have h1 := congrArg (fun z : (AdeleRing (𝓞 L) L)ˣ => (z : AdeleRing (𝓞 L) L)) hfinal
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h1
  exact Units.ext (hβinj h1).symm

theorem unitsMap_algebraMap_mem_range_idelicNorm_of_norm_eq
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a : Kˣ) (α : L) (hα : Algebra.norm K α = (a : K)) :
    Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a ∈
      Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm := by
  classical
  have hα0 : α ≠ 0 := by
    intro h0
    apply a.ne_zero
    rw [← hα, h0, Algebra.norm_zero]
  let eα : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ :=
    Units.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K).toMonoidHom (Units.mk0 α hα0)
  refine mem_range_idelicNorm_of_includeRight_eq_galNorm K L σ hgen _ eα ?_
  apply Units.ext
  rw [coe_galNorm]
  change (Algebra.TensorProduct.includeRight : AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom
      (algebraMap K (AdeleRing (𝓞 K) K) (a : K)) =
    ∏ i ∈ Finset.range (Module.finrank K L),
      (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) σ)^[i] (α ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K))
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]
  simp only [iterate_sigmaTensor_tmul]
  rw [← LT.TwistedNorm.prod_algEquiv_eq_prod_range_of_generator hgen (fun τ => τ α ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K))]
  have hprod : ∏ τ : L ≃ₐ[K] L, τ α ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K) =
      (∏ τ : L ≃ₐ[K] L, τ α) ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K) := by
    have hl : ∀ l : L, l ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K) =
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) l := fun _ => rfl
    simp only [hl]
    exact (map_prod _ _ _).symm
  rw [hprod, ← Algebra.norm_eq_prod_automorphisms, hα, ← Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.algebraMap_apply']

end Transport

end HW47NS

open HW47NS in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a b : Kˣ) (hab : a ≠ b)
    (ha : (a : K) ∈ Set.range (Algebra.norm K : L → K))
    (z : (AdeleRing (𝓞 K) K)ˣ)
    (h : ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ
        (AutomorphicForm.centralScalar (𝓞 K) K z * AutomorphicForm.globalPoints (𝓞 K) K (diagUnits2 a b)) δ) :
    z ∈ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm := by
  classical
  obtain ⟨δ, y, hy⟩ := h

  have hsG : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K), (⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[Module.finrank K L] g = g :=
    iterate_sigmaGL_finrank K L (AdeleRing (𝓞 K) K) σ
  set X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) := AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
      (AutomorphicForm.centralScalar (𝓞 K) K z * AutomorphicForm.globalPoints (𝓞 K) K (diagUnits2 a b)) with hXdef
  set δ' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) := y⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ y with hδ'
  have hy' : X = y⁻¹ * AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ * y := by
    rw [hXdef]; exact hy

  have hN' : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ' = X := by
    show ((List.range (Module.finrank K L)).map fun i =>
        (⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i] δ').prod = X
    rw [hδ', prod_range_conj, hsG, hy']
    rfl

  have hσN : AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ') =
      δ'⁻¹ * AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ' * δ' := by
    show AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ (((List.range (Module.finrank K L)).map fun i =>
        (⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i] δ').prod) =
      δ'⁻¹ * ((List.range (Module.finrank K L)).map fun i =>
        (⇑(AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i] δ').prod * δ'
    rw [sigmaGL_prod_range, hsG]
  have hfix : AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ X = X := by
    rw [hXdef]; exact sigmaGL_toTensorGL K L (AdeleRing (𝓞 K) K) σ _
  have hcomm : δ' * X = X * δ' := by
    have h1 := hσN
    rw [hN', hfix] at h1
    calc δ' * X = δ' * (δ'⁻¹ * X * δ') := by rw [← h1]
      _ = X * δ' := by simp only [mul_assoc, mul_inv_cancel_left]

  let iRr : AdeleRing (𝓞 K) K →+* L ⊗[K] AdeleRing (𝓞 K) K :=
    (Algebra.TensorProduct.includeRight : AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom
  have hXe : ∀ j k : Fin 2, ((X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) j k =
      iRr (((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
        algebraMap K (AdeleRing (𝓞 K) K) (((diagUnits2 a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) j k)) := by
    intro j k
    rw [hXdef]
    change iRr (((AutomorphicForm.centralScalar (𝓞 K) K z * AutomorphicForm.globalPoints (𝓞 K) K (diagUnits2 a b) :
        GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) j k) = _
    congr 1
    rw [Units.val_mul]
    change (Matrix.scalar (Fin 2) ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
        ((AutomorphicForm.globalPoints (𝓞 K) K (diagUnits2 a b) : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) j k = _
    rw [Matrix.scalar_apply, Matrix.diagonal_mul]
    congr 1
  have e00 : (((diagUnits2 a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 = (a : K) := rfl
  have e11 : (((diagUnits2 a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 1 1 = (b : K) := rfl
  have e10 : (((diagUnits2 a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 1 0 = 0 := rfl
  have e01 : (((diagUnits2 a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 1 = 0 := rfl
  have hX01 : ((X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 1 = 0 := by
    rw [hXe, e01, map_zero, mul_zero, map_zero]
  have hX10 : ((X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 0 = 0 := by
    rw [hXe, e10, map_zero, mul_zero, map_zero]
  have hXdiff : IsUnit (((X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 0 -
      ((X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 1) := by
    rw [hXe, hXe, e00, e11, ← map_sub, ← mul_sub, ← map_sub]
    refine IsUnit.map _ (IsUnit.mul (Units.isUnit z) (IsUnit.map _ ?_))
    exact IsUnit.mk0 _ (sub_ne_zero.mpr fun h => hab (Units.ext h))

  have hd01 : ((δ' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 1 = 0 := by
    have h := congrArg (fun g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 1) hcomm
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hX01, mul_zero, zero_add, zero_mul, add_zero] at h

    have h2 : (((X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 0 -
        ((X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 1) *
        ((δ' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 1 = 0 := by
      rw [sub_mul, ← h, mul_comm, sub_self]
    exact (hXdiff.mul_right_eq_zero).mp h2
  have hd10 : ((δ' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 0 = 0 := by
    have h := congrArg (fun g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 0) hcomm
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hX10, mul_zero, zero_add, zero_mul, add_zero] at h

    have h2 : (((X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 0 -
        ((X : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 1) *
        ((δ' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 0 = 0 := by
      rw [sub_mul, mul_comm _ (((δ' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 1 0), h, sub_self]
    exact (hXdiff.mul_right_eq_zero).mp h2

  obtain ⟨-, -, hN00, -⟩ := prod_range_diagonal K L (AdeleRing (𝓞 K) K) σ δ' hd10 hd01 (Module.finrank K L)
  have hdet : IsUnit (((δ' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))).det :=
    (Units.isUnit δ').map Matrix.detMonoidHom
  rw [Matrix.det_fin_two, hd10, mul_zero, sub_zero] at hdet
  have hu00 : IsUnit (((δ' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) 0 0) :=
    isUnit_of_mul_isUnit_left hdet
  have key1 : Units.map (Algebra.TensorProduct.includeRight :
        AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom.toMonoidHom
        (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) =
      galNorm K L (AdeleRing (𝓞 K) K) σ (Module.finrank K L) hu00.unit := by
    apply Units.ext
    rw [coe_galNorm, IsUnit.unit_spec, ← hN00]
    change iRr (((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (a : K)) = _
    have h := hXe 0 0
    rw [e00] at h
    rw [← h, ← hN']
    rfl
  have hzιa := mem_range_idelicNorm_of_includeRight_eq_galNorm K L σ hgen _ _ key1

  obtain ⟨α, hα⟩ := ha
  have hιa := unitsMap_algebraMap_mem_range_idelicNorm_of_norm_eq K L σ hgen a α hα
  obtain ⟨w₁, hw₁⟩ := hzιa
  obtain ⟨w₂, hw₂⟩ := hιa
  exact ⟨w₁ * w₂⁻¹, by rw [map_mul, map_inv, hw₁, hw₂, mul_inv_cancel_right]⟩

end S_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm
end P2MW
export P2MW.S_AutomorphicForm_mem_range_idelicNorm_of_isNormOf_centralScalar_mul_globalPoints_diagUnits2_of_mem_range_norm (solution)
