-- Prove2me | solution 1 for AutomorphicForm.exists_normString_diagUnits2_eq_toTensorGL_diagUnits2_iff_exists_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5f3ae0ad-3e9c-5d34-9ae5-795fd4f4f761

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_congr_apply_of_isGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_normString_diagUnits2_eq_toTensorGL_diagUnits2_iff_exists_norm_eq

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open LanglandsTunnell.CubicInduction (diagUnits2)

set_option linter.unusedSectionVars false

namespace TorusLift28

section Generic
variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

abbrev σU : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ := Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A)

def D : (L ⊗[K] A)ˣ × (L ⊗[K] A)ˣ →* GL (Fin 2) (L ⊗[K] A) where
  toFun p := diagUnits2 p.1 p.2
  map_one' := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
      LanglandsTunnell.CubicInduction.coe_diagUnits2]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem D_apply (p : (L ⊗[K] A)ˣ × (L ⊗[K] A)ˣ) : D K L A p = diagUnits2 p.1 p.2 := rfl

theorem sigmaGL_D (p : (L ⊗[K] A)ˣ × (L ⊗[K] A)ˣ) :
    AutomorphicForm.sigmaGL K L A σ (D K L A p) = D K L A (Prod.map (σU K L A σ) (σU K L A σ) p) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [D_apply, D_apply]
  show AutomorphicForm.sigmaTensor K L A σ ((diagUnits2 p.1 p.2 : GL (Fin 2) (L ⊗[K] A)) i j) = _
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp [Prod.map, Units.coe_map]

theorem sigmaGL_iterate_D (n : ℕ) (p : (L ⊗[K] A)ˣ × (L ⊗[K] A)ˣ) :
    (⇑(AutomorphicForm.sigmaGL K L A σ))^[n] (D K L A p) =
      D K L A ((Prod.map (σU K L A σ) (σU K L A σ))^[n] p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, sigmaGL_D, ih]

theorem list_range_map_prod {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ, List.map_singleton,
      List.prod_singleton]

theorem normString_D (p : (L ⊗[K] A)ˣ × (L ⊗[K] A)ˣ) :
    AutomorphicForm.normString K L A σ (D K L A p) =
      D K L A (∏ i ∈ Finset.range (Module.finrank K L), (Prod.map (σU K L A σ) (σU K L A σ))^[i] p) := by
  unfold AutomorphicForm.normString
  rw [← list_range_map_prod, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact sigmaGL_iterate_D K L A σ i p

theorem coe_iterate_σU (n : ℕ) (x : (L ⊗[K] A)ˣ) :
    (((⇑(σU K L A σ))^[n] x : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (⇑(AutomorphicForm.sigmaTensor K L A σ))^[n] (x : L ⊗[K] A) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

theorem iterate_sigmaTensor (n : ℕ) (x : L ⊗[K] A) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[n] x = AutomorphicForm.sigmaTensor K L A (σ ^ n) x := by
  induction n generalizing x with
  | zero =>
    show x = _
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show l ⊗ₜ a = Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K A) (l ⊗ₜ a)
      rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)
          (Algebra.TensorProduct.map (σ ^ n).toAlgHom (AlgHom.id K A) (l ⊗ₜ a)) =
        Algebra.TensorProduct.map (σ * σ ^ n).toAlgHom (AlgHom.id K A) (l ⊗ₜ a)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end Generic

section Norm
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (v : HeightOneSpectrum (𝓞 K))

include hgen in
open scoped TensorProduct.RightActions in

theorem prod_range_iterate_sigmaTensor_eq_algebraMap_norm (x : L ⊗[K] v.adicCompletion K) :
    ∏ i ∈ Finset.range (Module.finrank K L), (⇑(AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ))^[i] x =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (Algebra.norm (v.adicCompletion K) x) := by
  rw [Algebra.TensorProduct.algebraMap_norm_eq_prod_congr_apply_of_isGalois]
  have hord : orderOf σ = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  have htop : Subgroup.zpowers σ = ⊤ := by
    rw [eq_top_iff]; intro τ _; exact hgen τ
  let e : Fin (orderOf σ) ≃ (L ≃ₐ[K] L) :=
    (finEquivZPowers (isOfFinOrder_of_finite σ)).trans
      ((MulEquiv.subgroupCongr htop).toEquiv.trans Subgroup.topEquiv.toEquiv)
  have he : ∀ i : Fin (orderOf σ), e i = σ ^ (i : ℕ) := fun i => by
    simp only [e, Equiv.trans_apply, finEquivZPowers_apply]
    rfl
  rw [Finset.prod_range, ← hord]
  refine Fintype.prod_equiv e _ _ fun i => ?_
  rw [he, iterate_sigmaTensor, Algebra.TensorProduct.congr_apply]
  rfl

end Norm

end TorusLift28

open TorusLift28 in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (a b : (v.adicCompletion K)ˣ) :
    (∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b)) ↔
      ((∃ α : (L ⊗[K] v.adicCompletion K)ˣ, Algebra.norm (v.adicCompletion K) (α : (L ⊗[K] v.adicCompletion K)) = (a : (v.adicCompletion K))) ∧
        (∃ β : (L ⊗[K] v.adicCompletion K)ˣ, Algebra.norm (v.adicCompletion K) (β : (L ⊗[K] v.adicCompletion K)) = (b : (v.adicCompletion K)))) := by
  have hinj : Function.Injective (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

  have hns : ∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
      AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
        diagUnits2 (∏ i ∈ Finset.range (Module.finrank K L), (⇑(σU K L (v.adicCompletion K) σ))^[i] α)
          (∏ i ∈ Finset.range (Module.finrank K L), (⇑(σU K L (v.adicCompletion K) σ))^[i] β) := by
    intro α β
    have h := normString_D K L (v.adicCompletion K) σ (α, β)
    rw [D_apply, D_apply, Prod.fst_prod, Prod.snd_prod] at h
    simpa only [Prod.map_iterate, Prod.map_fst, Prod.map_snd] using h
  have hentry : ∀ α : (L ⊗[K] v.adicCompletion K)ˣ,
      ((∏ i ∈ Finset.range (Module.finrank K L), (⇑(σU K L (v.adicCompletion K) σ))^[i] α : (L ⊗[K] v.adicCompletion K)ˣ) :
        L ⊗[K] v.adicCompletion K) =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
        (Algebra.norm (v.adicCompletion K) (α : L ⊗[K] v.adicCompletion K)) := by
    intro α
    rw [Units.coe_prod, ← prod_range_iterate_sigmaTensor_eq_algebraMap_norm K L σ hgen v]
    exact Finset.prod_congr rfl fun i _ => coe_iterate_σU K L (v.adicCompletion K) σ i α
  have htt : ∀ a b : (v.adicCompletion K)ˣ, ∀ i j : Fin 2,
      ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) ((diagUnits2 a b : GL (Fin 2) (v.adicCompletion K)) i j) :=
    fun a b i j => rfl
  constructor
  · rintro ⟨α, β, h⟩
    rw [hns] at h
    have h00 := congrArg (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) h
    have h11 := congrArg (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) h
    simp only [htt, LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h11
    rw [hentry] at h00 h11
    exact ⟨⟨α, hinj h00⟩, ⟨β, hinj h11⟩⟩
  · rintro ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
    refine ⟨α, β, ?_⟩
    rw [hns]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [htt, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    fin_cases i <;> fin_cases j <;> simp [hentry, hα, hβ]

end S_AutomorphicForm_exists_normString_diagUnits2_eq_toTensorGL_diagUnits2_iff_exists_norm_eq
end P2MW
export P2MW.S_AutomorphicForm_exists_normString_diagUnits2_eq_toTensorGL_diagUnits2_iff_exists_norm_eq (solution)
