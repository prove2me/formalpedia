-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_forall_mem_localCentralizer_isNormConjugator_mul_of_isNormConjugator_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/276de07c-b46f-5c46-b08b-2fc0078e5df9

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_forall_mem_localCentralizer_isNormConjugator_mul_of_isNormConjugator_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace NormSweep

section Commutant
variable {R : Type*} [CommRing R]

theorem exists_eq_smul_one_add_smul_of_commute (g m : Matrix (Fin 2) (Fin 2) R)
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) :
    ∃ x y : R, m = x • (1 : Matrix (Fin 2) (Fin 2) R) + y • g := by
  obtain ⟨u, hu⟩ := hg
  have hinv : (↑u⁻¹ : R) * ((g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) = 1 := by
    have h := u.inv_mul
    rwa [hu, Matrix.trace_fin_two, Matrix.det_fin_two] at h
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  refine ⟨m 0 0 - (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)) * g 0 0,
    (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.zero_eta, Fin.mk_one, Fin.isValue, if_true, if_false, mul_one, mul_zero, zero_add, one_ne_zero,
    zero_ne_one]
  · ring
  · linear_combination (-(m 0 1)) * hinv + (-((↑u⁻¹ : R) * (g 0 0 - g 1 1))) * h01 + (2 * (↑u⁻¹ : R) * g 0 1) * h00
  · linear_combination (-(m 1 0)) * hinv + ((↑u⁻¹ : R) * (g 0 0 - g 1 1)) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h00
  · linear_combination (m 0 0 - m 1 1) * hinv + (2 * (↑u⁻¹ : R) * g 0 1) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h01

end Commutant

section Algebraic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "GE" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "GF" => GL (Fin 2) (v.adicCompletion K)
local notation "ME" => Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "MF" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

noncomputable def pns (δ : GE) (k : ℕ) : GE := ((List.range k).map fun i => (⇑(AutomorphicForm.sigmaGL K L F σ))^[i] δ).prod

theorem pns_zero (δ : GE) : pns K L σ v δ 0 = 1 := by simp [pns]

theorem pns_succ (δ : GE) (k : ℕ) :
    pns K L σ v δ (k + 1) = pns K L σ v δ k * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ := by
  simp [pns, List.range_succ, List.map_append, List.prod_append]

theorem normString_eq_pns (δ : GE) : AutomorphicForm.normString K L F σ δ = pns K L σ v δ (Module.finrank K L) := rfl

theorem mem_twistedCentralizer_iff (δ t : GE) :
    t ∈ AutomorphicForm.twistedCentralizer K L F σ δ ↔ t * δ = δ * AutomorphicForm.sigmaGL K L F σ t := by
  show t * δ * (AutomorphicForm.sigmaGL K L F σ t)⁻¹ = δ ↔ _
  rw [mul_inv_eq_iff_eq_mul]

theorem mul_pns_eq (δ t : GE) (ht : t ∈ AutomorphicForm.twistedCentralizer K L F σ δ) (k : ℕ) :
    t * pns K L σ v δ k = pns K L σ v δ k * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] t := by
  have htδ : t * δ = δ * AutomorphicForm.sigmaGL K L F σ t := (mem_twistedCentralizer_iff K L σ v δ t).mp ht
  induction k with
  | zero => simp [pns_zero]
  | succ k ih =>
    have hk : (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] t * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ =
        (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k + 1] t := by
      rw [← iterate_map_mul, htδ, iterate_map_mul, ← Function.iterate_succ_apply]
    rw [pns_succ, ← mul_assoc, ih, mul_assoc, hk, ← mul_assoc]

theorem pns_mul (δ t : GE) (ht : t ∈ AutomorphicForm.twistedCentralizer K L F σ δ) (k : ℕ) :
    pns K L σ v (t * δ) k = t ^ k * pns K L σ v δ k := by
  induction k with
  | zero => simp [pns_zero]
  | succ k ih =>
    rw [pns_succ, ih, iterate_map_mul, pow_succ, pns_succ]
    have := mul_pns_eq K L σ v δ t ht k

    calc t ^ k * pns K L σ v δ k * ((⇑(AutomorphicForm.sigmaGL K L F σ))^[k] t * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ)
        = t ^ k * (pns K L σ v δ k * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] t) * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ := by
          group
      _ = t ^ k * (t * pns K L σ v δ k) * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ := by rw [this]
      _ = t ^ k * t * (pns K L σ v δ k * (⇑(AutomorphicForm.sigmaGL K L F σ))^[k] δ) := by group

theorem normString_mul_of_mem_twistedCentralizer (δ t : GE)
    (ht : t ∈ AutomorphicForm.twistedCentralizer K L F σ δ) :
    AutomorphicForm.normString K L F σ (t * δ) = t ^ Module.finrank K L * AutomorphicForm.normString K L F σ δ := by
  rw [normString_eq_pns, normString_eq_pns, pns_mul K L σ v δ t ht]

theorem scalar_central (z : Eˣ) (g : GE) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact ((Matrix.scalar_commute (z : E) (fun r' => Commute.all _ r') (g : ME)).eq).symm

theorem toTensorGL_scalar (c : Fˣ) :
    AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap F E).toMonoidHom c) := by
  apply Units.ext
  change (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := F)).toRingHom.mapMatrix (Matrix.scalar (Fin 2) (c : F)) =
    Matrix.scalar (Fin 2) (algebraMap F E c)
  have hc : algebraMap F E (c : F) = (1 : L) ⊗ₜ[K] (c : F) := rfl
  ext i j
  by_cases hij : i = j
  · subst hij; simp [hc]
  · simp [hij]

theorem toTensorGL_scalar_central (c : Fˣ) (g : GE) :
    g * AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * g := by
  rw [toTensorGL_scalar]; exact scalar_central K L v _ g

theorem normString_eq_of_isNormOf_scalar (δ : GE) (c : Fˣ)
    (hδ : AutomorphicForm.IsNormOf K L F σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ) :
    AutomorphicForm.normString K L F σ δ = AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  obtain ⟨y, hy⟩ := hδ
  unfold AutomorphicForm.IsNormConjugator at hy
  calc AutomorphicForm.normString K L F σ δ
      = y * AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * y⁻¹ := by rw [hy]; group
    _ = AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * y * y⁻¹ := by
        rw [toTensorGL_scalar_central]
    _ = _ := mul_inv_cancel_right _ _

theorem isRegularSemisimple_toTensorGL (γ : GF) (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.toTensorGL K L F γ) := by
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  have h : ((AutomorphicForm.toTensorGL K L F γ : GE) : ME) =
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := F)).toRingHom.mapMatrix (γ : MF) := rfl
  rw [h, RingHom.mapMatrix_apply, Matrix.trace, Matrix.det_fin_two]
  rw [Matrix.trace, Matrix.det_fin_two] at hγ
  simp only [Matrix.diag_apply, Matrix.map_apply, Fin.sum_univ_two, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply] at hγ ⊢
  have := hγ.map (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := F))
  simp only [map_sub, map_pow, map_add, map_mul, map_ofNat, Algebra.TensorProduct.includeRight_apply] at this
  convert this using 2

theorem isRegularSemisimple_conj (g x : GE) (hg : AutomorphicForm.IsRegularSemisimple g) :
    AutomorphicForm.IsRegularSemisimple (x * g * x⁻¹) := by
  have := hg.conj x⁻¹
  rwa [inv_inv] at this

theorem exists_eq_smul_one_add_smul_of_mem_localCentralizer (γ₀ : GF) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (γ : GF) (hγ : γ ∈ AutomorphicForm.localCentralizer K v γ₀) :
    ∃ a b : F, (γ : MF) = a • (1 : MF) + b • (γ₀ : MF) := by
  refine exists_eq_smul_one_add_smul_of_commute (γ₀ : MF) (γ : MF) hγ₀ ?_
  rw [← Units.val_mul, ← Units.val_mul, (Subgroup.mem_centralizer_iff.1 hγ) γ₀ rfl]

end Algebraic

section TwistedCommutant

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "GE" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "GF" => GL (Fin 2) (v.adicCompletion K)
local notation "ME" => Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "MF" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

noncomputable def sigmaM : ME →+* ME := (AutomorphicForm.sigmaTensor K L F σ).mapMatrix

theorem coe_sigmaGL (g : GE) : ((AutomorphicForm.sigmaGL K L F σ g : GE) : ME) = sigmaM K L σ v (g : ME) := rfl

theorem sigmaTensor_algebraMap (x : F) :
    AutomorphicForm.sigmaTensor K L F σ (algebraMap F E x) = algebraMap F E x := by
  have hx : algebraMap F E x = (1 : L) ⊗ₜ[K] x := rfl
  rw [hx, AutomorphicForm.sigmaTensor]
  show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F)) ((1 : L) ⊗ₜ[K] x) = (1 : L) ⊗ₜ[K] x
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem sigmaM_algebraMap (r : F) : sigmaM K L σ v (algebraMap F ME r) = algebraMap F ME r := by
  rw [Matrix.algebraMap_eq_diagonal, sigmaM, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  simp only [Function.comp_apply, Pi.algebraMap_apply]
  exact sigmaTensor_algebraMap K L σ v r

noncomputable def Dalg (δ : GE) : Subalgebra F ME where
  carrier := {m | m * (δ : ME) = (δ : ME) * sigmaM K L σ v m}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc, map_mul]
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [add_mul, ha, hb, map_add, mul_add]
  zero_mem' := by simp
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq]
    rw [sigmaM_algebraMap, Algebra.commutes]

theorem mem_Dalg_iff (δ : GE) (m : ME) : m ∈ Dalg K L σ v δ ↔ m * (δ : ME) = (δ : ME) * sigmaM K L σ v m := Iff.rfl

theorem coe_mem_Dalg_iff (δ g : GE) : (g : ME) ∈ Dalg K L σ v δ ↔ g ∈ AutomorphicForm.twistedCentralizer K L F σ δ := by
  rw [mem_twistedCentralizer_iff, mem_Dalg_iff, Units.ext_iff, Units.val_mul, Units.val_mul, coe_sigmaGL]

theorem adjoin_le_Dalg (δ u₀ : GE) (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L F σ δ) :
    Algebra.adjoin F {(u₀ : ME)} ≤ Dalg K L σ v δ :=
  Algebra.adjoin_le (Set.singleton_subset_iff.2 ((coe_mem_Dalg_iff K L σ v δ u₀).2 hu₀))

theorem mem_Dalg_mul (δ u₀ : GE) (m : ME) (hm : m ∈ Dalg K L σ v δ) (hcomm : m * (u₀ : ME) = (u₀ : ME) * m) :
    m ∈ Dalg K L σ v (u₀ * δ) := by
  rw [mem_Dalg_iff] at hm ⊢
  rw [Units.val_mul, ← mul_assoc, hcomm, mul_assoc, hm, mul_assoc]

theorem commute_of_mem_adjoin_singleton (x m : ME) (hm : m ∈ Algebra.adjoin F {x}) : m * x = x * m :=
  (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hm (fun b hb => by
    rw [Set.mem_singleton_iff.1 hb]; exact Commute.refl x)).symm.eq

noncomputable def conjAlgHom (y : GE) : ME →ₐ[F] ME where
  toFun m := (y : ME) * m * ((y⁻¹ : GE) : ME)
  map_one' := by rw [mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  map_mul' a b := by
    calc (y : ME) * (a * b) * ((y⁻¹ : GE) : ME)
        = (y : ME) * a * (((y⁻¹ : GE) : ME) * (y : ME)) * b * ((y⁻¹ : GE) : ME) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]; noncomm_ring
      _ = (y : ME) * a * ((y⁻¹ : GE) : ME) * ((y : ME) * b * ((y⁻¹ : GE) : ME)) := by noncomm_ring
  map_zero' := by simp
  map_add' a b := by rw [mul_add, add_mul]
  commutes' r := by
    rw [(Algebra.commutes r (y : ME)).symm, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem conjAlgHom_apply (y : GE) (m : ME) : conjAlgHom K L v y m = (y : ME) * m * ((y⁻¹ : GE) : ME) := rfl

noncomputable def iotaM : MF →ₐ[F] ME := (Algebra.ofId F E).mapMatrix

theorem iotaM_coe (β : GF) : iotaM K L v (β : MF) = ((AutomorphicForm.toTensorGL K L F β : GE) : ME) := rfl

noncomputable def phi (y₀ : GE) : MF →ₐ[F] ME := (conjAlgHom K L v y₀).comp (iotaM K L v)

theorem phi_coe (y₀ : GE) (β : GF) :
    phi K L v y₀ (β : MF) = ((y₀ * AutomorphicForm.toTensorGL K L F β * y₀⁻¹ : GE) : ME) := by
  rw [phi, AlgHom.comp_apply, iotaM_coe, conjAlgHom_apply, Units.val_mul, Units.val_mul]

theorem coe_toTensorGL_scalar (c : Fˣ) :
    ((AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : GE) : ME) = algebraMap F ME (c : F) := by
  rw [toTensorGL_scalar, Matrix.algebraMap_eq_diagonal]
  change Matrix.scalar (Fin 2) (algebraMap F E (c : F)) = _
  rw [Matrix.scalar_apply]
  congr 1

theorem phi_mem (δ u₀ : GE) (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L F σ δ) (c : Fˣ)
    (hδ : AutomorphicForm.IsNormOf K L F σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (γ₀ : GF) (y₀ : GE) (hy₀ : AutomorphicForm.IsNormConjugator K L F σ γ₀ (u₀ * δ) y₀)
    (m : MF) (hm : m ∈ Algebra.adjoin F {(γ₀ : MF)}) :
    phi K L v y₀ m ∈ Algebra.adjoin F {(u₀ : ME)} := by

  have hφγ₀ : phi K L v y₀ (γ₀ : MF) =
      ((u₀ ^ Module.finrank K L * AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : GE) : ME) := by
    rw [phi_coe]
    congr 1
    unfold AutomorphicForm.IsNormConjugator at hy₀
    rw [hy₀, normString_mul_of_mem_twistedCentralizer K L σ v δ u₀ hu₀, normString_eq_of_isNormOf_scalar K L σ v δ c hδ]
    group
  have hmem : phi K L v y₀ (γ₀ : MF) ∈ Algebra.adjoin F {(u₀ : ME)} := by
    rw [hφγ₀, Units.val_mul, Units.val_pow_eq_pow_val, coe_toTensorGL_scalar]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _)
      (Subalgebra.algebraMap_mem _ _)
  have hmap : (Algebra.adjoin F {(γ₀ : MF)}).map (phi K L v y₀) ≤ Algebra.adjoin F {(u₀ : ME)} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hmem)
  exact hmap ⟨m, hm, rfl⟩

theorem continuous_toTensorGL : Continuous (AutomorphicForm.toTensorGL K L F : GF → GE) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L F
  have hf : Continuous (fun b : F => algebraMap F E b) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E)
  have hf' : Continuous ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := F)).toRingHom : F → E) := hf
  have hM : Continuous ((Algebra.TensorProduct.includeRight (R := K) (A := L) (B := F)).toRingHom.mapMatrix :
      MF → ME) := continuous_id.matrix_map hf'
  exact Continuous.units_map _ hM

theorem main (c : Fˣ) (δ : GE)
    (hδ : AutomorphicForm.IsNormOf K L F σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (u₀ : GE) (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L F σ δ)
    (γ₀ : GF) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (y₀ : GE) (hy₀ : AutomorphicForm.IsNormConjugator K L F σ γ₀ (u₀ * δ) y₀) :
    ∀ V ∈ nhds (1 : GE), ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GF),
      ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
        ∃ u ∈ V, u ∈ AutomorphicForm.twistedCentralizer K L F σ δ ∧
          u ∈ AutomorphicForm.twistedCentralizer K L F σ (u₀ * δ) ∧
          AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L F σ (u * δ)) ∧
          AutomorphicForm.IsNormConjugator K L F σ γ (u * δ) y₀ := by
  intro V hV
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L F

  set Ψ : GF → GE := fun β => y₀ * AutomorphicForm.toTensorGL K L F β * y₀⁻¹ with hΨ
  have hΨc : Continuous Ψ := (continuous_const.mul (continuous_toTensorGL K L v)).mul continuous_const
  have hΨ1 : Ψ 1 = 1 := by simp [hΨ]
  have hV' : Ψ ⁻¹' V ∈ nhds (1 : GF) := hΨc.continuousAt.preimage_mem_nhds (by rw [hΨ1]; exact hV)
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  obtain ⟨W, hW, hroot⟩ := AutomorphicForm.exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple K v γ₀ hγ₀ c
    (Module.finrank K L) hn (Ψ ⁻¹' V) hV'
  refine ⟨W, hW, fun γ hγW hγT hγreg => ?_⟩
  obtain ⟨β, hβV, hβadj, hβpow⟩ := hroot γ hγW hγT
  have hm := phi_mem K L σ v δ u₀ hu₀ c hδ γ₀ y₀ hy₀ _ hβadj
  have hΨβ : ((Ψ β : GE) : ME) = phi K L v y₀ (β : MF) := by rw [phi_coe]
  have hu1 : Ψ β ∈ AutomorphicForm.twistedCentralizer K L F σ δ := by
    rw [← coe_mem_Dalg_iff, hΨβ]
    exact adjoin_le_Dalg K L σ v δ u₀ hu₀ hm
  have hu2 : Ψ β ∈ AutomorphicForm.twistedCentralizer K L F σ (u₀ * δ) := by
    rw [← coe_mem_Dalg_iff, hΨβ]
    exact mem_Dalg_mul K L σ v δ u₀ _ (adjoin_le_Dalg K L σ v δ u₀ hu₀ hm) (commute_of_mem_adjoin_singleton K L v _ _ hm)

  have hN : AutomorphicForm.normString K L F σ (Ψ β * δ) = y₀ * AutomorphicForm.toTensorGL K L F γ * y₀⁻¹ := by
    rw [normString_mul_of_mem_twistedCentralizer K L σ v δ _ hu1, normString_eq_of_isNormOf_scalar K L σ v δ c hδ, hΨ]
    simp only []
    rw [conj_pow, ← map_pow, hβpow, map_mul, map_inv]

    set C : GE := AutomorphicForm.toTensorGL K L F (Matrix.GeneralLinearGroup.scalar (Fin 2) c) with hCdef
    have hc : ∀ g : GE, g * C = C * g := fun g => by rw [hCdef]; exact toTensorGL_scalar_central K L v c g
    have hcinv : ∀ g : GE, g * C⁻¹ = C⁻¹ * g := fun g => by
      calc g * C⁻¹ = C⁻¹ * (C * g) * C⁻¹ := by group
        _ = C⁻¹ * (g * C) * C⁻¹ := by rw [hc g]
        _ = C⁻¹ * g := by group
    set X : GE := y₀ * AutomorphicForm.toTensorGL K L F γ * y₀⁻¹ with hXdef
    calc y₀ * (C⁻¹ * AutomorphicForm.toTensorGL K L F γ) * y₀⁻¹ * C
        = (y₀ * C⁻¹) * AutomorphicForm.toTensorGL K L F γ * y₀⁻¹ * C := by group
      _ = (C⁻¹ * y₀) * AutomorphicForm.toTensorGL K L F γ * y₀⁻¹ * C := by rw [hcinv y₀]
      _ = C⁻¹ * (X * C) := by rw [hXdef]; group
      _ = C⁻¹ * (C * X) := by rw [hc X]
      _ = X := by group
  refine ⟨Ψ β, hβV, hu1, hu2, ?_, ?_⟩
  · rw [hN]; exact isRegularSemisimple_conj K L v _ y₀ (isRegularSemisimple_toTensorGL K L v γ hγreg)
  · show AutomorphicForm.toTensorGL K L F γ = y₀⁻¹ * AutomorphicForm.normString K L F σ (Ψ β * δ) * y₀
    rw [hN]; group

end TwistedCommutant

end NormSweep

open MeasureTheory NumberField IsDedekindDomain in
open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (y₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy₀ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ₀ (u₀ * δ) y₀) :
    ∀ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)),
        ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ → AutomorphicForm.IsRegularSemisimple γ →
          ∃ u ∈ V, u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ∧
            u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ∧
            AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ (u * δ)) ∧
            AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ (u * δ) y₀ :=
  NormSweep.main K L σ v c δ hδ u₀ hu₀ γ₀ hγ₀ y₀ hy₀

end S_AutomorphicForm_exists_nhds_forall_mem_localCentralizer_isNormConjugator_mul_of_isNormConjugator_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_forall_mem_localCentralizer_isNormConjugator_mul_of_isNormConjugator_mul (solution)
