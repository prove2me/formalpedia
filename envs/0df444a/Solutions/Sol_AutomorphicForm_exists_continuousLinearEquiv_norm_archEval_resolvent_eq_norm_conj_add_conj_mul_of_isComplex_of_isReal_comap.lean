-- Prove2me | solution 1 for AutomorphicForm.exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e7411d12-4a7c-5c3b-a099-2ed1e9691144

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

import Definitions.Def_M4aHerbrand_ArchSemilocal
import Theorems.Thm_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj
import Theorems.Thm_AutomorphicForm_sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul
import Theorems.Thm_AutomorphicForm_sigmaTensor_twistedResolvent_sub_mul_eq_one_sub_norm_smul_and_twistedResolvent_sigmaTensor_sub_mul_eq
import Theorems.Thm_AutomorphicForm_archIdent_tmul_apply
import Theorems.Thm_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isComplex
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped NumberField.LiesOver

noncomputable section

namespace TwICOS

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "E" => (L ⊗[K] InfiniteAdeleRing K)

omit K L in
theorem norm_algEquiv (A : Type) [CommRing A] {S T : Type} [Ring S] [Ring T] [Algebra A S] [Algebra A T]
    (e : S ≃ₐ[A] T) (x : S) : Algebra.norm A (e x) = Algebra.norm A x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : (Algebra.lmul A T (e x) : T →ₗ[A] T) =
      (e.toLinearEquiv : S →ₗ[A] T) ∘ₗ (Algebra.lmul A S x : S →ₗ[A] S) ∘ₗ (e.toLinearEquiv.symm : T →ₗ[A] S) := by
    ext y; simp [Algebra.coe_lmul_eq_mul]
  rw [h, LinearMap.det_conj]

theorem rcomm_map (A : Type) [CommRing A] [Algebra K A] (g : L ≃ₐ[K] L) (z : A ⊗[K] L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L (Algebra.TensorProduct.map (AlgHom.id K A) (g : L →ₐ[K] L) z) =
      AutomorphicForm.sigmaTensor K L A g (TensorProduct.RightActions.Algebra.TensorProduct.comm K A L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    rw [Algebra.TensorProduct.map_tmul]
    show (g : L →ₐ[K] L) l ⊗ₜ[K] (AlgHom.id K A) a = (Algebra.TensorProduct.map (g : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
    rw [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem algebraMap_norm_eq_prod_sigmaTensor [FiniteDimensional K L] [IsGalois K L] (A : Type) [CommRing A] [Algebra K A] (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) = ∏ g : L ≃ₐ[K] L, AutomorphicForm.sigmaTensor K L A g x := by
  classical
  set c := TensorProduct.RightActions.Algebra.TensorProduct.comm K A L with hc
  obtain ⟨z, rfl⟩ : ∃ z, x = c z := ⟨c.symm x, (c.apply_symm_apply x).symm⟩
  rw [norm_algEquiv, ← c.commutes, Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv K L A z, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [hc, rcomm_map]

variable [IsGalois K L] (σ : L ≃ₐ[K] L)

theorem finrank_eq_two (hdeg : (Module.finrank K L).Prime) (w : InfinitePlace K) (w' : InfinitePlace L)
    (hw'w : w'.comap (algebraMap K L) = w) (hw : w.IsReal) (hw' : w'.IsComplex) : Module.finrank K L = 2 := by
  have hnu : ¬ w'.IsUnramified K := by
    rw [NumberField.InfinitePlace.isUnramified_iff]
    push Not
    refine ⟨NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw', ?_⟩
    rw [hw'w]; exact NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr hw
  have hev := NumberField.InfinitePlace.even_finrank_of_not_isUnramified hnu
  exact (hdeg.even_iff).mp hev

theorem sigma_mul_self (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (h2 : Module.finrank K L = 2) : σ * σ = 1 := by
  have ho : orderOf σ = 2 := by
    rw [← h2, ← IsGalois.card_aut_eq_finrank, orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card]
  rw [← pow_two, ← ho, pow_orderOf_eq_one]

theorem sigma_ne_one (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (h2 : Module.finrank K L = 2) : σ ≠ 1 := by
  intro h
  have ho : orderOf σ = 2 := by
    rw [← h2, ← IsGalois.card_aut_eq_finrank, orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card]
  rw [h, orderOf_one] at ho
  exact absurd ho (by norm_num)

theorem symm_eq (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (h2 : Module.finrank K L = 2) : σ.symm = σ := by
  have := sigma_mul_self K L σ hgen h2
  rw [show σ.symm = σ⁻¹ from rfl]
  exact inv_eq_of_mul_eq_one_left this

theorem comap_sigma_eq (hdeg : (Module.finrank K L).Prime) (w : InfinitePlace K) (w' : InfinitePlace L)
    (hw'w : w'.comap (algebraMap K L) = w) (hw : w.IsReal) (hw' : w'.IsComplex) :
    w'.comap (σ : L →+* L) = w' := by
  classical
  have h2 := finrank_eq_two K L hdeg w w' hw'w hw hw'
  have hsum := (AutomorphicForm.sum_mult_mul_log_one_add_norm_archEval_archIdent_smul_inv_eq_and_sum_mult_eq_finrank_mul
    K L w 1 0).2.2
  rw [h2, NumberField.InfinitePlace.mult, if_pos hw, mul_one] at hsum
  by_contra hne
  have hmem1 : w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w) := by
    simp [hw'w]
  have hmem2 : w'.comap (σ : L →+* L) ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← NumberField.InfinitePlace.comap_comp, ← hw'w]
    congr 1; ext k; simp
  have hle : w'.mult + (w'.comap (σ : L →+* L)).mult ≤
      ∑ v ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w), v.mult := by
    rw [← Finset.sum_pair (fun h => hne h.symm)]
    · exact Finset.sum_le_sum_of_subset (by
        intro v hv
        rw [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hmem1
        · exact hmem2)
  rw [hsum] at hle
  have h1 : w'.mult = 2 := by rw [NumberField.InfinitePlace.mult, if_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw')]
  have h3 : 1 ≤ (w'.comap (σ : L →+* L)).mult := by unfold NumberField.InfinitePlace.mult; split_ifs <;> omega
  omega

theorem resolvent_eq (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (h2 : Module.finrank K L = 2)
    (r : E) (c : (InfiniteAdeleRing K)ˣ) (hc : (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r)
    (M : E →ₗ[InfiniteAdeleRing K] E)
    (hM1 : ∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y)
    (hM2 : ∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y)
    (y : E) :
    M y = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y + AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ r * y := by

  set T : E → E := fun y => AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y with hT
  have hsurj : ∃ y₀, y = T y₀ := by
    refine ⟨((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M y, ?_⟩
    have e1 : T (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M y) =
        ((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • T (M y) := by
      simp only [hT]
      rw [AutomorphicForm.rightActions_smul_eq, AutomorphicForm.rightActions_smul_eq, map_mul, mul_sub]
      congr 1
      · congr 1
        show (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K (InfiniteAdeleRing K))) ((1 : L) ⊗ₜ[K] _) = _
        rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
      · ring
    rw [e1]
    show y = ((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y)
    rw [hM1, smul_smul, Units.inv_mul, one_smul]
  obtain ⟨y₀, rfl⟩ := hsurj

  have hC1 := (AutomorphicForm.sigmaTensor_twistedResolvent_sub_mul_eq_one_sub_norm_smul_and_twistedResolvent_sigmaTensor_sub_mul_eq
    K L σ hgen (InfiniteAdeleRing K) r y₀).2
  rw [h2] at hC1
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Finset.prod_empty, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul, zero_add, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
    symm_eq K L σ hgen h2] at hC1

  have hss : ∀ x : E, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K (InfiniteAdeleRing K)))
          ((Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K (InfiniteAdeleRing K))) (l ⊗ₜ[K] a)) = l ⊗ₜ[K] a
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      show (σ (σ l)) ⊗ₜ[K] a = l ⊗ₜ[K] a
      rw [show σ (σ l) = (σ * σ) l from rfl, sigma_mul_self K L σ hgen h2]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [hss, Finset.prod_empty, one_mul] at hC1
  show M (T y₀) = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (T y₀) +
    AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ r * T y₀
  rw [hM2 y₀]
  simp only [hT]
  rw [AutomorphicForm.rightActions_smul_eq, ← TensorProduct.RightActions.algebraMap_eval, hc]
  exact hC1.symm

end TwICOS

end

open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (w : NumberField.InfinitePlace K) (w' : NumberField.InfinitePlace L) (hw'w : w'.comap (algebraMap K L) = w)
    (hw : w.IsReal) (hw' : w'.IsComplex) :
    ∃ (e : NumberField.mixedEmbedding.mixedSpace L ≃L[ℝ] (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)))) (κ : NNReal), κ ≠ 0 ∧
      Measure.map (fun y : (L ⊗[K] InfiniteAdeleRing K) => e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))) lam =
        κ • ((volume : Measure ℂ).prod
          ((volume : Measure ({v : NumberField.InfinitePlace L // v.IsReal} → ℝ)).prod
            (volume : Measure ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)))) ∧
      (∀ y : (L ⊗[K] InfiniteAdeleRing K), (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))).1 = (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩) ∧
      ∀ (r : (L ⊗[K] InfiniteAdeleRing K)) (c : (InfiniteAdeleRing K)ˣ),
        (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r →
      ∀ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K),
        (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) →
        (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) →
      (∀ y : (L ⊗[K] InfiniteAdeleRing K),
        ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ =
          ‖(starRingEnd ℂ) ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩) +
            (starRingEnd ℂ) ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L r)).2 ⟨w', hw'⟩) * (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩‖) ∧
      ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ =
        |1 - ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L r)).2 ⟨w', hw'⟩‖ ^ 2| := by
  classical
  haveI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have h2 := TwICOS.finrank_eq_two K L hdeg w w' hw'w hw hw'
  have hσσ : w'.comap (σ : L →+* L) = w' := TwICOS.comap_sigma_eq K L σ hdeg w w' hw'w hw hw'

  set C := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw' with hCdef
  have hCn : ∀ x : w'.Completion, ‖C x‖ = ‖x‖ := fun x => by
    rw [hCdef, NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w').norm_map_of_map_zero (map_zero _) x
  have hZ : ∀ x : L ⊗[K] InfiniteAdeleRing K,
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L x)).2 ⟨w', hw'⟩ =
        C (AutomorphicForm.archIdent K L x w') := fun x => by
    rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply, hCdef, NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]

  obtain ⟨hiso, hii, hiii, -, hv⟩ :=
    AutomorphicForm.archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj K L σ w'
  have hconj : ∀ y : L ⊗[K] InfiniteAdeleRing K,
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L
          (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y))).2 ⟨w', hw'⟩ =
        (starRingEnd ℂ) ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩) := by
    rcases hv w' hw' hw' hσσ.symm with heq | hc
    · exfalso
      apply TwICOS.sigma_ne_one K L σ hgen h2
      ext l
      have h1 := heq (l ⊗ₜ[K] (1 : InfiniteAdeleRing K))
      have eσ : AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (l ⊗ₜ[K] (1 : InfiniteAdeleRing K)) =
          (σ l) ⊗ₜ[K] (1 : InfiniteAdeleRing K) := by
        show (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K (InfiniteAdeleRing K))) (l ⊗ₜ[K] 1) = _
        rw [Algebra.TensorProduct.map_tmul]; rfl
      rw [eσ, hZ, hZ] at h1
      have h3 := C.injective h1
      have ht1 := AutomorphicForm.archIdent_tmul_apply K L (σ l) 1 w'
      have ht2 := AutomorphicForm.archIdent_tmul_apply K L l 1 w'
      rw [show (1 : InfiniteAdeleRing K) (w'.comap (algebraMap K L)) = 1 from rfl, map_one, one_mul] at ht1 ht2
      rw [ht1, ht2] at h3
      exact (algebraMap L w'.Completion).injective h3
    · exact hc

  obtain ⟨e, he, he1⟩ := NumberField.mixedEmbedding.exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isComplex L ⟨w', hw'⟩
  have hH := NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L
  set ι : L ⊗[K] InfiniteAdeleRing K → NumberField.mixedEmbedding.mixedSpace L :=
    fun y => NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y) with hι
  set eH : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ NumberField.mixedEmbedding.mixedSpace L :=
    (AutomorphicForm.archIdentHomeomorph K L).trans (hH.homeomorph _) with heH
  have heHc : (eH : L ⊗[K] InfiniteAdeleRing K → NumberField.mixedEmbedding.mixedSpace L) = ι := rfl
  set eA : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ+ NumberField.mixedEmbedding.mixedSpace L :=
    { ((AutomorphicForm.archIdentEquiv K L).toAddEquiv.trans (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).toAddEquiv) with
      continuous_toFun := eH.continuous
      continuous_invFun := by
        have : ⇑((AutomorphicForm.archIdentEquiv K L).toAddEquiv.trans
            (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).toAddEquiv).symm = ⇑eH.symm := by
          funext X
          apply eH.injective
          rw [eH.apply_symm_apply, heHc, hι]
          show NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdentEquiv K L
            ((AutomorphicForm.archIdentEquiv K L).symm ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).symm X))) = X
          rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        rw [AddEquiv.toEquiv_eq_coe]
        show Continuous ⇑((AutomorphicForm.archIdentEquiv K L).toAddEquiv.trans
            (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).toAddEquiv).symm
        rw [this]; exact eH.symm.continuous } with heA
  have heAc : (eA : L ⊗[K] InfiniteAdeleRing K → NumberField.mixedEmbedding.mixedSpace L) = ι := rfl
  haveI : (Measure.map ι lam).IsAddHaarMeasure := by rw [← heAc]; exact eA.isAddHaarMeasure_map lam
  obtain ⟨κ, hκ⟩ : ∃ κ : NNReal, Measure.map ι lam = κ • (volume : Measure (NumberField.mixedEmbedding.mixedSpace L)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hιm : Measurable ι := heHc ▸ eH.continuous.measurable
  have hκ0 : κ ≠ 0 := by
    intro h0
    have h1 : Measure.map ι lam = 0 := by rw [hκ, h0, zero_smul]
    have h3 : Measure.map ι lam Set.univ = 0 := by rw [h1]; rfl
    rw [Measure.map_apply hιm MeasurableSet.univ, Set.preimage_univ] at h3
    exact (IsOpen.measure_ne_zero lam isOpen_univ Set.univ_nonempty) h3
  have hmap : Measure.map (fun y : L ⊗[K] InfiniteAdeleRing K => e (ι y)) lam =
      κ • ((volume : Measure ℂ).prod
        ((volume : Measure ({v : NumberField.InfinitePlace L // v.IsReal} → ℝ)).prod
          (volume : Measure ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)))) := by
    rw [show (fun y : L ⊗[K] InfiniteAdeleRing K => e (ι y)) = (e : _ → _) ∘ ι from rfl,
      ← Measure.map_map e.continuous.measurable hιm, hκ, Measure.map_smul, he.map_eq]
    rfl
  refine ⟨e, κ, hκ0, hmap, fun y => he1 _, ?_⟩
  intro r c hc M hM1 hM2
  refine ⟨fun y => ?_, ?_⟩
  ·
    rw [TwICOS.resolvent_eq K L σ hgen h2 r c hc M hM1 hM2 y, map_add, map_mul, map_add, map_mul,
      NumberField.AdelicLevel.archEval_apply, NumberField.AdelicLevel.archEval_apply, NumberField.AdelicLevel.archEval_apply,
      ← hCn, map_add, map_mul, ← hZ, ← hZ, ← hZ, hconj y, hconj r]
  ·
    subst hw'w
    letI : w'.1.LiesOver (w'.comap (algebraMap K L)).1 := ⟨rfl⟩
    have ht := AutomorphicForm.archIdent_tmul_apply K L 1 (c : InfiniteAdeleRing K) w'
    rw [map_one, mul_one] at ht

    have hiso2 : ‖algebraMap (w'.comap (algebraMap K L)).Completion w'.Completion ((c : InfiniteAdeleRing K) (w'.comap (algebraMap K L)))‖ =
        ‖(c : InfiniteAdeleRing K) (w'.comap (algebraMap K L))‖ := by
      show ‖(NumberField.InfinitePlace.LiesOver.isometry_algebraMap w' (w'.comap (algebraMap K L))).mapRingHom _‖ = _
      exact (Isometry.isometry_mapRingHom _).norm_map_of_map_zero (map_zero _) _
    rw [NumberField.AdelicLevel.archEval_apply, ← hiso2, ← ht, ← hCn, ← hZ]

    have huniv : (Finset.univ : Finset (L ≃ₐ[K] L)) = {1, σ} := by
      symm
      apply Finset.eq_univ_of_card
      rw [Finset.card_pair (TwICOS.sigma_ne_one K L σ hgen h2).symm, ← Nat.card_eq_fintype_card,
        IsGalois.card_aut_eq_finrank, h2]
    have hσ1 : ∀ x : L ⊗[K] InfiniteAdeleRing K, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) 1 x = x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul l a =>
        show (Algebra.TensorProduct.map ((1 : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K (InfiniteAdeleRing K))) (l ⊗ₜ[K] a) = _
        rw [Algebra.TensorProduct.map_tmul]; rfl
      | add x y hx hy => rw [map_add, hx, hy]
    have hN : algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) (Algebra.norm (InfiniteAdeleRing K) r) =
        r * AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ r := by
      rw [TwICOS.algebraMap_norm_eq_prod_sigmaTensor K L, huniv, Finset.prod_pair (TwICOS.sigma_ne_one K L σ hgen h2).symm, hσ1]
    have h1c : ((1 : L) ⊗ₜ[K] (c : InfiniteAdeleRing K)) = 1 - r * AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ r := by
      rw [← TensorProduct.RightActions.algebraMap_eval, hc, map_sub, map_one, hN]
    rw [h1c, map_sub, map_one, map_mul, map_sub, map_one, map_mul, Prod.snd_sub, Prod.snd_one, Prod.snd_mul,
      Pi.sub_apply, Pi.one_apply, Pi.mul_apply, hconj r, mul_comm, Complex.conj_mul', ← Complex.ofReal_one,
      ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

end S_AutomorphicForm_exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap
end P2MW
export P2MW.S_AutomorphicForm_exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap (solution)
