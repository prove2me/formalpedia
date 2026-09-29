-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/29e159e2-9bb8-58fb-801c-9df595fa4a0f

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_isCuspSubrep_span_cyclic_and_mem_and_le
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_exists_integral_rightTranslate_eq_inv_card_mul_sum
import Theorems.Thm_AutomorphicForm_exists_integral_rightConv_eq_rightConv
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul
import Theorems.Thm_AutomorphicForm_exists_linearMap_archCutProjector
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self"
p2m_attr_erase "simp" "AdelicDock.coe_localEmbed"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace F4CutWords

variable (F : Type) [Field F] [NumberField F]

theorem commute_of_glArch_eq_one_of_glFin_eq_one {g k : AdelicGL2 (𝓞 F) F}
    (hg : glArch (𝓞 F) F g = 1) (hk : glFin (𝓞 F) F k = 1) : Commute g k := by
  have hg' : ∀ i j, adeleArch (𝓞 F) F ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := fun i j => by
    rw [adeleArch_apply, ← glArch_apply, hg, Units.val_one]
  have hk' : ∀ i j, adeleFin (𝓞 F) F ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := fun i j => by
    rw [adeleFin_apply, ← glFin_apply, hk, Units.val_one]
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · show adeleArch (𝓞 F) F (((g * k : AdelicGL2 (𝓞 F) F) : Matrix _ _ _) i j) =
      adeleArch (𝓞 F) F (((k * g : AdelicGL2 (𝓞 F) F) : Matrix _ _ _) i j)
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
    simp only [map_mul, hg', Matrix.one_apply, Fin.sum_univ_two, Fin.isValue]
    fin_cases i <;> fin_cases j <;> simp
  · show adeleFin (𝓞 F) F (((g * k : AdelicGL2 (𝓞 F) F) : Matrix _ _ _) i j) =
      adeleFin (𝓞 F) F (((k * g : AdelicGL2 (𝓞 F) F) : Matrix _ _ _) i j)
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
    simp only [map_mul, hk', Matrix.one_apply, Fin.sum_univ_two, Fin.isValue]
    fin_cases i <;> fin_cases j <;> simp

variable (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))

def subgroupProb : @Measure U (borel U) :=
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  Measure.haarMeasure ⊤

def levelAvg (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun x => ∫ u, φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂(subgroupProb F U hU)

theorem levelAvg_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ) :
    levelAvg F U hU (φ + ψ) = levelAvg F U hU φ + levelAvg F U hU ψ := by
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  haveI : (subgroupProb F U hU).IsHaarMeasure := by unfold subgroupProb; infer_instance
  funext x
  simp only [levelAvg, Pi.add_apply]
  have hi : ∀ {θ : AdelicGL2 (𝓞 F) F → ℂ}, Continuous θ →
      Integrable (fun u : U => θ (x * (u : AdelicGL2 (𝓞 F) F))) (subgroupProb F U hU) := fun hθ =>
    (hθ.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_add (hi hφ) (hi hψ)

theorem levelAvg_smul (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    levelAvg F U hU (c • φ) = c • levelAvg F U hU φ := by
  funext x
  simp only [levelAvg, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem levelAvg_eq_self {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x) : levelAvg F U hU φ = φ := by
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  haveI : (subgroupProb F U hU).IsHaarMeasure := by unfold subgroupProb; infer_instance
  haveI : IsProbabilityMeasure (subgroupProb F U hU) :=
    ⟨by rw [subgroupProb, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
  funext x
  simp only [levelAvg]
  rw [show (fun u : U => φ (x * (u : AdelicGL2 (𝓞 F) F))) = fun _ => φ x from funext fun u => hφ x u u.2]
  simp

theorem levelAvg_apply_mul (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ U) : levelAvg F U hU φ (x * u) = levelAvg F U hU φ x := by
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  haveI : (subgroupProb F U hU).IsHaarMeasure := by unfold subgroupProb; infer_instance
  simp only [levelAvg]
  have h := integral_mul_left_eq_self (μ := subgroupProb F U hU)
    (fun v : U => φ (x * (v : AdelicGL2 (𝓞 F) F))) ⟨u, hu⟩
  simp only [Subgroup.coe_mul, mul_assoc] at h ⊢
  rw [subgroupProb] at h ⊢
  exact h

theorem rightConv_comp_mul_left_eq (ψ f : AdelicGL2 (𝓞 F) F → ℂ) (h : AdelicGL2 (𝓞 F) F) :
    rightConv F ψ (fun z => f (h⁻¹ * z)) = rightTranslate F h (rightConv F ψ f) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext x
  show (∫ z, ψ (x * z) * f (h⁻¹ * z) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
    ∫ z, ψ (x * h * z) * f z ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
  rw [← MeasureTheory.integral_mul_left_eq_self (fun z => ψ (x * z) * f (h⁻¹ * z)) h]
  simp only [mul_assoc, inv_mul_cancel_left]

section Closure

private theorem glFin_eq_one_of_mem_iSup_range (F : Type) [Field F] [NumberField F]
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    glFin (𝓞 F) F k = 1 := by
  refine Subgroup.iSup_induction _ (C := fun k => glFin (𝓞 F) F k = 1) hk ?_ (map_one _) ?_
  · rintro w k ⟨k', rfl⟩; exact glFin_rowIsometryInclAt₀ F w k'
  · intro a b ha hb; rw [map_mul, ha, hb, mul_one]

private theorem rightTranslate_mem_of_mem_iSup_range (F : Type) [Field F] [NumberField F]
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hM : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    ∀ φ ∈ M, rightTranslate F k φ ∈ M := by
  refine Subgroup.iSup_induction _ (C := fun k => ∀ φ ∈ M, rightTranslate F k φ ∈ M) hk ?_ ?_ ?_
  · rintro w k ⟨k', rfl⟩; exact hM w k'
  · intro φ hφ
    have : rightTranslate F 1 φ = φ := by funext x; simp [rightTranslate]
    rwa [this]
  · intro a b ha hb φ hφ
    rw [← rightTranslate_rightTranslate]
    exact ha _ (hb _ hφ)

private theorem rightTranslate_mem_archCutSubmodule_of_mem_iSup_range (F : Type) [Field F] [NumberField F]
    (tys : ArchTypeFamily F)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    ∀ φ ∈ archCutSubmodule F tys, rightTranslate F k φ ∈ archCutSubmodule F tys :=
  rightTranslate_mem_of_mem_iSup_range F _
    (fun w k φ hφ => comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F hφ w k) hk

private theorem rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic (F : Type) [Field F] [NumberField F]
    (tys : ArchTypeFamily F) {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    ∀ φ ∈ archCutSubmodule F tys, rightTranslate F g φ ∈ archCutSubmodule F tys := by
  intro φ hφ
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun φ => rightTranslate F g φ ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i))
    (hφ w) ?_ ?_ ?_
  · intro i f hfi
    refine Submodule.mem_iSup_of_mem i ?_
    exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
      commute_of_glArch_eq_one_of_glFin_eq_one F ((mem_finiteAdelicGL2Subgroup_iff F g).mp hg)
        (glFin_rowIsometryInclAt₀ F w k')
  · exact Submodule.zero_mem _
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

private theorem rightTranslate_mem_levelInvariantSubmodule_of_glFin_eq_one (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (N : Ideal (𝓞 F)) (hU : pins.U N ≤ finiteAdelicGL2Subgroup F)
    {k : AdelicGL2 (𝓞 F) F} (hk : glFin (𝓞 F) F k = 1) :
    ∀ φ ∈ levelInvariantSubmodule F pins N, rightTranslate F k φ ∈ levelInvariantSubmodule F pins N := by
  intro φ hφ x u hu
  show φ (x * u * k) = φ (x * k)
  have hc : Commute u k :=
    commute_of_glArch_eq_one_of_glFin_eq_one F ((mem_finiteAdelicGL2Subgroup_iff F u).mp (hU hu)) hk
  rw [mul_assoc, hc.eq, ← mul_assoc]
  exact hφ (x * k) u hu

end Closure

private theorem continuous_of_mem_cuspKFiniteSubmodule (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hc, -⟩; exact hc
  · exact continuous_const
  · intro a b _ _ ha hb; exact ha.add hb
  · intro c a _ ha; exact ha.const_smul c

end F4CutWords

end

open F4CutWords in

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hMk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    (hMhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = u * g * u') →
        ∃ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N → i = j) →
      ∀ φ ∈ M ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N,
        (fun x => ∑ i, φ (x * reps i)) ∈ M)
    (hMconv : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, f (u * x) = f x ∧ f (x * u) = f x) →
      ∀ φ ∈ M, rightConv F φ f ∈ M) :
    (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
        (_ : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ W ∧
          V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ⊓ M ≤ W), W)
      ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ M := by
  classical
  set pins := productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F) with hpins
  set L : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := levelInvariantSubmodule F pins N with hL
  set A : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := archCutSubmodule F tys with hA
  set Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := V ⊓ L ⊓ A ⊓ M with hY
  let C : (AdelicGL2 (𝓞 F) F → ℂ) → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := fun Ψ => Submodule.span ℂ
      {φ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        φ = rightTranslate F (g * k) Ψ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          φ = rightTranslate F (g * k) (rightConv F Ψ f)}
  set S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := ⨆ y : Y, C (y : AdelicGL2 (𝓞 F) F → ℂ) with hS_def

  have hC : ∀ y : Y, IsCuspSubrep F pins ξ (C y) ∧ (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ C y ∧ C y ≤ V := by
    intro y
    have hyV : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ V := y.2.1.1.1
    obtain ⟨h1, h2, h3, -⟩ := AutomorphicForm.CuspidalConstituent.isCuspSubrep_span_cyclic_and_mem_and_le F D
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)
      ξ V hV (y : AdelicGL2 (𝓞 F) F → ℂ) hyV
    exact ⟨h1, h2, h3⟩
  have hSV : S ≤ V := iSup_le fun y => (hC y).2.2
  have hVc : ∀ φ ∈ V, Continuous φ := fun φ hφ =>
    continuous_of_mem_cuspKFiniteSubmodule F pins ξ (hV.le hφ)

  have hS : IsCuspSubrep F pins ξ S := by
    refine ⟨iSup_le fun y => (hC y).1.le, ?_, ?_, ?_⟩
    · intro g hg φ hφ
      refine Submodule.iSup_induction (motive := fun φ => rightTranslate F g φ ∈ S) _ hφ ?_ ?_ ?_
      · intro y φ hφy
        exact Submodule.mem_iSup_of_mem y ((hC y).1.rightTranslate_fin_mem g hg φ hφy)
      · show rightTranslate F _ 0 ∈ S
        rw [rightTranslate_zero]; exact Submodule.zero_mem _
      · intro a b ha hb
        show rightTranslate F _ (a + b) ∈ S
        rw [rightTranslate_add]; exact Submodule.add_mem _ ha hb
    · intro w k φ hφ
      refine Submodule.iSup_induction (motive := fun φ => rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ S) _ hφ ?_ ?_ ?_
      · intro y φ hφy
        exact Submodule.mem_iSup_of_mem y ((hC y).1.rightTranslate_arch_mem w k φ hφy)
      · show rightTranslate F _ 0 ∈ S
        rw [rightTranslate_zero]; exact Submodule.zero_mem _
      · intro a b ha hb
        show rightTranslate F _ (a + b) ∈ S
        rw [rightTranslate_add]; exact Submodule.add_mem _ ha hb
    · intro f tys' hf hbf φ hφ
      obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
      refine Submodule.iSup_induction' _ (motive := fun φ _ => rightConv F φ f ∈ S) ?_ ?_ ?_ hφ
      · intro y φ hφy
        exact Submodule.mem_iSup_of_mem y ((hC y).1.rightConv_mem f tys' hf hbf φ hφy)
      · show rightConv F 0 f ∈ S
        rw [show (0 : AdelicGL2 (𝓞 F) F → ℂ) = fun _ => 0 from rfl, rightConv_zero_left]
        exact Submodule.zero_mem _
      · intro a b ha hb ha' hb'
        show rightConv F (a + b) f ∈ S
        rw [rightConv_add_left F (hVc a (hSV ha)) (hVc b (hSV hb)) hfc hfs]
        exact Submodule.add_mem _ ha' hb'
  have hYS : Y ≤ S := by
    intro y hy
    exact Submodule.mem_iSup_of_mem (⟨y, hy⟩ : Y) (hC ⟨y, hy⟩).2.1

  have hW₀S : (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : IsCuspSubrep F pins ξ W ∧ V ⊓ L ⊓ A ⊓ M ≤ W), W) ≤ S :=
    iInf₂_le S ⟨hS, hYS⟩

  have hUO : pins.U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl
  have hUf : pins.U N ≤ finiteAdelicGL2Subgroup F := by rw [hUO]; exact inf_le_right
  have hUc : IsCompact ((pins.U N : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by
    rw [hUO]
    refine (isCompact_adelicMaximalCompact F).of_isClosed_subset ?_ ?_
    · rw [Subgroup.coe_inf]
      refine (isClosed_levelOne (𝓞 F) F N).inter ?_
      show IsClosed ((MonoidHom.ker (glArch (𝓞 F) F) : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))
      rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage (continuous_glArch (𝓞 F) F)
    · intro u hu
      rw [SetLike.mem_coe, mem_adelicMaximalCompact_iff]
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hu
      refine ⟨?_, fun w => ?_⟩
      · have h1' := mem_levelOne_iff.mp h1
        exact mem_finiteIntegralGL2_iff.mpr ⟨fun i j => h1'.1.integral i j, fun i j => h1'.2.integral i j⟩
      · rw [(mem_finiteAdelicGL2Subgroup_iff F u).mp h2, map_one]
        exact isRowIsometry_one

  letI : MeasurableSpace (pins.U N) := borel _
  haveI : BorelSpace (pins.U N) := ⟨rfl⟩
  haveI : CompactSpace (pins.U N) := isCompact_iff_compactSpace.mp hUc
  haveI : (subgroupProb F (pins.U N) hUc).IsHaarMeasure := by unfold subgroupProb; infer_instance
  haveI : IsProbabilityMeasure (subgroupProb F (pins.U N) hUc) :=
    ⟨by rw [subgroupProb, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

  obtain ⟨Q, hQid, -, hQconv⟩ := AutomorphicForm.exists_linearMap_archCutProjector F tys

  let Cont : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    { carrier := {φ | Continuous φ}
      zero_mem' := continuous_const
      add_mem' := fun {a b} ha hb => Continuous.add ha hb
      smul_mem' := fun c {a} ha => Continuous.const_smul ha c }
  let PN : Cont →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun φ => levelAvg F (pins.U N) hUc φ
      map_add' := fun a b => levelAvg_add F (pins.U N) hUc a.2 b.2
      map_smul' := fun c a => levelAvg_smul F (pins.U N) hUc c a }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend PN
  have hΛ' : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ), Continuous φ → Λ φ = levelAvg F (pins.U N) hUc φ := by
    intro φ hφ
    have := LinearMap.congr_fun hΛ ⟨φ, hφ⟩
    exact this

  have hP : ∃ P : V →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ φ : V, (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ L ⊓ A → P φ = φ) ∧
      (∀ y ∈ Y, ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ∀ hv : rightTranslate F (g * k) y ∈ V, P ⟨_, hv⟩ ∈ M) ∧
      (∀ y ∈ Y, ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys' : ArchTypeFamily F), IsFactorizableTestFn F f → IsArchBiFinite F tys' f →
        ∀ hv : rightTranslate F (g * k) (rightConv F y f) ∈ V, P ⟨_, hv⟩ ∈ M) := by
    refine ⟨Λ ∘ₗ Q ∘ₗ V.subtype, ?_, ?_, ?_⟩
    ·
      rintro φ ⟨hφL, hφA⟩
      show Λ (Q (φ : AdelicGL2 (𝓞 F) F → ℂ)) = φ
      rw [hQid _ (hVc _ φ.2) hφA, hΛ' _ (hVc _ φ.2)]
      exact levelAvg_eq_self F (pins.U N) hUc hφL
    ·
      intro y hy g hg k hk hv
      have hyV : y ∈ V := hy.1.1.1
      have hyL : y ∈ L := hy.1.1.2
      have hyA : y ∈ A := hy.1.2
      have hyM : y ∈ M := hy.2
      have hkfin : glFin (𝓞 F) F k = 1 := glFin_eq_one_of_mem_iSup_range F hk
      have hy'M : rightTranslate F k y ∈ M := rightTranslate_mem_of_mem_iSup_range F M hMk hk y hyM
      have hy'L : rightTranslate F k y ∈ L :=
        rightTranslate_mem_levelInvariantSubmodule_of_glFin_eq_one F pins N hUf hkfin y hyL
      have hy'A : rightTranslate F k y ∈ A := rightTranslate_mem_archCutSubmodule_of_mem_iSup_range F tys hk y hyA
      have hsplit : rightTranslate F (g * k) y = rightTranslate F g (rightTranslate F k y) :=
        (rightTranslate_rightTranslate F k g y).symm
      have hvA : rightTranslate F (g * k) y ∈ A := by
        rw [hsplit]; exact rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic F tys hg _ hy'A
      show Λ (Q (rightTranslate F (g * k) y)) ∈ M
      rw [hQid _ (hVc _ hv) hvA, hΛ' _ (hVc _ hv), hsplit]
      obtain ⟨n, reps, h1, h2, h3, hn, heq⟩ :=
        AutomorphicForm.exists_integral_rightTranslate_eq_inv_card_mul_sum F (pins.U N) hUc
          (levelOne (𝓞 F) F N) (isOpen_levelOne (𝓞 F) F hN) hUO (subgroupProb F (pins.U N) hUc) hy'L hg
      have hsum : levelAvg F (pins.U N) hUc (rightTranslate F g (rightTranslate F k y)) =
          (n : ℂ)⁻¹ • fun x => ∑ i, rightTranslate F k y (x * reps i) := by
        funext x
        exact heq x
      rw [hsum]
      exact M.smul_mem _ (hMhecke g hg n reps h1 h2 h3 _ ⟨hy'M, hy'L⟩)
    ·
      intro y hy g hg k hk f tys' hf hbf hv
      have hyV : y ∈ V := hy.1.1.1
      have hyL : y ∈ L := hy.1.1.2
      have hyA : y ∈ A := hy.1.2
      have hyM : y ∈ M := hy.2
      have hyc : Continuous y := hVc y hyV
      have hc1 : rightTranslate F (g * k) (rightConv F y f) = rightConv F y (fun z => f ((g * k)⁻¹ * z)) :=
        (rightConv_comp_mul_left_eq F y f (g * k)).symm
      obtain ⟨hf1, hbf1⟩ := AutomorphicForm.isFactorizableTestFn_comp_inv_mul F tys' hf hbf hg hk
      obtain ⟨f', hf', hbf', hQeq⟩ := hQconv y hyc hyA _ tys' hf1 hbf1
      show Λ (Q (rightTranslate F (g * k) (rightConv F y f))) ∈ M
      rw [hc1, hQeq]
      obtain ⟨hf'c, hf's⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f' hf'
      have hcont : Continuous (rightConv F y f') :=
        AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport F y hyc f' hf'c hf's
      rw [hΛ' _ hcont]
      obtain ⟨f'', hf'', hbf'', hinv'', heq''⟩ :=
        AutomorphicForm.exists_integral_rightConv_eq_rightConv F (pins.U N) hUc
          (levelOne (𝓞 F) F N) (isOpen_levelOne (𝓞 F) F hN) hUO (subgroupProb F (pins.U N) hUc) tys hyc hyL hf' hbf'
      have havg : levelAvg F (pins.U N) hUc (rightConv F y f') = rightConv F y f'' := funext heq''
      rw [havg]
      exact hMconv f'' hf'' hbf'' hinv'' y hyM

  have hmain : S ⊓ L ⊓ A ≤ M := by
    obtain ⟨P, hPid, hPgen, hPconv⟩ := hP
    rintro φ ⟨⟨hφS, hφL⟩, hφA⟩
    have hφV : φ ∈ V := hSV hφS
    have hfix : P ⟨φ, hφV⟩ = φ := hPid ⟨φ, hφV⟩ ⟨hφL, hφA⟩
    rw [← hfix]

    have key : ∀ ψ (hψ : ψ ∈ S), P ⟨ψ, hSV hψ⟩ ∈ M := by
      intro ψ hψ
      refine Submodule.iSup_induction' _
        (motive := fun ψ hψ => P ⟨ψ, hSV hψ⟩ ∈ M) ?_ ?_ ?_ hψ
      · rintro ⟨y, hy⟩ ψ hψC
        have hCV : C y ≤ V := (hC ⟨y, hy⟩).2.2
        suffices h : ∀ hv : ψ ∈ V, P ⟨ψ, hv⟩ ∈ M from h _
        refine Submodule.span_induction
          (p := fun ψ _ => ∀ hv : ψ ∈ V, P ⟨ψ, hv⟩ ∈ M) ?_ ?_ ?_ ?_ hψC
        · rintro χ ⟨g, hg, k, hk, hχ⟩ hv
          rcases hχ with rfl | ⟨f, tys', hf, hbf, rfl⟩
          · exact hPgen y hy g hg k hk hv
          · exact hPconv y hy g hg k hk f tys' hf hbf hv
        · intro hv
          have : (⟨0, hv⟩ : V) = 0 := rfl
          rw [this, map_zero]; exact M.zero_mem
        · intro a b ha hb iha ihb hv
          have : (⟨a + b, hv⟩ : V) = ⟨a, hCV ha⟩ + ⟨b, hCV hb⟩ := rfl
          rw [this, map_add]; exact M.add_mem (iha _) (ihb _)
        · intro c a ha iha hv
          have : (⟨c • a, hv⟩ : V) = c • ⟨a, hCV ha⟩ := rfl
          rw [this, map_smul]; exact M.smul_mem c (iha _)
      · show P ⟨0, hSV (Submodule.zero_mem _)⟩ ∈ M
        have : (⟨0, hSV (Submodule.zero_mem _)⟩ : V) = 0 := rfl
        rw [this, map_zero]; exact M.zero_mem
      · intro a b ha hb iha ihb
        show P ⟨a + b, hSV (Submodule.add_mem _ ha hb)⟩ ∈ M
        have : (⟨a + b, hSV (Submodule.add_mem _ ha hb)⟩ : V) = ⟨a, hSV ha⟩ + ⟨b, hSV hb⟩ := rfl
        rw [this, map_add]; exact M.add_mem iha ihb
    exact key φ hφS
  intro φ hφ
  rcases hφ with ⟨⟨hφW, hφL⟩, hφA⟩
  exact hmain ⟨⟨hW₀S hφW, hφL⟩, hφA⟩

end S_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le (solution)
