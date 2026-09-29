-- Prove2me | solution 1 for AutomorphicForm.isAutomorphicFnAt_pseudoEisenstein_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9605cac0-2b77-52f4-9f0a-6fd77eba448d

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_finite_support_pseudoEisenstein_summand
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "lsXiMemberAt_iff IsAutomorphicFnAt productionPinsOf AdelicGL2 globalPoints centralScalar unipotentGL2 IsSlabProfile pseudoEisenstein pseudoEisenstein_apply borelSubgroup globalPoints_apply gl2Weyl adelicWeyl finite_support_pseudoEisenstein_summand SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain"
namespace PseudoEisensteinAutomorphy
p2m_open "AutomorphicForm~ideleNorm_det_globalPoints"

open NumberField.AdelicHeight AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open Filter Topology

variable (F : Type) [Field F] [NumberField F]

private theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints, unipotentGL2]

private theorem adelicWeyl_mul_unipotentGL2_mem_range (β : F) :
    adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) ∈ (globalPoints (𝓞 F) F).range :=
  ⟨gl2Weyl * unipotentGL2 β, by rw [map_mul, globalPoints_unipotentGL2]; rfl⟩

private def bruhatSummand : Option F → (globalPoints (𝓞 F) F).range
  | none => 1
  | some β => ⟨_, adelicWeyl_mul_unipotentGL2_mem_range F β⟩

private def bruhatRep (i : Option F) : (globalPoints (𝓞 F) F).range :=
  (bruhatSummand F i)⁻¹

@[scoped simp]
private theorem bruhatRep_inv (i : Option F) : (bruhatRep F i)⁻¹ = bruhatSummand F i :=
  inv_inv _

private theorem bruhatRep_none_inv_smul (g : AdelicGL2 (𝓞 F) F) :
    ((bruhatRep F none : AdelicGL2 (𝓞 F) F)⁻¹) • g = g := by
  simp [bruhatRep, bruhatSummand]

private theorem bruhatRep_some_inv_smul (β : F) (g : AdelicGL2 (𝓞 F) F) :
    ((bruhatRep F (some β) : AdelicGL2 (𝓞 F) F)⁻¹) • g
      = adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g := by
  simp [bruhatRep, bruhatSummand, smul_eq_mul]

omit [NumberField F] in
private theorem summand_mul_entry (γ₀ : GL (Fin 2) F) :
    (((1 : GL (Fin 2) F) * γ₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
    ∀ β : F, ((gl2Weyl * unipotentGL2 β * γ₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0
      = (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 + β * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  refine ⟨by simp, fun β => ?_⟩
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem bruhatSummand_eq_globalPoints :
    ((bruhatSummand F none : AdelicGL2 (𝓞 F) F) = globalPoints (𝓞 F) F 1) ∧
    ∀ β : F, (bruhatSummand F (some β) : AdelicGL2 (𝓞 F) F) = globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 β) := by
  refine ⟨by simp [bruhatSummand], fun β => ?_⟩
  simp only [bruhatSummand, map_mul, globalPoints_unipotentGL2]
  rfl

private theorem globalPoints_mem_borel_map_iff (x₀ : GL (Fin 2) F) :
    globalPoints (𝓞 F) F x₀ ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F)
      ↔ (x₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  constructor
  · rintro ⟨b, hb, hbx⟩
    have hb' : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb
    have hentry := congrArg (fun y : AdelicGL2 (𝓞 F) F => (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) hbx
    simp only [globalPoints_apply, hb', map_zero] at hentry
    exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F (by simpa using hentry.symm)
  · intro h
    exact ⟨x₀, h, rfl⟩

private theorem bruhatRep_spec (γ : (globalPoints (𝓞 F) F).range) :
    ∃! i : Option F, ((bruhatRep F i)⁻¹ * γ : AdelicGL2 (𝓞 F) F) ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  obtain ⟨h1, hw⟩ := summand_mul_entry F γ₀
  obtain ⟨s1, sw⟩ := bruhatSummand_eq_globalPoints F
  have key : ∀ i : Option F,
      (((bruhatRep F i)⁻¹ * γ : AdelicGL2 (𝓞 F) F) ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F)) ↔
      (match i with
        | none => (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
        | some β => (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 + β * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) := by
    intro i

    rw [bruhatRep_inv, ← hγ₀]
    cases i with
    | none => rw [s1, ← map_mul, globalPoints_mem_borel_map_iff, h1]
    | some β => rw [sw β, ← map_mul, globalPoints_mem_borel_map_iff, hw β]
  have hdet : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 1
      - (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 1 * (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    have := (Matrix.isUnits_det_units γ₀).ne_zero
    rwa [Matrix.det_fin_two] at this
  by_cases hc : (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have ha : (γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro ha; apply hdet; rw [ha, hc]; ring
    refine ⟨none, (key none).2 hc, fun i hi => ?_⟩
    cases i with
    | none => rfl
    | some β =>
      exfalso
      have := (key (some β)).1 hi
      simp only [hc, mul_zero, add_zero] at this
      exact ha this
  · refine ⟨some (-(γ₀ : Matrix (Fin 2) (Fin 2) F) 0 0 / (γ₀ : Matrix (Fin 2) (Fin 2) F) 1 0), ?_, fun i hi => ?_⟩
    · refine (key _).2 ?_
      simp only [div_mul_cancel₀ _ hc, add_neg_cancel]
    · cases i with
      | none => exact absurd ((key none).1 hi) hc
      | some β =>
        have hβ := (key (some β)).1 hi
        congr 1
        field_simp
        linear_combination hβ

omit [Field F] [NumberField F] in
private theorem tsum_option_eq (u : Option F → ℂ) (hu : Summable u) :
    ∑' i, u i = u none + ∑' β : F, u (some β) := by
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} F).symm.tsum_eq]
  have h₁ : Summable ((fun s => u ((Equiv.optionEquivSumPUnit.{0, 0} F).symm s)) ∘ Sum.inl) :=
    ((Equiv.optionEquivSumPUnit.{0, 0} F).symm.summable_iff.2 hu).comp_injective Sum.inl_injective
  have h₂ : Summable ((fun s => u ((Equiv.optionEquivSumPUnit.{0, 0} F).symm s)) ∘ Sum.inr) :=
    ((Equiv.optionEquivSumPUnit.{0, 0} F).symm.summable_iff.2 hu).comp_injective Sum.inr_injective
  rw [h₁.tsum_sum h₂, add_comm]
  simp [tsum_fintype]

private theorem pseudoEisenstein_eq_tsum_bruhatRep (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F)
    (hs : Summable fun i : Option F => φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x)) :
    pseudoEisenstein F φ x = ∑' i : Option F, φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x) := by
  rw [tsum_option_eq F _ hs, bruhatRep_none_inv_smul, pseudoEisenstein_apply]
  congr 1

private theorem finite_support_bruhatRep (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F)
    (hLF : (Function.support fun β : F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * x)).Finite) :
    (Function.support fun i : Option F => φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x)).Finite := by
  refine ((hLF.image some).union (Set.finite_singleton none)).subset ?_
  intro i hi
  cases i with
  | none => exact Or.inr rfl
  | some β =>
    refine Or.inl ⟨β, ?_, rfl⟩
    simp [Function.mem_support, bruhatRep_some_inv_smul] at hi
    exact hi

private theorem existsUnique_bruhatSummand_mul_mem (γ' : (globalPoints (𝓞 F) F).range) :
    ∃! j : Option F, (bruhatSummand F j : AdelicGL2 (𝓞 F) F) * γ' ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  simpa [bruhatRep] using bruhatRep_spec F γ'

private theorem bruhatSummand_mul_inv_mem_iff (i i' : Option F) :
    (bruhatSummand F i' : AdelicGL2 (𝓞 F) F) * ((bruhatSummand F i : AdelicGL2 (𝓞 F) F))⁻¹
        ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) ↔ i' = i := by
  obtain ⟨j, -, hj⟩ := existsUnique_bruhatSummand_mul_mem F (bruhatSummand F i)⁻¹
  constructor
  · intro h
    have h₁ : i' = j := hj i' (by simpa using h)
    have h₂ : i = j := hj i (by simp)
    rw [h₁, h₂]
  · rintro rfl
    simp

private theorem exists_injective_reindex (γ : (globalPoints (𝓞 F) F).range) :
    ∃ σ : Option F → Option F, Function.Injective σ ∧ ∀ i : Option F,
      (bruhatSummand F i : AdelicGL2 (𝓞 F) F) * γ * ((bruhatSummand F (σ i) : AdelicGL2 (𝓞 F) F))⁻¹
        ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  have key : ∀ i : Option F, ∃ j : Option F,
      (bruhatSummand F i : AdelicGL2 (𝓞 F) F) * γ * ((bruhatSummand F j : AdelicGL2 (𝓞 F) F))⁻¹
        ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := fun i => by
    obtain ⟨j, hj, -⟩ := existsUnique_bruhatSummand_mul_mem F (bruhatSummand F i * γ)⁻¹
    refine ⟨j, ?_⟩
    have := Subgroup.inv_mem _ hj
    simpa [mul_assoc] using this
  choose σ hσ using key
  refine ⟨σ, fun i i' hii' => ?_, hσ⟩
  have h₁ := hσ i
  have h₂ := hσ i'
  rw [hii'] at h₁
  have h₃ := Subgroup.mul_mem _ h₂ (Subgroup.inv_mem _ h₁)
  have h₄ : (bruhatSummand F i' : AdelicGL2 (𝓞 F) F) * γ * ((bruhatSummand F (σ i') : AdelicGL2 (𝓞 F) F))⁻¹
      * ((bruhatSummand F i : AdelicGL2 (𝓞 F) F) * γ * ((bruhatSummand F (σ i') : AdelicGL2 (𝓞 F) F))⁻¹)⁻¹
      = (bruhatSummand F i' : AdelicGL2 (𝓞 F) F) * ((bruhatSummand F i : AdelicGL2 (𝓞 F) F))⁻¹ := by
    simp [mul_assoc]
  rw [h₄] at h₃
  exact ((bruhatSummand_mul_inv_mem_iff F i i').1 h₃).symm

private theorem finite_and_ncard_setOf_bruhatRep_mul_le (P : AdelicGL2 (𝓞 F) F → Prop)
    (hPB : ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ y : AdelicGL2 (𝓞 F) F, P (b * y) ↔ P y)
    (γ : (globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F)
    (hx : {i : Option F | P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x)}.Finite) :
    {i : Option F | P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • ((γ : AdelicGL2 (𝓞 F) F) * x))}.Finite ∧
      {i : Option F | P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • ((γ : AdelicGL2 (𝓞 F) F) * x))}.ncard
        ≤ {i : Option F | P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x)}.ncard := by
  obtain ⟨σ, hσinj, hσ⟩ := exists_injective_reindex F γ
  have hre : ∀ i : Option F, P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • ((γ : AdelicGL2 (𝓞 F) F) * x))
      ↔ P ((bruhatRep F (σ i) : AdelicGL2 (𝓞 F) F)⁻¹ • x) := fun i => by
    have hb := hPB _ (hσ i) ((bruhatSummand F (σ i) : AdelicGL2 (𝓞 F) F) * x)
    simp only [bruhatRep, Subgroup.coe_inv, inv_inv, smul_eq_mul] at hb ⊢
    simpa [mul_assoc] using hb
  have hset : {i : Option F | P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • ((γ : AdelicGL2 (𝓞 F) F) * x))}
      = σ ⁻¹' {i : Option F | P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x)} := by
    ext i
    exact hre i
  rw [hset]
  exact ⟨hx.preimage hσinj.injOn, Set.ncard_le_ncard_of_injOn σ (fun i hi => hi) hσinj.injOn hx⟩

private theorem ncard_setOf_bruhatRep_mul_eq (P : AdelicGL2 (𝓞 F) F → Prop)
    (hPB : ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ y : AdelicGL2 (𝓞 F) F, P (b * y) ↔ P y)
    (γ : (globalPoints (𝓞 F) F).range) (x : AdelicGL2 (𝓞 F) F)
    (hx : {i : Option F | P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x)}.Finite) :
    {i : Option F | P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • ((γ : AdelicGL2 (𝓞 F) F) * x))}.ncard
      = {i : Option F | P ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x)}.ncard := by
  obtain ⟨hfin, hle⟩ := finite_and_ncard_setOf_bruhatRep_mul_le F P hPB γ x hx
  refine le_antisymm hle ?_
  have h := (finite_and_ncard_setOf_bruhatRep_mul_le F P hPB γ⁻¹ ((γ : AdelicGL2 (𝓞 F) F) * x) hfin).2
  simpa [← mul_assoc] using h

private theorem exists_bijective_reindex (γ : (globalPoints (𝓞 F) F).range) :
    ∃ σ : Option F → Option F, Function.Bijective σ ∧ ∀ i : Option F,
      (bruhatSummand F i : AdelicGL2 (𝓞 F) F) * γ * ((bruhatSummand F (σ i) : AdelicGL2 (𝓞 F) F))⁻¹
        ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  obtain ⟨σ, hσinj, hσ⟩ := exists_injective_reindex F γ
  obtain ⟨τ, -, hτ⟩ := exists_injective_reindex F γ⁻¹
  refine ⟨σ, ⟨hσinj, fun j => ⟨τ j, ?_⟩⟩, hσ⟩
  have h₁ : (bruhatSummand F (τ j) : AdelicGL2 (𝓞 F) F) * γ * ((bruhatSummand F j : AdelicGL2 (𝓞 F) F))⁻¹
      ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
    have h := Subgroup.inv_mem _ (hτ j)
    simpa [mul_assoc] using h
  have h₂ := Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁) (hσ (τ j))
  have h₃ : ((bruhatSummand F (τ j) : AdelicGL2 (𝓞 F) F) * γ * ((bruhatSummand F j : AdelicGL2 (𝓞 F) F))⁻¹)⁻¹
      * ((bruhatSummand F (τ j) : AdelicGL2 (𝓞 F) F) * γ * ((bruhatSummand F (σ (τ j)) : AdelicGL2 (𝓞 F) F))⁻¹)
      = (bruhatSummand F j : AdelicGL2 (𝓞 F) F) * ((bruhatSummand F (σ (τ j)) : AdelicGL2 (𝓞 F) F))⁻¹ := by
    simp [mul_assoc]
  rw [h₃] at h₂
  exact ((bruhatSummand_mul_inv_mem_iff F (σ (τ j)) j).1 h₂).symm

variable {F}

private theorem borelImage_invariant {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) :
    ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ y : AdelicGL2 (𝓞 F) F, φ (b * y) = φ y := by
  intro b hb y
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hb
  exact hφ.borel_mul γ₀ hγ₀ y

private theorem finite_rep_support {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (x : AdelicGL2 (𝓞 F) F) :
    (Function.support fun i : Option F => φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x)).Finite :=
  finite_support_bruhatRep F φ x (AutomorphicForm.finite_support_pseudoEisenstein_summand F Z ξ φ hφ x)

private theorem summable_rep {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (x : AdelicGL2 (𝓞 F) F) :
    Summable fun i : Option F => φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x) :=
  summable_of_hasFiniteSupport (finite_rep_support hφ x)

private theorem pseudoEisenstein_range_mul {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (γ : (globalPoints (𝓞 F) F).range)
    (x : AdelicGL2 (𝓞 F) F) :
    pseudoEisenstein F φ ((γ : AdelicGL2 (𝓞 F) F) * x) = pseudoEisenstein F φ x := by
  obtain ⟨σ, hσbij, hσ⟩ := exists_bijective_reindex F γ
  have hre : ∀ i : Option F, φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • ((γ : AdelicGL2 (𝓞 F) F) * x))
      = φ ((bruhatRep F (σ i) : AdelicGL2 (𝓞 F) F)⁻¹ • x) := fun i => by
    have hb := borelImage_invariant hφ _ (hσ i) ((bruhatSummand F (σ i) : AdelicGL2 (𝓞 F) F) * x)
    simp only [bruhatRep, Subgroup.coe_inv, inv_inv, smul_eq_mul] at hb ⊢
    simpa [mul_assoc] using hb
  rw [pseudoEisenstein_eq_tsum_bruhatRep F φ _ (summable_rep hφ _),
    pseudoEisenstein_eq_tsum_bruhatRep F φ x (summable_rep hφ x), tsum_congr hre]
  exact (Equiv.ofBijective σ hσbij).tsum_eq fun j => φ ((bruhatRep F j : AdelicGL2 (𝓞 F) F)⁻¹ • x)

private theorem pseudoEisenstein_centralScalar_mul {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (z : Z) (g : AdelicGL2 (𝓞 F) F) :
    pseudoEisenstein F φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g)
      = ((ξ z : ℂˣ) : ℂ) * pseudoEisenstein F φ g := by
  have hterm : ∀ β : F,
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)
          * (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g))
        = ((ξ z : ℂˣ) : ℂ) * φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) := by
    intro β
    rw [← mul_assoc, mul_centralScalar_comm, mul_assoc, hφ.central_transform z]
  simp only [pseudoEisenstein_apply, hφ.central_transform z g, hterm, tsum_mul_left, mul_add]

private theorem setOf_ne_zero_mul_centralScalar {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (z : Z) (x : AdelicGL2 (𝓞 F) F) :
    {i : Option F |
        φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • (x * centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ))) ≠ 0}
      = {i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • x) ≠ 0} := by
  ext i
  simp only [Set.mem_setOf_eq, smul_eq_mul]
  rw [← mul_assoc, mul_centralScalar_comm, hφ.central_transform z]
  exact mul_ne_zero_iff.trans (and_iff_right (Units.ne_zero (ξ z)))

variable (F)

private theorem adelicHeight_weyl_unipotent_mul_mul_adelicHeight_le_one (β : F) (p : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * p)
      * adelicHeight F p ≤ 1 := by
  have hentry : ((gl2Weyl * unipotentGL2 β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    have h := (summand_mul_entry F 1).2 β
    rw [mul_one] at h
    rw [h]
    simp
  have hrep : adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)
      = globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 β) := (bruhatSummand_eq_globalPoints F).2 β
  rw [hrep]
  exact adelicHeight_globalPoints_mul_mul_adelicHeight_le_one (gl2Weyl * unipotentGL2 β) hentry p

private theorem exists_forall_finite_and_rpow_mul_ncard_le (c u : ℝ) (hc : 0 < c) (x : AdelicGL2 (𝓞 F) F)
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ centreCutSiegelSet F c u 1 1,
      {β : F | a ≤ adelicHeight F (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * (s * x))}.Finite ∧
      a ^ ((1 : ℝ) + 1 / 2) * ({β : F | a ≤ adelicHeight F (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * (s * x))}.ncard : ℝ)
        ≤ C * archHeight F (glArch (𝓞 F) F s) ^ ((1 : ℝ) + 1 / 2) := by
  obtain ⟨C, hC⟩ := AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet F c u
    1 1 hc x 1 (by norm_num)
  refine ⟨|C|, abs_nonneg C, fun s hs => ?_⟩
  obtain ⟨hsum, hle⟩ := hC s hs
  set hgt : F → ℝ := fun β => adelicHeight F (adelicWeyl (𝓞 F) F
    * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * (s * x)) with hgt_def
  have hterm_nonneg : ∀ β, 0 ≤ hgt β ^ ((1 : ℝ) + 1 / 2) := fun β => Real.rpow_nonneg (adelicHeight_pos _).le _
  have hfin : {β : F | a ≤ hgt β}.Finite := by
    have hev := hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.rpow_pos_of_pos ha ((1 : ℝ) + 1 / 2)))
    refine (Filter.eventually_cofinite.mp hev).subset fun β hβ => ?_
    exact not_lt.mpr (Real.rpow_le_rpow ha.le hβ (by norm_num))
  refine ⟨hfin, ?_⟩
  have hcard : a ^ ((1 : ℝ) + 1 / 2) * ({β : F | a ≤ hgt β}.ncard : ℝ)
      ≤ ∑ β ∈ hfin.toFinset, hgt β ^ ((1 : ℝ) + 1 / 2) := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    calc a ^ ((1 : ℝ) + 1 / 2) * (hfin.toFinset.card : ℝ)
        = ∑ _β ∈ hfin.toFinset, a ^ ((1 : ℝ) + 1 / 2) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ β ∈ hfin.toFinset, hgt β ^ ((1 : ℝ) + 1 / 2) :=
        Finset.sum_le_sum fun β hβ => Real.rpow_le_rpow ha.le (hfin.mem_toFinset.mp hβ) (by norm_num)
  have hsum_le : ∑ β ∈ hfin.toFinset, hgt β ^ ((1 : ℝ) + 1 / 2) ≤ ∑' β, hgt β ^ ((1 : ℝ) + 1 / 2) :=
    hsum.sum_le_tsum _ fun β _ => hterm_nonneg β
  have hdrop : ∑' β, hgt β ^ ((1 : ℝ) + 1 / 2) ≤ C * archHeight F (glArch (𝓞 F) F s) ^ ((1 : ℝ) + 1 / 2) :=
    (le_add_of_nonneg_left (Real.rpow_nonneg (adelicHeight_pos _).le _)).trans hle
  have habs : C * archHeight F (glArch (𝓞 F) F s) ^ ((1 : ℝ) + 1 / 2)
      ≤ |C| * archHeight F (glArch (𝓞 F) F s) ^ ((1 : ℝ) + 1 / 2) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (archHeight_pos F _).le _)
  exact hcard.trans (hsum_le.trans (hdrop.trans habs))

variable {F}

private theorem exists_forall_ncard_setOf_ne_zero_le {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (hZ : ∀ w : (AdeleRing (𝓞 F) F)ˣ, w ∈ Z) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ g : AdelicGL2 (𝓞 F) F,
      ({i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • g) ≠ 0}.ncard : ℝ) ≤ N := by
  obtain ⟨a, b, ha, hband⟩ := hφ.height_band
  obtain ⟨T, c, hc, u, hcov⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet F
  obtain ⟨κ, K₀, hκ, hκK⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F
      (T : Set (AdelicGL2 (𝓞 F) F)) T.finite_toSet.isCompact
  choose Cof hCof_nonneg hCof using fun x : AdelicGL2 (𝓞 F) F =>
    exists_forall_finite_and_rpow_mul_ncard_le F c u hc x a ha
  have hae_pos : 0 < a ^ ((1 : ℝ) + 1 / 2) := Real.rpow_pos_of_pos ha _
  set bnd : ℝ := 1 / a / κ with hbnd_def
  have hbnd_nonneg : 0 ≤ bnd := div_nonneg (div_nonneg zero_le_one ha.le) hκ.le
  set Cmax : ℝ := ∑ x ∈ T, Cof x with hCmax_def
  have hCmax_nonneg : 0 ≤ Cmax := Finset.sum_nonneg fun x _ => hCof_nonneg x
  set M : ℝ := Cmax * bnd ^ ((1 : ℝ) + 1 / 2) with hM_def
  have hM_nonneg : 0 ≤ M := mul_nonneg hCmax_nonneg (Real.rpow_nonneg hbnd_nonneg _)
  refine ⟨1 + M / a ^ ((1 : ℝ) + 1 / 2), add_nonneg zero_le_one (div_nonneg hM_nonneg hae_pos.le),
    fun g => ?_⟩

  have hcover : ∀ p ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u 1 1,
      ({i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • p) ≠ 0}.ncard : ℝ)
        ≤ 1 + M / a ^ ((1 : ℝ) + 1 / 2) := by
    intro p hp
    obtain ⟨x, hxT, hpx⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨s, hs, hsp⟩ := hpx
    have hsp' : s * x = p := hsp
    subst hsp'
    obtain ⟨hAfin, hAcard⟩ := hCof x s hs
    set S : Set F := {β : F |
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * (s * x)) ≠ 0} with hS_def
    set A : Set F := {β : F | a ≤ adelicHeight F (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * (s * x))} with hA_def
    have hSA : S ⊆ A := fun β hβ => (hband _ hβ).1
    have hSfin : S.Finite := hAfin.subset hSA
    have hsub : {i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • (s * x)) ≠ 0} ⊆ some '' S ∪ {none} := by
      intro i hi
      cases i with
      | none => exact Or.inr rfl
      | some β =>
        refine Or.inl ⟨β, ?_, rfl⟩
        simp [hS_def, bruhatRep_some_inv_smul] at hi
        exact hi
    have h₁ : {i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • (s * x)) ≠ 0}.ncard ≤ S.ncard + 1 := by
      refine (Set.ncard_le_ncard hsub ((hSfin.image some).union (Set.finite_singleton none))).trans ?_
      refine (Set.ncard_union_le _ _).trans ?_
      rw [Set.ncard_singleton]
      exact Nat.add_le_add_right (Set.ncard_image_le hSfin) 1
    have h₂ : S.ncard ≤ A.ncard := Set.ncard_le_ncard hSA hAfin
    rcases S.eq_empty_or_nonempty with hSe | ⟨β₀, hβ₀⟩
    ·
      have h₁' : ({i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • (s * x)) ≠ 0}.ncard : ℝ) ≤ 1 := by
        rw [hSe, Set.ncard_empty, zero_add] at h₁
        exact_mod_cast h₁
      exact h₁'.trans (le_add_of_nonneg_right (div_nonneg hM_nonneg hae_pos.le))
    ·
      have hβ₀' : a ≤ adelicHeight F (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β₀) * (s * x)) := hSA hβ₀
      have hHp : adelicHeight F (s * x) ≤ 1 / a := by
        rw [le_div_iff₀ ha]
        calc adelicHeight F (s * x) * a
            ≤ adelicHeight F (s * x) * adelicHeight F (adelicWeyl (𝓞 F) F
                * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β₀) * (s * x)) :=
              mul_le_mul_of_nonneg_left hβ₀' (adelicHeight_pos _).le
          _ = adelicHeight F (adelicWeyl (𝓞 F) F
                * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β₀) * (s * x)) * adelicHeight F (s * x) :=
              mul_comm _ _
          _ ≤ 1 := adelicHeight_weyl_unipotent_mul_mul_adelicHeight_le_one F β₀ (s * x)
      have hHs : adelicHeight F s ≤ bnd := by
        have hκs : κ * adelicHeight F s ≤ 1 / a := (hκK s x hxT).1.trans hHp
        rw [hbnd_def, le_div_iff₀ hκ, mul_comm]
        exact hκs
      have harch : archHeight F (glArch (𝓞 F) F s) ≤ bnd := by
        rw [← adelicHeight_eq_archHeight_of_mem (mem_centreCutSiegelSet_iff.mp hs).1]
        exact hHs
      have hA_bound : a ^ ((1 : ℝ) + 1 / 2) * (A.ncard : ℝ) ≤ M :=
        hAcard.trans (mul_le_mul (Finset.single_le_sum (fun y _ => hCof_nonneg y) hxT)
          (Real.rpow_le_rpow (archHeight_pos F _).le harch (by norm_num))
          (Real.rpow_nonneg (archHeight_pos F _).le _) hCmax_nonneg)
      have hA_le : (A.ncard : ℝ) ≤ M / a ^ ((1 : ℝ) + 1 / 2) := by
        rw [le_div_iff₀ hae_pos, mul_comm]
        exact hA_bound
      have h₁' : ({i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • (s * x)) ≠ 0}.ncard : ℝ)
          ≤ (S.ncard : ℝ) + 1 := by exact_mod_cast h₁
      have h₂' : (S.ncard : ℝ) ≤ (A.ncard : ℝ) := by exact_mod_cast h₂
      linarith

  obtain ⟨γ, z, hmem⟩ := hcov 1 1 one_pos le_rfl g
  have hPB : ∀ b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F), ∀ y : AdelicGL2 (𝓞 F) F,
      (φ (b * y) ≠ 0 ↔ φ y ≠ 0) := fun b hb y => by rw [borelImage_invariant hφ b hb y]
  have hleft : {i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • (globalPoints (𝓞 F) F γ * g)) ≠ 0}.ncard
      = {i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • g) ≠ 0}.ncard :=
    ncard_setOf_bruhatRep_mul_eq F (fun y => φ y ≠ 0) hPB
      ⟨globalPoints (𝓞 F) F γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩⟩ g (finite_rep_support hφ g)
  have hcentre : {i : Option F |
        φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z)) ≠ 0}
      = {i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • (globalPoints (𝓞 F) F γ * g)) ≠ 0} :=
    setOf_ne_zero_mul_centralScalar hφ ⟨z, hZ z⟩ (globalPoints (𝓞 F) F γ * g)
  have hp := hcover _ hmem
  rw [hcentre, hleft] at hp
  exact hp

variable (F)

private theorem det_globalPoints (m : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F m)
      = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Matrix.GeneralLinearGroup.det m) := by
  ext
  simp [globalPoints, Matrix.GeneralLinearGroup.map, RingHom.map_det]

private theorem ideleNorm_det_globalPoints (m : GL (Fin 2) F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F m)) = 1 := by
  rw [det_globalPoints, NumberField.TateGlobal.ideleNorm,
    @NumberField.AdeleRing.distribHaarChar_algebraMap F _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 F) F)
      (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F) (Matrix.GeneralLinearGroup.det m)]
  simp

private theorem ideleNorm_det_weyl_unipotent_mul (β : F) (g : AdelicGL2 (𝓞 F) F) :
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  have hrep : adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β)
      = globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 β) := (bruhatSummand_eq_globalPoints F).2 β
  rw [hrep, map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]

variable {F}

private theorem exists_forall_norm_pseudoEisenstein_le {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) (hZ : ∀ w : (AdeleRing (𝓞 F) F)ˣ, w ∈ Z)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) :
    ∃ K : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂ →
        ‖pseudoEisenstein F φ g‖ ≤ K := by
  obtain ⟨N, hN, hcount⟩ := exists_forall_ncard_setOf_ne_zero_le hφ hZ
  obtain ⟨C₀, hC₀⟩ := hφ.bounded_on_slab d₁ d₂ hd₁
  refine ⟨C₀ + N * C₀, fun g hg => ?_⟩
  have hC₀_nonneg : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ g hg)
  have hLF := AutomorphicForm.finite_support_pseudoEisenstein_summand F Z ξ φ hφ g

  have hterms : ‖∑' β : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)‖
      ≤ N * C₀ := by
    rw [tsum_eq_sum' hLF.coe_toFinset.ge]
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ β ∈ hLF.toFinset,
        ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)‖ ≤ C₀ := fun β _ =>
      hC₀ _ (by rw [ideleNorm_det_weyl_unipotent_mul]; exact hg)
    refine (Finset.sum_le_sum hle).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hC₀_nonneg

    have hinj : ((Function.support fun β : F =>
        φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)).ncard : ℝ)
          ≤ ({i : Option F | φ ((bruhatRep F i : AdelicGL2 (𝓞 F) F)⁻¹ • g) ≠ 0}.ncard : ℝ) := by
      refine Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn some (fun β hβ => ?_)
        (Option.some_injective F).injOn (finite_rep_support hφ g))
      simp [Function.mem_support, bruhatRep_some_inv_smul] at hβ
      exact hβ
    rw [← Set.ncard_eq_toFinset_card _ hLF]
    exact hinj.trans (hcount g)
  calc ‖pseudoEisenstein F φ g‖
      = ‖φ g + ∑' β : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)‖ := by
        rw [pseudoEisenstein_apply]
    _ ≤ ‖φ g‖ + ‖∑' β : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)‖ :=
        norm_add_le _ _
    _ ≤ C₀ + N * C₀ := add_le_add (hC₀ g hg) hterms

private theorem measurable_tsum_of_forall_summable {ι α : Type*} [Countable ι] [MeasurableSpace α] (f : ι → α → ℂ)
    (hf : ∀ i, Measurable (f i)) (hs : ∀ a, Summable fun i => f i a) : Measurable fun a => ∑' i, f i a := by
  refine measurable_of_tendsto_metrizable' (f := fun s : Finset ι => fun a => ∑ i ∈ s, f i a)
    (atTop : Filter (Finset ι)) (fun s => Finset.measurable_sum s fun i _ => hf i) ?_
  rw [tendsto_pi_nhds]
  intro a
  exact (hs a).hasSum

private theorem measurable_tsum_of_forall_finite_support {ι α : Type*} [Countable ι] [MeasurableSpace α]
    (f : ι → α → ℂ) (hf : ∀ i, Measurable (f i)) (hfin : ∀ a, (Function.support fun i => f i a).Finite) :
    Measurable fun a => ∑' i, f i a :=
  measurable_tsum_of_forall_summable f hf fun a => summable_of_hasFiniteSupport (hfin a)

private theorem countable_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

private theorem measurable_pseudoEisenstein {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSlabProfile F Z ξ φ) : Measurable (pseudoEisenstein F φ) := by
  haveI : Countable F := countable_numberField (F := F)
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  have hterm : ∀ β : F, Measurable fun g : AdelicGL2 (𝓞 F) F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) := fun β =>
    hφ.measurable.comp (measurable_const_mul _)
  have hsum : Measurable fun g : AdelicGL2 (𝓞 F) F =>
      ∑' β : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) :=
    measurable_tsum_of_forall_finite_support
      (fun β g => φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)) hterm
      fun g => AutomorphicForm.finite_support_pseudoEisenstein_summand F Z ξ φ hφ g
  show Measurable fun g : AdelicGL2 (𝓞 F) F =>
    φ g + ∑' β : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)
  exact hφ.measurable.add hsum

end AutomorphicForm.PseudoEisensteinAutomorphy
p2m_reactivate "P2MW.S_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab.AutomorphicForm P2MW.S_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab.AutomorphicForm.PseudoEisensteinAutomorphy"
p2m_reactivate "P2MW.S_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab.AutomorphicForm"

p2m_open "AutomorphicForm~ideleNorm_det_globalPoints P2MW.S_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab.AutomorphicForm"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφ : AutomorphicForm.IsSlabProfile F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ) :
    IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ (AutomorphicForm.pseudoEisenstein F φ) := by
  have hZ : ∀ w : (AdeleRing (𝓞 F) F)ˣ,
      w ∈ (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z :=
    fun w => Subgroup.mem_top w

  refine (lsXiMemberAt_iff (𝓞 F) F _ _ ξ Φ _).mpr ⟨⟨fun γ g => ?_, fun z g => ?_⟩, ?_⟩
  · exact PseudoEisensteinAutomorphy.pseudoEisenstein_range_mul _hφ
      ⟨globalPoints (𝓞 F) F γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩⟩ g
  · exact PseudoEisensteinAutomorphy.pseudoEisenstein_centralScalar_mul _hφ z g
  ·
    obtain ⟨K, hK⟩ := PseudoEisensteinAutomorphy.exists_forall_norm_pseudoEisenstein_le _hφ hZ d₁ d₂ _hd₁
    have hΦfin : adelicGLHaar (Fin 2) (𝓞 F) F Φ ≠ ⊤ := by
      have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain F d₁ d₂
        _hd₁ _hd Φ _hΦ
      exact ((measure_mono (Set.subset_inter subset_rfl _hΦs)).trans_lt h).ne
    haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ) := isFiniteMeasure_restrict.mpr hΦfin
    have hmeas : Measurable (pseudoEisenstein F φ) := PseudoEisensteinAutomorphy.measurable_pseudoEisenstein _hφ
    show MemLp (pseudoEisenstein F φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ)
    refine MemLp.of_bound hmeas.aestronglyMeasurable K ?_

    have hset : MeasurableSet {g : AdelicGL2 (𝓞 F) F | ¬ ‖pseudoEisenstein F φ g‖ ≤ K} := by
      simp only [not_le]
      exact hmeas.norm measurableSet_Ioi
    rw [ae_iff, Measure.restrict_apply hset]
    refine measure_mono_null (fun g hg => ?_) (measure_empty (μ := adelicGLHaar (Fin 2) (𝓞 F) F))
    exact absurd (hK g (_hΦs hg.2)) hg.1

end
p2m_reactivate "P2MW.S_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab.AutomorphicForm P2MW.S_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab.AutomorphicForm.PseudoEisensteinAutomorphy"

end S_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab
end P2MW
export P2MW.S_AutomorphicForm_isAutomorphicFnAt_pseudoEisenstein_slab (solution)
