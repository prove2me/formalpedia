-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/eaa960a1-2688-564d-987d-38eedf323806

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Ws28
namespace CUTOPHU

variable (F : Type) [Field F] [NumberField F]

theorem mem_invariants_rightRegular_iff (U : Subgroup (AdelicGL2 (𝓞 F) F)) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    φ ∈ Representation.invariants ((rightRegular F).comp U.subtype) ↔
      ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x := by
  rw [Representation.mem_invariants]
  constructor
  · intro h x u hu
    exact congrFun (h ⟨u, hu⟩) x
  · intro h u
    funext x
    exact h x u u.2

def cuspInvSubcarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (U : Subgroup (AdelicGL2 (𝓞 F) F)) :
    Submodule ℂ (Carrier F Φ₀ σ) :=
  (Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
        (cuspMemberSubmodule F Φ₀ ξ ⊓ Representation.invariants ((rightRegular F).comp U.subtype)))).topologicalClosure

theorem eq_of_glArch_eq_of_glFin_eq {a b : AdelicGL2 (𝓞 F) F}
    (h1 : glArch (𝓞 F) F a = glArch (𝓞 F) F b) (h2 : glFin (𝓞 F) F a = glFin (𝓞 F) F b) : a = b := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e1 := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h1
  have e2 := congrArg
    (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h2
  simp only [glArch_apply, glFin_apply] at e1 e2
  exact Prod.ext e1 e2

theorem mul_comm_of_glFin_eq_one_of_glArch_eq_one {a r : AdelicGL2 (𝓞 F) F}
    (ha : glFin (𝓞 F) F a = 1) (hr : glArch (𝓞 F) F r = 1) : r * a = a * r := by
  apply eq_of_glArch_eq_of_glFin_eq F
  · rw [map_mul, map_mul, hr, one_mul, mul_one]
  · rw [map_mul, map_mul, ha, one_mul, mul_one]

theorem sum_apply_mul_mul_reps_eq {G : Type*} [Group G] (U : Subgroup G) (g : G) {n : ℕ}
    (reps : Fin n → G)
    (hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u')
    (hcov : ∀ x : G, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j)
    (φ : G → ℂ) (hφU : ∀ x : G, ∀ u ∈ U, φ (x * u) = φ x) (x : G) {u : G} (hu : u ∈ U) :
    ∑ i, φ (x * u * reps i) = ∑ i, φ (x * reps i) := by
  have hmem : ∀ i, ∃ u₁ ∈ U, ∃ u' ∈ U, u * reps i = u₁ * g * u' := by
    intro i
    obtain ⟨u₁, hu₁, u', hu', hi⟩ := hreps i
    exact ⟨u * u₁, mul_mem hu hu₁, u', hu', by rw [hi, ← mul_assoc, ← mul_assoc]⟩
  choose σ w hw hσ using fun i => hcov (u * reps i) (hmem i)
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply hinj
    have e1 : (reps i)⁻¹ * reps j = (u * reps i)⁻¹ * (u * reps j) := by group
    rw [e1, hσ i, hσ j, hij]
    have e2 : (reps (σ j) * w i)⁻¹ * (reps (σ j) * w j) = (w i)⁻¹ * w j := by group
    rw [e2]
    exact mul_mem (inv_mem (hw i)) (hw j)
  have hσbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hσinj
  calc ∑ i, φ (x * u * reps i) = ∑ i, φ (x * reps (σ i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, hσ i, ← mul_assoc, hφU _ _ (hw i)]
    _ = ∑ i, φ (x * reps i) :=
        Fintype.sum_bijective σ hσbij (fun i => φ (x * reps (σ i))) (fun j => φ (x * reps j)) fun _ => rfl

theorem cosetSum_rightConv_eq (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUf : U ≤ finiteAdelicGL2Subgroup F)
    (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) (hfF : IsFactorizableTestFn F f)
    (hf : IsLevelSphericalOfType F tys U f)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u')
    (hcov : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u)
    (hinj : ∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x) :
    (fun x => ∑ i, rightConv F φ f (x * reps i)) = rightConv F (fun x => ∑ i, φ (x * reps i)) f := by
  classical
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨hfc, hfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hfF

  have hUfin : ∀ u ∈ U, glArch (𝓞 F) F u = 1 := fun u hu => (mem_finiteAdelicGL2Subgroup_iff F u).mp (hUf hu)
  have hgfin : glArch (𝓞 F) F g = 1 := (mem_finiteAdelicGL2Subgroup_iff F g).mp hg
  have hrepfin : ∀ i, glArch (𝓞 F) F (reps i) = 1 := by
    intro i
    obtain ⟨u, hu, u', hu', hi⟩ := hreps i
    rw [hi, map_mul, map_mul, hUfin u hu, hUfin u' hu', hgfin, one_mul, one_mul]

  obtain ⟨fa, -, -, -, hfeq⟩ := hf
  have hdec : ∀ y : AdelicGL2 (𝓞 F) F, f y ≠ 0 →
      ∃ a u : AdelicGL2 (𝓞 F) F, u ∈ U ∧ glFin (𝓞 F) F a = 1 ∧ y = a * u := by
    intro y hy
    have h2 : glFin (𝓞 F) F y ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
      by_contra h
      exact hy (by rw [hfeq y, Set.indicator_of_notMem h, mul_zero])
    obtain ⟨u, hu, huy⟩ := h2
    refine ⟨y * u⁻¹, u, hu, ?_, ?_⟩
    · rw [map_mul, map_inv, huy, mul_inv_cancel]
    · rw [inv_mul_cancel_right]

  have hint : ∀ z : AdelicGL2 (𝓞 F) F, Integrable (fun y => φ (z * y) * f y) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro z
    have hc : Continuous (fun y => φ (z * y) * f y) := (hφ.comp (continuous_const.mul continuous_id)).mul hfc
    exact hc.integrable_of_hasCompactSupport hfs.mul_left

  funext x
  simp only [rightConv_apply]
  rw [← integral_finsetSum _ (fun i _ => hint (x * reps i))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  by_cases hy : f y = 0
  · simp [hy]
  · rw [← Finset.sum_mul]
    congr 1
    obtain ⟨a, u, hu, ha, rfl⟩ := hdec y hy
    calc ∑ i, φ (x * reps i * (a * u)) = ∑ i, φ (x * a * reps i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [show x * reps i * (a * u) = (x * (reps i * a)) * u by simp only [mul_assoc], hφU _ _ hu,
            mul_comm_of_glFin_eq_one_of_glArch_eq_one F ha (hrepfin i), mul_assoc]
      _ = ∑ i, φ (x * a * u * reps i) :=
          (sum_apply_mul_mul_reps_eq U g reps hreps hcov hinj φ hφU (x * a) hu).symm
      _ = ∑ i, φ (x * (a * u) * reps i) := by simp only [mul_assoc]

theorem map_cuspSubcarrier_le_cuspInvSubcarrier
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, f (u * x) = f x)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T) :
    Submodule.map (T : Carrier F Φ₀ σ →ₗ[ℂ] Carrier F Φ₀ σ) (cuspSubcarrier F hΦ₀ σ ξ) ≤
      cuspInvSubcarrier F hΦ₀ σ ξ U := by
  set M : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hM
  set MN : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
        (cuspMemberSubmodule F Φ₀ ξ ⊓ Representation.invariants ((rightRegular F).comp U.subtype))) with hMN
  have hcl : cuspSubcarrier F hΦ₀ σ ξ = M.topologicalClosure := rfl
  have hclN : cuspInvSubcarrier F hΦ₀ σ ξ U = MN.topologicalClosure := rfl

  have hmaps : Set.MapsTo T (M : Set (Carrier F Φ₀ σ)) (MN : Set (Carrier F Φ₀ σ)) := by
    rintro w ⟨ψ, hψ, rfl⟩
    have hψ' : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hψ
    have hcont : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨ψ.2, hψ'.2⟩
    have hcomm := hT.comm (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont
    have hmt := hT.mapsTo (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont
    have hcusp : rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f ∈ cuspMemberSubmodule F Φ₀ ξ := by
      refine ⟨⟨⟨hmt.1, ?_⟩, AutomorphicForm.isKfSmooth_rightConv F _ f hf⟩, hmt.2⟩
      exact AutomorphicForm.isCuspidalFn_rightConv F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (ψ : AdelicGL2 (𝓞 F) F → ℂ) hψ'.2 hψ'.1.1.2 f hf
    have hlev : rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f ∈
        Representation.invariants ((rightRegular F).comp U.subtype) := by
      rw [mem_invariants_rightRegular_iff]
      intro g u hu
      rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
      have hfu : (fun y => f (u⁻¹ * y)) = f := funext fun y => hfU y u⁻¹ (inv_mem hu)
      rw [hfu]
    have heta : (⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hcont.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ψ := Subtype.coe_eta ψ hcont.1
    rw [heta] at hcomm
    refine ⟨⟨rightConv F (ψ : AdelicGL2 (𝓞 F) F → ℂ) f, hmt.1⟩, ⟨hcusp, hlev⟩, ?_⟩
    exact hcomm.symm

  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  have hv' : v ∈ closure (M : Set (Carrier F Φ₀ σ)) := by
    rw [← Submodule.topologicalClosure_coe, ← hcl]; exact hv
  have := map_mem_closure T.continuous hv' hmaps
  rw [← Submodule.topologicalClosure_coe, ← hclN] at this
  exact this

theorem apply_eq_zero_of_mem_orthogonal_cuspInvSubcarrier
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (hUf : U ≤ finiteAdelicGL2Subgroup F)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, f (x * u) = f x)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T)
    (v : Carrier F Φ₀ σ) (hv : v ∈ cuspSubcarrier F hΦ₀ σ ξ)
    (hperp : v ∈ (cuspInvSubcarrier F hΦ₀ σ ξ U)ᗮ) :
    T v = 0 := by
  classical
  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI hRinv : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ

  have hU_Kf : ∀ u ∈ U, u ∈ finiteAdelicGL2Subgroup F := fun u hu => hUf hu
  have hdet1 : ∀ u ∈ U, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := fun u hu =>
    NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem F U hU u hu

  set K : Set ↥(finiteAdelicGL2Subgroup F) := {k | (k : AdelicGL2 (𝓞 F) F) ∈ U} with hK
  have hKimg : ((↑) : ↥(finiteAdelicGL2Subgroup F) → AdelicGL2 (𝓞 F) F) '' K = (U : Set (AdelicGL2 (𝓞 F) F)) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hx
      exact ⟨⟨x, hUf hx⟩, hx, rfl⟩
  have hKcpt : IsCompact K := by
    have h : IsCompact (((↑) : ↥(finiteAdelicGL2Subgroup F) → AdelicGL2 (𝓞 F) F) '' K) := by
      rw [hKimg]
      exact hU
    exact Subtype.isCompact_iff.mpr h
  have hK_one : (1 : ↥(finiteAdelicGL2Subgroup F)) ∈ K := by
    show ((1 : ↥(finiteAdelicGL2Subgroup F)) : AdelicGL2 (𝓞 F) F) ∈ U; exact one_mem _
  have hK_mul : ∀ a b : ↥(finiteAdelicGL2Subgroup F), a ∈ K → b ∈ K → a * b ∈ K := fun a b ha hb => by
    show ((a * b : ↥(finiteAdelicGL2Subgroup F)) : AdelicGL2 (𝓞 F) F) ∈ U; exact mul_mem ha hb
  have hK_inv : ∀ a : ↥(finiteAdelicGL2Subgroup F), a ∈ K → a⁻¹ ∈ K := fun a ha => by
    show ((a⁻¹ : ↥(finiteAdelicGL2Subgroup F)) : AdelicGL2 (𝓞 F) F) ∈ U; exact inv_mem ha

  have hconv_eq : ∀ u ∈ U, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, rightConv F (rightTranslate F u φ) f = rightConv F φ f := by
    intro u hu φ
    funext x
    simp only [rightConv_apply, rightTranslate_apply]
    have h := integral_mul_right_eq_self (μ := μ) (fun y => φ (x * y) * f y) u
    rw [← hμ, ← h]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show φ (x * y * u) * f y = φ (x * (y * u)) * f (y * u)
    rw [mul_assoc, hfU y u hu]

  have hw_nonneg : ∀ x : AdelicGL2 (𝓞 F) F, 0 ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
    fun x => Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _
  have hwmeas : Measurable fun x : AdelicGL2 (𝓞 F) F => ENNReal.ofReal (weight F σ x) :=
    (((NumberField.TateGlobal.continuous_ideleNorm_det F).rpow_const fun x =>
      Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne').measurable).ennreal_ofReal
  have inner_toCarrier : ∀ (a b : AdelicGL2 (𝓞 F) F → ℂ) (ha : a ∈ memberSubmodule F Φ₀ ξ) (hb : b ∈ memberSubmodule F Φ₀ ξ),
      ⟪toCarrier F hΦ₀ σ ξ ⟨a, ha⟩, toCarrier F hΦ₀ σ ξ ⟨b, hb⟩⟫_ℂ = pairing F Φ₀ σ b a := by
    intro a b ha hb
    rw [MeasureTheory.L2.inner_def]
    have hae_a : (toCarrier F hΦ₀ σ ξ ⟨a, ha⟩ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[weightedMeasure F Φ₀ σ] a :=
      MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ ha)
    have hae_b : (toCarrier F hΦ₀ σ ξ ⟨b, hb⟩ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[weightedMeasure F Φ₀ σ] b :=
      MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ hb)
    have h1 : ∫ x, ⟪(toCarrier F hΦ₀ σ ξ ⟨a, ha⟩ : AdelicGL2 (𝓞 F) F → ℂ) x, (toCarrier F hΦ₀ σ ξ ⟨b, hb⟩ : AdelicGL2 (𝓞 F) F → ℂ) x⟫_ℂ
          ∂(weightedMeasure F Φ₀ σ) = ∫ x, b x * conj (a x) ∂(weightedMeasure F Φ₀ σ) := by
      apply integral_congr_ae
      filter_upwards [hae_a, hae_b] with x hxa hxb
      rw [hxa, hxb, RCLike.inner_apply]
    rw [h1]
    unfold weightedMeasure pairing
    rw [integral_withDensity_eq_integral_toReal_smul hwmeas (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show (ENNReal.ofReal (weight F σ x)).toReal • (b x * conj (a x)) = b x * conj (a x) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
    rw [weight_def, ENNReal.toReal_ofReal (hw_nonneg x), Complex.real_smul]
    ring
  set L : Submodule ℂ (Carrier F Φ₀ σ) := cuspInvSubcarrier F hΦ₀ σ ξ U with hLdef
  have hLclosed : IsClosed (L : Set (Carrier F Φ₀ σ)) := by
    rw [hLdef]; unfold cuspInvSubcarrier; exact Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace ↥L := hLclosed.completeSpace_coe
  let PL := L.orthogonalProjection

  have key : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
      T (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩) = T ((PL (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩) : Carrier F Φ₀ σ)) := by
    intro φ hφ

    have hOfin := AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact (F := F) (φ := φ) hφ.1.2 hKcpt
    set O : Finset (FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) := hOfin.toFinset with hO
    have hmemO : ∀ θ, θ ∈ O ↔ ∃ k ∈ K, k • (FLT.SmoothVectors.RightTranslationFn.mk φ :
        FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) = θ := by
      intro θ; rw [hO, Set.Finite.mem_toFinset, Set.mem_image]
    have hO_ne : O.Nonempty := ⟨_, (hmemO _).mpr ⟨1, hK_one, rfl⟩⟩
    have hcard : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hO_ne).ne'

    have hθ_tr : ∀ θ ∈ O, ∃ u ∈ U, (θ.toFun : AdelicGL2 (𝓞 F) F → ℂ) = rightTranslate F u φ := by
      intro θ hθ
      obtain ⟨k, hk, rfl⟩ := (hmemO θ).mp hθ
      refine ⟨(k : AdelicGL2 (𝓞 F) F), hk, funext fun x => ?_⟩
      rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul, FLT.SmoothVectors.RightTranslationFn.toFun_mk,
        rightTranslate_apply]
    have hθ_mem : ∀ θ ∈ O, (θ.toFun : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := by
      intro θ hθ
      obtain ⟨u, -, hu⟩ := hθ_tr θ hθ
      rw [hu]
      exact AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ u φ hφ

    set eφ : AdelicGL2 (𝓞 F) F → ℂ := (O.card : ℂ)⁻¹ • ∑ θ ∈ O, (θ.toFun : AdelicGL2 (𝓞 F) F → ℂ) with heφ
    have he_mem : eφ ∈ cuspMemberSubmodule F Φ₀ ξ :=
      Submodule.smul_mem _ _ (Submodule.sum_mem _ fun θ hθ => hθ_mem θ hθ)

    have he_lvl : eφ ∈ Representation.invariants ((rightRegular F).comp U.subtype) := by
      rw [mem_invariants_rightRegular_iff]
      intro x u hu
      have hu' : (⟨u, hU_Kf u hu⟩ : ↥(finiteAdelicGL2Subgroup F)) ∈ K := hu
      simp only [heφ, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      congr 1
      refine Finset.sum_bij' (fun θ _ => (⟨u, hU_Kf u hu⟩ : ↥(finiteAdelicGL2Subgroup F)) • θ)
        (fun θ _ => (⟨u, hU_Kf u hu⟩ : ↥(finiteAdelicGL2Subgroup F))⁻¹ • θ) ?_ ?_ ?_ ?_ ?_
      · intro θ hθ
        obtain ⟨k, hk, rfl⟩ := (hmemO θ).mp hθ
        exact (hmemO _).mpr ⟨_, hK_mul _ _ hu' hk, (mul_smul _ _ _)⟩
      · intro θ hθ
        obtain ⟨k, hk, rfl⟩ := (hmemO θ).mp hθ
        exact (hmemO _).mpr ⟨_, hK_mul _ _ (hK_inv _ hu') hk, (mul_smul _ _ _)⟩
      · intro θ _; exact inv_smul_smul _ _
      · intro θ _; exact smul_inv_smul _ _
      · intro θ _
        show θ.toFun (x * u) = (((⟨u, hU_Kf u hu⟩ : ↥(finiteAdelicGL2Subgroup F)) • θ).toFun x)
        rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul]

    have he_coe : (⟨eφ, he_mem.1.1.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) =
        (O.card : ℂ)⁻¹ • ∑ θ ∈ O.attach, (⟨(θ.1.toFun : AdelicGL2 (𝓞 F) F → ℂ), (hθ_mem θ.1 θ.2).1.1.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) := by
      apply Subtype.ext
      simp only [heφ, Submodule.coe_smul, Submodule.coe_sum]
      congr 1
      exact (Finset.sum_attach O (fun θ => (θ.toFun : AdelicGL2 (𝓞 F) F → ℂ))).symm

    have hT_orbit : ∀ θ : ↥O, T (toCarrier F hΦ₀ σ ξ ⟨(θ.1.toFun : AdelicGL2 (𝓞 F) F → ℂ), (hθ_mem θ.1 θ.2).1.1.1⟩) =
        T (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩) := by
      intro θ
      obtain ⟨u, hu, hθu⟩ := hθ_tr θ.1 θ.2
      have hcθ : (θ.1.toFun : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨(hθ_mem θ.1 θ.2).1.1.1, (hθ_mem θ.1 θ.2).2⟩
      have hcφ : φ ∈ contMemberSubmodule F Φ₀ ξ := ⟨hφ.1.1.1, hφ.2⟩
      rw [hT.comm _ hcθ, hT.comm _ hcφ]
      congr 1
      apply Subtype.ext
      show rightConv F θ.1.toFun f = rightConv F φ f
      rw [hθu, hconv_eq u hu φ]
    have hTe : T (toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩) = T (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩) := by
      rw [he_coe, map_smul, map_sum, map_smul, map_sum]
      simp only [hT_orbit, Finset.sum_const, Finset.card_attach]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

    have he_L : toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩ ∈ L := by
      rw [hLdef]; unfold cuspInvSubcarrier
      exact Submodule.le_topologicalClosure _ ⟨⟨eφ, he_mem.1.1.1⟩, Submodule.mem_inf.mpr ⟨he_mem, he_lvl⟩, rfl⟩
    have hpair_orbit : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ ∈ cuspMemberSubmodule F Φ₀ ξ →
        ψ ∈ Representation.invariants ((rightRegular F).comp U.subtype) → ∀ θ ∈ O, pairing F Φ₀ σ θ.toFun ψ = pairing F Φ₀ σ φ ψ := by
      intro ψ hψ hψU θ hθ
      rw [mem_invariants_rightRegular_iff] at hψU
      obtain ⟨u, hu, hθu⟩ := hθ_tr θ hθ
      have hcφ : φ ∈ contMemberSubmodule F Φ₀ ξ := ⟨hφ.1.1.1, hφ.2⟩
      have hcψ : ψ ∈ contMemberSubmodule F Φ₀ ξ := ⟨hψ.1.1.1, hψ.2⟩
      have hU1 := AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
        F hΦ₀ σ ξ φ ψ hcφ hcψ u (hdet1 u hu)
      have hψinv : rightTranslate F u⁻¹ ψ = ψ := funext fun x => hψU x u⁻¹ (inv_mem hu)
      rw [hθu, hU1.2.2, hψinv]
    have he_perp : toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩ - toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩ ∈ Lᗮ := by

      have hgen : ∀ w ∈ (Submodule.map (toCarrier F hΦ₀ σ ξ)
          (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
            (cuspMemberSubmodule F Φ₀ ξ ⊓ Representation.invariants ((rightRegular F).comp U.subtype)))),
          ⟪w, toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩ - toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩⟫_ℂ = 0 := by
        rintro _ ⟨ψ, hψ, rfl⟩
        obtain ⟨hψc, hψU⟩ := Submodule.mem_inf.mp hψ
        have hψ' : (ψ : ↥(memberSubmodule F Φ₀ ξ)) = ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2⟩ := rfl
        rw [inner_sub_right, hψ', he_coe, map_smul, map_sum, inner_smul_right, inner_sum, inner_toCarrier]
        have hθψ : ∀ θ ∈ O.attach, ⟪toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2⟩,
            toCarrier F hΦ₀ σ ξ ⟨(θ.1.toFun : AdelicGL2 (𝓞 F) F → ℂ), (hθ_mem θ.1 θ.2).1.1.1⟩⟫_ℂ = pairing F Φ₀ σ φ ψ := by
          intro θ _
          rw [inner_toCarrier]
          exact hpair_orbit ψ hψc hψU θ.1 θ.2
        rw [Finset.sum_congr rfl hθψ, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hcard, one_mul, sub_self]
      rw [Submodule.mem_orthogonal]
      intro w hw
      have hw' : w ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
          (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
            (cuspMemberSubmodule F Φ₀ ξ ⊓ Representation.invariants ((rightRegular F).comp U.subtype))) : Set (Carrier F Φ₀ σ))) := by
        rw [← Submodule.topologicalClosure_coe]; rw [hLdef] at hw; exact hw
      exact closure_minimal (s := _) (t := {w : Carrier F Φ₀ σ | ⟪w, toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩ - toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩⟫_ℂ = 0})
        hgen (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hw'

    have hP : ((PL (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩)) : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩ :=
      Submodule.eq_starProjection_of_mem_orthogonal he_L he_perp
    rw [hP, hTe]

  have hC : IsClosed {w : Carrier F Φ₀ σ | T w = T ((PL w : ↥L) : Carrier F Φ₀ σ)} :=
    isClosed_eq T.continuous (T.continuous.comp (continuous_subtype_val.comp PL.continuous))
  have hv' : v ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hv
  have hvC : T v = T ((PL v : ↥L) : Carrier F Φ₀ σ) := by
    refine closure_minimal ?_ hC hv'
    rintro _ ⟨ψ, hψ, rfl⟩
    have hψ' : (ψ : ↥(memberSubmodule F Φ₀ ξ)) = ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hψ.1.1.1⟩ := rfl
    show T (toCarrier F hΦ₀ σ ξ ψ) = T ((PL (toCarrier F hΦ₀ σ ξ ψ) : ↥L) : Carrier F Φ₀ σ)
    rw [hψ']
    exact key ψ hψ
  have hPv : PL v = 0 := Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hperp
  rw [hvC, hPv, Submodule.coe_zero, map_zero]

end Ws28.CUTOPHU

end

open Ws28.CUTOPHU in
theorem solution
    (F : Type) [Field F] [NumberField F]
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys U f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F) (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (h1 : ∀ i, ∃ u' ∈ U, ∃ u'' ∈ U, reps i = u' * g * u'')
    (h2 : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u' ∈ U, ∃ u'' ∈ U, x = u' * g * u'') → ∃ i, ∃ u' ∈ U, x = reps i * u')
    (h3 : ∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ), S.comp Tc = Tc.comp S ∧
      ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
        (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ Representation.invariants ((rightRegular F).comp U.subtype) →
        ∃ h : (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) ∈ cuspMemberSubmodule F Φ₀ ξ,
          S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i), h⟩ := by
  classical
  have hUf : U ≤ finiteAdelicGL2Subgroup F := by
    rw [hUO]
    exact inf_le_right
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier
    exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

  have hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ U, f (u' * x) = f x := by
    obtain ⟨fa, -, -, -, hfac⟩ := hsph
    intro x u' hu'
    have harch : AdelicLevel.glArch (𝓞 F) F u' = 1 := (mem_finiteAdelicGL2Subgroup_iff F u').mp (hUf hu')
    have himg : (AdelicLevel.glFin (𝓞 F) F u' * AdelicLevel.glFin (𝓞 F) F x ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) ↔
        (AdelicLevel.glFin (𝓞 F) F x ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := by
      constructor
      · rintro ⟨k, hk, hkz⟩
        refine ⟨u'⁻¹ * k, Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hk, ?_⟩
        rw [map_mul, map_inv, hkz, inv_mul_cancel_left]
      · rintro ⟨k, hk, hkx⟩
        exact ⟨u' * k, Subgroup.mul_mem _ hu' hk, by rw [map_mul, hkx]⟩
    rw [hfac, hfac x, map_mul, harch, one_mul, map_mul]
    simp only [Set.indicator_apply, himg]
  have hfU' : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u' ∈ U, f (x * u') = f x := by
    obtain ⟨fa, -, -, -, hfac⟩ := hsph
    intro x u' hu'
    have harch : AdelicLevel.glArch (𝓞 F) F u' = 1 := (mem_finiteAdelicGL2Subgroup_iff F u').mp (hUf hu')
    have himg : (AdelicLevel.glFin (𝓞 F) F x * AdelicLevel.glFin (𝓞 F) F u' ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) ↔
        (AdelicLevel.glFin (𝓞 F) F x ∈
        (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := by
      constructor
      · rintro ⟨k, hk, hkz⟩
        refine ⟨k * u'⁻¹, Subgroup.mul_mem _ hk (Subgroup.inv_mem _ hu'), ?_⟩
        rw [map_mul, map_inv, hkz, mul_inv_cancel_right]
      · rintro ⟨k, hk, hkx⟩
        exact ⟨k * u', Subgroup.mul_mem _ hk hu', by rw [map_mul, hkx]⟩
    rw [hfac, hfac x, map_mul, harch, mul_one, map_mul]
    simp only [Set.indicator_apply, himg]

  obtain ⟨Tf, -, hTf, -, -⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfcs
  have memf : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ := by
    intro φ
    have hcont : (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨φ.2.1.1.1, φ.2.2⟩
    have hmaps := hTf.mapsTo φ hcont
    refine ⟨⟨⟨hmaps.1, ?_⟩, AutomorphicForm.isKfSmooth_rightConv F φ f hf⟩, hmaps.2⟩
    exact AutomorphicForm.isCuspidalFn_rightConv F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) φ φ.2.2 φ.2.1.1.2 f hf
  have hdense : Dense (Set.range (toCuspSubcarrier F hΦ₀ σ ξ)) := by
    rw [Subtype.dense_iff]
    intro v hv
    have hv' : v ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hv
    refine closure_mono ?_ hv'
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩, ⟨_, rfl⟩, rfl⟩
  have hTc_eq : (cuspSubcarrier F hΦ₀ σ ξ).subtypeL.comp Tc = Tf.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL := by
    refine ContinuousLinearMap.ext_on (hdense.mono Submodule.subset_span) ?_
    rintro _ ⟨φ, rfl⟩
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.subtypeL_apply,
      hcomm φ (memf φ), toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact (hTf.comm φ ⟨φ.2.1.1.1, φ.2.2⟩).symm
  have hTc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), ((Tc v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) = Tf v := fun v =>
    congrArg (fun A : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] Carrier F Φ₀ σ => A v) hTc_eq

  have hLcH : cuspInvSubcarrier F hΦ₀ σ ξ U ≤ cuspSubcarrier F hΦ₀ σ ξ := by
    unfold cuspInvSubcarrier cuspSubcarrier
    exact Submodule.topologicalClosure_mono (Submodule.map_mono (Submodule.comap_mono inf_le_left))
  set LH : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) := Submodule.comap (cuspSubcarrier F hΦ₀ σ ξ).subtype (cuspInvSubcarrier F hΦ₀ σ ξ U) with hLH
  have hLHclosed : IsClosed (LH : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
    have h1 : IsClosed ((cuspInvSubcarrier F hΦ₀ σ ξ U : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
      unfold cuspInvSubcarrier
      exact Submodule.isClosed_topologicalClosure _
    exact h1.preimage continuous_subtype_val
  haveI : CompleteSpace ↥LH := hLHclosed.completeSpace_coe
  set PN : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := LH.starProjection with hPN

  have hrange : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Tc v ∈ LH := by
    intro v
    show ((Tc v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ cuspInvSubcarrier F hΦ₀ σ ξ U
    rw [hTc v]
    exact map_cuspSubcarrier_le_cuspInvSubcarrier F hΦ₀ σ ξ U f hf hfU Tf hTf (Submodule.mem_map_of_mem v.2)
  have hker : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), v ∈ LHᗮ → Tc v = 0 := by
    intro v hv
    apply Subtype.ext
    rw [hTc v]
    refine apply_eq_zero_of_mem_orthogonal_cuspInvSubcarrier F hΦ₀ σ ξ U hU hUf f hfU' Tf hTf v v.2 ?_
    rw [Submodule.mem_orthogonal]
    intro y hy
    exact (Submodule.mem_orthogonal _ _).mp hv ⟨y, hLcH hy⟩ hy

  have hL := fun i => AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ (reps i)
  choose Tr Tr' hTr hTr' hadj hnorm using hL
  have memr : ∀ (i : Fin n) (φ : AdelicGL2 (𝓞 F) F → ℂ), φ ∈ cuspMemberSubmodule F Φ₀ ξ →
      rightTranslate F (reps i) φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun i φ hφ =>
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (reps i) φ hφ
  have hinv : ∀ (i : Fin n) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), Tr i (v : Carrier F Φ₀ σ) ∈ cuspSubcarrier F hΦ₀ σ ξ := by
    intro i v
    have hM : ∀ x ∈ ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)),
        Tr i x ∈ ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
      rintro _ ⟨ψ, hψ, rfl⟩
      refine ⟨⟨rightTranslate F (reps i) ψ, (memr i ψ hψ).1.1.1⟩, memr i ψ hψ, ?_⟩
      exact ((hTr i).comm ψ ⟨ψ.2, hψ.2⟩).symm
    have hv : (v : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
        (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact v.2
    have h1 := image_closure_subset_closure_image (Tr i).continuous ⟨(v : Carrier F Φ₀ σ), hv, rfl⟩
    have h2 := closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact hM x hx) h1
    rw [← Submodule.topologicalClosure_coe] at h2
    exact h2
  let Sraw : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    ((∑ i, Tr i).comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) fun v => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hinv i v
  have Sraw_apply : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), (Sraw v : Carrier F Φ₀ σ) = ∑ i, Tr i v := by
    intro v
    show ((∑ i, Tr i).comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL) v = _
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    rfl

  have memsum : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) ∈ cuspMemberSubmodule F Φ₀ ξ := by
    intro φ
    have hfeq : (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) =
        ∑ i, rightTranslate F (reps i) (φ : AdelicGL2 (𝓞 F) F → ℂ) := by
      funext x; simp only [Finset.sum_apply, rightTranslate_apply]
    rw [hfeq]
    exact Submodule.sum_mem _ fun i _ => memr i φ φ.2
  have Sraw_lift : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
      Sraw (toCuspSubcarrier F hΦ₀ σ ξ φ) =
        toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i), memsum φ⟩ := by
    intro φ
    apply Subtype.ext
    rw [Sraw_apply, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    have hstep : ∀ i, Tr i (toCarrier F hΦ₀ σ ξ ⟨φ, φ.2.1.1.1⟩) =
        toCarrier F hΦ₀ σ ξ ⟨rightTranslate F (reps i) φ, (memr i φ φ.2).1.1.1⟩ :=
      fun i => (hTr i).comm φ ⟨φ.2.1.1.1, φ.2.2⟩
    simp only [hstep]
    rw [← map_sum]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_sum]
    funext x
    simp only [Finset.sum_apply, rightTranslate_apply]

  have key : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)),
      (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ Representation.invariants ((rightRegular F).comp U.subtype) →
      Sraw (Tc (toCuspSubcarrier F hΦ₀ σ ξ φ)) = Tc (Sraw (toCuspSubcarrier F hΦ₀ σ ξ φ)) := by
    intro φ hφU
    rw [hcomm φ (memf φ), Sraw_lift, Sraw_lift, hcomm _ (memf _)]
    congr 1
    apply Subtype.ext
    exact cosetSum_rightConv_eq F U hUf tys f hf hsph g hg n reps h1 h2 h3 φ φ.2.2
      ((mem_invariants_rightRegular_iff F U _).mp hφU)
  have hcommL : ∀ w : ↥LH, Sraw (Tc (w : ↥(cuspSubcarrier F hΦ₀ σ ξ))) = Tc (Sraw (w : ↥(cuspSubcarrier F hΦ₀ σ ξ))) := by

    let DL : Set ↥LH := {w | ∃ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)),
      (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ Representation.invariants ((rightRegular F).comp U.subtype) ∧ (w : ↥(cuspSubcarrier F hΦ₀ σ ξ)) = toCuspSubcarrier F hΦ₀ σ ξ φ}
    have hDL : Dense DL := by
      rw [Subtype.dense_iff]
      intro z hz
      rw [closure_subtype]
      have hz' : ((z : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
          (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
            (cuspMemberSubmodule F Φ₀ ξ ⊓ Representation.invariants ((rightRegular F).comp U.subtype)))) : Set (Carrier F Φ₀ σ)) := by
        rw [← Submodule.topologicalClosure_coe]
        exact hz
      refine closure_mono ?_ hz'
      rintro _ ⟨ψ, hψ, rfl⟩
      have hψm : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := (Submodule.mem_inf.mp hψ).1
      have hψU : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ Representation.invariants ((rightRegular F).comp U.subtype) := (Submodule.mem_inf.mp hψ).2
      have hmemLH : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ LH := by
        show ((toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ cuspInvSubcarrier F hΦ₀ σ ξ U
        rw [toCuspSubcarrier_apply_coe]
        unfold cuspInvSubcarrier
        exact Submodule.le_topologicalClosure _ ⟨ψ, hψ, rfl⟩
      exact ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩, ⟨⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩, hmemLH⟩, ⟨⟨ψ, hψm⟩, hψU, rfl⟩, rfl⟩, rfl⟩
    have hext : ((Sraw.comp Tc).comp LH.subtypeL) = ((Tc.comp Sraw).comp LH.subtypeL) := by
      refine ContinuousLinearMap.ext_on (hDL.mono Submodule.subset_span) ?_
      rintro w ⟨φ, hφU, hw⟩
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      rw [hw]
      exact key φ hφU
    intro w
    have := congrArg (fun A : ↥LH →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) => A w) hext
    simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using this

  refine ⟨Sraw.comp PN, ?_, ?_⟩
  · ext1 v
    have hPT : PN (Tc v) = Tc v := Submodule.starProjection_eq_self_iff.mpr (hrange v)
    have hdec : Tc v = Tc (PN v) := by
      have h0 : Tc (v - PN v) = 0 := hker _ (Submodule.sub_starProjection_mem_orthogonal v)
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have hPmem : PN v ∈ LH := by
      rw [hPN]
      exact (LH.orthogonalProjection v).2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hPT, hdec]
    exact hcommL ⟨PN v, hPmem⟩
  · intro φ hφU
    refine ⟨memsum φ, ?_⟩
    have hmemLH : toCuspSubcarrier F hΦ₀ σ ξ φ ∈ LH := by
      show ((toCuspSubcarrier F hΦ₀ σ ξ φ : ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Carrier F Φ₀ σ) ∈ cuspInvSubcarrier F hΦ₀ σ ξ U
      rw [toCuspSubcarrier_apply_coe]
      unfold cuspInvSubcarrier
      refine Submodule.le_topologicalClosure _ ⟨⟨φ, φ.2.1.1.1⟩, ?_, rfl⟩
      exact Submodule.mem_inf.mpr ⟨φ.2, hφU⟩
    rw [ContinuousLinearMap.comp_apply, Submodule.starProjection_eq_self_iff.mpr hmemLH]
    exact Sraw_lift φ

end S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact (solution)
