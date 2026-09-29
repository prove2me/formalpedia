-- Prove2me | solution 1 for AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6c0229f7-4eb5-5af3-90fd-0b66d84f17a0

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace Ws47
namespace REPRO
namespace FinIncl

variable (F : Type) [Field F] [NumberField F]

noncomputable def adelicFinGLIncl : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* AdelicGL2 (𝓞 F) F :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (1 : _ →* GL (Fin 2) (InfiniteAdeleRing F)) (MonoidHom.id _)

theorem glArch_adelicFinGLIncl (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (adelicFinGLIncl F k) = 1 := by
  ext i j
  rfl

theorem glFin_adelicFinGLIncl (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (adelicFinGLIncl F k) = k := by
  ext i j
  rfl

theorem adelicFinGLIncl_mem_finiteAdelicGL2Subgroup (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    adelicFinGLIncl F k ∈ finiteAdelicGL2Subgroup F :=
  (mem_finiteAdelicGL2Subgroup_iff F _).2 (glArch_adelicFinGLIncl F k)

theorem continuous_adelicFinGLIncl : Continuous (adelicFinGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      ((adelicFinGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem adelicFinGLIncl_glFin_of_glArch_eq_one (g : AdelicGL2 (𝓞 F) F) (hg : glArch (𝓞 F) F g = 1) :
    adelicFinGLIncl F (glFin (𝓞 F) F g) = g := by
  ext i j
  refine Prod.ext ?_ rfl
  exact (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
    hg).symm

theorem adelicArchGLIncl_glArch_of_glFin_eq_one (g : AdelicGL2 (𝓞 F) F) (hg : glFin (𝓞 F) F g = 1) :
    adelicArchGLIncl F (glArch (𝓞 F) F g) = g := by
  ext i j
  refine Prod.ext rfl ?_
  exact (congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) hg).symm

theorem image_glFin_eq_preimage (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hUf : U ≤ finiteAdelicGL2Subgroup F) :
    (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
      = adelicFinGLIncl F ⁻¹' (U : Set (AdelicGL2 (𝓞 F) F)) := by
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    show adelicFinGLIncl F (glFin (𝓞 F) F g) ∈ (U : Set (AdelicGL2 (𝓞 F) F))
    rw [adelicFinGLIncl_glFin_of_glArch_eq_one F g ((mem_finiteAdelicGL2Subgroup_iff F g).1 (hUf hg))]
    exact hg
  · intro hm
    exact ⟨adelicFinGLIncl F m, hm, glFin_adelicFinGLIncl F m⟩

theorem isOpen_image_glFin (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F))) :
    IsOpen ((glFin (𝓞 F) F) '' (↑(O ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [image_glFin_eq_preimage F _ inf_le_right]
  have h : adelicFinGLIncl F ⁻¹' (↑(O ⊓ finiteAdelicGL2Subgroup F) : Set (AdelicGL2 (𝓞 F) F))
      = adelicFinGLIncl F ⁻¹' (O : Set (AdelicGL2 (𝓞 F) F)) := by
    ext m
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, adelicFinGLIncl_mem_finiteAdelicGL2Subgroup F m⟩⟩
  rw [h]
  exact hO.preimage (continuous_adelicFinGLIncl F)

theorem isCompact_image_glFin (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F))) :
    IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) :=
  hU.image (continuous_glFin (𝓞 F) F)

end Ws47.REPRO.FinIncl

namespace Ws47
namespace REPRO

open Ws47.REPRO.FinIncl
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem hasCompactSupport_const_smul' {X : Type} [TopologicalSpace X] (c : ℂ) {f : X → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (c • f) :=
  hf.mono fun x hx => by
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or] at hx ⊢
    exact hx.2

theorem isArchTestFactor_add {fa fb : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (ha : IsArchTestFactor F fa)
    (hb : IsArchTestFactor F fb) : IsArchTestFactor F (fa + fb) := by
  obtain ⟨⟨Φa, hΦa, hfa⟩, hsa⟩ := ha
  obtain ⟨⟨Φb, hΦb, hfb⟩, hsb⟩ := hb
  refine ⟨⟨Φa + Φb, hΦa.add hΦb, fun g => ?_⟩, hsa.add hsb⟩
  simp only [Pi.add_apply, hfa g, hfb g]

theorem isArchTestFactor_smul (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (ha : IsArchTestFactor F fa) : IsArchTestFactor F (c • fa) := by
  obtain ⟨⟨Φa, hΦa, hfa⟩, hsa⟩ := ha
  refine ⟨⟨c • Φa, hΦa.const_smul c, fun g => ?_⟩, hasCompactSupport_const_smul' c hsa⟩
  simp only [Pi.smul_apply, hfa g]

variable (F) in

def sphericalFactors (tys : ArchTypeFamily F) : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) where
  carrier := {fa | IsArchSphericalOfType F tys fa}
  zero_mem' := isArchSphericalOfType_zero F tys
  add_mem' := by
    rintro fa fb ⟨ha1, ⟨ha2l, ha2r⟩, ha3⟩ ⟨hb1, ⟨hb2l, hb2r⟩, hb3⟩
    refine ⟨isArchTestFactor_add ha1 hb1, ⟨?_, Submodule.add_mem _ ha2r hb2r⟩, fun w k x => ?_⟩
    · have : (fun x => (fa + fb) x⁻¹) = (fun x => fa x⁻¹) + fun x => fb x⁻¹ := rfl
      rw [this]; exact Submodule.add_mem _ ha2l hb2l
    · simp only [Pi.add_apply, ha3 w k x, hb3 w k x]
  smul_mem' := by
    rintro c fa ⟨ha1, ⟨ha2l, ha2r⟩, ha3⟩
    refine ⟨isArchTestFactor_smul c ha1, ⟨?_, Submodule.smul_mem _ c ha2r⟩, fun w k x => ?_⟩
    · have : (fun x => (c • fa) x⁻¹) = c • fun x => fa x⁻¹ := rfl
      rw [this]; exact Submodule.smul_mem _ c ha2l
    · simp only [Pi.smul_apply, ha3 w k x]

theorem isFinTestFactor_indicator_image_glFin
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F) :
    IsFinTestFactor F (Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))) := by
  have hUo : IsOpen ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := by
    rw [hUO]
    exact isOpen_image_glFin F O hO
  have hUc : IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := isCompact_image_glFin F U hU
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 F) F))
  haveI : T2Space (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := Units.isEmbedding_embedProduct.t2Space
  have hcl : IsClosed ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) := hUc.isClosed
  refine ⟨?_, HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
  · exact ⟨_, hUo, hx, fun x' hx' => by rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]⟩
  · exact ⟨_, hcl.isOpen_compl, hx, fun x' hx' => by
      rw [Set.indicator_of_notMem (show x' ∉ _ from hx'), Set.indicator_of_notMem hx]⟩

theorem lincomb_levelSpherical
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → (AdelicGL2 (𝓞 F) F → ℂ))
    (hf : ∀ i ∈ s, IsFactorizableTestFn F (f i) ∧ IsLevelSphericalOfType F tys U (f i)) (hs : s.Nonempty) :
    IsFactorizableTestFn F (∑ i ∈ s, c i • f i) ∧ IsLevelSphericalOfType F tys U (∑ i ∈ s, c i • f i) ∧
      IsArchBiFinite F tys (∑ i ∈ s, c i • f i) := by
  classical

  set ind : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
    Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) with hind
  have hfin : IsFinTestFactor F ind := isFinTestFactor_indicator_image_glFin U hU O hO hUO
  have hfa : ∀ i ∈ s, ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, fa ∈ sphericalFactors F tys ∧
      ∀ g : AdelicGL2 (𝓞 F) F, f i g = fa (glArch (𝓞 F) F g) * ind (glFin (𝓞 F) F g) := by
    intro i hi
    obtain ⟨fa, hsph, hfeq⟩ := (isLevelSphericalOfType_iff' F tys U (f i)).mp (hf i hi).2
    exact ⟨fa, hsph, hfeq⟩
  choose! fa hfaS hfaEq using hfa
  set FA : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := ∑ i ∈ s, c i • fa i with hFA
  have hFAS : FA ∈ sphericalFactors F tys :=
    Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ (c i) (hfaS i hi)
  have hsumEq : ∀ g : AdelicGL2 (𝓞 F) F, (∑ i ∈ s, c i • f i) g = FA (glArch (𝓞 F) F g) * ind (glFin (𝓞 F) F g) := by
    intro g
    rw [hFA, Finset.sum_apply, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hfaEq i hi g, mul_assoc]
  obtain ⟨hFA1, hFA2, hFA3⟩ := hFAS
  refine ⟨⟨FA, ind, hFA1, hfin, hsumEq⟩, ⟨FA, hFA1, hFA2, hFA3, hsumEq⟩, ?_⟩
  exact IsArchBiFinite.of_factorization F hsumEq hFA2

section O2

open MeasureTheory

theorem integrable_conv_integrand {φ α : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (hαc : Continuous α)
    (hαs : HasCompactSupport α) (g : AdelicGL2 (𝓞 F) F) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
    Integrable (fun y => φ (g * y) * α y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ((hφ.comp (continuous_const.mul continuous_id)).mul hαc).integrable_of_hasCompactSupport (hαs.mono ?_)
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by show φ (g * y) * α y = 0; rw [h0, mul_zero])

end O2

theorem rightConv_finset_sum_smul (F : Type) [Field F] [NumberField F]
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → (AdelicGL2 (𝓞 F) F → ℂ))
    (hf : ∀ i ∈ s, IsFactorizableTestFn F (f i)) (y : AdelicGL2 (𝓞 F) F → ℂ) (hy : Continuous y) :
    rightConv F y (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • rightConv F y (f i) := by
  classical
  have hcs : ∀ i ∈ s, Continuous (f i) ∧ HasCompactSupport (f i) := fun i hi =>
    AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F (f i) (hf i hi)
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  funext g
  show (∫ x, y (g * x) * (∑ i ∈ s, c i • f i) x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
    (∑ i ∈ s, c i • rightConv F y (f i)) g
  rw [Finset.sum_apply]
  have : (fun x => y (g * x) * (∑ i ∈ s, c i • f i) x) = fun x => ∑ i ∈ s, c i * (y (g * x) * f i x) := by
    funext x
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  rw [this, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_const_mul, Pi.smul_apply, smul_eq_mul]
    rfl
  · intro i hi
    exact (integrable_conv_integrand hy (hcs i hi).1 (hcs i hi).2 g).const_mul (c i)

end Ws47.REPRO

namespace Ws47
namespace REPRO

theorem mem_span_range_of_tendsto {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (Φ : ℕ → X → ℂ) (hΦ : ∀ n, Φ n ∈ V) (Φlim : X → ℂ)
    (hlim : ∀ x, Filter.Tendsto (fun n => Φ n x) Filter.atTop (nhds (Φlim x))) :
    Φlim ∈ Submodule.span ℂ (Set.range Φ) := by
  set L : Submodule ℂ (X → ℂ) := Submodule.span ℂ (Set.range Φ) with hL
  have hLE : L ≤ V := by rw [hL, Submodule.span_le]; rintro _ ⟨n, rfl⟩; exact hΦ n
  haveI : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLE
  have ht : Filter.Tendsto Φ Filter.atTop (nhds Φlim) := tendsto_pi_nhds.2 hlim
  exact L.closed_of_finiteDimensional.mem_of_tendsto ht
    (Filter.Eventually.of_forall fun n => Submodule.subset_span ⟨n, rfl⟩)

noncomputable def convEnd (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hYc : ∀ y ∈ Y, Continuous y)
    (hYs : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsLevelSphericalOfType F tys U f →
      ∀ y ∈ Y, rightConv F y f ∈ Y)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hfl : IsLevelSphericalOfType F tys U f) :
    Y →ₗ[ℂ] Y where
  toFun y := ⟨rightConv F (y : AdelicGL2 (𝓞 F) F → ℂ) f, hYs f hf hfl y y.2⟩
  map_add' y z := by
    apply Subtype.ext
    have h := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
    show rightConv F ((y : AdelicGL2 (𝓞 F) F → ℂ) + z) f = rightConv F (y : AdelicGL2 (𝓞 F) F → ℂ) f + rightConv F (z : _ → ℂ) f
    exact rightConv_add_left F (hYc _ y.2) (hYc _ z.2) h.1 h.2
  map_smul' a y := by
    apply Subtype.ext
    show rightConv F (a • (y : AdelicGL2 (𝓞 F) F → ℂ)) f = a • rightConv F (y : AdelicGL2 (𝓞 F) F → ℂ) f
    exact convOp_smul F f a y

theorem convEnd_apply (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hYc : ∀ y ∈ Y, Continuous y)
    (hYs : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsLevelSphericalOfType F tys U f →
      ∀ y ∈ Y, rightConv F y f ∈ Y)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hfl : IsLevelSphericalOfType F tys U f) (y : Y) :
    ((convEnd F tys U Y hYc hYs f hf hfl y : Y) : AdelicGL2 (𝓞 F) F → ℂ) = rightConv F (y : AdelicGL2 (𝓞 F) F → ℂ) f :=
  rfl

def evalEnd (F : Type) [Field F] [NumberField F] (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) :
    (Y →ₗ[ℂ] Y) →ₗ[ℂ] (↥Y × AdelicGL2 (𝓞 F) F → ℂ) where
  toFun S p := ((S p.1 : Y) : AdelicGL2 (𝓞 F) F → ℂ) p.2
  map_add' S S' := rfl
  map_smul' a S := rfl

theorem exists_finset_sum_rightConv_eq
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys)
    (hYs : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsLevelSphericalOfType F tys U f →
      ∀ y ∈ Y, rightConv F y f ∈ Y) :
    ∃ (s : Finset ℕ) (c : ℕ → ℂ) (f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ i, IsFactorizableTestFn F (f i) ∧ IsLevelSphericalOfType F tys U (f i)) ∧ s.Nonempty ∧
      ∀ y ∈ Y, (∑ i ∈ s, c i • rightConv F y (f i)) = y := by
  classical
  haveI := hY
  obtain ⟨f, hf, htend⟩ :=
    AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
      F U hU O hO hUO tys 0 Y hY hYc hYU hYt

  let Φ : ℕ → (↥Y × AdelicGL2 (𝓞 F) F → ℂ) := fun n =>
    evalEnd F Y (convEnd F tys U Y hYc hYs (f n) (hf n).1 (hf n).2.1)
  have hΦ : ∀ n (p : ↥Y × AdelicGL2 (𝓞 F) F), Φ n p = rightConv F (p.1 : AdelicGL2 (𝓞 F) F → ℂ) (f n) p.2 :=
    fun n p => rfl
  haveI : Module.Finite ℂ (↥Y →ₗ[ℂ] ↥Y) := Module.Finite.linearMap ℂ ℂ Y Y
  haveI : FiniteDimensional ℂ (LinearMap.range (evalEnd F Y)) := Module.Finite.range (evalEnd F Y)
  have hΦmem : ∀ n, Φ n ∈ LinearMap.range (evalEnd F Y) := fun n => LinearMap.mem_range_self _ _
  have hlim : ∀ p : ↥Y × AdelicGL2 (𝓞 F) F,
      Filter.Tendsto (fun n => Φ n p) Filter.atTop (nhds ((p.1 : AdelicGL2 (𝓞 F) F → ℂ) p.2)) := by
    intro p
    have h := htend p.1 p.1.2 p.2
    refine (Filter.tendsto_congr (fun n => ?_)).2 h
    exact hΦ n p
  have hmem := mem_span_range_of_tendsto (LinearMap.range (evalEnd F Y)) Φ hΦmem
    (fun p => (p.1 : AdelicGL2 (𝓞 F) F → ℂ) p.2) hlim
  obtain ⟨cfs, hcfs⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hmem
  refine ⟨insert 0 cfs.support, fun i => cfs i, f, fun i => ⟨(hf i).1, (hf i).2.1⟩, Finset.insert_nonempty _ _, ?_⟩
  intro y hy
  have hsum0 : (∑ i ∈ insert 0 cfs.support, cfs i • rightConv F y (f i))
      = ∑ i ∈ cfs.support, cfs i • rightConv F y (f i) := by
    by_cases h0 : (0 : ℕ) ∈ cfs.support
    · rw [Finset.insert_eq_of_mem h0]
    · rw [Finset.sum_insert h0, Finsupp.notMem_support_iff.1 h0, zero_smul, zero_add]
  rw [hsum0]
  funext g
  have key := congrFun hcfs (⟨y, hy⟩, g)
  rw [Finsupp.sum, Finset.sum_apply] at key
  simp only [Pi.smul_apply, hΦ, smul_eq_mul] at key
  rw [Finset.sum_apply]
  simpa only [Pi.smul_apply, smul_eq_mul] using key

end Ws47.REPRO

open Ws47.REPRO in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys)
    (hYs : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsLevelSphericalOfType F tys U f →
      ∀ y ∈ Y, rightConv F y f ∈ Y) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ,
      IsFactorizableTestFn F f ∧ IsLevelSphericalOfType F tys U f ∧ IsArchBiFinite F tys f ∧
        ∀ y ∈ Y, rightConv F y f = y := by
  classical
  obtain ⟨s, c, f, hf, hs, hsum⟩ := exists_finset_sum_rightConv_eq F U hU O hO hUO tys Y hY hYc hYU hYt hYs
  refine ⟨∑ i ∈ s, c i • f i, ?_, ?_, ?_, ?_⟩
  · exact (lincomb_levelSpherical F U hU O hO hUO tys _ c f (fun i _ => hf i) hs).1
  · exact (lincomb_levelSpherical F U hU O hO hUO tys _ c f (fun i _ => hf i) hs).2.1
  · exact (lincomb_levelSpherical F U hU O hO hUO tys _ c f (fun i _ => hf i) hs).2.2
  · intro y hy
    rw [rightConv_finset_sum_smul F _ c f (fun i _ => (hf i).1) y (hYc y hy)]
    exact hsum y hy

end S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact (solution)
