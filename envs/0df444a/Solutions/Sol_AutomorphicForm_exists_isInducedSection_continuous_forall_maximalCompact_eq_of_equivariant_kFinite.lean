-- Prove2me | solution 1 for AutomorphicForm.exists_isInducedSection_continuous_forall_maximalCompact_eq_of_equivariant_kFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3ff7df11-f161-5b8f-9d05-34168c2d9abc

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isInducedSection_continuous_forall_maximalCompact_eq_of_equivariant_kFinite
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open AutomorphicForm.WindowedSiegel

noncomputable section

namespace IwExtC2

variable (F : Type) [Field F] [NumberField F]

def bOf (x : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  Classical.choose (AutomorphicForm.exists_mem_adelicBorel_mul_eq F x)

def kOf (x : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  Classical.choose (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq F x))

theorem bOf_mem (x : AdelicGL2 (𝓞 F) F) : bOf F x ∈ adelicBorel (𝓞 F) F :=
  (Classical.choose_spec (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq F x))).1

theorem kOf_mem (x : AdelicGL2 (𝓞 F) F) : kOf F x ∈ adelicMaximalCompact F :=
  AutomorphicForm.mem_adelicMaximalCompact_iff.mpr
    ⟨(Classical.choose_spec (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq F x))).2.1,
     (Classical.choose_spec (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq F x))).2.2.1⟩

theorem bOf_mul_kOf (x : AdelicGL2 (𝓞 F) F) : bOf F x * kOf F x = x :=
  (Classical.choose_spec (Classical.choose_spec (AutomorphicForm.exists_mem_adelicBorel_mul_eq F x))).2.2.2.symm

section Ext

variable (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
  (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)

def eta (b : ↥(adelicBorel (𝓞 F) F)) : ℂ :=
  ((etaFst μ α hα s (borelDiagFst b) : ℂˣ) : ℂ) * ((etaSnd ν α hα s (borelDiagSnd b) : ℂˣ) : ℂ)

theorem eta_mul (b c : ↥(adelicBorel (𝓞 F) F)) :
    eta F α hα s μ ν (b * c) = eta F α hα s μ ν b * eta F α hα s μ ν c := by
  unfold eta
  rw [map_mul, map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul]
  ring

theorem eta_one : eta F α hα s μ ν 1 = 1 := by
  unfold eta
  rw [map_one, map_one, map_one, map_one, Units.val_one, one_mul]

def Equivariant (u : ↥(adelicMaximalCompact F) → ℂ) : Prop :=
  ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (hbK : b ∈ adelicMaximalCompact F)
    (k : ↥(adelicMaximalCompact F)),
    u (⟨b, hbK⟩ * k) = eta F α hα s μ ν ⟨b, hb⟩ * u k

private def _root_.IwExtC2.ext (u : ↥(adelicMaximalCompact F) → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  eta F α hα s μ ν ⟨bOf F g, bOf_mem F g⟩ * u ⟨kOf F g, kOf_mem F g⟩

p2m_export "IwExtC2" "ext"
theorem ext_apply (u : ↥(adelicMaximalCompact F) → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    ext F α hα s μ ν u g = eta F α hα s μ ν ⟨bOf F g, bOf_mem F g⟩ * u ⟨kOf F g, kOf_mem F g⟩ := rfl

def extLin : (↥(adelicMaximalCompact F) → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun := ext F α hα s μ ν
  map_add' u u' := by funext g; simp only [ext_apply, Pi.add_apply]; ring
  map_smul' c u := by funext g; simp only [ext_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem extLin_apply (u : ↥(adelicMaximalCompact F) → ℂ) : extLin F α hα s μ ν u = ext F α hα s μ ν u := rfl

theorem ext_eq (u : ↥(adelicMaximalCompact F) → ℂ) (hu : Equivariant F α hα s μ ν u)
    (g b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (k : ↥(adelicMaximalCompact F))
    (e : g = b * (k : AdelicGL2 (𝓞 F) F)) :
    ext F α hα s μ ν u g = eta F α hα s μ ν ⟨b, hb⟩ * u k := by
  rw [ext_apply]
  have hb₀ : bOf F g ∈ adelicBorel (𝓞 F) F := bOf_mem F g
  have hk₀ : kOf F g ∈ adelicMaximalCompact F := kOf_mem F g
  have e₀ : bOf F g * kOf F g = g := bOf_mul_kOf F g
  set m : AdelicGL2 (𝓞 F) F := b⁻¹ * bOf F g with hm
  have hmB : m ∈ adelicBorel (𝓞 F) F := mul_mem (inv_mem hb) hb₀
  have hmk : m = (k : AdelicGL2 (𝓞 F) F) * (kOf F g)⁻¹ := by
    rw [hm, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, e₀]
    exact e
  have hmK : m ∈ adelicMaximalCompact F := by
    rw [hmk]; exact mul_mem k.2 (inv_mem hk₀)
  have hb₀m : bOf F g = b * m := by rw [hm, mul_inv_cancel_left]
  have hkm : (⟨kOf F g, hk₀⟩ : ↥(adelicMaximalCompact F)) = ⟨m⁻¹, inv_mem hmK⟩ * k := by
    apply Subtype.ext
    show kOf F g = m⁻¹ * (k : AdelicGL2 (𝓞 F) F)
    rw [hmk, mul_inv_rev, inv_inv, inv_mul_cancel_right]
  have h1 : eta F α hα s μ ν ⟨bOf F g, hb₀⟩ = eta F α hα s μ ν ⟨b, hb⟩ * eta F α hα s μ ν ⟨m, hmB⟩ := by
    have h' : (⟨bOf F g, hb₀⟩ : ↥(adelicBorel (𝓞 F) F)) = ⟨b, hb⟩ * ⟨m, hmB⟩ := Subtype.ext hb₀m
    rw [h', eta_mul]
  have hmiB : m⁻¹ ∈ adelicBorel (𝓞 F) F := inv_mem hmB
  have h2 : u ⟨kOf F g, hk₀⟩ = eta F α hα s μ ν ⟨m⁻¹, hmiB⟩ * u k := by
    rw [hkm]
    exact hu m⁻¹ hmiB (inv_mem hmK) k
  have h3 : eta F α hα s μ ν ⟨m, hmB⟩ * eta F α hα s μ ν ⟨m⁻¹, hmiB⟩ = 1 := by
    have h' : (⟨m, hmB⟩ : ↥(adelicBorel (𝓞 F) F)) * ⟨m⁻¹, hmiB⟩ = 1 := Subtype.ext (mul_inv_cancel m)
    rw [← eta_mul, h', eta_one]
  rw [h1, h2]
  calc eta F α hα s μ ν ⟨b, hb⟩ * eta F α hα s μ ν ⟨m, hmB⟩ * (eta F α hα s μ ν ⟨m⁻¹, hmiB⟩ * u k)
      = eta F α hα s μ ν ⟨b, hb⟩ * (eta F α hα s μ ν ⟨m, hmB⟩ * eta F α hα s μ ν ⟨m⁻¹, hmiB⟩) * u k := by ring
    _ = eta F α hα s μ ν ⟨b, hb⟩ * u k := by rw [h3, mul_one]

end Ext

end IwExtC2

end

section

open IwExtC2 AutomorphicForm.WindowedSiegel FLT.SmoothVectors
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (s : ℂ)
      (u : ↥(adelicMaximalCompact F) → ℂ) (_huc : Continuous u)
      (_huW : ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => u (k * k₀)) ∈ W)
      (_husm : ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u' : ↥(adelicMaximalCompact F)),
        (u' : AdelicGL2 (𝓞 F) F) ∈ V → (u' : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          u (k * u') = u k)
      (_hueq : ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (hbK : b ∈ adelicMaximalCompact F)
        (k : ↥(adelicMaximalCompact F)),
        u (⟨b, hbK⟩ * k) =
          ((etaFst μ α hα s (borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ) * ((etaSnd ν α hα s (borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ) *
            u k),
    ∃ φ₀ : AdelicGL2 (𝓞 F) F → ℂ,
      IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ₀ ∧
      IsArchKFinite F φ₀ ∧ IsKfSmooth F φ₀ ∧ Continuous φ₀ ∧
      ∀ k : ↥(adelicMaximalCompact F), φ₀ (k : AdelicGL2 (𝓞 F) F) = u k := by
  intro α hα μ ν hμc hνc s u huc huW husm hueq
  classical
  have hαv : ∀ t, ((α t : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm F t := fun t => rfl
  have hueq' : IwExtC2.Equivariant F α hα s μ ν u := fun b hb hbK k => by
    rw [hueq b hb hbK k]; rfl

  have hind : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (IwExtC2.ext F α hα s μ ν u) := by
    intro b hb g
    have e : b * g = (b * bOf F g) * ((⟨kOf F g, kOf_mem F g⟩ : ↥(adelicMaximalCompact F)) : AdelicGL2 (𝓞 F) F) := by
      rw [mul_assoc, bOf_mul_kOf]
    rw [ext_eq F α hα s μ ν u hueq' (b * g) (b * bOf F g) (mul_mem hb (bOf_mem F g)) _ e]
    have hsplit : (⟨b * bOf F g, mul_mem hb (bOf_mem F g)⟩ : ↥(adelicBorel (𝓞 F) F)) = ⟨b, hb⟩ * ⟨bOf F g, bOf_mem F g⟩ := rfl
    rw [hsplit, eta_mul, ext_apply]
    simp only [IwExtC2.eta]
    ring

  have hK : ∀ k : ↥(adelicMaximalCompact F), IwExtC2.ext F α hα s μ ν u (k : AdelicGL2 (𝓞 F) F) = u k := by
    intro k
    have e : (k : AdelicGL2 (𝓞 F) F) = 1 * (k : AdelicGL2 (𝓞 F) F) := (one_mul _).symm
    rw [ext_eq F α hα s μ ν u hueq' _ 1 (one_mem _) k e]
    show IwExtC2.eta F α hα s μ ν 1 * u k = u k
    rw [eta_one, one_mul]
  refine ⟨IwExtC2.ext F α hα s μ ν u, hind, ?_, ?_, ?_, hK⟩
  ·
    intro w
    obtain ⟨W, hWfd, hW⟩ := huW
    haveI : FiniteDimensional ℂ W := hWfd
    let bW := Module.finBasis ℂ W
    refine ⟨Finset.univ.image (fun i => extLin F α hα s μ ν ((bW i : W) : ↥(adelicMaximalCompact F) → ℂ)), ?_⟩
    intro kk hkk
    obtain ⟨kw, hkw, rfl⟩ := Subgroup.mem_map.mp hkk
    have hkk1 : glFin (𝓞 F) F (adelicArchGLInclAt F w kw) = 1 := glFin_adelicArchGLIncl F _
    have hkkK : adelicArchGLInclAt F w kw ∈ adelicMaximalCompact F := by
      refine AutomorphicForm.mem_adelicMaximalCompact_iff.mpr ⟨by rw [hkk1]; exact one_mem _, fun v => ?_⟩
      change IsRowIsometry (archComponent F v (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w kw))))
      rw [glArch_adelicArchGLIncl]
      by_cases hvw : v = w
      · subst hvw
        rw [archComponent_archGLIncl_self]
        exact hkw
      · rw [archComponent_archGLIncl_of_ne F hvw]
        exact isRowIsometry_one
    set k₀ : ↥(adelicMaximalCompact F) := ⟨adelicArchGLInclAt F w kw, hkkK⟩ with hk₀
    have key : (fun x => IwExtC2.ext F α hα s μ ν u (x * adelicArchGLInclAt F w kw))
        = IwExtC2.ext F α hα s μ ν (fun k => u (k * k₀)) := by
      funext x
      have e : x * adelicArchGLInclAt F w kw =
          bOf F x * ((⟨kOf F x, kOf_mem F x⟩ * k₀ : ↥(adelicMaximalCompact F)) : AdelicGL2 (𝓞 F) F) := by
        rw [Subgroup.coe_mul, ← mul_assoc, bOf_mul_kOf]
      rw [ext_eq F α hα s μ ν u hueq' _ _ (bOf_mem F x) _ e, ext_apply]
    rw [key, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hmem : (fun k => u (k * k₀)) ∈ W := hW k₀
    have hspan : (fun k => u (k * k₀)) ∈
        Submodule.span ℂ (Set.range (fun i => ((bW i : W) : ↥(adelicMaximalCompact F) → ℂ))) := by
      have h := bW.mem_span (⟨_, hmem⟩ : W)
      have hmap := Submodule.mem_map_of_mem (f := W.subtype) h
      rw [Submodule.map_span, ← Set.range_comp] at hmap
      exact hmap
    have hcomp : (Set.range fun i => extLin F α hα s μ ν ((bW i : W) : ↥(adelicMaximalCompact F) → ℂ))
        = extLin F α hα s μ ν '' Set.range (fun i => ((bW i : W) : ↥(adelicMaximalCompact F) → ℂ)) := by
      rw [← Set.range_comp]; rfl
    rw [hcomp, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hspan
  ·
    obtain ⟨V, hV, hVu⟩ := husm
    rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer]
    apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    have hKo : IsOpen {g : AdelicGL2 (𝓞 F) F | glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F} :=
      (isOpen_finiteLevelZero (R := 𝓞 F) (K := F) (N := ⊤) (by simp)).preimage (continuous_glFin (𝓞 F) F)
    have hN : ((Subtype.val : ↥(finiteAdelicGL2Subgroup F) → AdelicGL2 (𝓞 F) F) ⁻¹'
        (V ∩ {g : AdelicGL2 (𝓞 F) F | glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F})) ∈
        𝓝 (1 : ↥(finiteAdelicGL2Subgroup F)) := by
      apply continuous_subtype_val.continuousAt.preimage_mem_nhds
      refine Filter.inter_mem ?_ (hKo.mem_nhds ?_)
      · exact hV
      · show glFin (𝓞 F) F (1 : AdelicGL2 (𝓞 F) F) ∈ finiteIntegralGL2 (𝓞 F) F
        rw [map_one]; exact one_mem _
    refine Filter.mem_of_superset hN ?_
    rintro ⟨v, hvf⟩ ⟨hvV, hvint⟩
    have hvK : v ∈ adelicMaximalCompact F := by
      refine AutomorphicForm.mem_adelicMaximalCompact_iff.mpr ⟨hvint, fun w => ?_⟩
      rw [(mem_finiteAdelicGL2Subgroup_iff F v).mp hvf, map_one]
      exact isRowIsometry_one
    show (⟨v, hvf⟩ : ↥(finiteAdelicGL2Subgroup F)) ∈ MulAction.stabilizer _ _
    rw [MulAction.mem_stabilizer_iff]
    apply RightTranslationFn.ext
    intro x
    rw [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk]
    show IwExtC2.ext F α hα s μ ν u (x * v) = IwExtC2.ext F α hα s μ ν u x
    have e : x * v = bOf F x * ((⟨kOf F x, kOf_mem F x⟩ * ⟨v, hvK⟩ : ↥(adelicMaximalCompact F)) : AdelicGL2 (𝓞 F) F) := by
      rw [Subgroup.coe_mul, ← mul_assoc, bOf_mul_kOf]
    rw [ext_eq F α hα s μ ν u hueq' _ _ (bOf_mem F x) _ e, hVu ⟨kOf F x, kOf_mem F x⟩ ⟨v, hvK⟩ hvV hvf, ext_apply]
  ·
    have hαc : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ((α t : ℝˣ) : ℝ) := by
      simp_rw [hαv]; exact NumberField.TateGlobal.continuous_ideleNorm F
    have hχ₁c : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ((etaFst μ α hα s t : ℂˣ) : ℂ) := by
      have e : (fun t : (AdeleRing (𝓞 F) F)ˣ => ((etaFst μ α hα s t : ℂˣ) : ℂ))
          = fun t => ((μ t : ℂˣ) : ℂ) * ((((α t : ℝˣ) : ℝ)) : ℂ) ^ (s + 1 / 2) := by
        funext t; rw [etaFst, MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val]
      rw [e]
      exact hμc.mul ((Complex.continuous_ofReal.comp hαc).cpow continuous_const
        fun t => Complex.ofReal_mem_slitPlane.mpr (hα _))
    have hχ₂c : Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ((etaSnd ν α hα s t : ℂˣ) : ℂ) := by
      have e : (fun t : (AdeleRing (𝓞 F) F)ˣ => ((etaSnd ν α hα s t : ℂˣ) : ℂ))
          = fun t => ((ν t : ℂˣ) : ℂ) * ((((α t : ℝˣ) : ℝ)) : ℂ) ^ (-(s + 1 / 2)) := by
        funext t; rw [etaSnd, MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val]
      rw [e]
      exact hνc.mul ((Complex.continuous_ofReal.comp hαc).cpow continuous_const
        fun t => Complex.ofReal_mem_slitPlane.mpr (hα _))
    have hKc : ContinuousOn (fun p : Unit × AdelicGL2 (𝓞 F) F => IwExtC2.ext F α hα s μ ν u p.2)
        (Set.univ ×ˢ {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) := by
      have hset : {k : AdelicGL2 (𝓞 F) F | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}
          = ((adelicMaximalCompact F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by
        ext k; rw [Set.mem_setOf_eq, SetLike.mem_coe, AutomorphicForm.mem_adelicMaximalCompact_iff]
      rw [hset]
      have h1 : ContinuousOn (IwExtC2.ext F α hα s μ ν u) ((adelicMaximalCompact F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by
        rw [continuousOn_iff_continuous_restrict]
        have hres : ((adelicMaximalCompact F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)).domRestrict (IwExtC2.ext F α hα s μ ν u) = u := by
          funext k; exact hK k
        rw [hres]; exact huc
      exact h1.comp continuous_snd.continuousOn (fun p hp => (Set.mem_prod.mp hp).2)
    have hc : ContinuousOn (fun p : Unit × AdelicGL2 (𝓞 F) F => IwExtC2.ext F α hα s μ ν u p.2)
        (Set.univ ×ˢ Set.univ) :=
      AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact F (X := Unit)
        Set.univ isOpen_univ
        (fun _ => etaFst μ α hα s) (fun _ => etaSnd ν α hα s)
        ((hχ₁c.comp continuous_snd).continuousOn) ((hχ₂c.comp continuous_snd).continuousOn)
        (fun _ => IwExtC2.ext F α hα s μ ν u) (fun _ _ => hind) hKc
    rw [Set.univ_prod_univ, continuousOn_univ] at hc
    have h2 : Continuous fun g : AdelicGL2 (𝓞 F) F => (((), g) : Unit × AdelicGL2 (𝓞 F) F) :=
      continuous_const.prodMk continuous_id
    have h3 := hc.comp h2
    exact h3

end

end S_AutomorphicForm_exists_isInducedSection_continuous_forall_maximalCompact_eq_of_equivariant_kFinite
end P2MW
export P2MW.S_AutomorphicForm_exists_isInducedSection_continuous_forall_maximalCompact_eq_of_equivariant_kFinite (solution)
