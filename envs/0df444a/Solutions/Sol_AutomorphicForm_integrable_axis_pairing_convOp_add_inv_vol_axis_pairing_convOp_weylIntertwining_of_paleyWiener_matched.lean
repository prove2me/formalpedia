-- Prove2me | solution 1 for AutomorphicForm.integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/bbf02c48-6740-5507-9299-2e659444605a

import Theorems.Thm_AutomorphicForm_exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm
open scoped Pointwise

noncomputable section

namespace Ws31
namespace INT

variable {K : Type} [Field K] [NumberField K]

theorem continuous_rightConv_param {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P]
    [FirstCountableTopology P]
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (φ : P → AdelicGL2 (𝓞 K) K → ℂ)
    (hφjc : Continuous (fun p : P × AdelicGL2 (𝓞 K) K => φ p.1 p.2)) :
    Continuous (fun p : P × AdelicGL2 (𝓞 K) K => rightConv K (φ p.1) f p.2) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  have e : (fun p : P × AdelicGL2 (𝓞 K) K => rightConv K (φ p.1) f p.2)
      = fun p : P × AdelicGL2 (𝓞 K) K => ∫ a in tsupport f, φ p.1 (p.2 * a) * f a ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    funext p
    rw [rightConv_apply]
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => by
      rw [image_eq_zero_of_notMem_tsupport ha, mul_zero]
  rw [e]
  refine continuous_parametric_integral_of_continuous
    (f := fun (p : P × AdelicGL2 (𝓞 K) K) (a : AdelicGL2 (𝓞 K) K) => φ p.1 (p.2 * a) * f a) ?_ hfc
  show Continuous fun q : (P × AdelicGL2 (𝓞 K) K) × AdelicGL2 (𝓞 K) K => φ q.1.1 (q.1.2 * q.2) * f q.2
  exact (hφjc.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).mul continuous_snd))).mul (hf.comp continuous_snd)

theorem norm_rightConv_le (u f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : AdelicGL2 (𝓞 K) K) (M : ℝ) (hM : 0 ≤ M) (hu : ∀ y ∈ tsupport f, ‖u (x * y)‖ ≤ M) :
    ‖rightConv K u f x‖ ≤ M * ∫ y, ‖f y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  rw [rightConv_apply, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hf.integrable_of_hasCompactSupport hfc).norm.const_mul M)
    (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ tsupport f
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hu y hy) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hy]; simp

noncomputable def bPart (K : Type) [Field K] [NumberField K] (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K :=
  (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose
noncomputable def kPart (K : Type) [Field K] [NumberField K] (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K :=
  (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose
theorem bPart_mem (g : AdelicGL2 (𝓞 K) K) : bPart K g ∈ adelicBorel (𝓞 K) K :=
  (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose_spec.1
theorem kPart_mem (g : AdelicGL2 (𝓞 K) K) : kPart K g ∈ adelicMaximalCompact K :=
  ⟨(AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose_spec.2.1,
   (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose_spec.2.2.1⟩
theorem bPart_mul_kPart (g : AdelicGL2 (𝓞 K) K) : bPart K g * kPart K g = g :=
  (AutomorphicForm.exists_mem_adelicBorel_mul_eq K g).choose_spec.choose_spec.2.2.2.symm

theorem norm_etaPair (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ) (hν : IsUnitaryChar (𝓞 K) K ν)
    (s : ℂ) (hs : s.re = 0) (u v : (AdeleRing (𝓞 K) K)ˣ) :
    ‖((etaFst μ α hα s u : ℂˣ) : ℂ)‖ * ‖((etaSnd ν α hα s v : ℂˣ) : ℂ)‖
      = ((α u : ℝˣ) : ℝ) ^ (1 / 2 : ℝ) * ((α v : ℝˣ) : ℝ) ^ (-(1 / 2) : ℝ) := by
  rw [etaFst_apply, etaSnd_apply, Units.val_mul, Units.val_mul, norm_mul, norm_mul, hμ u, hν v, one_mul,
    one_mul, cpowChar_apply_val, cpowChar_apply_val, Complex.norm_cpow_eq_rpow_re_of_pos (hα u),
    Complex.norm_cpow_eq_rpow_re_of_pos (hα v)]
  congr 2
  · simp [hs]
  · simp [hs]

end Ws31.INT

end

open Ws31.INT in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (φf ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (Oψ : ιP → Set ℂ) (Eψ Nψ : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ : ∀ i : ιP,
      IsOpen (Oψ i) ∧ IsPreconnected (Oψ i) ∧ {s : ℂ | s.re = 0} ⊆ (Oψ i) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (Oψ i) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ i s g) (Oψ i)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ i s g) (Oψ i)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ i s g = ψf i s g + ∑' ξ : K, ψf i s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ i s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf i s) g))
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hNψ : ∀ (i : ιP), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (_hNE : ∀ (e : ιE) (j : Fin (nE e)), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (i : ιP),
    Integrable (fun t : ℝ =>
      (∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by
  intro αm hαm ιE _ μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμνE _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu
    _hφEflat _hφElev _hφEty _hφEon _hφEspan OE EE NE _hEE f hf hfc _hfF _hfB _hfA
    ιP _ μP νP _hμ _hν _hμic _hνic _hμc _hμν rP _hr _hdist φf ψf _hφf _hψf _hφjc _hψjc _hφhol _hψhol _hψK _hψsm
    _hψKu _hνc _hφdec _hψdec Oψ Eψ Nψ _hEψ em τ _hem _hNψ _hNE i
  classical
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set vol : ℝ := ((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal with hvol
  set If : ℝ := ∫ y, ‖f y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hIf
  have hIf0 : 0 ≤ If := integral_nonneg fun _ => norm_nonneg _

  have hKc : IsCompact ((adelicMaximalCompact K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) :=
    AutomorphicForm.isCompact_adelicMaximalCompact K
  set C₁ : Set (AdelicGL2 (𝓞 K) K) := ((adelicMaximalCompact K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)) * tsupport f with hC₁
  have hC₁c : IsCompact C₁ := hKc.mul hfc
  have hmemC₁ : ∀ (k : adelicMaximalCompact K), ∀ y ∈ tsupport f, (k : AdelicGL2 (𝓞 K) K) * y ∈ C₁ :=
    fun k y hy => Set.mul_mem_mul k.2 hy

  obtain ⟨mψ, hmψi, ⟨Bψ, hBψ⟩, hmψ⟩ := _hψdec i 0 0 C₁ hC₁c
  obtain ⟨A, n, hAn⟩ := _hNψ (rP i)
  obtain ⟨mφ0, hmφ0i, ⟨Bφ0, hBφ0⟩, hmφ0⟩ := _hφdec i 0 0 _ hKc
  obtain ⟨mφn, hmφni, ⟨Bφn, hBφn⟩, hmφn⟩ := _hφdec i n 0 _ hKc
  have hmψ' : ∀ (t : ℝ), ∀ g ∈ C₁, ‖ψf i ((t : ℂ) * Complex.I) g‖ ≤ mψ t := by
    intro t g hg; have := hmψ 0 (by simp) t g hg; simpa using this
  have hmφ0' : ∀ (t : ℝ) (k : adelicMaximalCompact K), ‖φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ mφ0 t := by
    intro t k; have := hmφ0 0 (by simp) t (k : AdelicGL2 (𝓞 K) K) k.2; simpa using this
  have hmφn' : ∀ (t : ℝ) (k : adelicMaximalCompact K),
      (1 + |t|) ^ n * ‖φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ mφn t := by
    intro t k; have := hmφn 0 (by simp) t (k : AdelicGL2 (𝓞 K) K) k.2; simpa using this

  have hψc : Continuous (fun p : ℝ × AdelicGL2 (𝓞 K) K => ψf i ((p.1 : ℂ) * Complex.I) p.2) :=
    (_hψjc i).comp (((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hφc : Continuous (fun p : ℝ × AdelicGL2 (𝓞 K) K => φf i ((p.1 : ℂ) * Complex.I) p.2) :=
    (_hφjc i).comp (((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  obtain ⟨hO, hOc, hax, hhalf, hEan, hNan, hEc, hNc, hEeq, hNeq⟩ := _hEψ (rP i)
  have hNc' : Continuous (fun p : ℝ × AdelicGL2 (𝓞 K) K => Nψ (rP i) (-((p.1 : ℂ) * Complex.I)) p.2) := by
    have hg : Continuous (fun p : ℝ × AdelicGL2 (𝓞 K) K => ((-((p.1 : ℂ) * Complex.I)), p.2)) :=
      (((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const).neg).prodMk continuous_snd
    exact hNc.comp_continuous hg fun p => ⟨hax (by simp), Set.mem_univ _⟩
  have hR1c := continuous_rightConv_param f hf hfc (fun (t : ℝ) g => ψf i ((t : ℂ) * Complex.I) g) hψc
  have hR2c := continuous_rightConv_param f hf hfc (fun (t : ℝ) g => Nψ (rP i) (-((t : ℂ) * Complex.I)) g) hNc'

  have hI1c : Continuous (fun p : ℝ × adelicMaximalCompact K =>
      φf i ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K) *
        conj (convOp K f (ψf i ((p.1 : ℂ) * Complex.I)) (p.2 : AdelicGL2 (𝓞 K) K))) := by
    have hφ' : Continuous (fun p : ℝ × adelicMaximalCompact K => φf i ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K)) :=
      hφc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have hR' : Continuous (fun p : ℝ × adelicMaximalCompact K => rightConv K (ψf i ((p.1 : ℂ) * Complex.I)) f (p.2 : AdelicGL2 (𝓞 K) K)) :=
      hR1c.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact hφ'.mul (Complex.continuous_conj.comp hR')
  have hI2c : Continuous (fun p : ℝ × adelicMaximalCompact K =>
      φf i ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K) *
        conj (convOp K f (Nψ (rP i) (-((p.1 : ℂ) * Complex.I))) (p.2 : AdelicGL2 (𝓞 K) K))) := by
    have hφ' : Continuous (fun p : ℝ × adelicMaximalCompact K => φf i ((p.1 : ℂ) * Complex.I) (p.2 : AdelicGL2 (𝓞 K) K)) :=
      hφc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have hR' : Continuous (fun p : ℝ × adelicMaximalCompact K => rightConv K (Nψ (rP i) (-((p.1 : ℂ) * Complex.I))) f (p.2 : AdelicGL2 (𝓞 K) K)) :=
      hR2c.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact hφ'.mul (Complex.continuous_conj.comp hR')
  have hT1c : Continuous (fun t : ℝ => ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
      conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by
    have := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K)
      (f := fun (t : ℝ) (k : adelicMaximalCompact K) => φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K))) hI1c isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hT2c : Continuous (fun t : ℝ => ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
      conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by
    have := continuous_parametric_integral_of_continuous (μ := maximalCompactHaar K)
      (f := fun (t : ℝ) (k : adelicMaximalCompact K) => φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K))) hI2c isCompact_univ
    simpa only [Measure.restrict_univ] using this

  have hR1b : ∀ (t : ℝ) (k : adelicMaximalCompact K),
      ‖convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)‖ ≤ max (mψ t) 0 * If := by
    intro t k
    exact norm_rightConv_le _ f hf hfc _ _ (le_max_right _ _) fun y hy => (hmψ' t _ (hmemC₁ k y hy)).trans (le_max_left _ _)
  have hmφ00 : ∀ t, 0 ≤ mφ0 t := fun t => (norm_nonneg _).trans (hmφ0' t ⟨1, one_mem _⟩)
  have hT1b : ∀ t : ℝ, ‖∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
      conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖
      ≤ mφ0 t * (max Bψ 0 * If) := by
    intro t
    have h1 : ∀ k : adelicMaximalCompact K, ‖φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K))‖ ≤ mφ0 t * (max Bψ 0 * If) := by
      intro k
      rw [norm_mul, Complex.norm_conj]
      refine mul_le_mul (hmφ0' t k) ((hR1b t k).trans ?_) (norm_nonneg _) (hmφ00 t)
      exact mul_le_mul_of_nonneg_right (max_le_max (hBψ t) le_rfl) hIf0
    have := norm_integral_le_of_norm_le_const (μ := maximalCompactHaar K) (Filter.Eventually.of_forall h1)
    simpa using this
  have hT1i : Integrable (fun t : ℝ => ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
      conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) :=
    Integrable.mono' (hmφ0i.mul_const _) hT1c.aestronglyMeasurable (Filter.Eventually.of_forall hT1b)

  by_cases hv : vol = 0
  · have : (fun t : ℝ =>
        (∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
        = fun t : ℝ => ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
      funext t
      rw [show ((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal = vol from rfl, hv]
      simp
    rw [this]
    exact hT1i

  obtain ⟨N', -, hlev⟩ := AutomorphicForm.exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable
    K (ψf (rP i)) (_hψsm (rP i)) (_hψhol (rP i))
  have hsec : ∀ t : ℝ, IsInducedSection (𝓞 K) K (etaFst (νP (rP i)) αm hαm (-(((-t : ℝ) : ℂ) * Complex.I)))
      (etaSnd (μP (rP i)) αm hαm (-(((-t : ℝ) : ℂ) * Complex.I)))
      (fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * Nψ (rP i) (((-t : ℝ) : ℂ) * Complex.I) g) :=
    fun t => (AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
      K hαm (μP (rP i)) (νP (rP i)) (_hμ _) (_hν _) (_hμic _) (_hνic _) (_hμc _) (_hνc _) N' (ψf (rP i)) (_hψf _)
      (_hψK _) (_hψsm _) (_hψjc _) (_hψhol _) (_hψKu _) hlev (Oψ (rP i)) (Eψ (rP i)) (Nψ (rP i)) (_hEψ (rP i)) (-t)).1

  obtain ⟨hαm', h1u, hH⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow K
  have hH0 := hH hαm 0

  obtain ⟨MH, hMH⟩ := hC₁c.exists_bound_of_continuousOn (f := NumberField.AdelicHeight.adelicHeight K)
    (NumberField.AdelicHeight.continuous_adelicHeight K).continuousOn
  set H1 : ℝ := NumberField.AdelicHeight.adelicHeight K 1 with hH1
  have hH1p : 0 < H1 := NumberField.AdelicHeight.adelicHeight_pos 1
  set Θ : ℝ := (max MH 0) ^ (1 / 2 : ℝ) * H1 ^ (-(1 / 2) : ℝ) with hΘ
  have hΘ0 : 0 ≤ Θ := mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (Real.rpow_nonneg hH1p.le _)

  have hA0 : 0 ≤ A := by
    have := hAn 0 ⟨1, one_mem _⟩
    have h' : (0 : ℝ) ≤ A * (1 + |(0:ℝ)|) ^ n := (norm_nonneg _).trans this
    simpa using h'
  have hNb : ∀ (t : ℝ), ∀ x ∈ C₁, ‖Nψ (rP i) (-((t : ℂ) * Complex.I)) x‖ ≤ Θ * (A * (1 + |t|) ^ n) := by
    intro t x hx
    have ecast : (((-t : ℝ) : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by push_cast; ring

    set b := bPart K x with hbdef
    set k := kPart K x with hkdef
    have hb : b ∈ adelicBorel (𝓞 K) K := bPart_mem x
    have hk : k ∈ adelicMaximalCompact K := kPart_mem x
    have hx' : b * k = x := bPart_mul_kPart x

    have hs1 := hsec t b hb k
    rw [hx'] at hs1
    simp only [ecast] at hs1

    have hre : (-(-((t : ℂ) * Complex.I))).re = 0 := by simp
    have hchar := norm_etaPair αm hαm (νP (rP i)) (μP (rP i)) (_hν _) (_hμ _) _ hre
      (borelDiagFst ⟨b, hb⟩) (borelDiagSnd ⟨b, hb⟩)

    have hs2 := hH0 b hb k
    rw [hx'] at hs2
    have hchar1 := norm_etaPair αm hαm (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) 1 h1u h1u 0 (by simp)
      (borelDiagFst ⟨b, hb⟩) (borelDiagSnd ⟨b, hb⟩)
    have hHk : NumberField.AdelicHeight.adelicHeight K k = H1 := by
      have := NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact K 1 k hk
      rwa [one_mul] at this
    have hnormH : ∀ g : AdelicGL2 (𝓞 K) K, ‖((NumberField.AdelicHeight.adelicHeight K g : ℝ) : ℂ) ^ ((0 : ℂ) + 1 / 2)‖
        = NumberField.AdelicHeight.adelicHeight K g ^ (1 / 2 : ℝ) := by
      intro g
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (NumberField.AdelicHeight.adelicHeight_pos g)]
      norm_num
    have hθ : ((αm (borelDiagFst ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (1 / 2 : ℝ) * ((αm (borelDiagSnd ⟨b, hb⟩) : ℝˣ) : ℝ) ^ (-(1 / 2) : ℝ)
        = NumberField.AdelicHeight.adelicHeight K x ^ (1 / 2 : ℝ) * H1 ^ (-(1 / 2) : ℝ) := by
      have hnormH1 : ‖((H1 : ℝ) : ℂ) ^ ((0 : ℂ) + 1 / 2)‖ = H1 ^ (1 / 2 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hH1p]; norm_num
      have h := congrArg (fun z : ℂ => ‖z‖) hs2
      simp only [norm_mul, hnormH, hHk, hnormH1] at h
      rw [hchar1] at h

      have hH1h : H1 ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hH1p _).ne'
      rw [Real.rpow_neg hH1p.le, eq_mul_inv_iff_mul_eq₀ hH1h]
      exact h.symm
    have hθle : NumberField.AdelicHeight.adelicHeight K x ^ (1 / 2 : ℝ) * H1 ^ (-(1 / 2) : ℝ) ≤ Θ := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hH1p.le _)
      refine Real.rpow_le_rpow (NumberField.AdelicHeight.adelicHeight_pos x).le ?_ (by norm_num)
      exact ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hMH x hx))).trans (le_max_left _ _)

    have hvC : ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)) ≠ 0 := by
      rw [show ((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal = vol from rfl]; exact_mod_cast hv
    have h := congrArg (fun z : ℂ => ‖z‖) hs1
    simp only [norm_mul, norm_inv] at h
    rw [hchar, hθ] at h

    have hvn : ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))‖ ≠ 0 := norm_ne_zero_iff.mpr hvC
    have hNx : ‖Nψ (rP i) (-((t : ℂ) * Complex.I)) x‖
        = (NumberField.AdelicHeight.adelicHeight K x ^ (1 / 2 : ℝ) * H1 ^ (-(1 / 2) : ℝ)) *
          ‖Nψ (rP i) (-((t : ℂ) * Complex.I)) k‖ := by
      field_simp at h
      linear_combination h
    rw [hNx]
    refine mul_le_mul hθle ?_ (norm_nonneg _) hΘ0
    have := hAn (-t) ⟨k, hk⟩
    rw [ecast, abs_neg] at this
    exact this
  have hR2b : ∀ (t : ℝ) (k : adelicMaximalCompact K),
      ‖convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)‖ ≤ (Θ * (A * (1 + |t|) ^ n)) * If := by
    intro t k
    exact norm_rightConv_le _ f hf hfc _ _ (mul_nonneg hΘ0 (mul_nonneg hA0 (by positivity)))
      fun y hy => hNb t _ (hmemC₁ k y hy)
  have hT2b : ∀ t : ℝ, ‖∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
      conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖
      ≤ mφn t * (Θ * A * If) := by
    intro t
    have h1 : ∀ k : adelicMaximalCompact K, ‖φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K))‖ ≤ mφn t * (Θ * A * If) := by
      intro k
      rw [norm_mul, Complex.norm_conj]
      calc ‖φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ * ‖convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)‖
          ≤ ‖φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ * ((Θ * (A * (1 + |t|) ^ n)) * If) :=
            mul_le_mul_of_nonneg_left (hR2b t k) (norm_nonneg _)
        _ = ((1 + |t|) ^ n * ‖φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖) * (Θ * A * If) := by ring
        _ ≤ mφn t * (Θ * A * If) :=
            mul_le_mul_of_nonneg_right (hmφn' t k) (mul_nonneg (mul_nonneg hΘ0 hA0) hIf0)
    have := norm_integral_le_of_norm_le_const (μ := maximalCompactHaar K) (Filter.Eventually.of_forall h1)
    simpa using this
  have hT2i : Integrable (fun t : ℝ => ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
      conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) :=
    Integrable.mono' (hmφni.mul_const _) hT2c.aestronglyMeasurable (Filter.Eventually.of_forall hT2b)
  exact hT1i.add (hT2i.const_mul _)

end S_AutomorphicForm_integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched
end P2MW
export P2MW.S_AutomorphicForm_integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched (solution)
