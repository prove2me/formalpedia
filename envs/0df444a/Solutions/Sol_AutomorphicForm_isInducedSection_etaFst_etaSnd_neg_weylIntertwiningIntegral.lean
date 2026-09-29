-- Prove2me | solution 1 for AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b4bde505-ef3c-5f73-987b-569e1927d92d

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_EisensteinGeneral_Piece_integral_smul_add_mul_addChar_neg_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center"
p2m_attr_erase "simp" "AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ),
    letI := adeleBorel (𝓞 F) F
    IsInducedSection (𝓞 F) F (etaFst ν α hα (-s)) (etaSnd μ α hα (-s))
      (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ) := by
  intro α hα μ ν s φ hφ
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  intro b hb g

  have hb10 : ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := hb
  set t₁ : (AdeleRing (𝓞 F) F)ˣ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with ht₁def
  set t₂ : (AdeleRing (𝓞 F) F)ˣ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) with ht₂def
  have ht₁ : (t₁ : AdeleRing (𝓞 F) F) = (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 := rfl
  have ht₂ : (t₂ : AdeleRing (𝓞 F) F) = (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 := rfl
  set u₀ : AdeleRing (𝓞 F) F := (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 with hu₀
  have hbm : ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₁ : AdeleRing (𝓞 F) F), u₀; 0, (t₂ : AdeleRing (𝓞 F) F)] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [ht₁]
    · simp [hu₀]
    · simp [hb10]
    · simp [ht₂]

  set w : AdelicGL2 (𝓞 F) F := adelicWeyl (𝓞 F) F with hwdef
  have hw : ((w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] := by
    ext i j
    rw [hwdef, adelicWeyl, globalPoints_apply, gl2Weyl_val]
    fin_cases i <;> fin_cases j <;> simp
  have hwinv_eq : w⁻¹ = w := by
    rw [hwdef, adelicWeyl, ← map_inv, gl2Weyl_inv]
  have hwinv : ((w⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] := by
    rw [hwinv_eq, hw]

  set T' : AdelicGL2 (𝓞 F) F :=
    w⁻¹ * (b * unipotentGL2 (-((↑t₁⁻¹ : AdeleRing (𝓞 F) F) * u₀))) * w with hT'def
  have hu₁ : (t₁ : AdeleRing (𝓞 F) F) * (↑t₁⁻¹ : AdeleRing (𝓞 F) F) = 1 := Units.mul_inv t₁
  have hu₂ : (t₂ : AdeleRing (𝓞 F) F) * (↑t₂⁻¹ : AdeleRing (𝓞 F) F) = 1 := Units.mul_inv t₂
  have hT' : ((T' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₂ : AdeleRing (𝓞 F) F), 0; 0, (t₁ : AdeleRing (𝓞 F) F)] := by
    rw [hT'def, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_mul, hwinv, hw, hbm, unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hT'mem : T' ∈ adelicBorel (𝓞 F) F := by
    show ((T' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
    rw [hT']; simp
  have hFst : borelDiagFst (⟨T', hT'mem⟩ : ↥(adelicBorel (𝓞 F) F)) = t₂ := by
    apply Units.ext
    show ((T' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = t₂
    rw [hT']; simp
  have hSnd : borelDiagSnd (⟨T', hT'mem⟩ : ↥(adelicBorel (𝓞 F) F)) = t₁ := by
    apply Units.ext
    show ((T' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = t₁
    rw [hT']; simp

  set a : (AdeleRing (𝓞 F) F)ˣ := t₁⁻¹ * t₂ with hadef
  set u' : AdeleRing (𝓞 F) F := (↑t₂⁻¹ : AdeleRing (𝓞 F) F) * u₀ with hu'
  have hy : ∀ x : AdeleRing (𝓞 F) F,
      (↑t₁⁻¹ : AdeleRing (𝓞 F) F) * (u₀ + x * (t₂ : AdeleRing (𝓞 F) F)) = a • (x + u') := by
    intro x
    rw [Units.smul_def, hadef, Units.val_mul, hu', smul_eq_mul]
    linear_combination (-((↑t₁⁻¹ : AdeleRing (𝓞 F) F) * u₀)) * hu₂

  have hkey : ∀ x : AdeleRing (𝓞 F) F,
      w⁻¹ * unipotentGL2 x * b
        = T' * (w⁻¹ * unipotentGL2 ((↑t₁⁻¹ : AdeleRing (𝓞 F) F) * (u₀ + x * (t₂ : AdeleRing (𝓞 F) F)))) := by
    intro x
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul, hwinv, hbm, hT', unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

  show weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ (b * g)
      = ((etaFst ν α hα (-s) t₁ : ℂˣ) : ℂ) * ((etaSnd μ α hα (-s) t₂ : ℂˣ) : ℂ)
        * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g
  simp only [weylIntertwiningIntegral]
  have hint : ∀ x : AdeleRing (𝓞 F) F,
      φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (b * g))
        = ((etaFst μ α hα s t₂ : ℂˣ) : ℂ) * ((etaSnd ν α hα s t₁ : ℂˣ) : ℂ)
          * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (a • (x + u')) * g) := by
    intro x
    rw [← hwdef, ← mul_assoc, hkey x, mul_assoc, hφ T' hT'mem, hFst, hSnd, hy x]
  simp_rw [hint]
  rw [integral_const_mul]
  have hcv := EisensteinGeneral.Piece.integral_smul_add_mul_addChar_neg_mul_eq F 1
    (fun z => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 z * g)) a u' 0
  simp only [zero_mul, neg_zero, AddChar.one_apply, mul_one] at hcv
  rw [hcv, ← mul_assoc]
  congr 1

  have hαa : (((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ) = (((α a : ℝˣ) : ℝ) : ℂ) := rfl
  rw [hαa]
  set A₁ : ℝ := ((α t₁ : ℝˣ) : ℝ) with hA₁
  set A₂ : ℝ := ((α t₂ : ℝˣ) : ℝ) with hA₂
  have hA₁pos : 0 < A₁ := hα t₁
  have hA₂pos : 0 < A₂ := hα t₂
  have hA₁ne : (A₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA₁pos.ne'
  have hA₂ne : (A₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA₂pos.ne'
  have hαa' : (((α a : ℝˣ) : ℝ) : ℂ) = (A₁ : ℂ)⁻¹ * (A₂ : ℂ) := by
    rw [hadef, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, Complex.ofReal_mul,
      Complex.ofReal_inv]
  rw [hαa']
  simp only [etaFst_apply, etaSnd_apply, Units.val_mul, cpowChar_apply_val]
  rw [← hA₁, ← hA₂]
  have e1 : (-s + 1 / 2 : ℂ) = -(s + 1 / 2) + 1 := by ring
  have e2 : (-(-s + 1 / 2) : ℂ) = (s + 1 / 2) + (-1) := by ring
  have p1 : (A₁ : ℂ) ^ (-(s + 1 / 2) + 1) = (A₁ : ℂ) ^ (-(s + 1 / 2)) * (A₁ : ℂ) := by
    rw [Complex.cpow_add _ _ hA₁ne, Complex.cpow_one]
  have p2 : (A₂ : ℂ) ^ ((s + 1 / 2) + -1) = (A₂ : ℂ) ^ (s + 1 / 2) * (A₂ : ℂ)⁻¹ := by
    rw [Complex.cpow_add _ _ hA₂ne, Complex.cpow_neg_one]
  rw [e2, e1, p1, p2]
  field_simp

end S_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral
end P2MW
export P2MW.S_AutomorphicForm_isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral (solution)
