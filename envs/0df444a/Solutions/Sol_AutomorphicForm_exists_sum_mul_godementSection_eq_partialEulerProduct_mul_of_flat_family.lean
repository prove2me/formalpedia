-- Prove2me | solution 1 for AutomorphicForm.exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/89fa0ab1-3e2e-5b38-a86d-5b1ecd2aadcd

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Theorems.Thm_AutomorphicForm_exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact
import Theorems.Thm_AutomorphicForm_exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite
import Theorems.Thm_AutomorphicForm_exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth
import Theorems.Thm_AutomorphicForm_isInducedSection_godementSection_of_forall_coe_eq_ideleNorm
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal SchwartzMap

namespace R4G1P

variable {F : Type} [Field F] [NumberField F]

variable (F) in

abbrev αF : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

def archPart (k : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F := adelicArchGLIncl F (glArch (𝓞 F) F k)

def finPart (k : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F := (archPart k)⁻¹ * k

theorem glArch_archPart (k : AdelicGL2 (𝓞 F) F) : glArch (𝓞 F) F (archPart k) = glArch (𝓞 F) F k :=
  glArch_adelicArchGLIncl F _

theorem glFin_archPart (k : AdelicGL2 (𝓞 F) F) : glFin (𝓞 F) F (archPart k) = 1 :=
  glFin_adelicArchGLIncl F _

theorem glArch_finPart (k : AdelicGL2 (𝓞 F) F) : glArch (𝓞 F) F (finPart k) = 1 := by
  rw [finPart, map_mul, map_inv, glArch_archPart, inv_mul_cancel]

theorem glFin_finPart (k : AdelicGL2 (𝓞 F) F) : glFin (𝓞 F) F (finPart k) = glFin (𝓞 F) F k := by
  rw [finPart, map_mul, map_inv, glFin_archPart, inv_one, one_mul]

theorem archPart_mul_finPart (k : AdelicGL2 (𝓞 F) F) : archPart k * finPart k = k :=
  mul_inv_cancel_left _ _

theorem archPart_mem {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) :
    archPart k ∈ adelicMaximalCompact F := by
  refine ⟨?_, fun w => ?_⟩
  · rw [glFin_archPart]; exact (finiteIntegralGL2 (𝓞 F) F).one_mem
  · rw [glArch_archPart]; exact hk.2 w

theorem finPart_mem {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ adelicMaximalCompact F) :
    finPart k ∈ adelicMaximalCompact F :=
  (adelicMaximalCompact F).mul_mem ((adelicMaximalCompact F).inv_mem (archPart_mem hk)) hk

theorem glFin_entry_eq {a : AdelicGL2 (𝓞 F) F} {c : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (ha : glFin (𝓞 F) F a = c) (i j : Fin 2) :
    ((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
      = (c : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) => M i j) (Units.ext_iff.mp ha)
  rw [← glFin_apply]; exact h

theorem glArch_entry_eq {a : AdelicGL2 (𝓞 F) F} {c : GL (Fin 2) (InfiniteAdeleRing F)}
    (ha : glArch (𝓞 F) F a = c) (i j : Fin 2) :
    ((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
      = (c : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) => M i j) (Units.ext_iff.mp ha)
  rw [← glArch_apply]; exact h

theorem mul_comm_of_glFin_eq_one_of_glArch_eq_one {a x : AdelicGL2 (𝓞 F) F}
    (ha : glFin (𝓞 F) F a = 1) (hx : glArch (𝓞 F) F x = 1) : a * x = x * a := by
  apply Units.ext
  apply (adelicMatrixProdEquiv F).injective
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  have ha1 : (adelicMatrixProdEquiv F (a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).2 = 1 := by
    show ((glFin (𝓞 F) F a).val : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = 1
    rw [ha]; rfl
  have hx1 : (adelicMatrixProdEquiv F (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).1 = 1 := by
    show ((glArch (𝓞 F) F x).val : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = 1
    rw [hx]; rfl
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_mul, Prod.fst_mul, hx1, mul_one, one_mul]
  · rw [Prod.snd_mul, Prod.snd_mul, ha1, mul_one, one_mul]

theorem norm_eq_one_of_valued_eq_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, h, map_one]; rfl

theorem distribHaarChar_eq_one_of_local (D : (AdeleRing (𝓞 F) F)ˣ)
    (harch : ∀ w : InfinitePlace F, ‖(D : AdeleRing (𝓞 F) F).1 w‖ = 1)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F), (D : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F)
    (hfin' : ∀ v : HeightOneSpectrum (𝓞 F), ((D⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      ∈ v.adicCompletionIntegers F) :
    distribHaarChar (AdeleRing (𝓞 F) F) D = 1 := by
  have h := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F D
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((D : AdeleRing (𝓞 F) F).2 v) = 1 := by
    intro v
    have h1 : Valued.v ((D : AdeleRing (𝓞 F) F).2 v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hfin v)
    have h2 : Valued.v (((D⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hfin' v)
    have hprod : Valued.v ((D : AdeleRing (𝓞 F) F).2 v)
        * Valued.v (((D⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) = 1 := by
      rw [← Valuation.map_mul]
      have : (D : AdeleRing (𝓞 F) F).2 v * ((D⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
        show ((D : AdeleRing (𝓞 F) F) * ((D⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v = 1
        rw [Units.mul_inv]; rfl
      rw [this, Valuation.map_one]
    exact le_antisymm h1 (by
      by_contra hlt
      push Not at hlt
      have : Valued.v ((D : AdeleRing (𝓞 F) F).2 v)
          * Valued.v (((D⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) < 1 :=
        calc _ ≤ Valued.v ((D : AdeleRing (𝓞 F) F).2 v) * 1 := mul_le_mul_right h2 _
          _ = _ := mul_one _
          _ < 1 := hlt
      rw [hprod] at this
      exact lt_irrefl _ this)
  have hfin1 : ∀ v : HeightOneSpectrum (𝓞 F), ‖(D : AdeleRing (𝓞 F) F).2 v‖ = 1 := fun v =>
    norm_eq_one_of_valued_eq_one v _ (hval v)
  simp only [harch, one_pow, Finset.prod_const_one, hfin1, finprod_one, mul_one] at h
  exact_mod_cast h

theorem cpowChar_eq_one_of_distribHaarChar_eq_one
    (hα : ∀ x, 0 < ((αF F x : ℝˣ) : ℝ)) (z : ℂ) (D : (AdeleRing (𝓞 F) F)ˣ)
    (hD : distribHaarChar (AdeleRing (𝓞 F) F) D = 1) :
    cpowChar (αF F) hα z D = 1 := by
  apply Units.ext
  rw [cpowChar_apply_val, Units.val_one]
  have : ((αF F D : ℝˣ) : ℝ) = 1 := by
    show ((distribHaarChar (AdeleRing (𝓞 F) F) D : ℝ≥0) : ℝ) = 1
    rw [hD]; rfl
  rw [this, Complex.ofReal_one, Complex.one_cpow]

theorem norm_diag_eq_one_of_isRowIsometry {L : Type*} [NormedField L] (k : GL (Fin 2) L)
    (hk : IsRowIsometry k) (h10 : (k : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ‖(k : Matrix (Fin 2) (Fin 2) L) 0 0‖ = 1 ∧ ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
  obtain ⟨hdet, hrow⟩ := hk
  have h11 : ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ = 1 := by
    have h := hrow 0 1
    rw [h10, zero_mul, zero_mul, mul_zero, zero_add, zero_add, one_mul, norm_zero, norm_one] at h
    have h' : ‖(k : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2 = 1 := by nlinarith [h]
    have hn := norm_nonneg ((k : Matrix (Fin 2) (Fin 2) L) 1 1)
    nlinarith [h', hn]
  refine ⟨?_, h11⟩
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero, norm_mul, h11, mul_one] at hdet
  exact hdet

section Borel

variable (hαpos : ∀ x, 0 < ((αF F x : ℝˣ) : ℝ))

theorem eta_apply_of_arch_borel (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
    (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (hbf : glFin (𝓞 F) F b = 1)
    (hbi : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) :
    ((etaFst μ (αF F) hαpos s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
      * ((etaSnd ν (αF F) hαpos s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
      = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) := by
  have h10 : ∀ w : InfinitePlace F,
      (archComponent F w (glArch (𝓞 F) F b) : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := by
    intro w
    rw [archComponent_apply, glArch_apply]
    have : ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) = 0 := hb
    rw [this]; rfl
  have hfinb : ∀ i j, (((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2)
      = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := fun i j => by
    rw [glFin_entry_eq hbf i j, Units.val_one]
  have hbf' : glFin (𝓞 F) F b⁻¹ = 1 := by rw [map_inv, hbf, inv_one]
  have hfinb' : ∀ i j, ((((b⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2)
      = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := fun i j => by
    rw [glFin_entry_eq hbf' i j, Units.val_one]
  have einv1 : (((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
      AdeleRing (𝓞 F) F) = ((b⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 := rfl
  have einv2 : (((borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
      AdeleRing (𝓞 F) F) = ((b⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 := rfl
  have hD1 : distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) = 1 := by
    refine distribHaarChar_eq_one_of_local _ (fun w => ?_) (fun v => ?_) (fun v => ?_)
    · show ‖((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).1 w‖ = 1
      have := (norm_diag_eq_one_of_isRowIsometry _ (hbi w) (h10 w)).1
      rwa [archComponent_apply, glArch_apply] at this
    · show ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 v ∈ _
      rw [hfinb]; exact one_mem _
    · rw [einv1, hfinb']; exact one_mem _
  have hD2 : distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) = 1 := by
    refine distribHaarChar_eq_one_of_local _ (fun w => ?_) (fun v => ?_) (fun v => ?_)
    · show ‖((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖ = 1
      have := (norm_diag_eq_one_of_isRowIsometry _ (hbi w) (h10 w)).2
      rwa [archComponent_apply, glArch_apply] at this
    · show ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v ∈ _
      rw [hfinb]; exact one_mem _
    · rw [einv2, hfinb']; exact one_mem _
  rw [etaFst_apply, etaSnd_apply, cpowChar_eq_one_of_distribHaarChar_eq_one hαpos _ _ hD1,
    cpowChar_eq_one_of_distribHaarChar_eq_one hαpos _ _ hD2, mul_one, mul_one]

theorem eta_apply_of_fin_borel (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
    (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (hba : glArch (𝓞 F) F b = 1)
    (hbi : glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F) :
    ((etaFst μ (αF F) hαpos s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
      * ((etaSnd ν (αF F) hαpos s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
      = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) := by
  have harchb : ∀ i j, (((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1)
      = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := fun i j => by
    rw [glArch_entry_eq hba i j, Units.val_one]
  have einv1 : (((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
      AdeleRing (𝓞 F) F) = ((b⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 := rfl
  have einv2 : (((borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
      AdeleRing (𝓞 F) F) = ((b⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 := rfl
  have hint := (mem_finiteIntegralGL2_iff.1 hbi)
  have hD1 : distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) = 1 := by
    refine distribHaarChar_eq_one_of_local _ (fun w => ?_) (fun v => ?_) (fun v => ?_)
    · show ‖((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).1 w‖ = 1
      rw [harchb, Matrix.one_apply_eq]
      exact norm_one
    · exact hint.1 0 0 v
    · rw [einv1]
      have := hint.2 0 0 v
      rwa [← map_inv] at this
  have hD2 : distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) = 1 := by
    refine distribHaarChar_eq_one_of_local _ (fun w => ?_) (fun v => ?_) (fun v => ?_)
    · show ‖((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖ = 1
      rw [harchb, Matrix.one_apply_eq]
      exact norm_one
    · exact hint.1 1 1 v
    · rw [einv2]
      have := hint.2 1 1 v
      rwa [← map_inv] at this
  rw [etaFst_apply, etaSnd_apply, cpowChar_eq_one_of_distribHaarChar_eq_one hαpos _ _ hD1,
    cpowChar_eq_one_of_distribHaarChar_eq_one hαpos _ _ hD2, mul_one, mul_one]

end Borel

theorem eq_of_isInducedSection_of_eqOn_maximalCompact (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (f g : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsInducedSection (𝓞 F) F χ₁ χ₂ f)
    (hg : IsInducedSection (𝓞 F) F χ₁ χ₂ g)
    (h : ∀ k ∈ adelicMaximalCompact F, f k = g k) : f = g := by
  funext x
  obtain ⟨b, k, hb, hk1, hk2, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F x
  rw [hf b hb k, hg b hb k, h k ⟨hk1, hk2⟩]

theorem isInducedSection_sum_mul {ι : Type*} [Fintype ι] (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (a : ι → ℂ) (f : ι → AdelicGL2 (𝓞 F) F → ℂ) (hf : ∀ i, IsInducedSection (𝓞 F) F χ₁ χ₂ (f i)) :
    IsInducedSection (𝓞 F) F χ₁ χ₂ (fun x => ∑ i, a i * f i x) := by
  intro b hb g
  simp only [hf _ b hb g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

open FLT.SmoothVectors

theorem apply_mul_eq_of_mem_stabilizer (φ : AdelicGL2 (𝓞 F) F → ℂ)
    {v : ↥(finiteAdelicGL2Subgroup F)}
    (hv : v ∈ MulAction.stabilizer (↥(finiteAdelicGL2Subgroup F)) (RightTranslationFn.mk φ))
    (x : AdelicGL2 (𝓞 F) F) : φ (x * (v : AdelicGL2 (𝓞 F) F)) = φ x := by
  have h := MulAction.mem_stabilizer_iff.mp hv
  have h' := congrArg (fun f => RightTranslationFn.toFun f x) h
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul] at h'
  exact h'

theorem exists_split (ψ₀ : AdelicGL2 (𝓞 F) F → ℂ) (hsm : IsKfSmooth F ψ₀) :
    ∃ (ι : Type) (_ : Fintype ι) (t : ι → AdelicGL2 (𝓞 F) F)
      (c : ι → GL (Fin 2) (InfiniteAdeleRing F) →₀ ℂ),
      (∀ i, t i ∈ adelicMaximalCompact F ∧ glArch (𝓞 F) F (t i) = 1) ∧
      ∀ (a : GL (Fin 2) (InfiniteAdeleRing F)) (x : AdelicGL2 (𝓞 F) F),
        x ∈ adelicMaximalCompact F → glArch (𝓞 F) F x = 1 →
          ψ₀ (adelicArchGLIncl F a * x)
            = ∑ i, ψ₀ (adelicArchGLIncl F a * t i)
                * ∑ a' ∈ (c i).support, (c i) a' * ψ₀ (adelicArchGLIncl F a' * x) := by
  classical

  set Γ : Subgroup (AdelicGL2 (𝓞 F) F) := finiteAdelicGL2Subgroup F with hΓ
  set V : Subgroup ↥Γ := MulAction.stabilizer ↥Γ (RightTranslationFn.mk ψ₀) with hV_def
  have hV : IsOpen (V : Set ↥Γ) := hsm

  set Kf : Subgroup (AdelicGL2 (𝓞 F) F) := maximalCompactAway F ∅ with hKf_def
  have hKf_mem : ∀ x : ↥Kf, (x : AdelicGL2 (𝓞 F) F) ∈ adelicMaximalCompact F ∧
      glArch (𝓞 F) F (x : AdelicGL2 (𝓞 F) F) = 1 := fun x =>
    ⟨(mem_maximalCompactAway_iff.1 x.2).1, (mem_maximalCompactAway_iff.1 x.2).2.1⟩
  have hKf_of : ∀ x : AdelicGL2 (𝓞 F) F, x ∈ adelicMaximalCompact F → glArch (𝓞 F) F x = 1 → x ∈ Kf :=
    fun x hx hxa => mem_maximalCompactAway_iff.2 ⟨hx, hxa, fun v hv => (Finset.notMem_empty v hv).elim⟩
  let toΓ : ↥Kf → ↥Γ := fun x => ⟨x.1, (mem_finiteAdelicGL2Subgroup_iff F _).2 (hKf_mem x).2⟩
  have htoΓ : ∀ x : ↥Kf, ((toΓ x : ↥Γ) : AdelicGL2 (𝓞 F) F) = x := fun x => rfl
  set KΓ : Set ↥Γ := Subtype.val ⁻¹' (Kf : Set (AdelicGL2 (𝓞 F) F)) with hKΓ
  have hKΓc : IsCompact KΓ :=
    (IsClosed.isClosedEmbedding_subtypeVal (isClosed_finiteAdelicGL2Subgroup F)).isCompact_preimage
      (isCompact_maximalCompactAway F ∅)
  let U : ↥Kf → Set ↥Γ := fun t => (fun y : ↥Γ => (toΓ t)⁻¹ * y) ⁻¹' (V : Set ↥Γ)
  have hUo : ∀ t, IsOpen (U t) := fun t => hV.preimage (continuous_const.mul continuous_id)
  have hcov : KΓ ⊆ ⋃ t, U t := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y.1, hy⟩, ?_⟩
    show (toΓ ⟨y.1, hy⟩)⁻¹ * y ∈ V
    have : toΓ ⟨y.1, hy⟩ = y := Subtype.ext rfl
    rw [this, inv_mul_cancel]
    exact V.one_mem
  obtain ⟨T0, hT0⟩ := hKΓc.elim_finite_subcover U hUo hcov
  have hcover : ∀ x : ↥Kf, ∃ t ∈ T0, (toΓ t)⁻¹ * toΓ x ∈ V := by
    intro x
    have hx : toΓ x ∈ KΓ := by
      show ((toΓ x : ↥Γ) : AdelicGL2 (𝓞 F) F) ∈ (Kf : Set (AdelicGL2 (𝓞 F) F))
      rw [htoΓ]; exact x.2
    have := hT0 hx
    simp only [Set.mem_iUnion] at this
    obtain ⟨t, ht, hmem⟩ := this
    exact ⟨t, ht, hmem⟩

  let Sl : GL (Fin 2) (InfiniteAdeleRing F) → (↥Kf → ℂ) := fun a x => ψ₀ (adelicArchGLIncl F a * x)
  let Esub : Submodule ℂ (↥Kf → ℂ) :=
    { carrier := {f | ∀ x t : ↥Kf, (toΓ t)⁻¹ * toΓ x ∈ V → f x = f t}
      add_mem' := fun {f g} hf hg x t h => by
        show f x + g x = f t + g t
        rw [hf x t h, hg x t h]
      zero_mem' := fun x t _ => rfl
      smul_mem' := fun r f hf x t h => by
        show r • f x = r • f t
        rw [hf x t h] }
  have hSl : ∀ a, Sl a ∈ Esub := by
    intro a x t h
    show ψ₀ (adelicArchGLIncl F a * x) = ψ₀ (adelicArchGLIncl F a * t)
    have key := apply_mul_eq_of_mem_stabilizer ψ₀ h (adelicArchGLIncl F a * t)
    have e : (((toΓ t)⁻¹ * toΓ x : ↥Γ) : AdelicGL2 (𝓞 F) F) = (t : AdelicGL2 (𝓞 F) F)⁻¹ * x := rfl
    rw [e, ← mul_assoc, mul_assoc (adelicArchGLIncl F a), mul_inv_cancel, mul_one] at key
    exact key
  set W : Submodule ℂ (↥Kf → ℂ) := Submodule.span ℂ (Set.range Sl) with hW_def
  have hWE : W ≤ Esub := Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hSl a)

  let R : (↥Kf → ℂ) →ₗ[ℂ] (↥T0 → ℂ) := LinearMap.funLeft ℂ ℂ (fun t : ↥T0 => (t : ↥Kf))
  have hRinj : ∀ f ∈ Esub, R f = 0 → f = 0 := by
    intro f hf hRf
    funext x
    obtain ⟨t, ht, hmem⟩ := hcover x
    have h1 : f x = f t := hf x t hmem
    have h2 : f t = 0 := by
      have := congrFun hRf ⟨t, ht⟩
      simpa [R, LinearMap.funLeft_apply] using this
    rw [h1, h2]; rfl
  set Rw : ↥W →ₗ[ℂ] (↥T0 → ℂ) := R.domRestrict W with hRw_def
  have hker : LinearMap.ker Rw = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun w hw => ?_
    apply Subtype.ext
    exact hRinj w.1 (hWE w.2) hw
  obtain ⟨Lft, hL⟩ := LinearMap.exists_leftInverse_of_injective Rw hker

  let e : ↥T0 → (↥T0 → ℂ) := fun t j => if t = j then 1 else 0
  have hwmem : ∀ t : ↥T0, ((Lft (e t) : ↥W) : ↥Kf → ℂ) ∈ Submodule.span ℂ (Set.range Sl) := fun t => (Lft (e t)).2
  choose c hc using fun t : ↥T0 => Finsupp.mem_span_range_iff_exists_finsupp.1 (hwmem t)

  have hexp : ∀ a : GL (Fin 2) (InfiniteAdeleRing F),
      Sl a = ∑ t : ↥T0, Sl a t • ((Lft (e t) : ↥W) : ↥Kf → ℂ) := by
    intro a
    have hmem : Sl a ∈ W := Submodule.subset_span ⟨a, rfl⟩
    set sa : ↥W := ⟨Sl a, hmem⟩ with hsa
    have h1 : Lft (Rw sa) = sa := by
      have := LinearMap.congr_fun hL sa
      simpa using this
    have h2 : Rw sa = ∑ t : ↥T0, Sl a t • e t := by
      have : Rw sa = R (Sl a) := rfl
      rw [this]
      have hR : R (Sl a) = fun t : ↥T0 => Sl a t := by
        funext t; simp [R, LinearMap.funLeft_apply]
      rw [hR]
      exact pi_eq_sum_univ _
    have h3 : sa = ∑ t : ↥T0, Sl a t • Lft (e t) := by
      rw [← h1, h2, map_sum]
      simp only [map_smul]
    have h4 := congrArg (fun w : ↥W => (w : ↥Kf → ℂ)) h3
    simpa [Submodule.coe_sum, Submodule.coe_smul] using h4
  refine ⟨↥T0, inferInstance, fun t => ((t : ↥Kf) : AdelicGL2 (𝓞 F) F), c, fun t => hKf_mem _, ?_⟩
  intro a x hx hxa
  have hxK : x ∈ Kf := hKf_of x hx hxa
  have h := congrFun (hexp a) ⟨x, hxK⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  refine h.trans (Finset.sum_congr rfl fun t _ => ?_)
  congr 1
  have := congrFun (hc t) ⟨x, hxK⟩
  rw [← this]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem isArchKFinite_translate (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchKFinite F φ)
    (t : AdelicGL2 (𝓞 F) F) (ht : glArch (𝓞 F) F t = 1) :
    IsArchKFinite F (fun g => φ (g * t)) := by
  classical
  intro w
  obtain ⟨s₀, hs₀⟩ := hφ w
  refine ⟨s₀.image (fun f => fun x => f (x * t)), ?_⟩
  intro κ hκ
  have hκf : glFin (𝓞 F) F κ = 1 := by
    obtain ⟨κ', -, rfl⟩ := Subgroup.mem_map.1 hκ
    exact glFin_adelicArchGLIncl F _
  have hcomm : κ * t = t * κ := mul_comm_of_glFin_eq_one_of_glArch_eq_one hκf ht
  have hmem := hs₀ κ hκ
  have heq : (fun x => φ (x * κ * t)) = (LinearMap.funLeft ℂ ℂ (fun x => x * t)) (fun x => φ (x * κ)) := by
    funext x
    rw [LinearMap.funLeft_apply, mul_assoc, hcomm, ← mul_assoc]
  show (fun x => φ (x * κ * t)) ∈ _
  have himg : ((fun f x => f (x * t)) '' (↑s₀ : Set (AdelicGL2 (𝓞 F) F → ℂ)))
      = (LinearMap.funLeft ℂ ℂ fun x => x * t) '' ↑s₀ := rfl
  rw [heq, Finset.coe_image, himg, Submodule.span_image]
  exact Submodule.mem_map_of_mem hmem

open scoped Classical in
theorem main
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (hα : ∀ x, 0 < ((αF F x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ (αF F) hα s) (etaSnd ν (αF F) hα s) (ψ s))
    (hψK : ∀ s, IsArchKFinite F (ψ s))
    (hψf : ∀ s, IsKfSmooth F (ψ s))
    (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
    (hψflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        ψ s k = ψ s' k) :
    ∃ (n : ℕ) (Φ : Fin n → (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (B : Fin n → ℂ → ℂ)
      (S : Finset (HeightOneSpectrum (𝓞 F)))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
      (∀ i, Φ i ∈ schwartzBruhat2 F) ∧
      (∀ i, Differentiable ℂ (B i)) ∧
      (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
      ∀ s : ℂ, 0 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        (∑ i, B i s * godementSection F ν₀ μ ν (αF F) hα (Φ i) s g)
          = (∏' v : {v // v ∉ S},
              (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹)
            * ψ s g := by

  letI mV : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v => borel _
  haveI bV : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v => ⟨rfl⟩
  letI mW : ∀ w : InfinitePlace F, MeasurableSpace w.Completion := fun w => borel _
  haveI bW : ∀ w : InfinitePlace F, BorelSpace w.Completion := fun w => ⟨rfl⟩
  let μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F) := fun v => Measure.addHaar
  haveI : ∀ v, (μf v).IsAddHaarMeasure := fun v => by
    show (Measure.addHaar : Measure (v.adicCompletion F)).IsAddHaarMeasure
    infer_instance
  let μa : (w : InfinitePlace F) → Measure w.Completion := fun w => Measure.addHaar
  haveI : ∀ w, (μa w).IsAddHaarMeasure := fun w => by
    show (Measure.addHaar : Measure w.Completion).IsAddHaarMeasure
    infer_instance
  let ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ := fun v => uniformizerUnit F v
  have hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := fun v =>
    valued_uniformizerUnit F v

  set ψ₀ : AdelicGL2 (𝓞 F) F → ℂ := ψ 0 with hψ₀_def
  have hψ₀c : Continuous ψ₀ := hψjc.comp (Continuous.prodMk continuous_const continuous_id)
  obtain ⟨ι, instι, t, c, ht, hsplit⟩ := exists_split ψ₀ (hψf 0)

  set αfun : ι → AdelicGL2 (𝓞 F) F → ℂ := fun i g => ψ₀ (g * t i) with hαfun
  set βfun : ι → AdelicGL2 (𝓞 F) F → ℂ := fun i g =>
    ∑ a' ∈ (c i).support, (c i) a' * ψ₀ (adelicArchGLIncl F a' * g) with hβfun

  have hαc : ∀ i, Continuous (αfun i) := fun i => hψ₀c.comp (continuous_id.mul continuous_const)
  have hαK : ∀ i, IsArchKFinite F (αfun i) := fun i => isArchKFinite_translate ψ₀ (hψK 0) (t i) (ht i).2
  have hαB : ∀ i (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
      glFin (𝓞 F) F b = 1 →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) →
      ∀ g : AdelicGL2 (𝓞 F) F,
        αfun i (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
          * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * αfun i g := by
    intro i b hb hbf hbi g
    show ψ₀ (b * g * t i) = _ * ψ₀ (g * t i)
    rw [mul_assoc, show ψ₀ = ψ 0 from rfl, hψ 0 b hb (g * t i), eta_apply_of_arch_borel hα μ ν 0 b hb hbf hbi]

  have hβf : ∀ i, IsKfSmooth F (βfun i) := by
    intro i
    show IsOpen ((MulAction.stabilizer (↥(finiteAdelicGL2Subgroup F)) (RightTranslationFn.mk (βfun i)) :
      Subgroup ↥(finiteAdelicGL2Subgroup F)) : Set ↥(finiteAdelicGL2Subgroup F))
    refine Subgroup.isOpen_mono ?_ (hψf 0)
    intro v hv
    refine MulAction.mem_stabilizer_iff.2 (RightTranslationFn.ext fun x => ?_)
    rw [Subgroup.smul_def, RightTranslationFn.toFun_smul]
    show βfun i (x * (v : AdelicGL2 (𝓞 F) F)) = βfun i x
    simp only [hβfun]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← mul_assoc, apply_mul_eq_of_mem_stabilizer ψ₀ hv]
  have hβB : ∀ (i : ι) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
      glArch (𝓞 F) F b = 1 → glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F →
      ∀ g : AdelicGL2 (𝓞 F) F,
        βfun i (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
          * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * βfun i g := by
    intro i b hb hba hbi g
    simp only [hβfun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    have hcomm : adelicArchGLIncl F a' * b = b * adelicArchGLIncl F a' :=
      mul_comm_of_glFin_eq_one_of_glArch_eq_one (glFin_adelicArchGLIncl F a') hba
    rw [← mul_assoc, hcomm, mul_assoc, show ψ₀ = ψ 0 from rfl, hψ 0 b hb,
      eta_apply_of_fin_borel hα μ ν 0 b hb hba hbi]
    ring

  set n : ℕ := Fintype.card ι with hn
  set eι : ι ≃ Fin n := Fintype.equivFin ι with heι

  obtain ⟨S, hSunr, p, h, Φf, hhlc, hhcs, hh0, hh1, hβid⟩ :=
    AutomorphicForm.exists_finset_sum_mul_prod_localZeta_bottomRow_eq_of_isKfSmooth F μf μ ν hμc hνc n
      (fun i => βfun (eι.symm i)) (fun i => hβf _) (fun i b hb hba hbi g => hβB _ b hb hba hbi g)

  have hA := fun i : Fin n =>
    AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite F μa μ ν hμ hν hμc hνc
      (αfun (eι.symm i)) (hαc _) (hαK _) (fun b hb hbf hbi g => hαB _ b hb hbf hbi g)
  choose m g Φa E hE hg hαid using hA

  have hSχ : ∀ v ∉ S, IsUnramifiedCharAt (μ * ν⁻¹) v := by
    intro v hv u hu hu'
    have h1 := (hSunr v hv).1 u hu hu'
    have h2 := (hSunr v hv).2 u hu hu'
    rw [localChar_apply] at h1 h2 ⊢
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, inv_one, mul_one]
  obtain ⟨cE, hcE, hEuler⟩ :=
    AutomorphicForm.exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact F ν₀ S
      μf μa ϖ hϖ hα

  let J : Type := Σ i : Fin n, Fin (m i) × Fin (p i)
  set N : ℕ := Fintype.card J with hN
  set eJ : J ≃ Fin N := Fintype.equivFin J with heJ
  let ΦJ : J → (Fin 2 → AdeleRing (𝓞 F) F) → ℂ := fun q x =>
    g q.1 q.2.1 (fun r => InfiniteAdeleRing.ringEquiv_mixedSpace F (x r).1) * h q.1 q.2.2 (fun r => (x r).2)
  let BJ : J → ℂ → ℂ := fun q s => (cE : ℂ)⁻¹ * E q.1 q.2.1 (2 * s + 1)
  refine ⟨N, fun q => ΦJ (eJ.symm q), fun q => BJ (eJ.symm q), S, ϖ, ?_, ?_, hϖ, ?_⟩
  ·
    intro q
    exact mem_schwartzBruhat2_of_mem_pureTensorSet2
      (tensor_mem_pureTensorSet2 (g _ _) (h _ _) (hhlc _ _) (hhcs _ _))
  ·
    intro q
    show Differentiable ℂ (fun s => (cE : ℂ)⁻¹ * E (eJ.symm q).1 (eJ.symm q).2.1 (2 * s + 1))
    exact (differentiable_const _).mul ((hE _ _).comp (by fun_prop))
  ·
    intro s hs
    obtain ⟨hM, hP, hEid⟩ := hEuler μ ν hμ hν hμc hνc hSχ s hs
    set P : ℂ := ∏' v : {v // v ∉ S},
        (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) with hP_def

    have hprodinv : (∏' v : {v // v ∉ S},
        (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹) = P⁻¹ := by
      have h1 : Filter.Tendsto (fun T : Finset {v // v ∉ S} => ∏ v ∈ T,
          (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) Filter.atTop (nhds P) := by
        have h := hM.hasProd
        rw [HasProd] at h
        simp only [SummationFilter.unconditional_filter] at h
        exact h
      have h2 : Filter.Tendsto (fun T : Finset {v // v ∉ S} => ∏ v ∈ T,
          (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹) Filter.atTop (nhds P⁻¹) := by
        refine (h1.inv₀ hP).congr fun T => ?_
        rw [Finset.prod_inv_distrib]
      have h3 : HasProd (fun v : {v // v ∉ S} =>
          (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹) P⁻¹ := by
        rw [HasProd]
        simp only [SummationFilter.unconditional_filter]
        exact h2
      exact h3.tprod_eq
    have hcE' : (cE : ℂ) ≠ 0 := by exact_mod_cast hcE.ne'
    have hz : 0 < (2 * s + 1).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
        Complex.one_re]
      linarith

    have hK : ∀ k ∈ adelicMaximalCompact F,
        (∑ q, BJ (eJ.symm q) s * godementSection F ν₀ μ ν (αF F) hα (ΦJ (eJ.symm q)) s k) = P⁻¹ * ψ s k := by
      intro k hk

      rw [Equiv.sum_comp eJ.symm (fun q => BJ q s * godementSection F ν₀ μ ν (αF F) hα (ΦJ q) s k)]

      have hfac : ∀ q : J, godementSection F ν₀ μ ν (αF F) hα (ΦJ q) s k
          = P⁻¹ * (cE * ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
            * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                (fun t => Φa q.1 q.2.1 w (fun i => t
                  * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                (archLocalChar (μ * ν⁻¹) w) (2 * s + 1))
            * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                (fun t => Φf q.1 q.2.2 v (fun i => t
                  * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
                      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i))
                (localChar (μ * ν⁻¹) v) (2 * s + 1)) := by
        intro q
        have hΦ0 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∃ v ∉ S, ∃ i, (x i).2 v ∉ v.adicCompletionIntegers F) → ΦJ q x = 0 := by
          intro x hx
          show g q.1 q.2.1 _ * h q.1 q.2.2 (fun r => (x r).2) = 0
          rw [hh0 q.1 q.2.2 (fun r => (x r).2) hx, mul_zero]
        have hΦ1 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∀ v ∉ S, ∀ i, (x i).2 v ∈ v.adicCompletionIntegers F) →
              ΦJ q x = (∏ w, Φa q.1 q.2.1 w (fun i => (x i).1 w))
                * ∏ v ∈ S, Φf q.1 q.2.2 v (fun i => (x i).2 v) := by
          intro x hx
          show g q.1 q.2.1 (fun r => InfiniteAdeleRing.ringEquiv_mixedSpace F (x r).1)
              * h q.1 q.2.2 (fun r => (x r).2) = _
          rw [hg q.1 q.2.1 (fun r => (x r).1), hh1 q.1 q.2.2 (fun r => (x r).2) hx]
        have := hEid (ΦJ q) (Φa q.1 q.2.1) (Φf q.1 q.2.2) hΦ0 hΦ1 k hk
        rw [← this]
        field_simp
      simp only [hfac]

      have hsum : (∑ q : J, BJ q s * (P⁻¹ * (cE * ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
            * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                (fun t => Φa q.1 q.2.1 w (fun i => t
                  * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                (archLocalChar (μ * ν⁻¹) w) (2 * s + 1))
            * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                (fun t => Φf q.1 q.2.2 v (fun i => t
                  * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
                      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i))
                (localChar (μ * ν⁻¹) v) (2 * s + 1))))
          = P⁻¹ * ∑ i : Fin n,
              (∑ j : Fin (m i), E i j (2 * s + 1)
                * (((μ (Matrix.GeneralLinearGroup.det (archPart k)) : ℂˣ) : ℂ)
                  * ∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                    (fun t => Φa i j w (fun i' => t
                      * (archComponent F w (glArch (𝓞 F) F (archPart k)) :
                          Matrix (Fin 2) (Fin 2) w.Completion) 1 i'))
                    (archLocalChar (μ * ν⁻¹) w) (2 * s + 1)))
              * ∑ l : Fin (p i), ((μ (Matrix.GeneralLinearGroup.det (finPart k)) : ℂˣ) : ℂ)
                  * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                    (fun t => Φf i l v (fun i' => t
                      * (finComponent (𝓞 F) F v (glFin (𝓞 F) F (finPart k)) :
                          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i'))
                    (localChar (μ * ν⁻¹) v) (2 * s + 1) := by
        rw [glArch_archPart, glFin_finPart]
        have hdet : ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
            = ((μ (Matrix.GeneralLinearGroup.det (archPart k)) : ℂˣ) : ℂ)
              * ((μ (Matrix.GeneralLinearGroup.det (finPart k)) : ℂˣ) : ℂ) := by
          rw [← Units.val_mul, ← map_mul, ← map_mul, archPart_mul_finPart]
        rw [hdet, Finset.mul_sum, Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum, Finset.univ_product_univ]
        refine Finset.sum_congr rfl fun jl _ => ?_
        simp only [BJ]
        field_simp
      rw [hsum]

      have harch : ∀ i : Fin n, (∑ j : Fin (m i), E i j (2 * s + 1)
          * (((μ (Matrix.GeneralLinearGroup.det (archPart k)) : ℂˣ) : ℂ)
            * ∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
              (fun t => Φa i j w (fun i' => t
                * (archComponent F w (glArch (𝓞 F) F (archPart k)) :
                    Matrix (Fin 2) (Fin 2) w.Completion) 1 i'))
              (archLocalChar (μ * ν⁻¹) w) (2 * s + 1))) = αfun (eι.symm i) (archPart k) :=
        fun i => hαid i (2 * s + 1) hz (archPart k) (archPart_mem hk) (glFin_archPart k)
      have hfin : ∀ i : Fin n, (∑ l : Fin (p i), ((μ (Matrix.GeneralLinearGroup.det (finPart k)) : ℂˣ) : ℂ)
          * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
            (fun t => Φf i l v (fun i' => t
              * (finComponent (𝓞 F) F v (glFin (𝓞 F) F (finPart k)) :
                  Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i'))
            (localChar (μ * ν⁻¹) v) (2 * s + 1)) = βfun (eι.symm i) (finPart k) :=
        fun i => hβid i (2 * s + 1) (finPart k) (finPart_mem hk) (glArch_finPart k)
      simp only [harch, hfin]
      congr 1

      have hsp := hsplit (glArch (𝓞 F) F k) (finPart k) (finPart_mem hk) (glArch_finPart k)
      have hkk : adelicArchGLIncl F (glArch (𝓞 F) F k) * finPart k = k := archPart_mul_finPart k
      rw [hkk] at hsp
      rw [hψflat s 0 k hk.1 hk.2, show ψ 0 k = ψ₀ k from rfl, hsp,
        ← Equiv.sum_comp eι.symm]
      rfl

    intro x
    have hαN : ∀ y, ((αF F y : ℝˣ) : ℝ) = ideleNorm F y := fun y => rfl
    have h1 : IsInducedSection (𝓞 F) F (etaFst μ (αF F) hα s) (etaSnd ν (αF F) hα s)
        (fun y => ∑ q, BJ (eJ.symm q) s * godementSection F ν₀ μ ν (αF F) hα (ΦJ (eJ.symm q)) s y) :=
      isInducedSection_sum_mul _ _ (fun q => BJ (eJ.symm q) s) _ (fun q =>
        AutomorphicForm.isInducedSection_godementSection_of_forall_coe_eq_ideleNorm F ν₀ μ ν (αF F) hα hαN _ s)
    have h2 : IsInducedSection (𝓞 F) F (etaFst μ (αF F) hα s) (etaSnd ν (αF F) hα s)
        (fun y => P⁻¹ * ψ s y) := by
      intro b hb y
      dsimp only
      rw [hψ s b hb y]; ring
    beta_reduce
    have hfinal := congrFun (eq_of_isInducedSection_of_eqOn_maximalCompact _ _ _ _ h1 h2 hK) x
    rw [← hprodinv] at hfinal
    exact hfinal

end R4G1P

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      (_hψK : ∀ s, IsArchKFinite F (ψ s))
      (_hψf : ∀ s, IsKfSmooth F (ψ s))
      (_hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
      (_hψhol : ∀ g, Differentiable ℂ (fun s => ψ s g))
      (_hψflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ s k = ψ s' k),
    ∃ (n : ℕ) (Φ : Fin n → (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (B : Fin n → ℂ → ℂ)
      (S : Finset (HeightOneSpectrum (𝓞 F)))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
      (∀ i, Φ i ∈ schwartzBruhat2 F) ∧
      (∀ i, Differentiable ℂ (B i)) ∧
      (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
      ∀ s : ℂ, 0 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        (∑ i, B i s * godementSection F ν₀ μ ν α hα (Φ i) s g)
          = (∏' v : {v // v ∉ S},
              (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹)
            * ψ s g := by
  intro α hα μ ν hμ hν hμc hνc ψ hψ hψK hψf hψjc _hψhol hψflat
  exact R4G1P.main ν₀ hα μ ν hμ hν hμc hνc ψ hψ hψK hψf hψjc hψflat

end

end S_AutomorphicForm_exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family
end P2MW
export P2MW.S_AutomorphicForm_exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family (solution)
