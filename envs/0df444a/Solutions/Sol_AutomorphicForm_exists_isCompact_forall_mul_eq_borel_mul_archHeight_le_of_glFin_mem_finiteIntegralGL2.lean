-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a76880c4-21c1-54d0-9094-16ee354fa442

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

namespace B3Translate

variable (F : Type) [Field F] [NumberField F]

local notation "G" => AdelicGL2 (𝓞 F) F
local notation "𝔸" => AdeleRing (𝓞 F) F

theorem continuous_entry (i j : Fin 2) : Continuous fun g : G => ((g : G) : Matrix (Fin 2) (Fin 2) 𝔸) i j :=
  (Units.continuous_val.matrix_elem i j)

theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 F) F : Set G) := by
  have : (adelicBorel (𝓞 F) F : Set G) = (fun g : G => ((g : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 0) ⁻¹' {0} := by
    ext g; exact mem_borelSubgroup_iff _
  rw [this]
  exact isClosed_singleton.preimage (continuous_entry F 1 0)

noncomputable def hgt (b : ↥(adelicBorel (𝓞 F) F)) : ℝ :=
  NumberField.TateGlobal.ideleNorm F (borelDiagFst b) / NumberField.TateGlobal.ideleNorm F (borelDiagSnd b)

theorem hgt_mul (b c : ↥(adelicBorel (𝓞 F) F)) : hgt F (b * c) = hgt F b * hgt F c := by
  simp only [hgt, map_mul, NumberField.TateGlobal.ideleNorm_mul]
  rw [mul_div_mul_comm]

theorem hgt_pos (b : ↥(adelicBorel (𝓞 F) F)) : 0 < hgt F b :=
  div_pos (NumberField.TateGlobal.ideleNorm_pos _) (NumberField.TateGlobal.ideleNorm_pos _)

theorem continuous_borelDiagFst : Continuous (borelDiagFst : ↥(adelicBorel (𝓞 F) F) → 𝔸ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_entry F 0 0).comp continuous_subtype_val
  · have : (fun b : ↥(adelicBorel (𝓞 F) F) => ((borelDiagFst b)⁻¹ : 𝔸ˣ).val)
        = fun b => ((b⁻¹ : ↥(adelicBorel (𝓞 F) F)) : G).val 0 0 := by
      funext b; rw [← map_inv]; rfl
    rw [this]
    exact (continuous_entry F 0 0).comp (continuous_subtype_val.comp continuous_inv)

theorem continuous_borelDiagSnd : Continuous (borelDiagSnd : ↥(adelicBorel (𝓞 F) F) → 𝔸ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_entry F 1 1).comp continuous_subtype_val
  · have : (fun b : ↥(adelicBorel (𝓞 F) F) => ((borelDiagSnd b)⁻¹ : 𝔸ˣ).val)
        = fun b => ((b⁻¹ : ↥(adelicBorel (𝓞 F) F)) : G).val 1 1 := by
      funext b; rw [← map_inv]; rfl
    rw [this]
    exact (continuous_entry F 1 1).comp (continuous_subtype_val.comp continuous_inv)

theorem continuous_hgt : Continuous (hgt F) :=
  ((NumberField.TateGlobal.continuous_ideleNorm F).comp (continuous_borelDiagFst F)).div
    ((NumberField.TateGlobal.continuous_ideleNorm F).comp (continuous_borelDiagSnd F))
    fun b => (NumberField.TateGlobal.ideleNorm_pos _).ne'

end B3Translate

namespace B3Translate

variable (F : Type) [Field F] [NumberField F]

local notation "G" => AdelicGL2 (𝓞 F) F
local notation "𝔸" => AdeleRing (𝓞 F) F

theorem norm_snd_eq_one_of_integral (x : 𝔸ˣ)
    (h1 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (x : 𝔸).2 v ∈ v.adicCompletionIntegers F)
    (h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ((x⁻¹ : 𝔸ˣ) : 𝔸).2 v ∈ v.adicCompletionIntegers F)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ‖(x : 𝔸).2 v‖ = 1 := by
  have ha : ‖(x : 𝔸).2 v‖ ≤ 1 := NumberField.AdelicHeight.norm_le_one_of_mem_adicCompletionIntegers (h1 v)
  have hb : ‖((x⁻¹ : 𝔸ˣ) : 𝔸).2 v‖ ≤ 1 := NumberField.AdelicHeight.norm_le_one_of_mem_adicCompletionIntegers (h2 v)
  have hprod : ‖(x : 𝔸).2 v‖ * ‖((x⁻¹ : 𝔸ˣ) : 𝔸).2 v‖ = 1 := by
    rw [← norm_mul]
    have := congrArg (fun y : 𝔸 => y.2 v) x.mul_inv
    change ((x : 𝔸).2 * ((x⁻¹ : 𝔸ˣ) : 𝔸).2) v = (1 : 𝔸).2 v at this
    rw [show ((x : 𝔸).2 * ((x⁻¹ : 𝔸ˣ) : 𝔸).2) v = (x : 𝔸).2 v * ((x⁻¹ : 𝔸ˣ) : 𝔸).2 v from rfl] at this
    rw [this]
    exact norm_one
  refine le_antisymm ha ?_
  calc (1 : ℝ) = ‖(x : 𝔸).2 v‖ * ‖((x⁻¹ : 𝔸ˣ) : 𝔸).2 v‖ := hprod.symm
    _ ≤ ‖(x : 𝔸).2 v‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := mul_one _

theorem ideleNorm_eq_prod_of_integral (x : 𝔸ˣ)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(x : 𝔸).2 v‖ = 1) :
    NumberField.TateGlobal.ideleNorm F x = ∏ w : InfinitePlace F, ‖(x : 𝔸).1 w‖ ^ w.mult := by
  show ((distribHaarChar 𝔸 x : ℝ≥0) : ℝ) = _
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm,
    finprod_eq_one_of_forall_eq_one h, mul_one]

theorem archComponent_glArch_apply (w : InfinitePlace F) (g : G) (i j : Fin 2) :
    ((archComponent F w (glArch (𝓞 F) F g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = (((g : G) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w := by
  rw [archComponent_apply, glArch_apply]

theorem localHeight_archComponent_borel (w : InfinitePlace F) (b : ↥(adelicBorel (𝓞 F) F)) :
    localHeight (archComponent F w (glArch (𝓞 F) F (b : G)))
      = ‖(((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).1 w‖ / ‖(((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w‖ := by
  set M := ((archComponent F w (glArch (𝓞 F) F (b : G)) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
    with hM
  have h10 : M 1 0 = 0 := by
    rw [hM, archComponent_glArch_apply, borel_entry_one_zero]; rfl
  have h00 : M 0 0 = (((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).1 w := by rw [hM, archComponent_glArch_apply]
  have h11 : M 1 1 = (((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w := by rw [hM, archComponent_glArch_apply]

  have hne : M 1 1 ≠ 0 := by
    rw [h11]
    have hu : IsUnit ((((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w) := by
      have := (borelDiagSnd b).isUnit
      have hmap := this.map ((Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) w).comp
        (RingHom.fst (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
      exact hmap
    exact hu.ne_zero
  unfold localHeight rowNormSq
  rw [← hM, Matrix.det_fin_two, h10, mul_zero, sub_zero, norm_mul, norm_zero, h00, h11]
  have hpos : 0 < ‖(((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w‖ := norm_pos_iff.mpr (by rwa [h11] at hne)
  field_simp
  ring

theorem hgt_eq_archHeight {g b k : G} (hb : b ∈ adelicBorel (𝓞 F) F) (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F)
    (hkf : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F)
    (hka : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) (hgeq : g = b * k) :
    hgt F ⟨b, hb⟩ = archHeight F (glArch (𝓞 F) F g) := by

  have hbf : glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F := by
    have : b = g * k⁻¹ := by rw [hgeq, mul_inv_cancel_right]
    rw [this, map_mul, map_inv]
    exact (finiteIntegralGL2 (𝓞 F) F).mul_mem hg ((finiteIntegralGL2 (𝓞 F) F).inv_mem hkf)
  obtain ⟨hint, hint'⟩ := mem_finiteIntegralGL2_iff.mp hbf
  set bb : ↥(adelicBorel (𝓞 F) F) := ⟨b, hb⟩ with hbb

  have hfst : ∀ v, ‖((borelDiagFst bb : 𝔸ˣ) : 𝔸).2 v‖ = 1 := by
    refine norm_snd_eq_one_of_integral F _ (fun v => hint 0 0 v) (fun v => ?_)
    rw [← map_inv]
    have := (mem_finiteIntegralGL2_iff.mp ((finiteIntegralGL2 (𝓞 F) F).inv_mem hbf)).1 0 0 v
    rw [← map_inv] at this
    exact this
  have hsnd : ∀ v, ‖((borelDiagSnd bb : 𝔸ˣ) : 𝔸).2 v‖ = 1 := by
    refine norm_snd_eq_one_of_integral F _ (fun v => hint 1 1 v) (fun v => ?_)
    rw [← map_inv]
    have := (mem_finiteIntegralGL2_iff.mp ((finiteIntegralGL2 (𝓞 F) F).inv_mem hbf)).1 1 1 v
    rw [← map_inv] at this
    exact this

  have hH : archHeight F (glArch (𝓞 F) F g) = archHeight F (glArch (𝓞 F) F b) := by
    rw [hgeq, map_mul]
    unfold archHeight
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_mul, localHeight_mul_rowIsometry _ (hka w)]
  rw [hH, hgt, ideleNorm_eq_prod_of_integral F _ hfst, ideleNorm_eq_prod_of_integral F _ hsnd, ← Finset.prod_div_distrib]
  unfold archHeight
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← div_pow]
  congr 1
  exact (localHeight_archComponent_borel F w bb).symm

end B3Translate

open B3Translate in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∀ t : AdelicGL2 (𝓞 F) F,
      ∃ (k₁ k₂ : ℝ) (Ω : Set (AdelicGL2 (𝓞 F) F)), 0 < k₁ ∧ k₁ ≤ k₂ ∧ IsCompact Ω ∧
        ∀ g : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F →
          ∃ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F), ω ∈ Ω ∧
            g * t = (b : AdelicGL2 (𝓞 F) F) * ω ∧
            k₁ * archHeight F (glArch (𝓞 F) F g) ≤ hgt b ∧
            hgt b ≤ k₂ * archHeight F (glArch (𝓞 F) F g) := by
  intro α hgt t
  have hhgt : ∀ b, hgt b = B3Translate.hgt F b := fun b => rfl
  set K : Subgroup (AdelicGL2 (𝓞 F) F) := adelicMaximalCompact F with hK
  have hKc : IsCompact (K : Set (AdelicGL2 (𝓞 F) F)) := isCompact_adelicMaximalCompact F
  have hmemK : ∀ {k : AdelicGL2 (𝓞 F) F}, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) → k ∈ K :=
    fun h1 h2 => ⟨h1, h2⟩

  set KtK : Set (AdelicGL2 (𝓞 F) F) :=
    (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * t * p.2) '' ((K : Set (AdelicGL2 (𝓞 F) F)) ×ˢ (K : Set (AdelicGL2 (𝓞 F) F)))
    with hKtK
  have hKtKc : IsCompact KtK :=
    (hKc.prod hKc).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  set S : Set ↥(adelicBorel (𝓞 F) F) := Subtype.val ⁻¹' KtK with hS
  have hSc : IsCompact S := (isClosed_adelicBorel F).isClosedEmbedding_subtypeVal.isCompact_preimage hKtKc

  obtain ⟨b₀, k₀, hb₀, hk₀f, hk₀a, ht⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F t
  have hb₀S : (⟨b₀, hb₀⟩ : ↥(adelicBorel (𝓞 F) F)) ∈ S := by
    refine ⟨(1, k₀⁻¹), ⟨K.one_mem, K.inv_mem (hmemK hk₀f hk₀a)⟩, ?_⟩
    show 1 * t * k₀⁻¹ = b₀
    rw [one_mul, ht, mul_inv_cancel_right]

  obtain ⟨bmin, hbminS, hmin⟩ := hSc.exists_isMinOn ⟨_, hb₀S⟩ (continuous_hgt F).continuousOn
  obtain ⟨bmax, hbmaxS, hmax⟩ := hSc.exists_isMaxOn ⟨_, hb₀S⟩ (continuous_hgt F).continuousOn
  refine ⟨B3Translate.hgt F bmin, B3Translate.hgt F bmax, K, hgt_pos F bmin, hmin hbmaxS, hKc, fun g hg => ?_⟩

  obtain ⟨bg, kg, hbg, hkgf, hkga, hgeq⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  obtain ⟨b', k', hb', hk'f, hk'a, heq'⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F (kg * t)
  have hb'S : (⟨b', hb'⟩ : ↥(adelicBorel (𝓞 F) F)) ∈ S := by
    refine ⟨(kg, k'⁻¹), ⟨hmemK hkgf hkga, K.inv_mem (hmemK hk'f hk'a)⟩, ?_⟩
    show kg * t * k'⁻¹ = b'
    rw [heq', mul_inv_cancel_right]
  have hH : B3Translate.hgt F ⟨bg, hbg⟩ = archHeight F (glArch (𝓞 F) F g) := hgt_eq_archHeight F hbg hg hkgf hkga hgeq
  have hHnn : 0 ≤ archHeight F (glArch (𝓞 F) F g) := by rw [← hH]; exact (hgt_pos F _).le
  refine ⟨⟨bg, hbg⟩ * ⟨b', hb'⟩, k', hmemK hk'f hk'a, ?_, ?_, ?_⟩
  · show g * t = bg * b' * k'
    rw [hgeq, mul_assoc, heq', mul_assoc]
  · rw [hhgt, hgt_mul, hH, mul_comm]
    exact mul_le_mul_of_nonneg_left (hmin hb'S) hHnn
  · rw [hhgt, hgt_mul, hH, mul_comm (B3Translate.hgt F bmax)]
    exact mul_le_mul_of_nonneg_left (hmax hb'S) hHnn

end S_AutomorphicForm_exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2 (solution)
