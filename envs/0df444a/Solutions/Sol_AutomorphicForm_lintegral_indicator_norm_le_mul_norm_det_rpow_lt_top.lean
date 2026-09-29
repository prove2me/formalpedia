-- Prove2me | solution 1 for AutomorphicForm.lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8390eec0-e69c-522f-98b8-3802bc0c4fb0

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_eq_mul_lintegral_prod_lintegral_unipotent_diagUnits2
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Ws48DetInt

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem norm_le_one_of_mem_integers {x : F} (hx : x ∈ p.adicCompletionIntegers ℚ) : ‖x‖ ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hx
  exact (Valued.toNormedField.norm_le_one_iff).mpr hx

theorem norm_entry_le_one_of_mem {k : G₂} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) (i j : Fin 2) :
    ‖(k : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1 ∧ ‖((k⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1 := by
  rw [AdelicDock.mem_localLevelOne_iff] at hk
  exact ⟨norm_le_one_of_mem_integers (hk.1.integral i j), norm_le_one_of_mem_integers (hk.2.integral i j)⟩

theorem norm_det_le_one_of_entries {M : Matrix (Fin 2) (Fin 2) F} (hM : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hM _ _) (norm_nonneg _) (hM _ _)
  · rw [norm_neg, norm_mul]; exact mul_le_one₀ (hM _ _) (norm_nonneg _) (hM _ _)

theorem norm_det_eq_one_of_mem {k : G₂} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    ‖((Matrix.GeneralLinearGroup.det k : Fˣ) : F)‖ = 1 := by
  have h1 : ‖((Matrix.GeneralLinearGroup.det k : Fˣ) : F)‖ ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_le_one_of_entries fun i j => (norm_entry_le_one_of_mem hk i j).1
  have h2 : ‖((Matrix.GeneralLinearGroup.det k⁻¹ : Fˣ) : F)‖ ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_le_one_of_entries fun i j => (norm_entry_le_one_of_mem hk i j).2
  have h3 : ((Matrix.GeneralLinearGroup.det k : Fˣ) : F) * ((Matrix.GeneralLinearGroup.det k⁻¹ : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h4 : ‖((Matrix.GeneralLinearGroup.det k : Fˣ) : F)‖ * ‖((Matrix.GeneralLinearGroup.det k⁻¹ : Fˣ) : F)‖ = 1 := by
    rw [← norm_mul, h3, norm_one]
  nlinarith [norm_nonneg ((Matrix.GeneralLinearGroup.det k : Fˣ) : F), norm_nonneg ((Matrix.GeneralLinearGroup.det k⁻¹ : Fˣ) : F)]

theorem norm_mul_entry_le {M N : Matrix (Fin 2) (Fin 2) F} {B : ℝ} (hM : ∀ i j, ‖M i j‖ ≤ B) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (i j : Fin 2) : ‖(M * N) i j‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hM 0 0)
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
  · rw [norm_mul]
    calc _ ≤ B * 1 := mul_le_mul (hM _ _) (hN _ _) (norm_nonneg _) hB
      _ = B := mul_one B

theorem coords_of_mem_ball {B : ℝ} {x : F} {a₁ a₂ : Fˣ} {k : G₂} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (hB : ∀ i j : Fin 2, ‖((unipotent x * diagUnits2 a₁ a₂ * k : G₂) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ B) :
    ‖(a₁ : F)‖ ≤ B ∧ ‖(a₂ : F)‖ ≤ B ∧ ‖x‖ * ‖(a₂ : F)‖ ≤ B := by
  have key : ∀ i j : Fin 2, ‖((unipotent x * diagUnits2 a₁ a₂ : G₂) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ B := by
    have e : ((unipotent x * diagUnits2 a₁ a₂ : G₂) : Matrix (Fin 2) (Fin 2) F) =
        ((unipotent x * diagUnits2 a₁ a₂ * k : G₂) : Matrix (Fin 2) (Fin 2) F) * ((k⁻¹ : G₂) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact norm_mul_entry_le hB (fun i j => (norm_entry_le_one_of_mem hk i j).2)
  have hmat : ((unipotent x * diagUnits2 a₁ a₂ : G₂) : Matrix (Fin 2) (Fin 2) F) = !![(a₁ : F), x * (a₂ : F); 0, (a₂ : F)] := by
    rw [Units.val_mul, coe_diagUnits2]
    rw [show ((unipotent x : G₂) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] from rfl]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have k00 := key 0 0; have k01 := key 0 1; have k11 := key 1 1
  rw [hmat] at k00 k01 k11
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at k00 k01 k11
  exact ⟨k00, k11, by rwa [norm_mul] at k01⟩

theorem norm_det_coords {x : F} {a₁ a₂ : Fˣ} {k : G₂} (hk : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤) :
    ‖((Matrix.GeneralLinearGroup.det (unipotent x * diagUnits2 a₁ a₂ * k) : Fˣ) : F)‖ = ‖(a₁ : F)‖ * ‖(a₂ : F)‖ := by
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, norm_mul, norm_mul, norm_det_eq_one_of_mem hk, mul_one]
  have h1 : ((Matrix.GeneralLinearGroup.det (unipotent x : G₂) : Fˣ) : F) = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, show ((unipotent x : G₂) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] from rfl]
    simp [Matrix.det_fin_two_of]
  have h2 : ((Matrix.GeneralLinearGroup.det (diagUnits2 a₁ a₂ : G₂) : Fˣ) : F) = (a₁ : F) * (a₂ : F) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits2]
    simp [Matrix.det_fin_two_of]
  rw [h1, h2, norm_one, one_mul, norm_mul]

end Ws48DetInt

end

namespace Ws48DetInt

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction MeasureTheory
open scoped ENNReal NNReal

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

def shell (p : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) : Set (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  {y | Valued.v (y : HeightOneSpectrum.adicCompletion ℚ p) = WithZero.exp (-(n))}

theorem lintegral_units_le_tsum (φ : Fˣ → ℝ≥0∞) (c : ℤ → ℝ≥0∞)
    (hφ : ∀ (n : ℤ) (y : Fˣ), y ∈ shell p n → φ y ≤ c n) :
    ∫⁻ y, φ y ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ≤
      (∑' n : ℤ, c n) * (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) := by
  obtain ⟨hmeas, huniq, hmass, -, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  set μx : Measure Fˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hμx
  have hunion : (Set.univ : Set Fˣ) = ⋃ n : ℤ, shell p n := by
    ext y; simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    obtain ⟨n, hn, -⟩ := huniq y
    exact ⟨n, hn⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℤ => shell p n) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_iff]
    rintro y ⟨hym, hyn⟩
    obtain ⟨k, -, hk⟩ := huniq y
    exact hmn ((hk m hym).trans (hk n hyn).symm)
  calc ∫⁻ y, φ y ∂μx = ∫⁻ y in Set.univ, φ y ∂μx := by rw [Measure.restrict_univ]
    _ = ∫⁻ y in ⋃ n : ℤ, shell p n, φ y ∂μx := by rw [← hunion]
    _ = ∑' n : ℤ, ∫⁻ y in shell p n, φ y ∂μx := lintegral_iUnion (fun n => hmeas n) hdisj φ
    _ ≤ ∑' n : ℤ, c n * μx (shell p 0) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        calc ∫⁻ y in shell p n, φ y ∂μx ≤ ∫⁻ y in shell p n, c n ∂μx := setLIntegral_mono' (hmeas n) (fun y hy => hφ n y hy)
          _ = c n * μx (shell p n) := setLIntegral_const _ _
          _ = c n * μx (shell p 0) := by simp only [shell]; rw [(hmass n).1]
    _ = (∑' n : ℤ, c n) * μx (shell p 0) := ENNReal.tsum_mul_right

theorem norm_eq_of_mem_shell {n : ℤ} {y : Fˣ} (hy : y ∈ shell p n) :
    ‖(y : F)‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-n) := by
  obtain ⟨-, -, -, hmod, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  have := hmod n y hy
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm] at this
  exact this

theorem measure_shell_zero_lt_top :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (shell p 0) < ⊤ := by
  obtain ⟨-, -, hmass, -, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  exact (hmass 0).2.2

theorem tsum_indicator_zpow_lt_top (r : ℝ≥0) (hr0 : r ≠ 0) (hr : r < 1) (b : ℕ) :
    (∑' n : ℤ, (if (-(b : ℤ) ≤ n) then ((r : ℝ≥0∞) ^ n) else 0)) < ⊤ := by
  have hsplit := tsum_of_nat_of_neg_add_one (f := fun n : ℤ => (if (-(b : ℤ) ≤ n) then ((r : ℝ≥0∞) ^ n) else 0))
    ENNReal.summable ENNReal.summable
  rw [hsplit]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · have : (fun n : ℕ => (if (-(b : ℤ) ≤ (n : ℤ)) then ((r : ℝ≥0∞) ^ (n : ℤ)) else 0)) = fun n : ℕ => (r : ℝ≥0∞) ^ n := by
      funext n
      rw [if_pos (by omega), zpow_natCast]
    rw [this, ENNReal.tsum_geometric]
    exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt (by exact_mod_cast hr))
  ·
    have hzero : ∀ n : ℕ, n ∉ Finset.range b →
        (fun n : ℕ => (if (-(b : ℤ) ≤ (-(n + 1 : ℤ))) then ((r : ℝ≥0∞) ^ (-(n + 1 : ℤ))) else 0)) n = 0 := by
      intro n hn
      rw [Finset.mem_range, not_lt] at hn
      simp only []
      rw [if_neg (by omega)]
    rw [tsum_eq_sum hzero]
    refine ENNReal.sum_lt_top.mpr fun n _ => ?_
    split_ifs
    · exact ENNReal.zpow_lt_top (by exact_mod_cast hr0) ENNReal.coe_ne_top _
    · exact ENNReal.zero_lt_top

end Ws48DetInt

namespace Ws48DetInt

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction MeasureTheory
open scoped ENNReal NNReal Pointwise

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem measurable_units_val : Measurable (fun a : Fˣ => (a : F)) :=
  comap_measurable Units.val

theorem measurable_units_norm : Measurable (fun a : Fˣ => ‖(a : F)‖) :=
  measurable_norm.comp measurable_units_val

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

theorem regular_selfDualHaarAt : (selfDualHaarAt ℚ p : Measure F).Regular := by
  show ((((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F)).Regular
  rw [ENNReal.smul_def]
  exact Measure.Regular.smul ENNReal.coe_ne_top

theorem map_mul_left_selfDualHaarAt (u : Fˣ) :
    Measure.map (fun x : F => (u : F) * x) (selfDualHaarAt ℚ p) =
      ((modulus (u : F))⁻¹ : ℝ≥0) • (selfDualHaarAt ℚ p : Measure F) := by
  haveI := isAddHaarMeasure_selfDualHaarAt (p := p)
  haveI := regular_selfDualHaarAt (p := p)
  set μ : Measure F := selfDualHaarAt ℚ p with hμ
  ext s hs
  rw [Measure.map_apply (measurable_const_mul (u : F)) hs, Measure.smul_apply]
  have hpre : (fun x : F => (u : F) * x) ⁻¹' s = (u⁻¹ : Fˣ) • s := by
    ext x
    rw [Set.mem_preimage, Set.mem_inv_smul_set_iff, Units.smul_def, smul_eq_mul]
  rw [hpre, ← distribHaarChar_mul μ (u⁻¹ : Fˣ) s, map_inv, modulus_coe_units, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_inv (distribHaarChar_pos).ne']

theorem lintegral_comp_mul_left_selfDualHaarAt (u : Fˣ) (H : F → ℝ≥0∞) :
    ∫⁻ x, H ((u : F) * x) ∂(selfDualHaarAt ℚ p) = ((modulus (u : F))⁻¹ : ℝ≥0) * ∫⁻ x, H x ∂(selfDualHaarAt ℚ p) := by
  set e : F ≃ᵐ F := MeasurableEquiv.mulLeft₀ (u : F) u.ne_zero with he
  have hcoe : (fun x : F => (u : F) * x) = e := by
    funext x; simp [he, MeasurableEquiv.coe_mulLeft₀]
  calc ∫⁻ x, H ((u : F) * x) ∂(selfDualHaarAt ℚ p) = ∫⁻ x, H (e x) ∂(selfDualHaarAt ℚ p) := by
        simp_rw [← hcoe]
    _ = ∫⁻ y, H y ∂(Measure.map e (selfDualHaarAt ℚ p)) := (lintegral_map_equiv H e).symm
    _ = ∫⁻ y, H y ∂(((modulus (u : F))⁻¹ : ℝ≥0) • (selfDualHaarAt ℚ p : Measure F)) := by
        rw [← hcoe, map_mul_left_selfDualHaarAt]
    _ = _ := by rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

theorem measure_unitBall_lt_top : (selfDualHaarAt ℚ p) {x : F | ‖x‖ ≤ 1} < ⊤ := by
  haveI := isAddHaarMeasure_selfDualHaarAt (p := p)
  have hsub : {x : F | ‖x‖ ≤ 1} = ((integersPositiveCompacts ℚ p : TopologicalSpace.PositiveCompacts F) : Set F) := by
    ext x
    show ‖x‖ ≤ 1 ↔ x ∈ ((integersPositiveCompacts ℚ p : TopologicalSpace.PositiveCompacts F) : Set F)
    rw [show ((integersPositiveCompacts ℚ p : TopologicalSpace.PositiveCompacts F) : Set F) =
        (p.adicCompletionIntegers ℚ : Set F) from rfl,
      SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]
  rw [hsub]
  exact (integersPositiveCompacts ℚ p).isCompact.measure_lt_top

theorem lintegral_indicator_norm_mul_le_one (u : Fˣ) :
    ∫⁻ x, {x : F | ‖(u : F) * x‖ ≤ 1}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂(selfDualHaarAt ℚ p) =
      ((modulus (u : F))⁻¹ : ℝ≥0) * (selfDualHaarAt ℚ p) {x : F | ‖x‖ ≤ 1} := by
  have hmeas : MeasurableSet {x : F | ‖x‖ ≤ 1} := (isClosed_le continuous_norm continuous_const).measurableSet
  rw [← lintegral_indicator_one hmeas, ← lintegral_comp_mul_left_selfDualHaarAt u]
  rfl

end Ws48DetInt

namespace Ws48DetInt

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction MeasureTheory
open scoped ENNReal NNReal Pointwise

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem ofReal_zpow_rpow (N : ℕ) (hN : 1 < N) (s : ℝ) (n : ℤ) :
    ENNReal.ofReal ((((N : ℝ)) ^ (-n)) ^ s) = (((N : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞) ^ n := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr0 : ((N : ℝ≥0) ^ (-s) : ℝ≥0) ≠ 0 := by
    apply ne_of_gt; exact NNReal.rpow_pos (by exact_mod_cast (show 0 < N by omega))
  rw [← ENNReal.coe_zpow hr0, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_zpow, NNReal.coe_rpow, NNReal.coe_natCast]
  congr 1
  rw [← Real.rpow_intCast _ (-n), ← Real.rpow_mul hN0, ← Real.rpow_intCast, ← Real.rpow_mul hN0]
  congr 1; push_cast; ring

theorem rN_lt_one (N : ℕ) (hN : 1 < N) (s : ℝ) (hs : 0 < s) : ((N : ℝ≥0) ^ (-s) : ℝ≥0) < 1 :=
  NNReal.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) (by linarith)

theorem rN_ne_zero (N : ℕ) (hN : 1 < N) (s : ℝ) : ((N : ℝ≥0) ^ (-s) : ℝ≥0) ≠ 0 := by
  apply ne_of_gt; exact NNReal.rpow_pos (by exact_mod_cast (show 0 < N by omega))

theorem norm_uniformizerUnit_zpow (m : ℤ) :
    ‖((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ m : Fˣ) : F)‖ = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ (-m) := by
  have hmem : (NumberField.AdelicLevel.uniformizerUnit ℚ p ^ m : Fˣ) ∈ shell p m := by
    show Valued.v (((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ m : Fˣ)) : F) = WithZero.exp (-m)
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul]
    congr 1; ring
  exact norm_eq_of_mem_shell hmem

theorem main (B t : ℝ) (ht : 1 < t) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure],
      ∫⁻ h : GL (Fin 2) (p.adicCompletion ℚ),
          Set.indicator {h : GL (Fin 2) (p.adicCompletion ℚ) | ∀ i j : Fin 2, ‖((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j‖ ≤ B} (fun _ => (1 : ENNReal)) h *
            ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ t) ∂ν < ⊤ := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro ν _
  haveI := isAddHaarMeasure_selfDualHaarAt (p := p)
  haveI := locallyCompactSpace_localGL ℚ p
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  set N : ℕ := Ideal.absNorm p.asIdeal with hNdef
  have hN : 1 < N := NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨b, hb⟩ : ∃ b : ℕ, B < (N : ℝ) ^ b := pow_unbounded_of_one_lt B hNR
  have ht0 : 0 < t := by linarith

  set ball : Set G₂ := {h | ∀ i j : Fin 2, ‖(h : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ B} with hballdef
  have hentry : ∀ i j : Fin 2, Continuous fun h : G₂ => (h : Matrix (Fin 2) (Fin 2) F) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have hball : MeasurableSet ball := by
    have : ball = ⋂ i : Fin 2, ⋂ j : Fin 2, {h : G₂ | ‖(h : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ B} := by
      ext h; simp [hballdef]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      (isClosed_le ((hentry i j).norm) continuous_const).measurableSet
  have hdet : Continuous fun h : G₂ => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) := by
    have : (fun h : G₂ => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F)) = fun h : G₂ => ((h : G₂) : Matrix (Fin 2) (Fin 2) F).det := by
      funext h; rw [Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]; exact Units.continuous_val.matrix_det
  set G : G₂ → ℝ≥0∞ := fun h => ball.indicator (fun _ => (1 : ℝ≥0∞)) h *
    ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖ ^ t) with hGdef
  have hGm : Measurable G :=
    ((measurable_const.indicator hball).mul (ENNReal.measurable_ofReal.comp ((hdet.norm.measurable).pow_const t)))
  show ∫⁻ h, G h ∂ν < ⊤

  obtain ⟨κ, hκ, hI⟩ :=
    LanglandsTunnell.RankinSelberg.exists_pos_forall_lintegral_eq_mul_lintegral_prod_lintegral_unipotent_diagUnits2 p ν
  rw [hI G hGm]

  set μx : Measure Fˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hμx
  set K₀ : Set G₂ := (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G₂) with hK₀
  set V : ℝ≥0∞ := (selfDualHaarAt ℚ p) {x : F | ‖x‖ ≤ 1} with hV
  set r : ℝ≥0 := (N : ℝ≥0) ^ (-(t - 1)) with hr
  have hr1 : r < 1 := rN_lt_one N hN (t - 1) (by linarith)
  have hr0 : r ≠ 0 := rN_ne_zero N hN (t - 1)

  set Ψ₁ : Fˣ → ℝ≥0∞ := fun a => {a : Fˣ | ‖(a : F)‖ ≤ (N : ℝ) ^ b}.indicator
    (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t * ‖(a : F)‖⁻¹)) a with hΨ₁
  set Ψ₂ : Fˣ → ℝ≥0∞ := fun a => {a : Fˣ | ‖(a : F)‖ ≤ (N : ℝ) ^ b}.indicator
    (fun a => ENNReal.ofReal (‖(a : F)‖ ^ t) * (ENNReal.ofReal ((N : ℝ) ^ b * ‖(a : F)‖⁻¹) * V) * ENNReal.ofReal ‖(a : F)‖) a with hΨ₂
  have hSmeas : MeasurableSet {a : Fˣ | ‖(a : F)‖ ≤ (N : ℝ) ^ b} := measurableSet_le measurable_units_norm measurable_const
  have hΨ₁m : Measurable Ψ₁ := by
    refine Measurable.indicator ?_ hSmeas
    exact ENNReal.measurable_ofReal.comp ((measurable_units_norm.pow_const t).mul measurable_units_norm.inv)
  have hΨ₂m : Measurable Ψ₂ := by
    refine Measurable.indicator ?_ hSmeas
    exact ((ENNReal.measurable_ofReal.comp (measurable_units_norm.pow_const t)).mul
      ((ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_units_norm.inv)).mul measurable_const)).mul
      (ENNReal.measurable_ofReal.comp measurable_units_norm)

  set ϖ : Fˣ := NumberField.AdelicLevel.uniformizerUnit ℚ p with hϖ
  have hϖb : ‖((ϖ ^ (b : ℤ) : Fˣ) : F)‖ = ((N : ℝ) ^ b)⁻¹ := by
    rw [hϖ, norm_uniformizerUnit_zpow, zpow_neg, zpow_natCast]
  have hNb : (0 : ℝ) < (N : ℝ) ^ b := by positivity

  have hA : ∀ (k : G₂), k ∈ K₀ → ∀ (a₁ a₂ : Fˣ),
      (∫⁻ x : F, G (unipotent x * diagUnits2 a₁ a₂ * k) ∂(selfDualHaarAt ℚ p)) *
          (modulus ((a₂ * a₁⁻¹ : Fˣ) : F) : ℝ≥0∞) ≤ Ψ₁ a₁ * Ψ₂ a₂ := by
    intro k hk a₁ a₂
    by_cases hS : ‖(a₁ : F)‖ ≤ B ∧ ‖(a₂ : F)‖ ≤ B
    · have h1 : 0 < ‖(a₁ : F)‖ := norm_pos_iff.mpr a₁.ne_zero
      have h2 : 0 < ‖(a₂ : F)‖ := norm_pos_iff.mpr a₂.ne_zero
      set u : Fˣ := a₂ * ϖ ^ (b : ℤ) with hu
      have hnu : ‖(u : F)‖ = ‖(a₂ : F)‖ * ((N : ℝ) ^ b)⁻¹ := by
        rw [hu, Units.val_mul, norm_mul, hϖb]
      have hpt : ∀ x : F, G (unipotent x * diagUnits2 a₁ a₂ * k) ≤
          ENNReal.ofReal ((‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ t) *
            {x : F | ‖(u : F) * x‖ ≤ 1}.indicator (fun _ => (1 : ℝ≥0∞)) x := by
        intro x
        simp only [hGdef]
        by_cases hmem : (unipotent x * diagUnits2 a₁ a₂ * k) ∈ ball
        · rw [Set.indicator_of_mem hmem, one_mul, norm_det_coords hk, Set.indicator_of_mem, mul_one]
          show ‖(u : F) * x‖ ≤ 1
          have hx := (coords_of_mem_ball hk hmem).2.2
          rw [norm_mul, hnu]
          calc ‖(a₂ : F)‖ * ((N : ℝ) ^ b)⁻¹ * ‖x‖ = (‖x‖ * ‖(a₂ : F)‖) * ((N : ℝ) ^ b)⁻¹ := by ring
            _ ≤ B * ((N : ℝ) ^ b)⁻¹ := by gcongr
            _ ≤ (N : ℝ) ^ b * ((N : ℝ) ^ b)⁻¹ := by gcongr
            _ = 1 := mul_inv_cancel₀ hNb.ne'
        · rw [Set.indicator_of_notMem hmem, zero_mul]; exact bot_le
      have hmeasU : MeasurableSet {x : F | ‖(u : F) * x‖ ≤ 1} :=
        (isClosed_le ((continuous_const.mul continuous_id).norm) continuous_const).measurableSet
      have hint : (∫⁻ x : F, G (unipotent x * diagUnits2 a₁ a₂ * k) ∂(selfDualHaarAt ℚ p)) ≤
          ENNReal.ofReal ((‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ t) * (ENNReal.ofReal ((N : ℝ) ^ b * ‖(a₂ : F)‖⁻¹) * V) := by
        calc (∫⁻ x : F, G (unipotent x * diagUnits2 a₁ a₂ * k) ∂(selfDualHaarAt ℚ p))
            ≤ ∫⁻ x : F, ENNReal.ofReal ((‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ t) *
                {x : F | ‖(u : F) * x‖ ≤ 1}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂(selfDualHaarAt ℚ p) := lintegral_mono hpt
          _ = ENNReal.ofReal ((‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ t) * (((modulus (u : F))⁻¹ : ℝ≥0) * V) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_norm_mul_le_one]
          _ = _ := by
              congr 2
              rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv,
                coe_nnnorm, hnu, mul_inv, inv_inv, mul_comm]
      have hmod : (modulus ((a₂ * a₁⁻¹ : Fˣ) : F) : ℝ≥0∞) = ENNReal.ofReal (‖(a₂ : F)‖ * ‖(a₁ : F)‖⁻¹) := by
        rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Units.val_mul,
          norm_mul, Units.val_inv_eq_inv_val, norm_inv]
      have hin1 : a₁ ∈ {a : Fˣ | ‖(a : F)‖ ≤ (N : ℝ) ^ b} := le_of_lt (hS.1.trans_lt hb)
      have hin2 : a₂ ∈ {a : Fˣ | ‖(a : F)‖ ≤ (N : ℝ) ^ b} := le_of_lt (hS.2.trans_lt hb)
      rw [hmod]
      simp only [hΨ₁, hΨ₂, Set.indicator_of_mem hin1, Set.indicator_of_mem hin2]
      calc (∫⁻ x : F, G (unipotent x * diagUnits2 a₁ a₂ * k) ∂(selfDualHaarAt ℚ p)) * ENNReal.ofReal (‖(a₂ : F)‖ * ‖(a₁ : F)‖⁻¹)
          ≤ ENNReal.ofReal ((‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ t) * (ENNReal.ofReal ((N : ℝ) ^ b * ‖(a₂ : F)‖⁻¹) * V) *
              ENNReal.ofReal (‖(a₂ : F)‖ * ‖(a₁ : F)‖⁻¹) := by gcongr
        _ = (ENNReal.ofReal ((N : ℝ) ^ b * ‖(a₂ : F)‖⁻¹) * V) *
              (ENNReal.ofReal ((‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ t) * ENNReal.ofReal (‖(a₂ : F)‖ * ‖(a₁ : F)‖⁻¹)) := by ring
        _ = (ENNReal.ofReal ((N : ℝ) ^ b * ‖(a₂ : F)‖⁻¹) * V) *
              ENNReal.ofReal ((‖(a₁ : F)‖ * ‖(a₂ : F)‖) ^ t * (‖(a₂ : F)‖ * ‖(a₁ : F)‖⁻¹)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
        _ = (ENNReal.ofReal ((N : ℝ) ^ b * ‖(a₂ : F)‖⁻¹) * V) *
              ENNReal.ofReal ((‖(a₁ : F)‖ ^ t * ‖(a₁ : F)‖⁻¹) * (‖(a₂ : F)‖ ^ t * ‖(a₂ : F)‖)) := by
            congr 2
            rw [Real.mul_rpow h1.le h2.le]; ring
        _ = (ENNReal.ofReal ((N : ℝ) ^ b * ‖(a₂ : F)‖⁻¹) * V) *
              (ENNReal.ofReal (‖(a₁ : F)‖ ^ t * ‖(a₁ : F)‖⁻¹) * (ENNReal.ofReal (‖(a₂ : F)‖ ^ t) * ENNReal.ofReal ‖(a₂ : F)‖)) := by
            rw [ENNReal.ofReal_mul (q := ‖(a₂ : F)‖ ^ t * ‖(a₂ : F)‖) (by positivity),
              ENNReal.ofReal_mul (q := ‖(a₂ : F)‖) (by positivity)]
        _ = _ := by ring
    · have hzero : ∀ x : F, G (unipotent x * diagUnits2 a₁ a₂ * k) = 0 := by
        intro x
        simp only [hGdef]
        rw [Set.indicator_of_notMem, zero_mul]
        intro hmem
        exact hS ⟨(coords_of_mem_ball hk hmem).1, (coords_of_mem_ball hk hmem).2.1⟩
      simp only [hzero, lintegral_zero, zero_mul, zero_le]

  obtain ⟨hmeasS, huniq, hmass, -, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  haveI : SigmaFinite μx := by
    refine Measure.sigmaFinite_of_countable (S := Set.range (shell p)) (Set.countable_range _) ?_ ?_
    · rintro s ⟨n, rfl⟩; exact (hmass n).2.2
    · rw [Set.sUnion_range]; ext y
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨n, hn, -⟩ := huniq y; exact ⟨n, hn⟩

  obtain ⟨hK₀c, hK₀o⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (⊤ : Ideal (𝓞 ℚ)) top_ne_bot
  have hK₀m : MeasurableSet K₀ := hK₀o.measurableSet
  have hB : (∫⁻ q : G₂ × (Fˣ × Fˣ), (∫⁻ x : F, G (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1) ∂(selfDualHaarAt ℚ p)) *
        (modulus ((q.2.2 * q.2.1⁻¹ : Fˣ) : F) : ℝ≥0∞) ∂((ν.restrict K₀).prod (μx.prod μx))) ≤
      ∫⁻ q : G₂ × (Fˣ × Fˣ), Ψ₁ q.2.1 * Ψ₂ q.2.2 ∂((ν.restrict K₀).prod (μx.prod μx)) := by
    rw [Measure.restrict_prod_eq_prod_univ K₀]
    refine setLIntegral_mono' (hK₀m.prod MeasurableSet.univ) fun q hq => ?_
    exact hA q.1 hq.1 q.2.1 q.2.2

  have hC : (∫⁻ q : G₂ × (Fˣ × Fˣ), Ψ₁ q.2.1 * Ψ₂ q.2.2 ∂((ν.restrict K₀).prod (μx.prod μx))) =
      ν K₀ * ((∫⁻ a, Ψ₁ a ∂μx) * ∫⁻ a, Ψ₂ a ∂μx) := by
    have e1 : (∫⁻ q : G₂ × (Fˣ × Fˣ), Ψ₁ q.2.1 * Ψ₂ q.2.2 ∂((ν.restrict K₀).prod (μx.prod μx))) =
        ∫⁻ q : G₂ × (Fˣ × Fˣ), (fun _ : G₂ => (1 : ℝ≥0∞)) q.1 * (fun a : Fˣ × Fˣ => Ψ₁ a.1 * Ψ₂ a.2) q.2
          ∂((ν.restrict K₀).prod (μx.prod μx)) := by simp only [one_mul]
    have hprodm : Measurable (fun a : Fˣ × Fˣ => Ψ₁ a.1 * Ψ₂ a.2) :=
      (hΨ₁m.comp measurable_fst).mul (hΨ₂m.comp measurable_snd)
    rw [e1, lintegral_prod_mul (f := fun _ : G₂ => (1 : ℝ≥0∞)) (g := fun a : Fˣ × Fˣ => Ψ₁ a.1 * Ψ₂ a.2)
      aemeasurable_const hprodm.aemeasurable,
      lintegral_const, Measure.restrict_apply_univ, one_mul,
      lintegral_prod_mul (f := Ψ₁) (g := Ψ₂) hΨ₁m.aemeasurable hΨ₂m.aemeasurable]

  have hzpow_le : ∀ (n : ℤ), ((N : ℝ)) ^ (-n) ≤ (N : ℝ) ^ b → -(b : ℤ) ≤ n := by
    intro n h
    rw [← zpow_natCast] at h
    have := (zpow_le_zpow_iff_right₀ hNR).mp h
    omega
  have hD1 : (∫⁻ a, Ψ₁ a ∂μx) < ⊤ := by
    have hle := lintegral_units_le_tsum (p := p) Ψ₁ (fun n => if (-(b : ℤ) ≤ n) then ((r : ℝ≥0∞) ^ n) else 0) ?_
    · exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (tsum_indicator_zpow_lt_top r hr0 hr1 b) measure_shell_zero_lt_top)
    · intro n y hy
      have hny := norm_eq_of_mem_shell hy
      simp only [hΨ₁]
      by_cases hyb : y ∈ {a : Fˣ | ‖(a : F)‖ ≤ (N : ℝ) ^ b}
      · have hyb' : ‖(y : F)‖ ≤ (N : ℝ) ^ b := hyb
        have hnb : -(b : ℤ) ≤ n := hzpow_le n (hny ▸ hyb')
        rw [Set.indicator_of_mem hyb, if_pos hnb]
        have hy0 : ‖(y : F)‖ ≠ 0 := norm_ne_zero_iff.mpr y.ne_zero
        rw [show ‖(y : F)‖ ^ t * ‖(y : F)‖⁻¹ = ‖(y : F)‖ ^ (t - 1) from by rw [Real.rpow_sub_one hy0]; ring, hny, hr,
          ofReal_zpow_rpow N hN (t - 1) n]
      · rw [Set.indicator_of_notMem hyb]; exact bot_le
  set r₂ : ℝ≥0 := (N : ℝ≥0) ^ (-t) with hr₂
  have hr₂1 : r₂ < 1 := rN_lt_one N hN t ht0
  have hr₂0 : r₂ ≠ 0 := rN_ne_zero N hN t
  have hV : V < ⊤ := measure_unitBall_lt_top
  have hD2 : (∫⁻ a, Ψ₂ a ∂μx) < ⊤ := by
    have hle := lintegral_units_le_tsum (p := p) Ψ₂
      (fun n => if (-(b : ℤ) ≤ n) then (V * ENNReal.ofReal ((N : ℝ) ^ b)) * ((r₂ : ℝ≥0∞) ^ n) else 0) ?_
    · refine lt_of_le_of_lt hle (ENNReal.mul_lt_top ?_ measure_shell_zero_lt_top)
      have : (fun n : ℤ => if (-(b : ℤ) ≤ n) then (V * ENNReal.ofReal ((N : ℝ) ^ b)) * ((r₂ : ℝ≥0∞) ^ n) else 0) =
          fun n : ℤ => (V * ENNReal.ofReal ((N : ℝ) ^ b)) * (if (-(b : ℤ) ≤ n) then ((r₂ : ℝ≥0∞) ^ n) else 0) := by
        funext n; split_ifs <;> simp
      rw [this, ENNReal.tsum_mul_left]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hV ENNReal.ofReal_lt_top) (tsum_indicator_zpow_lt_top r₂ hr₂0 hr₂1 b)
    · intro n y hy
      have hny := norm_eq_of_mem_shell hy
      simp only [hΨ₂]
      by_cases hyb : y ∈ {a : Fˣ | ‖(a : F)‖ ≤ (N : ℝ) ^ b}
      · have hyb' : ‖(y : F)‖ ≤ (N : ℝ) ^ b := hyb
        have hnb : -(b : ℤ) ≤ n := hzpow_le n (hny ▸ hyb')
        rw [Set.indicator_of_mem hyb, if_pos hnb]
        have hy0 : ‖(y : F)‖ ≠ 0 := norm_ne_zero_iff.mpr y.ne_zero
        have hypos : 0 ≤ ‖(y : F)‖ := norm_nonneg _
        calc ENNReal.ofReal (‖(y : F)‖ ^ t) * (ENNReal.ofReal ((N : ℝ) ^ b * ‖(y : F)‖⁻¹) * V) * ENNReal.ofReal ‖(y : F)‖
            = V * (ENNReal.ofReal ((N : ℝ) ^ b * ‖(y : F)‖⁻¹) * ENNReal.ofReal ‖(y : F)‖) * ENNReal.ofReal (‖(y : F)‖ ^ t) := by ring
          _ = V * ENNReal.ofReal ((N : ℝ) ^ b) * ENNReal.ofReal (‖(y : F)‖ ^ t) := by
              rw [← ENNReal.ofReal_mul (by positivity), show (N : ℝ) ^ b * ‖(y : F)‖⁻¹ * ‖(y : F)‖ = (N : ℝ) ^ b from by
                field_simp]
          _ ≤ _ := by rw [hny, hr₂, ofReal_zpow_rpow N hN t n]
      · rw [Set.indicator_of_notMem hyb]; exact bot_le

  have hνK : ν K₀ < ⊤ := hK₀c.measure_lt_top
  calc ENNReal.ofReal κ * (∫⁻ q : G₂ × (Fˣ × Fˣ), (∫⁻ x : F, G (unipotent x * diagUnits2 q.2.1 q.2.2 * q.1) ∂(selfDualHaarAt ℚ p)) *
        (modulus ((q.2.2 * q.2.1⁻¹ : Fˣ) : F) : ℝ≥0∞) ∂((ν.restrict K₀).prod (μx.prod μx)))
      ≤ ENNReal.ofReal κ * (ν K₀ * ((∫⁻ a, Ψ₁ a ∂μx) * ∫⁻ a, Ψ₂ a ∂μx)) := by
        rw [← hC]; exact mul_le_mul_right hB _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hνK (ENNReal.mul_lt_top hD1 hD2))

end Ws48DetInt

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (B t : ℝ) (ht : 1 < t) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure],
      ∫⁻ h : GL (Fin 2) (p.adicCompletion ℚ),
          Set.indicator {h : GL (Fin 2) (p.adicCompletion ℚ) | ∀ i j : Fin 2, ‖((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j‖ ≤ B} (fun _ => (1 : ENNReal)) h *
            ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ t) ∂ν < ⊤ :=
  Ws48DetInt.main B t ht

end S_AutomorphicForm_lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top
end P2MW
export P2MW.S_AutomorphicForm_lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top (solution)
