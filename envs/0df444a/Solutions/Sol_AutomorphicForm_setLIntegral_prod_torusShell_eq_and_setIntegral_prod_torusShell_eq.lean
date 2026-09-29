-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_prod_torusShell_eq_and_setIntegral_prod_torusShell_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e41fc742-0608-5f0c-bd93-1a82404ae833

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_Idele_secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setLIntegral_prod_torusShell_eq_and_setIntegral_prod_torusShell_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 globalPoints centralScalar gl2Weyl adelicWeyl"
namespace ProdEval
p2m_open "AutomorphicForm"

variable (L : Type) [Field L] [NumberField L]

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L z) = z * z := by
  apply Units.ext
  simp [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.scalar]
  ring

theorem det_diagOne (t : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne t) = t := by
  apply Units.ext
  simp [diagOne, Matrix.det_fin_two]

theorem adelicWeyl_mul_diagOne (t : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.adelicWeyl (𝓞 L) L * diagOne t =
      AutomorphicForm.centralScalar (𝓞 L) L t * diagOne t⁻¹ * AutomorphicForm.adelicWeyl (𝓞 L) L := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, AutomorphicForm.adelicWeyl, AutomorphicForm.globalPoints, AutomorphicForm.gl2Weyl,
    AutomorphicForm.centralScalar, diagOne]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar,
      Matrix.diagonal]

theorem ideleNorm_det_psi_mul (z t : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    NumberField.TateGlobal.ideleNorm L
        (Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne t * y)) =
      NumberField.TateGlobal.ideleNorm L z ^ 2 * NumberField.TateGlobal.ideleNorm L t *
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) := by
  rw [map_mul, map_mul, det_centralScalar, det_diagOne, NumberField.TateGlobal.ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul]
  ring

theorem adelicHeight_psi_mul (z t : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne t * y) =
      NumberField.TateGlobal.ideleNorm L t * NumberField.AdelicHeight.adelicHeight L y := by
  rw [mul_assoc, (NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul L).2,
    NumberField.AdelicHeight.adelicHeight_diagOne_mul]

theorem ideleNorm_inv (t : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L t⁻¹ = (NumberField.TateGlobal.ideleNorm L t)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := L) t⁻¹ t
  rw [inv_mul_cancel] at h
  have h1 : NumberField.TateGlobal.ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
    have h' := NumberField.TateGlobal.ideleNorm_mul (F := L) 1 1
    rw [one_mul] at h'
    have hp := NumberField.TateGlobal.ideleNorm_pos (F := L) 1
    field_simp at h'
    nlinarith [h', hp]
  rw [h1] at h
  have hp := NumberField.TateGlobal.ideleNorm_pos (F := L) t
  field_simp
  linarith

theorem adelicHeight_weyl_psi_mul (z t : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    NumberField.AdelicHeight.adelicHeight L
        (AutomorphicForm.adelicWeyl (𝓞 L) L * (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne t * y)) =
      (NumberField.TateGlobal.ideleNorm L t)⁻¹ *
        NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y) := by
  have hWD := adelicWeyl_mul_diagOne L t
  set w := AutomorphicForm.adelicWeyl (𝓞 L) L with hw
  set cz := AutomorphicForm.centralScalar (𝓞 L) L z with hcz
  set ct := AutomorphicForm.centralScalar (𝓞 L) L t with hct
  have hcomm : w * cz = cz * w := by
    have hz : cz ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
      rw [hcz, Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨z, rfl⟩
    exact (Subgroup.mem_center_iff.mp hz) w
  have key : w * (cz * diagOne t * y) = cz * (ct * (diagOne t⁻¹ * (w * y))) := by
    calc w * (cz * diagOne t * y) = (w * cz) * diagOne t * y := by group
      _ = (cz * w) * diagOne t * y := by rw [hcomm]
      _ = cz * (w * diagOne t) * y := by group
      _ = cz * (ct * diagOne t⁻¹ * w) * y := by rw [hWD]
      _ = cz * (ct * (diagOne t⁻¹ * (w * y))) := by group
  rw [key, hcz, (NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul L).2, hct,
    (NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul L).2,
    NumberField.AdelicHeight.adelicHeight_diagOne_mul, ideleNorm_inv]

section pointwise
variable (K : Type) [Field K] [NumberField K] [Algebra K L]

noncomputable def bfun (ℓ : ℕ) (R Hy Hwy s : ℝ) : ℂ :=
  (1 : ℂ) - (if Real.exp R < s ^ ℓ * Hy then 1 else 0) - (if Real.exp R < (s ^ ℓ)⁻¹ * Hwy then 1 else 0)

theorem thr2 (ℓ : ℕ) (hℓ : 0 < ℓ) (R Hy s : ℝ) (hHy : 0 < Hy) (hs : 0 < s) :
    Real.exp R < s ^ ℓ * Hy ↔ Real.exp ((R - Real.log Hy) / ℓ) < s := by
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hsl : 0 < s ^ ℓ := pow_pos hs ℓ
  rw [← Real.log_lt_log_iff (Real.exp_pos R) (mul_pos hsl hHy), Real.log_exp, Real.log_mul hsl.ne' hHy.ne',
    Real.log_pow, ← Real.lt_log_iff_exp_lt hs, div_lt_iff₀ hℓr]
  constructor <;> intro h <;> linarith

theorem thr1 (ℓ : ℕ) (hℓ : 0 < ℓ) (R Hwy s : ℝ) (hHwy : 0 < Hwy) (hs : 0 < s) :
    Real.exp R < (s ^ ℓ)⁻¹ * Hwy ↔ s < Real.exp ((Real.log Hwy - R) / ℓ) := by
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hsl : 0 < s ^ ℓ := pow_pos hs ℓ
  rw [← Real.log_lt_log_iff (Real.exp_pos R) (mul_pos (inv_pos.mpr hsl) hHwy), Real.log_exp,
    Real.log_mul (inv_pos.mpr hsl).ne' hHwy.ne', Real.log_inv, Real.log_pow, ← Real.log_lt_iff_lt_exp hs,
    lt_div_iff₀ hℓr]
  constructor <;> intro h <;> linarith

theorem norm_bfun_eq_indicator (ℓ : ℕ) (hℓ : 0 < ℓ) (R Hy Hwy s : ℝ) (hHy : 0 < Hy) (hHwy : 0 < Hwy) (hs : 0 < s) :
    ‖bfun ℓ R Hy Hwy s‖ =
      if (Real.exp ((Real.log Hwy - R) / ℓ) ≤ s ∧ s ≤ Real.exp ((R - Real.log Hy) / ℓ)) ∨
          (Real.exp ((R - Real.log Hy) / ℓ) < s ∧ s < Real.exp ((Real.log Hwy - R) / ℓ)) then 1 else 0 := by
  have e2 := thr2 ℓ hℓ R Hy s hHy hs
  have e1 := thr1 ℓ hℓ R Hwy s hHwy hs
  simp only [bfun]
  by_cases ha : Real.exp R < s ^ ℓ * Hy
  · have ha' := e2.mp ha
    by_cases hb : Real.exp R < (s ^ ℓ)⁻¹ * Hwy
    · have hb' := e1.mp hb
      rw [if_pos ha, if_pos hb, if_pos (Or.inr ⟨ha', hb'⟩)]; norm_num
    · have hb' : ¬ s < Real.exp ((Real.log Hwy - R) / ℓ) := fun h => hb (e1.mpr h)
      rw [if_pos ha, if_neg hb, if_neg (by
        rintro (⟨-, h2⟩ | ⟨-, h2⟩)
        · exact absurd ha' (not_lt.mpr h2)
        · exact hb' h2)]
      norm_num
  · have ha' : ¬ Real.exp ((R - Real.log Hy) / ℓ) < s := fun h => ha (e2.mpr h)
    by_cases hb : Real.exp R < (s ^ ℓ)⁻¹ * Hwy
    · have hb' := e1.mp hb
      rw [if_neg ha, if_pos hb, if_neg (by
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact absurd hb' (not_lt.mpr h1)
        · exact ha' h1)]
      norm_num
    · have hb' : ¬ s < Real.exp ((Real.log Hwy - R) / ℓ) := fun h => hb (e1.mpr h)
      rw [if_neg ha, if_neg hb, if_pos (Or.inl ⟨not_lt.mp hb', not_lt.mp ha'⟩)]; norm_num

theorem bfun_eq_indicator_of_le (ℓ : ℕ) (hℓ : 0 < ℓ) (R Hy Hwy s : ℝ) (hHy : 0 < Hy) (hHwy : 0 < Hwy) (hs : 0 < s)
    (hA : Hy * Hwy ≤ Real.exp (2 * R)) :
    bfun ℓ R Hy Hwy s =
      if (Real.exp ((Real.log Hwy - R) / ℓ) ≤ s ∧ s ≤ Real.exp ((R - Real.log Hy) / ℓ)) then 1 else 0 := by
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hu : Real.exp ((Real.log Hwy - R) / ℓ) ≤ Real.exp ((R - Real.log Hy) / ℓ) := by
    rw [Real.exp_le_exp]
    have := (Real.log_le_log_iff (mul_pos hHy hHwy) (Real.exp_pos _)).mpr hA
    rw [Real.log_mul hHy.ne' hHwy.ne', Real.log_exp] at this
    have h' : Real.log Hwy - R ≤ R - Real.log Hy := by linarith
    exact div_le_div_of_nonneg_right h' hℓr.le
  have e2 := thr2 ℓ hℓ R Hy s hHy hs
  have e1 := thr1 ℓ hℓ R Hwy s hHwy hs
  simp only [bfun]
  by_cases ha : Real.exp R < s ^ ℓ * Hy
  · have ha' := e2.mp ha
    have hb : ¬ Real.exp R < (s ^ ℓ)⁻¹ * Hwy := fun h => absurd (hu.trans ha'.le) (not_le.mpr (e1.mp h))
    rw [if_pos ha, if_neg hb, if_neg (fun h => absurd h.2 (not_le.mpr ha'))]; norm_num
  · have ha' : ¬ Real.exp ((R - Real.log Hy) / ℓ) < s := fun h => ha (e2.mpr h)
    by_cases hb : Real.exp R < (s ^ ℓ)⁻¹ * Hwy
    · have hb' := e1.mp hb
      rw [if_neg ha, if_pos hb, if_neg (fun h => absurd h.1 (not_le.mpr hb'))]; norm_num
    · have hb' : ¬ s < Real.exp ((Real.log Hwy - R) / ℓ) := fun h => hb (e1.mpr h)
      rw [if_neg ha, if_neg hb, if_pos ⟨not_lt.mp hb', not_lt.mp ha'⟩]; norm_num

end pointwise

end AutomorphicForm.ProdEval

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 globalPoints centralScalar gl2Weyl adelicWeyl"
namespace ProdEval
p2m_open "AutomorphicForm"
section measlemmas

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) (Ω : Set X) (nrm : X → ℝ) (V : ℝ)

theorem measure_inter_shell_eq_ofReal (hVpos : 0 < V)
    (hV : ∀ a b : ℝ, 0 < a → a ≤ b → ν.real (Ω ∩ {x | nrm x ∈ Set.Icc a b}) = V * (Real.log b - Real.log a))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ν (Ω ∩ {x | nrm x ∈ Set.Icc a b}) = ENNReal.ofReal (V * (Real.log b - Real.log a)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hbe : b ≤ b * Real.exp 1 := by nlinarith [Real.add_one_le_exp (1:ℝ)]
  have hbig := hV a (b * Real.exp 1) ha (hab.trans hbe)
  have hbigpos : 0 < V * (Real.log (b * Real.exp 1) - Real.log a) := by
    rw [Real.log_mul hb.ne' (Real.exp_pos 1).ne', Real.log_exp]
    have := Real.log_le_log ha hab
    nlinarith
  have hne : ν (Ω ∩ {x | nrm x ∈ Set.Icc a (b * Real.exp 1)}) ≠ ⊤ := by
    intro htop
    rw [Measure.real, htop, ENNReal.toReal_top] at hbig
    linarith
  have hsub : Ω ∩ {x | nrm x ∈ Set.Icc a b} ⊆ Ω ∩ {x | nrm x ∈ Set.Icc a (b * Real.exp 1)} := by
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans hbe⟩
  have hfin : ν (Ω ∩ {x | nrm x ∈ Set.Icc a b}) ≠ ⊤ := ne_top_of_le_ne_top hne (measure_mono hsub)
  rw [← hV a b ha hab, Measure.real, ENNReal.ofReal_toReal hfin]

theorem measure_inter_level_eq_zero (hVpos : 0 < V)
    (hV : ∀ a b : ℝ, 0 < a → a ≤ b → ν.real (Ω ∩ {x | nrm x ∈ Set.Icc a b}) = V * (Real.log b - Real.log a))
    (u : ℝ) (hu : 0 < u) :
    ν (Ω ∩ {x | nrm x = u}) = 0 := by
  refine le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  rw [zero_add]
  have hε' : 0 < (ε : ℝ) / V := by positivity
  set b : ℝ := u * Real.exp ((ε : ℝ) / V) with hb
  have hub : u ≤ b := by
    have h1 : 1 ≤ Real.exp ((ε : ℝ) / V) := by linarith [Real.add_one_le_exp ((ε:ℝ)/V)]
    rw [hb]; exact le_mul_of_one_le_right hu.le h1
  have hm := measure_inter_shell_eq_ofReal ν Ω nrm V hVpos hV u b hu hub
  have hval : V * (Real.log b - Real.log u) = ε := by
    rw [hb, Real.log_mul hu.ne' (Real.exp_pos _).ne', Real.log_exp]; field_simp; ring
  calc ν (Ω ∩ {x | nrm x = u}) ≤ ν (Ω ∩ {x | nrm x ∈ Set.Icc u b}) := by
        apply measure_mono
        intro x hx
        refine ⟨hx.1, ?_⟩
        have hxu : nrm x = u := hx.2
        show nrm x ∈ Set.Icc u b
        rw [hxu]; exact ⟨le_rfl, hub⟩
    _ = ENNReal.ofReal ε := by rw [hm, hval]
    _ = (ε : ENNReal) := ENNReal.ofReal_coe_nnreal

theorem setOf_sq_mul_mem_Icc (hpos : ∀ x, 0 < nrm x) (m α β : ℝ) (hm : 0 < m) :
    {x | nrm x ^ 2 * m ∈ Set.Icc α β} = {x | nrm x ∈ Set.Icc (Real.sqrt (α / m)) (Real.sqrt (β / m))} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  have hx := hpos x
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [← Real.sqrt_sq hx.le]
      exact Real.sqrt_le_sqrt (by rw [div_le_iff₀ hm]; linarith)
    · rw [← Real.sqrt_sq hx.le]
      exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hm]; linarith)
  · rintro ⟨h1, h2⟩
    constructor
    · have hsq : Real.sqrt (α / m) ^ 2 ≤ nrm x ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      by_cases hαm : 0 ≤ α / m
      · rw [Real.sq_sqrt hαm, div_le_iff₀ hm] at hsq; linarith
      · push_neg at hαm
        have : α < 0 := by
          by_contra h; push_neg at h; exact absurd (div_nonneg h hm.le) (not_le.mpr hαm)
        nlinarith [sq_nonneg (nrm x)]
    · have hβm : 0 ≤ β / m := by
        by_contra hneg
        push_neg at hneg
        have : Real.sqrt (β / m) = 0 := Real.sqrt_eq_zero'.mpr hneg.le
        rw [this] at h2; linarith
      have hsq : nrm x ^ 2 ≤ Real.sqrt (β / m) ^ 2 := pow_le_pow_left₀ hx.le h2 2
      rw [Real.sq_sqrt hβm, le_div_iff₀ hm] at hsq; linarith

end measlemmas
end AutomorphicForm.ProdEval

open scoped TensorProduct.RightActions in
open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_setLIntegral_prod_torusShell_eq_and_setIntegral_prod_torusShell_eq.AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ)
    (hθn : ∀ a, NumberField.TateGlobal.ideleNorm L (θ a) = NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L)
    (y : AdelicGL2 (𝓞 L) L) (R : ℝ) :
    (∫⁻ p in ΩL ×ˢ ΩK, ‖(Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))‖ₑ ∂(νZL.prod νK) =
      ENNReal.ofReal (((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      Real.log (β / α) / (2 * Module.finrank K L)) * |(2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
            - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))|)) ∧
    (NumberField.AdelicHeight.adelicHeight L y *
        NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y) ≤ Real.exp (2 * R) →
      IntegrableOn (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))) (ΩL ×ˢ ΩK) (νZL.prod νK) ∧
      ∫ p in ΩL ×ˢ ΩK, (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y))) ∂(νZL.prod νK) =
        ((((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      Real.log (β / α) / (2 * Module.finrank K L)) * (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
            - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))) : ℝ) : ℂ))  := by
  classical
  have hℓpos : 0 < Module.finrank K L := Module.finrank_pos
  have hℓr : (0 : ℝ) < (Module.finrank K L : ℕ) := by exact_mod_cast hℓpos
  have hHy0 : 0 < NumberField.AdelicHeight.adelicHeight L y := NumberField.AdelicHeight.adelicHeight_pos y
  have hHwy0 : 0 < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y) := NumberField.AdelicHeight.adelicHeight_pos _
  have hdy0 : 0 < NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) := NumberField.TateGlobal.ideleNorm_pos _

  have hpt : ∀ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
      (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y))) =
      (if NumberField.TateGlobal.ideleNorm L p.1 ^ 2 * NumberField.TateGlobal.ideleNorm K p.2 ^ Module.finrank K L * NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ∈
          Set.Icc α β then (1 : ℂ) else 0) *
        AutomorphicForm.ProdEval.bfun (Module.finrank K L) R (NumberField.AdelicHeight.adelicHeight L y) (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) (NumberField.TateGlobal.ideleNorm K p.2) := by
    intro p
    simp only [Set.indicator_apply, Set.mem_setOf_eq, AutomorphicForm.ProdEval.bfun,
      AutomorphicForm.ProdEval.ideleNorm_det_psi_mul L, AutomorphicForm.ProdEval.adelicHeight_psi_mul L,
      AutomorphicForm.ProdEval.adelicHeight_weyl_psi_mul L, hθn]

  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ :=
    (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box L L).1
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.Idele.secondCountableTopology_and_semiLocalUnits_and_archUnits_and_integralUnits_and_surjective_and_isCompact_box K K).1

  obtain ⟨VL, hVL, hVL1, -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      L L νZL ΩL hΩL (MonoidHom.id _) continuous_id 1 one_pos (fun y => by simp)
  obtain ⟨VK, hVK, hVK1, -⟩ :=
    NumberField.AdelicHeight.exists_forall_measureReal_inter_ideleNorm_mem_Icc_eq_mul_log_and_setIntegral_weight_comp_eq
      K L νK ΩK hΩK θ hθ (Module.finrank K L) Module.finrank_pos hθn
  have hVLeq : (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal = VL := by
    have := hVL1 1 (Real.exp 1) one_pos (by have := Real.add_one_le_exp (1:ℝ); linarith)
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one] at this
    rw [← this, Measure.real]
  have hVKeq : (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal = VK := by
    have := hVK1 1 (Real.exp 1) one_pos (by have := Real.add_one_le_exp (1:ℝ); linarith)
    rw [Real.log_exp, Real.log_one, sub_zero, mul_one] at this
    rw [← this, Measure.real]
  rw [hVLeq, hVKeq]

  have hzshell : ∀ m : ℝ, 0 < m →
      νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ^ 2 * m ∈ Set.Icc α β}) =
        ENNReal.ofReal (VL * (Real.log β - Real.log α) / 2) := by
    intro m hm
    rw [AutomorphicForm.ProdEval.setOf_sq_mul_mem_Icc (NumberField.TateGlobal.ideleNorm L)
      (fun z => NumberField.TateGlobal.ideleNorm_pos z) m α β hm,
      AutomorphicForm.ProdEval.measure_inter_shell_eq_ofReal νZL ΩL (NumberField.TateGlobal.ideleNorm L) VL hVL hVL1
        _ _ (Real.sqrt_pos.mpr (div_pos hα hm)) (Real.sqrt_le_sqrt (by gcongr))]
    congr 1
    rw [Real.log_sqrt (div_pos hα hm).le, Real.log_sqrt (div_pos (hα.trans hαβ) hm).le,
      Real.log_div (hα.trans hαβ).ne' hm.ne', Real.log_div hα.ne' hm.ne']
    ring

  have hashell : νK (ΩK ∩ {a | (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)) ≤ NumberField.TateGlobal.ideleNorm K a ∧
        NumberField.TateGlobal.ideleNorm K a ≤ Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) ∨
        (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ)) < NumberField.TateGlobal.ideleNorm K a ∧ NumberField.TateGlobal.ideleNorm K a < Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)))}) =
      ENNReal.ofReal (VK * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))| / (Module.finrank K L : ℕ)) := by
    have hu₁ : 0 < Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)) := Real.exp_pos _
    have hu₂ : 0 < Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ)) := Real.exp_pos _
    have hlog : Real.log (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) - Real.log (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))) =
        (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))) / (Module.finrank K L : ℕ) := by
      rw [Real.log_exp, Real.log_exp]; field_simp; ring
    by_cases hcase : Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)) ≤ Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))
    ·
      have hA : 0 ≤ (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))) / (Module.finrank K L : ℕ) := by
        rw [← hlog]; linarith [Real.log_le_log hu₁ hcase]
      have hset : {a : (AdeleRing (𝓞 K) K)ˣ | (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)) ≤ NumberField.TateGlobal.ideleNorm K a ∧
          NumberField.TateGlobal.ideleNorm K a ≤ Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) ∨
          (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ)) < NumberField.TateGlobal.ideleNorm K a ∧ NumberField.TateGlobal.ideleNorm K a < Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)))} =
          {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))) (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ)))} := by
        ext a; simp only [Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · rintro (h | h)
          · exact h
          · exfalso; linarith [h.1, h.2]
        · intro h; exact Or.inl h
      rw [hset, AutomorphicForm.ProdEval.measure_inter_shell_eq_ofReal νK ΩK (NumberField.TateGlobal.ideleNorm K) VK hVK hVK1
        _ _ hu₁ hcase, hlog, abs_of_nonneg (by
          have : (0:ℝ) < (Module.finrank K L : ℕ) := hℓr
          exact (div_nonneg_iff.mp hA).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr this)))]
      congr 1; ring
    ·
      push_neg at hcase
      have hset : {a : (AdeleRing (𝓞 K) K)ˣ | (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)) ≤ NumberField.TateGlobal.ideleNorm K a ∧
          NumberField.TateGlobal.ideleNorm K a ≤ Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) ∨
          (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ)) < NumberField.TateGlobal.ideleNorm K a ∧ NumberField.TateGlobal.ideleNorm K a < Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)))} =
          {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)))} \
            ({a | NumberField.TateGlobal.ideleNorm K a = Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))} ∪ {a | NumberField.TateGlobal.ideleNorm K a = Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))}) := by
        ext a; simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_diff, Set.mem_union]
        constructor
        · rintro (h | h)
          · exfalso; linarith [h.1, h.2]
          · exact ⟨⟨h.1.le, h.2.le⟩, fun h' => h'.elim (fun e => by linarith [h.1, e]) (fun e => by linarith [h.2, e])⟩
        · rintro ⟨⟨h1, h2⟩, hne⟩
          right
          refine ⟨lt_of_le_of_ne h1 (fun e => hne (Or.inl e.symm)), lt_of_le_of_ne h2 (fun e => hne (Or.inr e))⟩
      have hnull : νK (({a : (AdeleRing (𝓞 K) K)ˣ | NumberField.TateGlobal.ideleNorm K a = Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))} ∪
          {a | NumberField.TateGlobal.ideleNorm K a = Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))}) ∩
          (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)))})) = 0 := by
        have h2 := AutomorphicForm.ProdEval.measure_inter_level_eq_zero νK ΩK (NumberField.TateGlobal.ideleNorm K) VK hVK hVK1 _ hu₂
        have h1 := AutomorphicForm.ProdEval.measure_inter_level_eq_zero νK ΩK (NumberField.TateGlobal.ideleNorm K) VK hVK hVK1 _ hu₁
        refine le_antisymm ?_ bot_le
        calc νK (({a : (AdeleRing (𝓞 K) K)ˣ | NumberField.TateGlobal.ideleNorm K a = Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))} ∪
              {a | NumberField.TateGlobal.ideleNorm K a = Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))}) ∩
              (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)))}))
            ≤ νK ((ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a = Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))}) ∪
                (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a = Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))})) := by
              apply measure_mono
              rintro a ⟨(ha | ha), hΩ, -⟩
              · exact Or.inl ⟨hΩ, ha⟩
              · exact Or.inr ⟨hΩ, ha⟩
          _ ≤ νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a = Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))}) +
                νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a = Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))}) := measure_union_le _ _
          _ = 0 := by rw [h1, h2, add_zero]
      have hA : (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))) / (Module.finrank K L : ℕ) < 0 := by
        rw [← hlog]; linarith [Real.log_lt_log hu₂ hcase]
      have hA' : 2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) < 0 := by
        by_contra h; push_neg at h; exact absurd (div_nonneg h hℓr.le) (not_le.mpr hA)
      rw [hset, ← Set.inter_diff_assoc, ← Set.diff_inter_self_eq_diff, measure_diff_null hnull,
        AutomorphicForm.ProdEval.measure_inter_shell_eq_ofReal νK ΩK (NumberField.TateGlobal.ideleNorm K) VK hVK hVK1
          _ _ hu₂ hcase.le, abs_of_neg hA']
      congr 1
      have : Real.log (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))) - Real.log (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) =
          -(2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))) / (Module.finrank K L : ℕ) := by
        rw [Real.log_exp, Real.log_exp]; field_simp; ring
      rw [this]; field_simp

  set Sl : Set ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) :=
    {p | NumberField.TateGlobal.ideleNorm L p.1 ^ 2 * NumberField.TateGlobal.ideleNorm K p.2 ^ Module.finrank K L * NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc α β} with hSl
  set Bc : Set (AdeleRing (𝓞 K) K)ˣ := {a | (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)) ≤ NumberField.TateGlobal.ideleNorm K a ∧ NumberField.TateGlobal.ideleNorm K a ≤ Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) ∨
        (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ)) < NumberField.TateGlobal.ideleNorm K a ∧ NumberField.TateGlobal.ideleNorm K a < Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)))} with hBc
  have hcontL : Continuous (NumberField.TateGlobal.ideleNorm L) := NumberField.TateGlobal.continuous_ideleNorm L
  have hcontK : Continuous (NumberField.TateGlobal.ideleNorm K) := NumberField.TateGlobal.continuous_ideleNorm K
  have hSlm : MeasurableSet Sl := by
    rw [hSl]
    exact (measurableSet_Icc.preimage
      ((((hcontL.comp continuous_fst).pow 2).mul ((hcontK.comp continuous_snd).pow _)).mul continuous_const).measurable)
  have hBcm : MeasurableSet Bc := by
    rw [hBc]
    have h1 : MeasurableSet {a : (AdeleRing (𝓞 K) K)ˣ | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))) (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ)))} :=
      measurableSet_Icc.preimage hcontK.measurable
    have h2 : MeasurableSet {a : (AdeleRing (𝓞 K) K)ˣ | NumberField.TateGlobal.ideleNorm K a ∈ Set.Ioo (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))) (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)))} :=
      measurableSet_Ioo.preimage hcontK.measurable
    convert h1.union h2 using 1
    rfl
  have hnorm : ∀ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
      ‖(Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))‖ₑ = Sl.indicator 1 p * Bc.indicator 1 p.2 := by
    intro p
    rw [hpt p, enorm_mul, ← ofReal_norm_eq_enorm (AutomorphicForm.ProdEval.bfun _ _ _ _ _),
      AutomorphicForm.ProdEval.norm_bfun_eq_indicator _ hℓpos R _ _ _ hHy0 hHwy0 (NumberField.TateGlobal.ideleNorm_pos _)]
    congr 1
    · simp only [hSl, Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs <;> simp
    · simp only [hBc, Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs <;> simp

  have hmain : ∫⁻ p in ΩL ×ˢ ΩK, Sl.indicator 1 p * Bc.indicator 1 p.2 ∂(νZL.prod νK) =
      ENNReal.ofReal (VL * VK * Real.log (β / α) / (2 * (Module.finrank K L : ℕ)) *
        |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))|) := by
    have hFm : Measurable (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
        Sl.indicator (1 : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) → ENNReal) p * Bc.indicator 1 p.2) :=
      ((measurable_one.indicator hSlm).mul ((measurable_one.indicator hBcm).comp measurable_snd))
    rw [← Measure.prod_restrict, MeasureTheory.lintegral_prod_symm _ hFm.aemeasurable]

    have hinner : ∀ a : (AdeleRing (𝓞 K) K)ˣ,
        ∫⁻ z, Sl.indicator (1 : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) → ENNReal) (z, a) * Bc.indicator 1 a ∂(νZL.restrict ΩL) =
          Bc.indicator 1 a * ENNReal.ofReal (VL * (Real.log β - Real.log α) / 2) := by
      intro a
      have hm : 0 < NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L * NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) := mul_pos (pow_pos (NumberField.TateGlobal.ideleNorm_pos _) _) hdy0
      set Sa : Set (AdeleRing (𝓞 L) L)ˣ := {z | NumberField.TateGlobal.ideleNorm L z ^ 2 * (NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L * NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y)) ∈ Set.Icc α β} with hSa
      have hSam : MeasurableSet Sa := by
        rw [hSa]; exact measurableSet_Icc.preimage (((hcontL.pow 2).mul continuous_const).measurable)
      have hind : ∀ z, Sl.indicator (1 : ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) → ENNReal) (z, a) = Sa.indicator 1 z := by
        intro z; rw [hSl, hSa]; simp only [Set.indicator_apply, Set.mem_setOf_eq, mul_assoc, Pi.one_apply]
      simp_rw [hind]
      rw [lintegral_mul_const _ (measurable_one.indicator hSam), lintegral_indicator_one hSam, Measure.restrict_apply hSam,
        Set.inter_comm, hSa, hzshell _ hm, mul_comm]
    simp_rw [hinner]
    rw [lintegral_mul_const _ (measurable_one.indicator hBcm), lintegral_indicator_one hBcm, Measure.restrict_apply hBcm,
      Set.inter_comm, hBc, hashell, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.log_div (hα.trans hαβ).ne' hα.ne']
    field_simp
  refine ⟨?_, fun hyR => ?_⟩
  · rw [lintegral_congr (fun p => hnorm p), hmain]
  ·
    have hA0 : 0 ≤ 2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) := by
      have := (Real.log_le_log_iff (mul_pos hHy0 hHwy0) (Real.exp_pos _)).mpr hyR
      rw [Real.log_mul hHy0.ne' hHwy0.ne', Real.log_exp] at this
      linarith
    set E : Set ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ) :=
      Sl ∩ {p | NumberField.TateGlobal.ideleNorm K p.2 ∈ Set.Icc (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))) (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ)))} with hE
    have hEm : MeasurableSet E := by
      rw [hE]; exact hSlm.inter (measurableSet_Icc.preimage (hcontK.comp continuous_snd).measurable)
    have hTE : ∀ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
        (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y))) = E.indicator (fun _ => (1 : ℂ)) p := by
      intro p
      rw [hpt p, AutomorphicForm.ProdEval.bfun_eq_indicator_of_le _ hℓpos R _ _ _ hHy0 hHwy0
        (NumberField.TateGlobal.ideleNorm_pos _) hyR]
      have hmemE : p ∈ E ↔ (NumberField.TateGlobal.ideleNorm L p.1 ^ 2 * NumberField.TateGlobal.ideleNorm K p.2 ^ Module.finrank K L * NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc α β ∧
          NumberField.TateGlobal.ideleNorm K p.2 ∈ Set.Icc (Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ))) (Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ)))) := by rw [hE, hSl]; exact Iff.rfl
      rw [Set.indicator_apply]
      by_cases hS : NumberField.TateGlobal.ideleNorm L p.1 ^ 2 * NumberField.TateGlobal.ideleNorm K p.2 ^ Module.finrank K L * NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ∈ Set.Icc α β
      · by_cases hC : Real.exp ((Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)) - R) / (Module.finrank K L : ℕ)) ≤ NumberField.TateGlobal.ideleNorm K p.2 ∧ NumberField.TateGlobal.ideleNorm K p.2 ≤ Real.exp ((R - Real.log (NumberField.AdelicHeight.adelicHeight L y)) / (Module.finrank K L : ℕ))
        · rw [if_pos hS, if_pos hC, if_pos (hmemE.mpr ⟨hS, hC⟩), one_mul]
        · rw [if_pos hS, if_neg hC, if_neg (fun h => hC (hmemE.mp h).2), mul_zero]
      · rw [if_neg hS, if_neg (fun h => hS (hmemE.mp h).1), zero_mul]
    have hμE : ((νZL.prod νK).restrict (ΩL ×ˢ ΩK)) E =
        ENNReal.ofReal (VL * VK * Real.log (β / α) / (2 * (Module.finrank K L : ℕ)) *
          |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))|) := by
      rw [← lintegral_indicator_one hEm, ← hmain]
      refine lintegral_congr (fun p => ?_)
      rw [← hnorm p, hTE p]
      simp only [Set.indicator_apply, Pi.one_apply]
      split_ifs <;> simp
    refine ⟨?_, ?_⟩
    · rw [IntegrableOn, show (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)))) =
          E.indicator (fun _ => (1 : ℂ)) from funext hTE, integrable_indicator_iff hEm]
      refine integrableOn_const ?_
      rw [hμE]; exact ENNReal.ofReal_ne_top
    · rw [show (∫ p in ΩL ×ˢ ΩK, (Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((AutomorphicForm.centralScalar (𝓞 L) L p.1 * diagOne (θ p.2)) * y))) ∂(νZL.prod νK)) =
          ∫ p in ΩL ×ˢ ΩK, E.indicator (fun _ => (1 : ℂ)) p ∂(νZL.prod νK) from by simp_rw [hTE]]
      have hnn : 0 ≤ VL * VK * Real.log (β / α) / (2 * (Module.finrank K L : ℕ)) *
          |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))| := by
        have hlog : 0 < Real.log (β / α) := Real.log_pos ((one_lt_div hα).mpr hαβ)
        have h1 : 0 ≤ VL * VK * Real.log (β / α) / (2 * (Module.finrank K L : ℕ)) :=
          div_nonneg (mul_nonneg (mul_nonneg hVL.le hVK.le) hlog.le) (by positivity)
        exact mul_nonneg h1 (abs_nonneg _)
      rw [integral_indicator_const (1 : ℂ) hEm, measureReal_def, hμE, ENNReal.toReal_ofReal hnn, abs_of_nonneg hA0,
        Complex.real_smul, mul_one]

end S_AutomorphicForm_setLIntegral_prod_torusShell_eq_and_setIntegral_prod_torusShell_eq
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_prod_torusShell_eq_and_setIntegral_prod_torusShell_eq (solution)
