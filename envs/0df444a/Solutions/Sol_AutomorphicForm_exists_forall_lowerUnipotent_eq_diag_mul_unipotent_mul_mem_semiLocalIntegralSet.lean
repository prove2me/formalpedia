-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fbdee98a-f760-5e0f-8f87-a6b56c3ad669

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
import Theorems.Thm_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
import Theorems.Thm_NumberField_AdicCompletion_lintegral_inv_max_one_norm_sq_lt_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

noncomputable section

namespace K45Absorb

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "ee" => HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

section Coord
variable {K L v}
variable (c : Π w : v.Extension (𝓞 L), w.1.adicCompletion L)

open Classical in
def etaPi : Π w : v.Extension (𝓞 L), w.1.adicCompletion L := fun w => if ‖c w‖ ≤ 1 then 1 else c w
open Classical in
def etaInvPi : Π w : v.Extension (𝓞 L), w.1.adicCompletion L := fun w => if ‖c w‖ ≤ 1 then 1 else (c w)⁻¹
open Classical in
def tPi : Π w : v.Extension (𝓞 L), w.1.adicCompletion L := fun w => if ‖c w‖ ≤ 1 then 0 else c w

theorem etaPi_mul_etaInvPi (w : v.Extension (𝓞 L)) : etaPi c w * etaInvPi c w = 1 := by
  unfold etaPi etaInvPi
  split_ifs with h
  · exact one_mul 1
  · exact mul_inv_cancel₀ (fun h0 => h (by rw [h0, norm_zero]; exact zero_le_one))

theorem norm_etaPi (w : v.Extension (𝓞 L)) : ‖etaPi c w‖ = max 1 ‖c w‖ := by
  unfold etaPi
  split_ifs with h
  · rw [norm_one, max_eq_left h]
  · rw [max_eq_right (le_of_lt (not_le.1 h))]

theorem norm_e00_le (w : v.Extension (𝓞 L)) : ‖etaPi c w - tPi c w * etaInvPi c w * c w‖ ≤ 1 := by
  unfold etaPi etaInvPi tPi
  split_ifs with h
  · rw [zero_mul, zero_mul, sub_zero, norm_one]
  · have h0 : c w ≠ 0 := fun h0 => h (by rw [h0, norm_zero]; exact zero_le_one)
    rw [mul_inv_cancel₀ h0, one_mul, sub_self, norm_zero]; exact zero_le_one

theorem norm_e01_le (w : v.Extension (𝓞 L)) : ‖tPi c w * etaInvPi c w‖ ≤ 1 := by
  unfold etaInvPi tPi
  split_ifs with h
  · rw [zero_mul, norm_zero]; exact zero_le_one
  · have h0 : c w ≠ 0 := fun h0 => h (by rw [h0, norm_zero]; exact zero_le_one)
    rw [mul_inv_cancel₀ h0, norm_one]

theorem norm_e10_le (w : v.Extension (𝓞 L)) : ‖etaInvPi c w * c w‖ ≤ 1 := by
  unfold etaInvPi
  split_ifs with h
  · rw [one_mul]; exact h
  · have h0 : c w ≠ 0 := fun h0 => h (by rw [h0, norm_zero]; exact zero_le_one)
    rw [inv_mul_cancel₀ h0, norm_one]

theorem norm_e11_le (w : v.Extension (𝓞 L)) : ‖etaInvPi c w‖ ≤ 1 := by
  unfold etaInvPi
  split_ifs with h
  · rw [norm_one]
  · rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h))

end Coord

theorem mem_semiLocalIntegers_iff (x : L ⊗[K] Kv) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔ ∀ w : v.Extension (𝓞 L), ‖ee x w‖ ≤ 1 := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage]
  simp only [Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
  exact Iff.rfl

def eta (y : L ⊗[K] Kv) : L ⊗[K] Kv := (ee).symm (etaPi (ee y))
def etaInv (y : L ⊗[K] Kv) : L ⊗[K] Kv := (ee).symm (etaInvPi (ee y))
def tt (y : L ⊗[K] Kv) : L ⊗[K] Kv := (ee).symm (tPi (ee y))

theorem e_eta (y : L ⊗[K] Kv) : ee (eta K L v y) = etaPi (ee y) := (ee).apply_symm_apply _
theorem e_etaInv (y : L ⊗[K] Kv) : ee (etaInv K L v y) = etaInvPi (ee y) := (ee).apply_symm_apply _
theorem e_tt (y : L ⊗[K] Kv) : ee (tt K L v y) = tPi (ee y) := (ee).apply_symm_apply _

theorem eta_mul_etaInv (y : L ⊗[K] Kv) : eta K L v y * etaInv K L v y = 1 := by
  apply (ee).injective
  rw [map_mul, map_one, e_eta, e_etaInv]
  funext w
  exact etaPi_mul_etaInvPi _ w

theorem isUnit_eta (y : L ⊗[K] Kv) : IsUnit (eta K L v y) :=
  isUnit_iff_exists_inv.2 ⟨_, eta_mul_etaInv K L v y⟩

theorem inverse_eta (y : L ⊗[K] Kv) : Ring.inverse (eta K L v y) = etaInv K L v y := by
  rw [← (isUnit_eta K L v y).unit_spec, Ring.inverse_unit]
  exact Units.inv_eq_of_mul_eq_one_right (by rw [(isUnit_eta K L v y).unit_spec]; exact eta_mul_etaInv K L v y)

def kMat (y : L ⊗[K] Kv) : Matrix (Fin 2) (Fin 2) (L ⊗[K] Kv) :=
  !![eta K L v y - tt K L v y * etaInv K L v y * y, -(tt K L v y * etaInv K L v y);
     etaInv K L v y * y, etaInv K L v y]

def kInvMat (y : L ⊗[K] Kv) : Matrix (Fin 2) (Fin 2) (L ⊗[K] Kv) :=
  !![etaInv K L v y, tt K L v y * etaInv K L v y;
     -(etaInv K L v y * y), eta K L v y - tt K L v y * etaInv K L v y * y]

theorem kMat_mul_kInvMat (y : L ⊗[K] Kv) : kMat K L v y * kInvMat K L v y = 1 := by
  have h := eta_mul_etaInv K L v y
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kMat, kInvMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h | ring

theorem kInvMat_mul_kMat (y : L ⊗[K] Kv) : kInvMat K L v y * kMat K L v y = 1 := by
  have h := eta_mul_etaInv K L v y
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kMat, kInvMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h | ring

def kGL (y : L ⊗[K] Kv) : GL (Fin 2) (L ⊗[K] Kv) :=
  ⟨kMat K L v y, kInvMat K L v y, kMat_mul_kInvMat K L v y, kInvMat_mul_kMat K L v y⟩

set_option maxHeartbeats 3200000 in
theorem lowerUnipotent_eq (y : L ⊗[K] Kv) :
    (!![1, 0; y, 1] : Matrix (Fin 2) (Fin 2) (L ⊗[K] Kv)) =
      !![etaInv K L v y, 0; 0, eta K L v y] * !![1, tt K L v y; 0, 1] * kMat K L v y := by
  have h := eta_mul_etaInv K L v y
  have hDU : (!![etaInv K L v y, 0; 0, eta K L v y] * !![1, tt K L v y; 0, 1] :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] Kv)) = !![etaInv K L v y, etaInv K L v y * tt K L v y; 0, eta K L v y] := by
    rw [Matrix.mul_fin_two]
    simp only [mul_one, mul_zero, add_zero, zero_add, zero_mul]
  rw [hDU, kMat, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | linear_combination h | linear_combination (-1 : L ⊗[K] Kv) * h | linear_combination y * h |
      linear_combination (-y) * h | ring

theorem kGL_mem (y : L ⊗[K] Kv) : kGL K L v y ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  have hy : ee ((ee).symm (ee y)) = ee y := (ee).apply_symm_apply _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [mem_semiLocalIntegers_iff]
    intro w
    fin_cases i <;> fin_cases j
    · show ‖ee (eta K L v y - tt K L v y * etaInv K L v y * y) w‖ ≤ 1
      rw [map_sub, map_mul, map_mul, e_eta, e_etaInv, e_tt]
      exact norm_e00_le (ee y) w
    · show ‖ee (-(tt K L v y * etaInv K L v y)) w‖ ≤ 1
      rw [map_neg, map_mul, e_etaInv, e_tt, Pi.neg_apply, norm_neg]
      exact norm_e01_le (ee y) w
    · show ‖ee (etaInv K L v y * y) w‖ ≤ 1
      rw [map_mul, e_etaInv]
      exact norm_e10_le (ee y) w
    · show ‖ee (etaInv K L v y) w‖ ≤ 1
      rw [e_etaInv]
      exact norm_e11_le (ee y) w
  · rw [mem_semiLocalIntegers_iff]
    intro w
    show ‖ee ((kInvMat K L v y) i j) w‖ ≤ 1
    fin_cases i <;> fin_cases j
    · show ‖ee (etaInv K L v y) w‖ ≤ 1
      rw [e_etaInv]
      exact norm_e11_le (ee y) w
    · show ‖ee (tt K L v y * etaInv K L v y) w‖ ≤ 1
      rw [map_mul, e_etaInv, e_tt]
      exact norm_e01_le (ee y) w
    · show ‖ee (-(etaInv K L v y * y)) w‖ ≤ 1
      rw [map_neg, map_mul, e_etaInv, Pi.neg_apply, norm_neg]
      exact norm_e10_le (ee y) w
    · show ‖ee (eta K L v y - tt K L v y * etaInv K L v y * y) w‖ ≤ 1
      rw [map_sub, map_mul, map_mul, e_eta, e_etaInv, e_tt]
      exact norm_e00_le (ee y) w

end K45Absorb

namespace K45Absorb

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "ee" => HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

scoped instance instFintypeExtension : Fintype (v.Extension (𝓞 L)) :=
  @Fintype.ofFinite _ (HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v)

def fw (w : v.Extension (𝓞 L)) (z : w.1.adicCompletion L) : ℝ := ((max 1 ‖z‖) ^ 2)⁻¹

theorem fw_nonneg (w : v.Extension (𝓞 L)) (z : w.1.adicCompletion L) : 0 ≤ fw K L v w z := by
  unfold fw; positivity

def Y (y : L ⊗[K] Kv) : ℝ≥0∞ := (ENNReal.ofReal ‖Algebra.norm Kv (eta K L v y ^ 2)‖)⁻¹

theorem Y_eq (y : L ⊗[K] Kv) :
    Y K L v y = ∏ w : v.Extension (𝓞 L), ENNReal.ofReal (fw K L v w (ee y w)) := by
  obtain ⟨-, -, h3⟩ :=
    HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm K L v
  unfold Y
  rw [h3, finprod_eq_prod_of_fintype]
  have hw : ∀ w : v.Extension (𝓞 L), ‖(ee (eta K L v y ^ 2)) w‖ = (max 1 ‖ee y w‖) ^ 2 := by
    intro w
    rw [map_pow, Pi.pow_apply, norm_pow, e_eta, norm_etaPi]
  simp_rw [hw]
  have hpos : 0 < ∏ w : v.Extension (𝓞 L), (max 1 ‖ee y w‖) ^ 2 :=
    Finset.prod_pos fun w _ => by positivity
  rw [← ENNReal.ofReal_inv_of_pos hpos, ← Finset.prod_inv_distrib]
  rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity)]
  rfl

def G (c : Π w : v.Extension (𝓞 L), w.1.adicCompletion L) : ℝ≥0∞ :=
  ∏ w : v.Extension (𝓞 L), ENNReal.ofReal (fw K L v w (c w))

theorem Y_eq_G (y : L ⊗[K] Kv) : Y K L v y = G K L v (ee y) := Y_eq K L v y

end K45Absorb
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet.K45Absorb"

open K45Absorb in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ Y : L ⊗[K] v.adicCompletion K → ℝ≥0∞, Measurable Y ∧ ∫⁻ y, Y y ∂ν ≠ ⊤ ∧
      ∀ y : L ⊗[K] v.adicCompletion K, ∃ η t : L ⊗[K] v.adicCompletion K, IsUnit η ∧
        Y y = (ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (η ^ 2)‖)⁻¹ ∧
        ∃ k ∈ AutomorphicForm.semiLocalIntegralSet K L v,
          (!![1, 0; y, 1] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            !![Ring.inverse η, 0; 0, η] * !![1, t; 0, 1] * (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  letI : ∀ w : v.Extension (𝓞 L), MeasurableSpace (w.1.adicCompletion L) := fun w => borel _
  haveI : ∀ w : v.Extension (𝓞 L), BorelSpace (w.1.adicCompletion L) := fun w => ⟨rfl⟩
  haveI : ∀ w : v.Extension (𝓞 L), ProperSpace (w.1.adicCompletion L) := fun w =>
    NumberField.AdelicHaar.properSpace_adicCompletion (𝓞 L) L w.1
  let νw : ∀ w : v.Extension (𝓞 L), Measure (w.1.adicCompletion L) := fun w => Measure.addHaar

  have he : Measurable (fun y : L ⊗[K] v.adicCompletion K =>
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y :
        Π w : v.Extension (𝓞 L), w.1.adicCompletion L)) := by
    refine measurable_pi_iff.2 fun w => ?_
    exact ((continuous_apply w).comp (AutomorphicForm.semiLocalHomeomorph K L v).continuous).measurable
  have hfw : ∀ w : v.Extension (𝓞 L), Measurable (fw K L v w) := fun w =>
    ((measurable_const.max measurable_norm).pow_const 2).inv
  have hG : Measurable (G K L v) := by
    refine Finset.measurable_prod _ fun w _ => ?_
    exact ENNReal.measurable_ofReal.comp ((hfw w).comp (measurable_pi_apply w))
  refine ⟨Y K L v, ?_, ?_, fun y => ⟨eta K L v y, tt K L v y, isUnit_eta K L v y, rfl,
    kGL K L v y, kGL_mem K L v y, ?_⟩⟩
  ·
    have : Y K L v = G K L v ∘ fun y => HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y :=
      funext fun y => Y_eq_G K L v y
    rw [this]
    exact hG.comp he
  ·
    have hY : (fun y => Y K L v y) = fun y => G K L v (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y) :=
      funext fun y => Y_eq_G K L v y
    rw [hY, ← lintegral_map hG he]
    obtain ⟨c0, -, hc0, hmap⟩ :=
      (AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
        K L v).2.2.2.2 ν νw
    rw [hmap, lintegral_smul_measure, smul_eq_mul]

    have hint : ∀ w : v.Extension (𝓞 L), Integrable (fw K L v w) (νw w) := by
      intro w
      refine ⟨(hfw w).aestronglyMeasurable, ?_⟩
      show ∫⁻ z, ‖fw K L v w z‖ₑ ∂(νw w) < ⊤
      have h := NumberField.AdicCompletion.lintegral_inv_max_one_norm_sq_lt_top L w.1 (νw w)
      refine lt_of_le_of_lt (le_of_eq ?_) h
      refine lintegral_congr fun z => ?_
      rw [Real.enorm_eq_ofReal (fw_nonneg K L v w z)]
      show ENNReal.ofReal (((max 1 ‖z‖) ^ 2)⁻¹) = _
      rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    have hprod := (MeasureTheory.Integrable.fintype_prod_dep hint).2
    have hGe : ∀ c : Π w : v.Extension (𝓞 L), w.1.adicCompletion L,
        G K L v c = ‖∏ w : v.Extension (𝓞 L), fw K L v w (c w)‖ₑ := by
      intro c
      rw [Real.enorm_eq_ofReal (Finset.prod_nonneg fun w _ => fw_nonneg K L v w _),
        ENNReal.ofReal_prod_of_nonneg fun w _ => fw_nonneg K L v w _]
      rfl
    refine ENNReal.mul_ne_top hc0 (ne_of_lt ?_)
    calc ∫⁻ c, G K L v c ∂(Measure.pi νw) = ∫⁻ c, ‖∏ w : v.Extension (𝓞 L), fw K L v w (c w)‖ₑ ∂(Measure.pi νw) :=
          lintegral_congr fun c => hGe c
      _ < ⊤ := hprod
  ·
    rw [inverse_eta]
    exact lowerUnipotent_eq K L v y

end
end S_AutomorphicForm_exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet (solution)
