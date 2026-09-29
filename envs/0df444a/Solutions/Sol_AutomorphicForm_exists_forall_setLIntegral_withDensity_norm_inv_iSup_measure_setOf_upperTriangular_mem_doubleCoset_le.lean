-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/58cebf25-d52d-55b3-8e6e-9b4ac98977c7

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
import Theorems.Thm_AutomorphicForm_exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card
import Theorems.Thm_AutomorphicForm_mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quot_span_eq_absNorm
import Theorems.Thm_AutomorphicForm_unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le
import Theorems.Thm_AutomorphicForm_norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply
import Theorems.Thm_AutomorphicForm_exists_uniformizers_forall_exists_cartanType_mem_doubleCoset_and_prod_pow_le_semiLocalHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

set_option autoImplicit false
open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions Pointwise ENNReal

noncomputable section

namespace Ws35H

section Local
variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem norm_eq_absNorm_zpow (x : v.adicCompletion K) (hx : x ≠ 0) :
    ‖x‖ = ((Ideal.absNorm v.asIdeal : NNReal) : ℝ) ^
      Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff Valued.v).mpr hx)) := by
  rw [NumberField.FinitePlace.norm_def v x,
    WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff Valued.v).mpr hx)]
  push_cast
  rfl

theorem exists_pi :
    ∃ π : v.adicCompletion K, π ≠ 0 ∧ ‖π‖ < 1 ∧
      ∀ x : v.adicCompletion K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k := by
  obtain ⟨π₀, hπ₀⟩ := v.valuation_exists_uniformizer K
  set π : v.adicCompletion K := ((WithVal.equiv (v.valuation K)).symm π₀ : v.adicCompletion K) with hπdef
  have hvπ : Valued.v π = WithZero.exp (-1 : ℤ) := by
    rw [hπdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ₀
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hvπ; exact WithZero.exp_ne_zero hvπ.symm
  set b : NNReal := (Ideal.absNorm v.asIdeal : NNReal) with hb
  have hb1 : 1 < b := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (0 : NNReal) < b := zero_lt_one.trans hb1
    exact_mod_cast this.ne'
  have hnπ : ‖π‖ = (b : ℝ) ^ (-1 : ℤ) := by
    rw [norm_eq_absNorm_zpow K v π hπ0]
    congr 1
    have h0 : (Valued.v π) ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hπ0
    have : (WithZero.unzero h0 : Multiplicative ℤ) = Multiplicative.ofAdd (-1 : ℤ) := by
      rw [← WithZero.coe_inj, WithZero.coe_unzero h0, hvπ]; rfl
    rw [this]; rfl
  refine ⟨π, hπ0, ?_, ?_⟩
  · rw [hnπ, zpow_neg, zpow_one]
    have : (1 : ℝ) < b := by exact_mod_cast hb1
    exact inv_lt_one_of_one_lt₀ this
  · intro x hx
    refine ⟨-(Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff Valued.v).mpr hx))), ?_⟩
    rw [norm_eq_absNorm_zpow K v x hx, hnπ, ← zpow_mul]
    congr 1; ring

end Local

end Ws35H

namespace Ws35H

section Local2
variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem mem_integers_iff_norm_le_one (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, NumberField.FinitePlace.norm_def v x]
  have hb1 : 1 < (Ideal.absNorm v.asIdeal : NNReal) := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [← NNReal.coe_one, NNReal.coe_le_coe, WithZeroMulInt.toNNReal_le_one_iff hb1]

theorem integralUnitsSet_mul_mem {A : Type*} [CommRing A] {U : Set A}
    (hadd : ∀ a ∈ U, ∀ b ∈ U, a + b ∈ U) (hmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U)
    {g h : GL (Fin 2) A} (hg : g ∈ AutomorphicForm.integralUnitsSet U)
    (hh : h ∈ AutomorphicForm.integralUnitsSet U) : g * h ∈ AutomorphicForm.integralUnitsSet U := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact hadd _ (hmul _ (hg.1 i 0) _ (hh.1 0 j)) _ (hmul _ (hg.1 i 1) _ (hh.1 1 j))
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact hadd _ (hmul _ (hh.2 i 0) _ (hg.2 0 j)) _ (hmul _ (hh.2 i 1) _ (hg.2 1 j))

theorem integralUnitsSet_inv_mem {A : Type*} [CommRing A] {U : Set A}
    {g : GL (Fin 2) A} (hg : g ∈ AutomorphicForm.integralUnitsSet U) :
    g⁻¹ ∈ AutomorphicForm.integralUnitsSet U := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg ⊢
  rw [inv_inv]; exact ⟨hg.2, hg.1⟩

theorem norm_sub_le_max' {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E] (x y : E) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem localIntegralSet_mul_mem {g h : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.localIntegralSet K v) (hh : h ∈ AutomorphicForm.localIntegralSet K v) :
    g * h ∈ AutomorphicForm.localIntegralSet K v :=
  integralUnitsSet_mul_mem (fun _ ha _ hb => add_mem ha hb) (fun _ ha _ hb => mul_mem ha hb) hg hh

theorem localIntegralSet_inv_mem {g : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.localIntegralSet K v) : g⁻¹ ∈ AutomorphicForm.localIntegralSet K v :=
  integralUnitsSet_inv_mem hg

theorem doubleCoset_subset {ρ d : GL (Fin 2) (v.adicCompletion K)}
    (h : ρ ∈ AutomorphicForm.localIntegralSet K v * {d} * AutomorphicForm.localIntegralSet K v) :
    AutomorphicForm.localIntegralSet K v * {ρ} * AutomorphicForm.localIntegralSet K v ⊆
      AutomorphicForm.localIntegralSet K v * {d} * AutomorphicForm.localIntegralSet K v := by
  obtain ⟨y, hy, k₂, hk₂, rfl⟩ := h
  obtain ⟨k₁, hk₁, d', hd', rfl⟩ := hy
  rw [Set.mem_singleton_iff] at hd'; subst d'
  rintro x ⟨y', hy', c₂, hc₂, rfl⟩
  obtain ⟨c₁, hc₁, ρ', hρ', rfl⟩ := hy'
  rw [Set.mem_singleton_iff] at hρ'; subst ρ'
  refine ⟨c₁ * k₁ * d, ⟨c₁ * k₁, localIntegralSet_mul_mem K v hc₁ hk₁, d, rfl, rfl⟩, k₂ * c₂,
    localIntegralSet_mul_mem K v hk₂ hc₂, by group⟩

theorem mem_doubleCoset_symm {ρ d : GL (Fin 2) (v.adicCompletion K)}
    (h : ρ ∈ AutomorphicForm.localIntegralSet K v * {d} * AutomorphicForm.localIntegralSet K v) :
    d ∈ AutomorphicForm.localIntegralSet K v * {ρ} * AutomorphicForm.localIntegralSet K v := by
  obtain ⟨y, hy, k₂, hk₂, rfl⟩ := h
  obtain ⟨k₁, hk₁, d', hd', rfl⟩ := hy
  rw [Set.mem_singleton_iff] at hd'; subst d'
  refine ⟨k₁⁻¹ * (k₁ * d * k₂), ⟨k₁⁻¹, localIntegralSet_inv_mem K v hk₁, _, rfl, rfl⟩, k₂⁻¹,
    localIntegralSet_inv_mem K v hk₂, by group⟩

def diagGL {F : Type*} [Field F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) : GL (Fin 2) F where
  val := Matrix.diagonal ![a, b]
  inv := Matrix.diagonal ![a⁻¹, b⁻¹]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1
    ext i; fin_cases i <;> simp [ha, hb]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1
    ext i; fin_cases i <;> simp [ha, hb]

theorem diagGL_coe {F : Type*} [Field F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((diagGL a b ha hb : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![a, b] := rfl

theorem diagGL_inv_coe {F : Type*} [Field F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (((diagGL a b ha hb)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![a⁻¹, b⁻¹] := rfl

theorem diagGL_coe' {F : Type*} [Field F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((diagGL a b ha hb : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, b] := by
  rw [diagGL_coe]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diagGL_inv_coe' {F : Type*} [Field F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (((diagGL a b ha hb)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![a⁻¹, 0; 0, b⁻¹] := by
  rw [diagGL_inv_coe]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_cartanType (π : v.adicCompletion K) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hpow : ∀ x : v.adicCompletion K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k)
    (ρ : GL (Fin 2) (v.adicCompletion K)) :
    ∃ m₁ m₂ : ℤ, m₂ ≤ m₁ ∧
      ρ ∈ AutomorphicForm.localIntegralSet K v *
          {diagGL (π ^ m₁) (π ^ m₂) (zpow_ne_zero m₁ hπ0) (zpow_ne_zero m₂ hπ0)} *
        AutomorphicForm.localIntegralSet K v := by
  classical
  have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0

  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun p => ‖(ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) p.1 p.2‖) Finset.univ_nonempty
  set M := ‖(ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) p.1 p.2‖ with hM
  have hle : ∀ i j, ‖(ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ M :=
    fun i j => hp (i, j) (Finset.mem_univ _)
  have hdet0 : (ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 :=
    (Matrix.GeneralLinearGroup.det ρ).ne_zero
  have hdetle : ‖(ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ≤ M * M := by
    rw [Matrix.det_fin_two]
    refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul (hle 0 0) (hle 1 1) (norm_nonneg _) (le_trans (norm_nonneg _) (hle 0 0))
    · rw [norm_mul]; exact mul_le_mul (hle 0 1) (hle 1 0) (norm_nonneg _) (le_trans (norm_nonneg _) (hle 0 1))
  have hMpos : 0 < M := by
    rcases (norm_nonneg _ : 0 ≤ M).eq_or_lt with h | h
    · exfalso; apply hdet0
      have : ‖(ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ ≤ 0 := by
        rw [hM, ← h, mul_zero] at hdetle; exact hdetle
      exact norm_le_zero_iff.mp this
    · exact h
  have hp0 : (ρ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) p.1 p.2 ≠ 0 := by
    intro h; rw [h, norm_zero] at hM; exact (lt_irrefl (0:ℝ)) (hM ▸ hMpos)
  obtain ⟨m₂, hm₂⟩ := hpow _ hp0
  obtain ⟨d, hd⟩ := hpow _ hdet0
  refine ⟨d - m₂, m₂, ?_, ?_⟩
  ·
    have h1 : ‖π‖ ^ d ≤ ‖π‖ ^ (m₂ + m₂) := by
      rw [← hd, zpow_add₀ hπpos.ne', ← hm₂]; exact hdetle
    have := (zpow_le_zpow_iff_right_of_lt_one₀ hπpos hπ1).mp h1
    omega
  · rw [AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm K v π hπ0
      hπ1.le (d - m₂) m₂ (by
        have h1 : ‖π‖ ^ d ≤ ‖π‖ ^ (m₂ + m₂) := by
          rw [← hd, zpow_add₀ hπpos.ne', ← hm₂]; exact hdetle
        have := (zpow_le_zpow_iff_right_of_lt_one₀ hπpos hπ1).mp h1
        omega) _ (diagGL_coe _ _ _ _) ρ]
    refine ⟨?_, fun i j => hm₂ ▸ hle i j, p.1, p.2, hm₂⟩
    rw [hd]; congr 1; ring

end Local2

end Ws35H

namespace Ws35H

section Local3
variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem ratio_window {a b e P M : ℝ} (ha : 0 < a) (hb : 0 < b) (hP : a * b = P) (hPpos : 0 < P)
    (haM : a ≤ M) (hbM : b ≤ M) (he : 0 ≤ e) (heM : e ≤ M) :
    P / (M * M) ≤ b / a ∧ b / a ≤ M * M / P ∧ e / a ≤ M * M / P := by
  have hM : 0 < M := lt_of_lt_of_le ha haM
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (mul_pos hM hM) ha]
    calc P * a = a * b * a := by rw [hP]
      _ ≤ M * b * M := by nlinarith [mul_le_mul haM (le_refl b) (le_of_lt hb) hM.le]
      _ = b * (M * M) := by ring
  · rw [div_le_div_iff₀ ha hPpos]
    calc b * P = b * (a * b) := by rw [hP]
      _ = (b * b) * a := by ring
      _ ≤ (M * M) * a := by nlinarith [mul_le_mul hbM hbM hb.le hM.le]
  · rw [div_le_div_iff₀ ha hPpos]
    calc e * P = e * (a * b) := by rw [hP]
      _ = (e * b) * a := by ring
      _ ≤ (M * M) * a := by nlinarith [mul_le_mul heM hbM hb.le hM.le]

theorem ratio_bounds (π : v.adicCompletion K) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) (m₁ m₂ : ℤ) (hm : m₂ ≤ m₁)
    (X : GL (Fin 2) (v.adicCompletion K))
    (hX : X ∈ AutomorphicForm.localIntegralSet K v *
          {diagGL (π ^ m₁) (π ^ m₂) (zpow_ne_zero m₁ hπ0) (zpow_ne_zero m₂ hπ0)} *
        AutomorphicForm.localIntegralSet K v)
    (h10 : (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) :
    (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 ≠ 0 ∧
    ‖π‖ ^ (m₁ - m₂) ≤ ‖(X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
        (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ ∧
    ‖(X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 /
        (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ ≤ ‖π‖ ^ (m₂ - m₁) ∧
    ‖(X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 /
        (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ ≤ ‖π‖ ^ (m₂ - m₁) := by
  have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  obtain ⟨hdet, hle, -⟩ :=
    (AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm K v π hπ0
      hπ1.le m₁ m₂ hm _ (diagGL_coe _ _ _ _) X).mp hX
  have hdet' : (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det =
      (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 * (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 := by
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero]
  have hAB : ‖(X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ *
      ‖(X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1‖ = ‖π‖ ^ (m₁ + m₂) := by
    rw [← norm_mul, ← hdet', hdet]
  have hP : 0 < ‖π‖ ^ (m₁ + m₂) := zpow_pos hπpos _
  have hA0 : (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 ≠ 0 := by
    intro h; rw [h, norm_zero, zero_mul] at hAB; exact hP.ne' hAB.symm
  have hB0 : (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 ≠ 0 := by
    intro h; rw [h, norm_zero, mul_zero] at hAB; exact hP.ne' hAB.symm
  obtain ⟨h1, h2, h3⟩ := ratio_window (norm_pos_iff.mpr hA0) (norm_pos_iff.mpr hB0) hAB hP (hle 0 0) (hle 1 1)
    (norm_nonneg _) (hle 0 1)
  have hMM : ‖π‖ ^ m₂ * ‖π‖ ^ m₂ / ‖π‖ ^ (m₁ + m₂) = ‖π‖ ^ (m₂ - m₁) := by
    rw [← zpow_add₀ hπpos.ne', ← zpow_sub₀ hπpos.ne']; congr 1; ring
  have hMM' : ‖π‖ ^ (m₁ + m₂) / (‖π‖ ^ m₂ * ‖π‖ ^ m₂) = ‖π‖ ^ (m₁ - m₂) := by
    rw [← zpow_add₀ hπpos.ne', ← zpow_sub₀ hπpos.ne']; congr 1; ring
  refine ⟨hA0, ?_, ?_, ?_⟩
  · rw [norm_div, ← hMM']; exact h1
  · rw [norm_div, ← hMM]; exact h2
  · rw [norm_div, ← hMM]; exact h3

theorem abs_log_le_of_window {r t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℤ) (hn : 0 ≤ n)
    (h1 : t ^ n ≤ r) (h2 : r ≤ t ^ (-n)) : |Real.log r| ≤ n * (-Real.log t) := by
  have hr : 0 < r := lt_of_lt_of_le (zpow_pos ht0 _) h1
  rw [abs_le]
  constructor
  · have := Real.log_le_log (zpow_pos ht0 _) h1
    rw [Real.log_zpow] at this; linarith
  · have := Real.log_le_log hr h2
    rw [Real.log_zpow] at this; push_cast at this; linarith

theorem posLog_le_of_le {r t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℤ) (hn : 0 ≤ n) (hr : 0 ≤ r)
    (h2 : r ≤ t ^ (-n)) : Real.posLog r ≤ n * (-Real.log t) := by
  rw [Real.posLog, max_le_iff]
  refine ⟨?_, ?_⟩
  · have : Real.log t < 0 := Real.log_neg ht0 ht1
    have hn' : (0:ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg hn' (by linarith)
  · rcases hr.eq_or_lt with h | h
    · rw [← h, Real.log_zero]
      have : Real.log t < 0 := Real.log_neg ht0 ht1
      have hn' : (0:ℝ) ≤ n := by exact_mod_cast hn
      exact mul_nonneg hn' (by linarith)
    · have := Real.log_le_log h h2
      rw [Real.log_zpow] at this; push_cast at this; linarith

theorem exists_separated (π : v.adicCompletion K) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) (n : ℕ) :
    ∃ s : Finset (v.adicCompletion K), s.card = 2 ^ n ∧ (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ‖π‖ ^ n < ‖x - y‖ := by
  classical
  have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  induction n with
  | zero => exact ⟨{0}, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨s, hcard, hint, hsep⟩ := ih
    have hsmall : ∀ x ∈ s, ∀ y ∈ s, ‖π * (x - y)‖ < 1 := by
      intro x hx y hy
      rw [norm_mul]
      calc ‖π‖ * ‖x - y‖ ≤ ‖π‖ * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ hπpos.le
            exact (norm_sub_le_max' x y).trans (max_le (hint x hx) (hint y hy))
        _ < 1 := by rw [mul_one]; exact hπ1
    refine ⟨s.image (fun x => π * x) ∪ s.image (fun x => π * x + 1), ?_, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun x y h => ?_),
        Finset.card_image_of_injective _ (fun x y h => ?_), hcard, pow_succ]; · ring
      · exact mul_left_cancel₀ hπ0 (add_right_cancel h)
      · exact mul_left_cancel₀ hπ0 h
      · rw [Finset.disjoint_left]
        intro a ha ha'
        rw [Finset.mem_image] at ha ha'
        obtain ⟨x, hx, rfl⟩ := ha
        obtain ⟨y, hy, hxy⟩ := ha'
        have h1 : ‖π * (y - x)‖ = 1 := by
          have : π * (y - x) = -(π * x - (π * y + 1)) - 1 := by ring
          rw [this, ← hxy, sub_self, neg_zero, zero_sub, norm_neg, norm_one]
        exact (hsmall y hy x hx).ne h1
    · intro z hz
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hz
      rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · rw [norm_mul]; exact mul_le_one₀ hπ1.le (norm_nonneg _) (hint x hx)
      · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_one]))
        rw [norm_mul]; exact mul_le_one₀ hπ1.le (norm_nonneg _) (hint x hx)
    · intro z hz z' hz' hzz'
      have key1 : ∀ x ∈ s, ∀ y ∈ s, π * x ≠ π * y → ‖π‖ ^ (n + 1) < ‖π * x - π * y‖ := by
        intro x hx y hy hne
        have hxy : x ≠ y := fun h => hne (by rw [h])
        rw [← mul_sub, norm_mul, pow_succ, mul_comm ‖π‖ ‖x - y‖]
        exact mul_lt_mul_of_pos_right (hsep x hx y hy hxy) hπpos
      have key2 : ∀ x ∈ s, ∀ y ∈ s, ‖π * x + 1 - π * y‖ = 1 := by
        intro x hx y hy
        have : π * x + 1 - π * y = π * (x - y) + 1 := by ring
        rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_one, max_eq_right (hsmall x hx y hy).le]
        rw [norm_one]; exact (hsmall x hx y hy).ne
      have hlt1 : ‖π‖ ^ (n + 1) < 1 := pow_lt_one₀ hπpos.le hπ1 (Nat.succ_ne_zero n)
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hz hz'
      rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;> rcases hz' with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · exact key1 x hx y hy hzz'
      · rw [← norm_neg (π * x - (π * y + 1)), neg_sub, key2 y hy x hx]; exact hlt1
      · rw [key2 x hx y hy]; exact hlt1
      · have : π * x + 1 - (π * y + 1) = π * x - π * y := by ring
        rw [this]; exact key1 x hx y hy (fun h => hzz' (by rw [h]))

end Local3

end Ws35H

namespace Ws35H

section Local4
variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem unipotentGL2_mem_localIntegralSet {x : v.adicCompletion K} (hx : ‖x‖ ≤ 1) :
    AutomorphicForm.unipotentGL2 x ∈ AutomorphicForm.localIntegralSet K v := by
  have hx' : x ∈ v.adicCompletionIntegers K := (mem_integers_iff_norm_le_one K v x).mpr hx
  have hinv : (((AutomorphicForm.unipotentGL2 x)⁻¹ : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, -x; 0, 1] := rfl
  rw [AutomorphicForm.mem_localIntegralSet, hinv, AutomorphicForm.unipotentGL2_coe]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;> fin_cases i <;> fin_cases j <;>
    simp [one_mem, zero_mem, hx', neg_mem hx']

theorem inv_mul_entry {F : Type*} [Field F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) (x y : F) :
    ((((AutomorphicForm.unipotentGL2 x * diagGL a b ha hb)⁻¹ *
        (AutomorphicForm.unipotentGL2 y * diagGL a b ha hb) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 1) = a⁻¹ * (y - x) * b := by
  have hUinv : (((AutomorphicForm.unipotentGL2 x)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, -x; 0, 1] := rfl
  rw [mul_inv_rev, Units.val_mul, Units.val_mul, Units.val_mul, hUinv, diagGL_inv_coe', diagGL_coe',
    AutomorphicForm.unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem not_mem_localIntegralSet_of_sep (π : v.adicCompletion K) (hπ0 : π ≠ 0) (m₁ m₂ : ℤ)
    (x y : v.adicCompletion K) (hsep : ‖π‖ ^ (m₁ - m₂) < ‖x - y‖) :
    (AutomorphicForm.unipotentGL2 x * diagGL (π ^ m₁) (π ^ m₂) (zpow_ne_zero m₁ hπ0) (zpow_ne_zero m₂ hπ0))⁻¹ *
        (AutomorphicForm.unipotentGL2 y * diagGL (π ^ m₁) (π ^ m₂) (zpow_ne_zero m₁ hπ0) (zpow_ne_zero m₂ hπ0)) ∉
      AutomorphicForm.localIntegralSet K v := by
  intro h
  have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have h01 := (AutomorphicForm.mem_localIntegralSet K v).mp h |>.1 0 1
  rw [inv_mul_entry, mem_integers_iff_norm_le_one] at h01
  rw [norm_mul, norm_mul, norm_inv, norm_zpow, norm_zpow, norm_sub_rev] at h01

  have : ‖x - y‖ ≤ ‖π‖ ^ (m₁ - m₂) := by
    rw [zpow_sub₀ hπpos.ne', div_eq_mul_inv]
    have h1 : 0 < (‖π‖ ^ m₁)⁻¹ := inv_pos.mpr (zpow_pos hπpos _)
    have h2 : 0 < ‖π‖ ^ m₂ := zpow_pos hπpos _
    calc ‖x - y‖ = ((‖π‖ ^ m₁)⁻¹ * ‖x - y‖ * ‖π‖ ^ m₂) * (‖π‖ ^ m₁ * (‖π‖ ^ m₂)⁻¹) := by
          field_simp
      _ ≤ 1 * (‖π‖ ^ m₁ * (‖π‖ ^ m₂)⁻¹) :=
          mul_le_mul_of_nonneg_right h01 (mul_nonneg (zpow_pos hπpos _).le (inv_pos.mpr h2).le)
      _ = ‖π‖ ^ m₁ * (‖π‖ ^ m₂)⁻¹ := one_mul _
  exact (not_lt.mpr this) hsep

theorem unipotent_mul_diag_mem (π : v.adicCompletion K) (hπ0 : π ≠ 0) (m₁ m₂ : ℤ) {x : v.adicCompletion K}
    (hx : ‖x‖ ≤ 1) {ρ : GL (Fin 2) (v.adicCompletion K)}
    (hρ : ρ ∈ AutomorphicForm.localIntegralSet K v *
          {diagGL (π ^ m₁) (π ^ m₂) (zpow_ne_zero m₁ hπ0) (zpow_ne_zero m₂ hπ0)} *
        AutomorphicForm.localIntegralSet K v) :
    AutomorphicForm.unipotentGL2 x * diagGL (π ^ m₁) (π ^ m₂) (zpow_ne_zero m₁ hπ0) (zpow_ne_zero m₂ hπ0) ∈
      AutomorphicForm.localIntegralSet K v * {ρ} * AutomorphicForm.localIntegralSet K v := by
  apply doubleCoset_subset K v (mem_doubleCoset_symm K v hρ)
  exact ⟨_, ⟨_, unipotentGL2_mem_localIntegralSet K v hx, _, rfl, rfl⟩, 1,
    AutomorphicForm.one_mem_localIntegralSet K v, mul_one _⟩

end Local4

section SemiLocal
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

open scoped TensorProduct

abbrev coordGL (w : v.Extension (𝓞 L)) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L) :=
  Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
        L ⊗[K] v.adicCompletion K →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L))

theorem semiLocalIntegralSet_mul_mem {g h : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) (hh : h ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    g * h ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  refine integralUnitsSet_mul_mem ?_ ?_ hg hh
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a + b, map_add _ _ _⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩

theorem semiLocalIntegralSet_inv_mem {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) : g⁻¹ ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
  integralUnitsSet_inv_mem hg

end SemiLocal

end Ws35H

namespace Ws35H
namespace HT

section Residue
variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem exists_uniformizer :
    ∃ π : v.adicCompletion K, Valued.v π = Multiplicative.ofAdd (-1 : ℤ) ∧ π ≠ 0 ∧
      ‖π‖ = ((Ideal.absNorm v.asIdeal : NNReal) : ℝ)⁻¹ ∧ ‖π‖ < 1 ∧ ‖π‖ ≤ 1 ∧
      ∀ x : v.adicCompletion K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k := by
  obtain ⟨π₀, hπ₀⟩ := v.valuation_exists_uniformizer K
  set π : v.adicCompletion K := ((WithVal.equiv (v.valuation K)).symm π₀ : v.adicCompletion K) with hπdef
  have hvπ : Valued.v π = WithZero.exp (-1 : ℤ) := by
    rw [hπdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ₀
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hvπ; exact WithZero.exp_ne_zero hvπ.symm
  set b : NNReal := (Ideal.absNorm v.asIdeal : NNReal) with hb
  have hb1 : 1 < b := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hb1' : (1 : ℝ) < b := by exact_mod_cast hb1
  have hnorm : ∀ (x : v.adicCompletion K) (hx : x ≠ 0), ‖x‖ = (b : ℝ) ^
      Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff Valued.v).mpr hx)) := by
    intro x hx
    rw [NumberField.FinitePlace.norm_def v x,
      WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff Valued.v).mpr hx)]
    push_cast; rfl
  have hnπ : ‖π‖ = (b : ℝ) ^ (-1 : ℤ) := by
    rw [hnorm π hπ0]
    congr 1
    have h0 : (Valued.v π) ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hπ0
    have : (WithZero.unzero h0 : Multiplicative ℤ) = Multiplicative.ofAdd (-1 : ℤ) := by
      rw [← WithZero.coe_inj, WithZero.coe_unzero h0, hvπ]; rfl
    rw [this]; rfl
  have hlt : ‖π‖ < 1 := by rw [hnπ, zpow_neg, zpow_one]; exact inv_lt_one_of_one_lt₀ hb1'
  refine ⟨π, hvπ, hπ0, by rw [hnπ, zpow_neg, zpow_one], hlt, hlt.le, fun x hx => ?_⟩
  refine ⟨-(Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff Valued.v).mpr hx))), ?_⟩
  rw [hnorm x hx, hnπ, ← zpow_mul]
  congr 1; ring

theorem mem_integers_iff_norm_le_one (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, NumberField.FinitePlace.norm_def v x]
  have hb1 : 1 < (Ideal.absNorm v.asIdeal : NNReal) := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [← NNReal.coe_one, NNReal.coe_le_coe, WithZeroMulInt.toNNReal_le_one_iff hb1]

theorem norm_sub_le_max' {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E] (x y : E) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem norm_eq_one_of_gt (π : v.adicCompletion K) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hpow : ∀ x : v.adicCompletion K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k)
    (x : v.adicCompletion K) (hx1 : ‖x‖ ≤ 1) (hx2 : ‖π‖ < ‖x‖) : ‖x‖ = 1 := by
  have hπpos' : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx2; exact (not_lt.mpr (norm_nonneg π)) hx2
  obtain ⟨k, hk⟩ := hpow x hx0
  rw [hk] at hx1 hx2 ⊢
  have h1 : k < 1 := by
    have hx2' : ‖π‖ ^ (1 : ℤ) < ‖π‖ ^ k := by rwa [zpow_one]
    exact (zpow_lt_zpow_iff_right_of_lt_one₀ hπpos' hπ1).mp hx2'
  have h2 : 0 ≤ k := by
    have hx1' : ‖π‖ ^ k ≤ ‖π‖ ^ (0 : ℤ) := by rwa [zpow_zero]
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hπpos' hπ1).mp hx1'
  have : k = 0 := by omega
  rw [this, zpow_zero]

theorem exists_residues (π : v.adicCompletion K) (hvπ : Valued.v π = Multiplicative.ofAdd (-1 : ℤ))
    (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) (hpow : ∀ x : v.adicCompletion K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) :
    ∃ R : Finset (v.adicCompletion K), R.card = Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, ‖r‖ ≤ 1) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → ‖r - r'‖ = 1 := by
  classical
  have hπint : π ∈ v.adicCompletionIntegers K := (mem_integers_iff_norm_le_one K v π).mpr hπ1.le
  set ϖ : v.adicCompletionIntegers K := ⟨π, hπint⟩ with hϖ
  have hcard := IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_quot_span_eq_absNorm K v ϖ hvπ
  set Q := v.adicCompletionIntegers K ⧸ Ideal.span ({ϖ} : Set (v.adicCompletionIntegers K)) with hQ
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne')
  haveI : Fintype Q := Fintype.ofFinite Q
  set sec : Q → v.adicCompletionIntegers K := Function.surjInv Ideal.Quotient.mk_surjective with hsec
  have hsec_inj : Function.Injective sec := Function.injective_surjInv _
  set R : Finset (v.adicCompletion K) := Finset.univ.image (fun q : Q => ((sec q : v.adicCompletionIntegers K) : v.adicCompletion K)) with hR
  have hinj : Function.Injective (fun q : Q => ((sec q : v.adicCompletionIntegers K) : v.adicCompletion K)) :=
    fun q q' h => hsec_inj (Subtype.ext h)
  refine ⟨R, ?_, ?_, ?_⟩
  · rw [hR, Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
  · intro r hr
    rw [hR, Finset.mem_image] at hr
    obtain ⟨q, -, rfl⟩ := hr
    exact (mem_integers_iff_norm_le_one K v _).mp (sec q).2
  · intro r hr r' hr' hne
    rw [hR, Finset.mem_image] at hr hr'
    obtain ⟨q, -, rfl⟩ := hr
    obtain ⟨q', -, rfl⟩ := hr'
    have hqq : q ≠ q' := fun h => hne (by rw [h])

    have hnot : (sec q - sec q' : v.adicCompletionIntegers K) ∉ Ideal.span ({ϖ} : Set (v.adicCompletionIntegers K)) := by
      intro hmem
      apply hqq
      have h1 : Ideal.Quotient.mk (Ideal.span ({ϖ} : Set (v.adicCompletionIntegers K))) (sec q) =
          Ideal.Quotient.mk (Ideal.span ({ϖ} : Set (v.adicCompletionIntegers K))) (sec q') :=
        Ideal.Quotient.eq.mpr hmem
      have hq1 : Ideal.Quotient.mk _ (sec q) = q := Function.surjInv_eq Ideal.Quotient.mk_surjective q
      have hq2 : Ideal.Quotient.mk _ (sec q') = q' := Function.surjInv_eq Ideal.Quotient.mk_surjective q'
      rw [hq1, hq2] at h1; exact h1

    have hle1 : ‖((sec q : v.adicCompletionIntegers K) : v.adicCompletion K) - (sec q' : v.adicCompletionIntegers K)‖ ≤ 1 :=
      (norm_sub_le_max' _ _).trans (max_le ((mem_integers_iff_norm_le_one K v _).mp (sec q).2)
        ((mem_integers_iff_norm_le_one K v _).mp (sec q').2))
    apply norm_eq_one_of_gt K v π hπ0 hπ1 hpow _ hle1
    by_contra hge
    rw [not_lt] at hge
    apply hnot
    rw [Ideal.mem_span_singleton']

    have hint : (((sec q : v.adicCompletionIntegers K) : v.adicCompletion K) - (sec q' : v.adicCompletionIntegers K)) * π⁻¹ ∈
        v.adicCompletionIntegers K := by
      rw [mem_integers_iff_norm_le_one, norm_mul, norm_inv]
      rw [mul_inv_le_iff₀ (norm_pos_iff.mpr hπ0), one_mul]; exact hge
    refine ⟨⟨_, hint⟩, ?_⟩
    apply Subtype.ext
    show (((sec q : v.adicCompletionIntegers K) : v.adicCompletion K) - (sec q' : v.adicCompletionIntegers K)) * π⁻¹ * π = _
    rw [inv_mul_cancel_right₀ hπ0]; rfl

theorem exists_separated_full (π : v.adicCompletion K) (hvπ : Valued.v π = Multiplicative.ofAdd (-1 : ℤ))
    (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1) (hpow : ∀ x : v.adicCompletion K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) (n : ℕ) :
    ∃ s : Finset (v.adicCompletion K), s.card = (Ideal.absNorm v.asIdeal) ^ n ∧ (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ‖π‖ ^ n < ‖x - y‖ := by
  classical
  have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ0
  obtain ⟨R, hRcard, hRint, hRsep⟩ := exists_residues K v π hvπ hπ0 hπ1 hpow
  induction n with
  | zero => exact ⟨{0}, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨s, hcard, hint, hsep⟩ := ih
    have hsmall : ∀ x ∈ s, ∀ y ∈ s, ‖π * (x - y)‖ < 1 := by
      intro x hx y hy
      rw [norm_mul]
      calc ‖π‖ * ‖x - y‖ ≤ ‖π‖ * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ hπpos.le
            exact (norm_sub_le_max' x y).trans (max_le (hint x hx) (hint y hy))
        _ < 1 := by rw [mul_one]; exact hπ1

    set f : v.adicCompletion K → v.adicCompletion K → v.adicCompletion K := fun r x => π * x + r with hf
    have hfinj : ∀ r, Function.Injective (f r) := fun r x y h => mul_left_cancel₀ hπ0 (add_right_cancel h)

    have hdiff : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → ∀ x ∈ s, ∀ y ∈ s, ‖f r x - f r' y‖ = 1 := by
      intro r hr r' hr' hrr x hx y hy
      have : f r x - f r' y = π * (x - y) + (r - r') := by simp only [hf]; ring
      rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, hRsep r hr r' hr' hrr,
        max_eq_right (hsmall x hx y hy).le]
      rw [hRsep r hr r' hr' hrr]; exact (hsmall x hx y hy).ne
    have hdisj : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → Disjoint (s.image (f r)) (s.image (f r')) := by
      intro r hr r' hr' hrr
      rw [Finset.disjoint_left]
      intro z hz hz'
      rw [Finset.mem_image] at hz hz'
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨y, hy, hxy⟩ := hz'
      have h1 := hdiff r hr r' hr' hrr x hx y hy
      rw [← hxy, sub_self, norm_zero] at h1
      exact zero_ne_one h1
    refine ⟨R.biUnion (fun r => s.image (f r)), ?_, ?_, ?_⟩
    · rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun r _ => Finset.card_image_of_injective s (hfinj r)),
        Finset.sum_const, hRcard, hcard, pow_succ, smul_eq_mul, mul_comm]
    · intro z hz
      rw [Finset.mem_biUnion] at hz
      obtain ⟨r, hr, hz⟩ := hz
      rw [Finset.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      simp only [hf]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hRint r hr))
      rw [norm_mul]; exact mul_le_one₀ hπ1.le (norm_nonneg _) (hint x hx)
    · intro z hz z' hz' hzz'
      rw [Finset.mem_biUnion] at hz hz'
      obtain ⟨r, hr, hz⟩ := hz
      obtain ⟨r', hr', hz'⟩ := hz'
      rw [Finset.mem_image] at hz hz'
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨y, hy, rfl⟩ := hz'
      have hlt1 : ‖π‖ ^ (n + 1) < 1 := pow_lt_one₀ hπpos.le hπ1 (Nat.succ_ne_zero n)
      by_cases hrr : r = r'
      · subst hrr
        have hxy : x ≠ y := fun h => hzz' (by rw [h])
        have : f r x - f r y = π * (x - y) := by simp only [hf]; ring
        rw [this, norm_mul, pow_succ, mul_comm ‖π‖ ‖x - y‖]
        exact mul_lt_mul_of_pos_right (hsep x hx y hy hxy) hπpos
      · rw [hdiff r hr r' hr' hrr x hx y hy]; exact hlt1

end Residue

end Ws35H.HT

namespace Ws35H
namespace HT

section MultiPlace
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]

local notation "E" => L ⊗[K] HeightOneSpectrum.adicCompletion K v

abbrev cw (w : v.Extension (𝓞 L)) : GL (Fin 2) E →* GL (Fin 2) (w.1.adicCompletion L) :=
  Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v :
        E →+* Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L))

omit [Fintype (v.Extension (𝓞 L))] in
theorem cw_apply (w : v.Extension (𝓞 L)) (g : GL (Fin 2) E) (i j : Fin 2) :
    ((cw K L v w g : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j =
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
        ((g : Matrix (Fin 2) (Fin 2) E) i j) w := rfl

omit [Fintype (v.Extension (𝓞 L))] in

theorem eq_of_forall_cw_eq (g g' : GL (Fin 2) E) (h : ∀ w, cw K L v w g = cw K L v w g') : g = g' := by
  apply Units.ext
  ext i j
  apply (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).injective
  funext w
  have := congrArg (fun u : GL (Fin 2) (w.1.adicCompletion L) =>
    (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j) (h w)
  simpa only [cw_apply] using this

omit [Fintype (v.Extension (𝓞 L))] in

theorem exists_forall_cw_eq (G : ∀ w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L)) :
    ∃ g : GL (Fin 2) E, ∀ w, cw K L v w g = G w := by
  set e := HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v with he
  set M : Matrix (Fin 2) (Fin 2) (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
    fun i j w => (G w : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j with hM
  set M' : Matrix (Fin 2) (Fin 2) (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
    fun i j w => (((G w)⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j
    with hM'
  have hMM' : M * M' = 1 := by
    ext i j w
    have h2 := congrFun (congrFun (Units.mul_inv (G w)) i) j
    rw [Matrix.mul_apply] at h2
    rw [Matrix.mul_apply, Finset.sum_apply]
    simp only [hM, hM', Matrix.one_apply, Pi.mul_apply, ite_apply, Pi.one_apply, Pi.zero_apply] at h2 ⊢
    exact h2
  have hM'M : M' * M = 1 := by
    ext i j w
    have h2 := congrFun (congrFun (Units.inv_mul (G w)) i) j
    rw [Matrix.mul_apply] at h2
    rw [Matrix.mul_apply, Finset.sum_apply]
    simp only [hM, hM', Matrix.one_apply, Pi.mul_apply, ite_apply, Pi.one_apply, Pi.zero_apply] at h2 ⊢
    exact h2
  set U : GL (Fin 2) (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) := ⟨M, M', hMM', hM'M⟩ with hU
  refine ⟨Matrix.GeneralLinearGroup.map e.symm.toRingEquiv.toRingHom U, fun w => ?_⟩
  apply Units.ext; ext i j
  rw [cw_apply]
  show e (e.symm (M i j)) w = _
  rw [AlgEquiv.apply_symm_apply]

omit [Fintype (v.Extension (𝓞 L))] in
theorem cw_mem_of_mem {g : GL (Fin 2) E} (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v)
    (w : v.Extension (𝓞 L)) : cw K L v w g ∈ AutomorphicForm.localIntegralSet L w.1 := by
  classical
  haveI : Fintype (v.Extension (𝓞 L)) :=
    @Fintype.ofFinite _ (HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v)
  exact ((AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
    K L v).1 g).mp hg w

theorem mem_of_forall_cw_mem {g : GL (Fin 2) E}
    (hg : ∀ w, cw K L v w g ∈ AutomorphicForm.localIntegralSet L w.1) :
    g ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
  ((AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
    K L v).1 g).mpr hg

theorem cw_mem_doubleCoset {a g : GL (Fin 2) E}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v)
    (w : v.Extension (𝓞 L)) :
    cw K L v w g ∈ AutomorphicForm.localIntegralSet L w.1 * {cw K L v w a} * AutomorphicForm.localIntegralSet L w.1 := by
  obtain ⟨y, hy, k₂, hk₂, rfl⟩ := hg
  obtain ⟨k₁, hk₁, a', ha', rfl⟩ := hy
  rw [Set.mem_singleton_iff] at ha'; subst a'
  refine ⟨_, ⟨_, cw_mem_of_mem K L v hk₁ w, _, rfl, rfl⟩, _, cw_mem_of_mem K L v hk₂ w, ?_⟩
  rw [map_mul, map_mul]

theorem mem_doubleCoset_of_forall_cw {a g : GL (Fin 2) E}
    (hg : ∀ w, cw K L v w g ∈
      AutomorphicForm.localIntegralSet L w.1 * {cw K L v w a} * AutomorphicForm.localIntegralSet L w.1) :
    g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v := by
  classical
  have hex : ∀ w : v.Extension (𝓞 L), ∃ k₁ k₂ : GL (Fin 2) (w.1.adicCompletion L),
      k₁ ∈ AutomorphicForm.localIntegralSet L w.1 ∧ k₂ ∈ AutomorphicForm.localIntegralSet L w.1 ∧
        cw K L v w g = k₁ * cw K L v w a * k₂ := by
    intro w
    obtain ⟨y, hy, k₂, hk₂, hyk⟩ := hg w
    obtain ⟨k₁, hk₁, a', ha', rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha'; subst a'
    exact ⟨k₁, k₂, hk₁, hk₂, hyk.symm⟩
  choose k₁ k₂ hk₁ hk₂ hgk using hex
  obtain ⟨K₁, hK₁⟩ := exists_forall_cw_eq K L v k₁
  obtain ⟨K₂, hK₂⟩ := exists_forall_cw_eq K L v k₂
  have h1 : K₁ ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
    mem_of_forall_cw_mem K L v (fun w => by rw [hK₁]; exact hk₁ w)
  have h2 : K₂ ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
    mem_of_forall_cw_mem K L v (fun w => by rw [hK₂]; exact hk₂ w)
  have hg' : g = K₁ * a * K₂ := eq_of_forall_cw_eq K L v _ _ (fun w => by rw [map_mul, map_mul, hK₁, hK₂, hgk])
  rw [hg']
  exact ⟨_, ⟨_, h1, _, rfl, rfl⟩, _, h2, rfl⟩

end MultiPlace

end Ws35H.HT

namespace Ws35H
namespace HT

section Volume
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]

local notation "E" => L ⊗[K] HeightOneSpectrum.adicCompletion K v

set_option synthInstance.maxHeartbeats 1600000 in

theorem h2_main :
    ∃ π : ∀ w : v.Extension (𝓞 L), w.1.adicCompletion L,
      (∀ w, π w ≠ 0 ∧ ‖π w‖ = ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)⁻¹) ∧
      ∀ a : GL (Fin 2) E,
        ∃ (k : v.Extension (𝓞 L) → ℤ) (m : v.Extension (𝓞 L) → ℕ)
          (d : ∀ w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L)),
          (∀ w, ((d w : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
              Matrix.diagonal ![π w ^ (k w + m w), π w ^ (k w)]) ∧
          (∀ g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v,
            ∀ w : v.Extension (𝓞 L), cw K L v w g ∈
                AutomorphicForm.localIntegralSet L w.1 * {d w} * AutomorphicForm.localIntegralSet L w.1) ∧
          (∏ w, ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ) ^ (m w)) ≤
            (AutomorphicForm.semiLocalHaar K L v
              (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v)).toReal ∧
          AutomorphicForm.semiLocalHaar K L v
              (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v) ≠ ⊤ := by
  classical

  have hU := fun w : v.Extension (𝓞 L) => exists_uniformizer L w.1
  choose π hvπ hπ0 hπq hπ1 hπ1' hpow using hU
  refine ⟨π, fun w => ⟨hπ0 w, by rw [hπq w]; norm_cast⟩, fun a => ?_⟩

  have hC := fun w : v.Extension (𝓞 L) => exists_cartanType L w.1 (π w) (hπ0 w) (hπ1 w) (hpow w) (cw K L v w a)
  choose m₁ m₂ hm hmem using hC
  set m : v.Extension (𝓞 L) → ℕ := fun w => (m₁ w - m₂ w).toNat with hmdef
  have hkm : ∀ w, m₂ w + (m w : ℤ) = m₁ w := by
    intro w
    have h0 : 0 ≤ m₁ w - m₂ w := by have := hm w; omega
    simp only [hmdef]; rw [Int.toNat_of_nonneg h0]; ring
  set d : ∀ w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L) := fun w =>
    diagGL (π w ^ m₁ w) (π w ^ m₂ w) (zpow_ne_zero _ (hπ0 w)) (zpow_ne_zero _ (hπ0 w)) with hd
  refine ⟨m₂, m, d, fun w => ?_, fun g hg w => ?_, ?_, ?_⟩
  ·
    simp only [hd, diagGL_coe]
    congr 1
    funext i; fin_cases i
    · show π w ^ m₁ w = π w ^ (m₂ w + (m w : ℤ))
      rw [hkm w]
    · rfl
  ·
    exact doubleCoset_subset L w.1 (hmem w) (cw_mem_doubleCoset K L v hg w)
  ·
    obtain ⟨n, kk, hkk, hUn, hdisj, hμ⟩ :=
      AutomorphicForm.exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card K L v a
    rw [hμ, ENNReal.toReal_natCast]

    have hS := fun w : v.Extension (𝓞 L) => exists_separated_full L w.1 (π w) (hvπ w) (hπ0 w) (hπ1 w) (hpow w) (m w)
    choose s hscard hsint hssep using hS

    set pt : (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) → GL (Fin 2) E := fun x =>
      Classical.choose (exists_forall_cw_eq K L v (fun w => AutomorphicForm.unipotentGL2 (x w) * d w)) with hpt
    have hpt_cw : ∀ x w, cw K L v w (pt x) = AutomorphicForm.unipotentGL2 (x w) * d w := fun x =>
      Classical.choose_spec (exists_forall_cw_eq K L v (fun w => AutomorphicForm.unipotentGL2 (x w) * d w))
    set S : Finset (∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) := Fintype.piFinset s with hSdef
    have hScard : S.card = ∏ w, (Ideal.absNorm w.1.asIdeal) ^ (m w) := by
      rw [hSdef, Fintype.card_piFinset]; exact Finset.prod_congr rfl fun w _ => hscard w
    have hmemS : ∀ x ∈ S, ∀ w, x w ∈ s w := fun x hx w => Fintype.mem_piFinset.mp hx w

    have hpt_mem : ∀ x ∈ S, pt x ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} *
        AutomorphicForm.semiLocalIntegralSet K L v := by
      intro x hx
      apply mem_doubleCoset_of_forall_cw K L v
      intro w
      rw [hpt_cw]
      exact unipotent_mul_diag_mem L w.1 (π w) (hπ0 w) (m₁ w) (m₂ w) (hsint w _ (hmemS x hx w)) (hmem w)
    have hidx : ∀ x ∈ S, ∃ i : Fin n, pt x ∈ kk i • (a • AutomorphicForm.semiLocalIntegralSet K L v) := by
      intro x hx
      have := hpt_mem x hx
      rw [hUn, Set.mem_iUnion] at this
      exact this
    have hSne : S.Nonempty := Finset.card_pos.mp (by
      rw [hScard]; exact Finset.prod_pos fun w _ => pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (by exact w.1.ne_bot))) _)
    haveI : Nonempty (Fin n) := by
      obtain ⟨x, hx⟩ := hSne; obtain ⟨i, -⟩ := hidx x hx; exact ⟨i⟩
    choose! f hf using hidx
    have hinj : Set.InjOn f S := by
      intro x hx y hy hxy
      by_contra hne
      have h1 := hf x hx
      have h2 := hf y hy
      rw [hxy] at h1
      simp only [Set.mem_smul_set, smul_eq_mul] at h1 h2
      obtain ⟨c, ⟨c₀, hc₀, rfl⟩, hc⟩ := h1
      obtain ⟨c', ⟨c₀', hc₀', rfl⟩, hc'⟩ := h2
      have hq : (pt x)⁻¹ * pt y ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
        rw [← hc, ← hc']
        simp only [mul_inv_rev]
        have : c₀⁻¹ * a⁻¹ * (kk (f y))⁻¹ * (kk (f y) * (a * c₀')) = c₀⁻¹ * c₀' := by group
        rw [this]
        exact semiLocalIntegralSet_mul_mem K L v (semiLocalIntegralSet_inv_mem K L v hc₀) hc₀'

      have hne' : ∃ w, x w ≠ y w := by
        by_contra hall; push Not at hall; exact hne (funext hall)
      obtain ⟨w, hw⟩ := hne'
      have hq' := cw_mem_of_mem K L v hq w
      rw [map_mul, map_inv, hpt_cw, hpt_cw] at hq'
      refine not_mem_localIntegralSet_of_sep L w.1 (π w) (hπ0 w) (m₁ w) (m₂ w) (x w) (y w) ?_ hq'
      have : ((m₁ w - m₂ w : ℤ)) = (m w : ℕ) := by
        have h0 : 0 ≤ m₁ w - m₂ w := by have := hm w; omega
        simp only [hmdef]; rw [Int.toNat_of_nonneg h0]
      rw [this, zpow_natCast]
      exact hssep w _ (hmemS x hx w) _ (hmemS y hy w) hw
    have hle : S.card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
    rw [Finset.card_univ, Fintype.card_fin, hScard] at hle
    exact_mod_cast hle
  · obtain ⟨n, kk, -, -, -, hμ⟩ :=
      AutomorphicForm.exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card K L v a
    rw [hμ]; exact ENNReal.natCast_ne_top n

end Volume

end Ws35H.HT

namespace Ws35H
namespace HT

section SliceBounds
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]

local notation "E" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "bc" => HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

theorem slice_bounds (π : ∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) (hπ0 : ∀ w, π w ≠ 0)
    (hπ1 : ∀ w, ‖π w‖ ≤ 1) (k : v.Extension (𝓞 L) → ℤ) (m : v.Extension (𝓞 L) → ℕ)
    (d : ∀ w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L))
    (hd : ∀ w, ((d w : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      Matrix.diagonal ![π w ^ (k w + m w), π w ^ (k w)])
    (a : GL (Fin 2) E)
    (hcell : ∀ g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v,
      ∀ w : v.Extension (𝓞 L), cw K L v w g ∈
        AutomorphicForm.localIntegralSet L w.1 * {d w} * AutomorphicForm.localIntegralSet L w.1)
    (α β ξ : E) (g : GL (Fin 2) E)
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v)
    (hgv : (g : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]) (w : v.Extension (𝓞 L)) :
    ‖bc ξ w‖ ≤ ‖π w‖ ^ (k w) ∧ ‖π w‖ ^ (k w + (m w : ℤ)) ≤ ‖bc α w‖ ∧ ‖bc α w‖ ≤ ‖π w‖ ^ (k w) := by
  have hπpos : 0 < ‖π w‖ := norm_pos_iff.mpr (hπ0 w)
  have hm : k w ≤ k w + (m w : ℤ) := by omega
  have hd' : ((d w : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      Matrix.diagonal ![π w ^ (k w + (m w : ℤ)), π w ^ (k w)] := by
    rw [hd w]
  obtain ⟨hdet, hle, -⟩ :=
    (AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm L w.1 (π w) (hπ0 w)
      (hπ1 w) (k w + (m w : ℤ)) (k w) hm (d w) hd' (cw K L v w g)).mp (hcell g hg w)
  have hent : ∀ i j, ((cw K L v w g : GL (Fin 2) (w.1.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j = bc (!![α, ξ; 0, β] i j) w := by
    intro i j; rw [cw_apply, hgv]
  have h01 : ‖bc ξ w‖ ≤ ‖π w‖ ^ (k w) := by
    have := hle 0 1; rw [hent] at this; simpa using this
  have h00 : ‖bc α w‖ ≤ ‖π w‖ ^ (k w) := by
    have := hle 0 0; rw [hent] at this; simpa using this
  have h11 : ‖bc β w‖ ≤ ‖π w‖ ^ (k w) := by
    have := hle 1 1; rw [hent] at this; simpa using this
  have hdet' : ‖bc α w‖ * ‖bc β w‖ = ‖π w‖ ^ (k w + (m w : ℤ) + k w) := by
    rw [← hdet, Matrix.det_fin_two, hent, hent, hent, hent]
    simp [map_zero]
  refine ⟨h01, ?_, h00⟩

  have hP : 0 < ‖π w‖ ^ (k w + (m w : ℤ) + k w) := zpow_pos hπpos _
  have hβpos : 0 < ‖bc β w‖ := by
    rcases (norm_nonneg (bc β w)).eq_or_lt with h | h
    · exfalso; rw [← h, mul_zero] at hdet'; exact hP.ne hdet'
    · exact h
  have key : ‖π w‖ ^ (k w + (m w : ℤ)) * ‖π w‖ ^ (k w) = ‖bc α w‖ * ‖bc β w‖ := by
    rw [hdet', ← zpow_add₀ hπpos.ne']

  have h2 : ‖π w‖ ^ (k w + (m w : ℤ)) * ‖π w‖ ^ (k w) ≤ ‖bc α w‖ * ‖π w‖ ^ (k w) := by
    rw [key]; exact mul_le_mul_of_nonneg_left h11 (norm_nonneg _)
  exact le_of_mul_le_mul_right h2 (zpow_pos hπpos _)

def boxXi (π : ∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) (k : v.Extension (𝓞 L) → ℤ) : Set E :=
  {ξ | ∀ w, ‖bc ξ w‖ ≤ ‖π w‖ ^ (k w)}

def boxAlpha (π : ∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) (k : v.Extension (𝓞 L) → ℤ)
    (m : v.Extension (𝓞 L) → ℕ) : Set E :=
  {α | ∀ w, ‖π w‖ ^ (k w + (m w : ℤ)) ≤ ‖bc α w‖ ∧ ‖bc α w‖ ≤ ‖π w‖ ^ (k w)}

theorem iSup_slice_le [MeasurableSpace E] (ν : Measure E)
    (π : ∀ w : v.Extension (𝓞 L), w.1.adicCompletion L) (hπ0 : ∀ w, π w ≠ 0)
    (hπ1 : ∀ w, ‖π w‖ ≤ 1) (k : v.Extension (𝓞 L) → ℤ) (m : v.Extension (𝓞 L) → ℕ)
    (d : ∀ w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L))
    (hd : ∀ w, ((d w : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      Matrix.diagonal ![π w ^ (k w + m w), π w ^ (k w)])
    (a : GL (Fin 2) E)
    (hcell : ∀ g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v,
      ∀ w : v.Extension (𝓞 L), cw K L v w g ∈
        AutomorphicForm.localIntegralSet L w.1 * {d w} * AutomorphicForm.localIntegralSet L w.1)
    (α : E) :
    (⨆ β : E, ν {ξ : E | ∃ g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v,
        (g : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]}) ≤
      (boxAlpha K L v π k m).indicator (fun _ => ν (boxXi K L v π k)) α := by
  classical
  refine iSup_le fun β => ?_
  by_cases hα : α ∈ boxAlpha K L v π k m
  · rw [Set.indicator_of_mem hα]
    refine measure_mono fun ξ hξ => ?_
    obtain ⟨g, hg, hgv⟩ := hξ
    exact fun w => (slice_bounds K L v π hπ0 hπ1 k m d hd a hcell α β ξ g hg hgv w).1
  · rw [Set.indicator_of_notMem hα]
    have : {ξ : E | ∃ g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v,
        (g : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]} = ∅ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨g, hg, hgv⟩
      exact hα fun w => (slice_bounds K L v π hπ0 hπ1 k m d hd a hcell α β ξ g hg hgv w).2
    rw [this, measure_empty]

end SliceBounds

end Ws35H.HT

namespace Ws35H
namespace HT

section LocalVolumes
variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem _root_.Ws35H.HT.exists_irreducible : ∃ ϖ : v.adicCompletionIntegers K, Irreducible ϖ :=
  IsDiscreteValuationRing.exists_irreducible _

p2m_export "Ws35H.HT" "exists_irreducible"
theorem norm_lt_one_of_irreducible (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) :
    ‖(ϖ : v.adicCompletion K)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff, ← NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one]
  exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit

theorem coe_ne_zero_of_irreducible (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) :
    (ϖ : v.adicCompletion K) ≠ 0 := by
  intro h; apply hϖ.ne_zero; exact_mod_cast h

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]

theorem ball_sphere_volume (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) :
    ‖(ϖ : v.adicCompletion K)‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ∧
    (∀ n : ℤ, ν.real {u : v.adicCompletion K | ‖u‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ n} =
      ‖(ϖ : v.adicCompletion K)‖ ^ n * ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∧
    (∀ n : ℤ, ν.real {u : v.adicCompletion K | ‖u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ n} =
      ‖(ϖ : v.adicCompletion K)‖ ^ n * (1 - ‖(ϖ : v.adicCompletion K)‖) *
        ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
  have hϖ0 := coe_ne_zero_of_irreducible K v ϖ hϖ
  have hϖlt := norm_lt_one_of_irreducible K v ϖ hϖ
  have hϖpos : 0 < ‖(ϖ : v.adicCompletion K)‖ := norm_pos_iff.mpr hϖ0
  set a : v.adicCompletion K := 1 + ϖ with ha
  have ha0 : a ≠ 0 := by
    intro h
    have h1 : (ϖ : v.adicCompletion K) = -1 := by rw [ha] at h; linear_combination h
    have : ‖(ϖ : v.adicCompletion K)‖ = 1 := by rw [h1, norm_neg, norm_one]
    exact hϖlt.ne this
  have hab : a ≠ 1 := by
    intro h; apply hϖ0; rw [ha] at h; linear_combination h
  have hsub : a - 1 = (ϖ : v.adicCompletion K) := by rw [ha]; ring
  set t : GL (Fin 2) (v.adicCompletion K) := diagGL a 1 ha0 one_ne_zero with htdef
  have ht : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![a, 1] := diagGL_coe _ _ _ _
  have hdl : ((1 : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖ : v.adicCompletion K) ^ (0 : ℤ), (ϖ : v.adicCompletion K) ^ (0 : ℤ)] := by
    rw [zpow_zero, Units.val_one, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> rfl
  obtain ⟨h0, -, h2, h3, -⟩ :=
    AutomorphicForm.unipotentGL2_conj_diagonal_mem_doubleCoset_iff_and_norm_sub_mul_measureReal_le K v ϖ hϖ 0 0
      le_rfl 1 hdl a 1 hab t ht ν
  refine ⟨h0, fun n => ?_, fun n => ?_⟩
  · have := h2 (n + 1)
    rw [hsub] at this
    have hset : {u : v.adicCompletion K | ‖(ϖ : v.adicCompletion K) * u‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ (n + 1)} =
        {u : v.adicCompletion K | ‖u‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ n} := by
      ext u
      simp only [Set.mem_setOf_eq, norm_mul, zpow_add_one₀ hϖpos.ne', mul_comm (‖(ϖ : v.adicCompletion K)‖ ^ n)]
      exact ⟨fun h => le_of_mul_le_mul_left h hϖpos, fun h => mul_le_mul_of_nonneg_left h hϖpos.le⟩
    rw [hset, zpow_add_one₀ hϖpos.ne'] at this
    have h' : ‖(ϖ : v.adicCompletion K)‖ * ν.real {u : v.adicCompletion K | ‖u‖ ≤ ‖(ϖ : v.adicCompletion K)‖ ^ n} =
        ‖(ϖ : v.adicCompletion K)‖ * (‖(ϖ : v.adicCompletion K)‖ ^ n *
          ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
      rw [this]; ring
    exact mul_left_cancel₀ hϖpos.ne' h'
  · have := h3 (n + 1)
    rw [hsub] at this
    have hset : {u : v.adicCompletion K | ‖(ϖ : v.adicCompletion K) * u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ (n + 1)} =
        {u : v.adicCompletion K | ‖u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ n} := by
      ext u
      simp only [Set.mem_setOf_eq, norm_mul, zpow_add_one₀ hϖpos.ne', mul_comm (‖(ϖ : v.adicCompletion K)‖ ^ n)]
      exact (mul_right_injective₀ hϖpos.ne').eq_iff
    rw [hset, zpow_add_one₀ hϖpos.ne'] at this
    have h' : ‖(ϖ : v.adicCompletion K)‖ * ν.real {u : v.adicCompletion K | ‖u‖ = ‖(ϖ : v.adicCompletion K)‖ ^ n} =
        ‖(ϖ : v.adicCompletion K)‖ * (‖(ϖ : v.adicCompletion K)‖ ^ n * (1 - ‖(ϖ : v.adicCompletion K)‖) *
          ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
      rw [this]; ring
    exact mul_left_cancel₀ hϖpos.ne' h'

theorem measure_ball_ne_top (R : ℝ) : ν {u : v.adicCompletion K | ‖u‖ ≤ R} ≠ ⊤ := by
  have : {u : v.adicCompletion K | ‖u‖ ≤ R} = Metric.closedBall 0 R := by
    ext u; simp [Metric.mem_closedBall, dist_zero_right]
  rw [this]
  exact (isCompact_closedBall _ _).measure_lt_top.ne

theorem measurableSet_ball (R : ℝ) : MeasurableSet {u : v.adicCompletion K | ‖u‖ ≤ R} := by
  have : {u : v.adicCompletion K | ‖u‖ ≤ R} = Metric.closedBall 0 R := by
    ext u; simp [Metric.mem_closedBall, dist_zero_right]
  rw [this]; exact Metric.isClosed_closedBall.measurableSet

theorem measurableSet_sphere (R : ℝ) : MeasurableSet {u : v.adicCompletion K | ‖u‖ = R} := by
  have : {u : v.adicCompletion K | ‖u‖ = R} = Metric.sphere 0 R := by
    ext u; simp [Metric.mem_sphere, dist_zero_right]
  rw [this]; exact Metric.isClosed_sphere.measurableSet

end LocalVolumes

end Ws35H.HT

namespace Ws35H
namespace HT

section ProductMeasure
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]

local notation "E" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "bc" => HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

theorem continuous_bc : Continuous (fun x : E => bc x) :=
  (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).continuous

variable [MeasurableSpace (L ⊗[K] HeightOneSpectrum.adicCompletion K v)]
  [BorelSpace (L ⊗[K] HeightOneSpectrum.adicCompletion K v)]
  [∀ w : v.Extension (𝓞 L), MeasurableSpace (w.1.adicCompletion L)]
  [∀ w : v.Extension (𝓞 L), BorelSpace (w.1.adicCompletion L)]

theorem measurable_bc : Measurable (fun x : E => bc x) :=
  measurable_pi_iff.mpr fun w => ((continuous_apply w).comp (continuous_bc K L v)).measurable

theorem setOf_forall_eq_preimage (S : ∀ w : v.Extension (𝓞 L), Set (w.1.adicCompletion L)) :
    {x : E | ∀ w, bc x w ∈ S w} = (fun x : E => bc x) ⁻¹' Set.pi Set.univ S := by
  ext x; simp [Set.mem_pi]

theorem measurableSet_coordBox (S : ∀ w : v.Extension (𝓞 L), Set (w.1.adicCompletion L))
    (hS : ∀ w, MeasurableSet (S w)) : MeasurableSet {x : E | ∀ w, bc x w ∈ S w} := by
  rw [setOf_forall_eq_preimage]
  exact measurable_bc K L v (MeasurableSet.univ_pi hS)

theorem measure_coordBox (ν : Measure E) (νw : ∀ w : v.Extension (𝓞 L), Measure (w.1.adicCompletion L))
    [∀ w, SigmaFinite (νw w)] (c : ℝ≥0∞)
    (hmap : Measure.map (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v) ν = c • Measure.pi νw)
    (S : ∀ w : v.Extension (𝓞 L), Set (w.1.adicCompletion L)) (hS : ∀ w, MeasurableSet (S w)) :
    ν {x : E | ∀ w, bc x w ∈ S w} = c * ∏ w, νw w (S w) := by
  rw [setOf_forall_eq_preimage, ← Measure.map_apply (measurable_bc K L v) (MeasurableSet.univ_pi hS)]
  change (Measure.map (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v) ν) (Set.pi Set.univ S) = _
  rw [hmap, Measure.smul_apply, Measure.pi_pi, smul_eq_mul]

end ProductMeasure

end Ws35H.HT

namespace Ws35H
namespace HT

section RealBound

theorem real_bound {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp0 : ∀ i, 0 < p i) (hp2 : ∀ i, p i ≤ 1 / 2)
    (k : ι → ℤ) (m : ι → ℕ) (M : ℝ) (hM : ∏ i, (p i)⁻¹ ^ (m i) ≤ M) :
    (∏ i, p i ^ k i) * ∏ i, ((m i : ℝ) + 1) ≤
      (Real.log 2)⁻¹ ^ Fintype.card ι *
        (((∏ i, p i ^ (2 * k i + (m i : ℤ))) * M) ^ ((1 : ℝ) / 2) * (1 + Real.log M) ^ Fintype.card ι) := by
  classical
  have hp1 : ∀ i, p i ≤ 1 := fun i => (hp2 i).trans (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith

  have hge1 : ∀ i, (1 : ℝ) ≤ (p i)⁻¹ ^ (m i) := fun i =>
    one_le_pow₀ ((one_le_inv₀ (hp0 i)).mpr (hp1 i))
  have hprod_ge : ∀ i, (p i)⁻¹ ^ (m i) ≤ ∏ j, (p j)⁻¹ ^ (m j) := by
    intro i
    calc (p i)⁻¹ ^ (m i) = ∏ j, (if j = i then (p i)⁻¹ ^ (m i) else 1) := by
          rw [Finset.prod_ite_eq']; simp
      _ ≤ ∏ j, (p j)⁻¹ ^ (m j) := Finset.prod_le_prod (fun j _ => by
            by_cases h : j = i
            · rw [if_pos h]; exact pow_nonneg (inv_nonneg.mpr (hp0 i).le) _
            · rw [if_neg h]; exact zero_le_one) (fun j _ => by
          by_cases h : j = i
          · rw [if_pos h]; subst h; exact le_rfl
          · rw [if_neg h]; exact hge1 j)
  have hM1 : 1 ≤ M := by
    refine le_trans ?_ hM
    calc (1 : ℝ) = ∏ j : ι, (1 : ℝ) := by simp
      _ ≤ ∏ j, (p j)⁻¹ ^ (m j) := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => hge1 j)
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1

  have hm : ∀ i, (m i : ℝ) + 1 ≤ (1 + Real.log M) / Real.log 2 := by
    intro i
    rw [le_div_iff₀ hlog2]
    have h2m : (2 : ℝ) ^ (m i) ≤ M := by
      refine le_trans ?_ ((hprod_ge i).trans hM)
      apply pow_le_pow_left₀ (by norm_num)
      rw [le_inv_comm₀ (by norm_num) (hp0 i)]; simpa using hp2 i
    have : (m i : ℝ) * Real.log 2 ≤ Real.log M := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2m
    nlinarith
  have hii : ∏ i, ((m i : ℝ) + 1) ≤ (Real.log 2)⁻¹ ^ Fintype.card ι * (1 + Real.log M) ^ Fintype.card ι := by
    rw [← mul_pow, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
    rw [inv_mul_eq_div]; exact hm i

  have hPk : 0 ≤ ∏ i, p i ^ k i := Finset.prod_nonneg fun i _ => (zpow_pos (hp0 i) _).le
  have hi : ∏ i, p i ^ k i ≤ ((∏ i, p i ^ (2 * k i + (m i : ℤ))) * M) ^ ((1 : ℝ) / 2) := by
    have hsq : (∏ i, p i ^ k i) ^ 2 ≤ (∏ i, p i ^ (2 * k i + (m i : ℤ))) * M := by
      calc (∏ i, p i ^ k i) ^ 2 = (∏ i, p i ^ (2 * k i + (m i : ℤ))) * ∏ i, (p i)⁻¹ ^ (m i) := by
            rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [inv_pow, ← zpow_natCast (p i) (m i), ← zpow_neg, ← zpow_add₀ (hp0 i).ne',
              ← zpow_natCast (p i ^ k i) 2, ← zpow_mul]
            congr 1; push_cast; ring
        _ ≤ (∏ i, p i ^ (2 * k i + (m i : ℤ))) * M :=
            mul_le_mul_of_nonneg_left hM (Finset.prod_nonneg fun i _ => (zpow_pos (hp0 i) _).le)
    calc ∏ i, p i ^ k i = ((∏ i, p i ^ k i) ^ 2) ^ ((1 : ℝ) / 2) := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hPk]
      _ ≤ ((∏ i, p i ^ (2 * k i + (m i : ℤ))) * M) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) hsq (by norm_num)
  calc (∏ i, p i ^ k i) * ∏ i, ((m i : ℝ) + 1)
      ≤ ((∏ i, p i ^ (2 * k i + (m i : ℤ))) * M) ^ ((1 : ℝ) / 2) *
          ((Real.log 2)⁻¹ ^ Fintype.card ι * (1 + Real.log M) ^ Fintype.card ι) :=
        mul_le_mul hi hii (Finset.prod_nonneg fun i _ => by positivity)
          (Real.rpow_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => (zpow_pos (hp0 i) _).le) hMpos.le) _)
    _ = _ := by ring

end RealBound

end Ws35H.HT

namespace Ws35H
namespace HT

section Main
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

local notation "E" => L ⊗[K] HeightOneSpectrum.adicCompletion K v
local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "bc" => HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
local notation "𝒦" => AutomorphicForm.semiLocalIntegralSet K L v
local notation "μ'" => AutomorphicForm.semiLocalHaar K L v

set_option maxHeartbeats 3200000 in

theorem h3_main [MeasurableSpace (L ⊗[K] HeightOneSpectrum.adicCompletion K v)]
    [BorelSpace (L ⊗[K] HeightOneSpectrum.adicCompletion K v)]
    (ν : Measure (L ⊗[K] HeightOneSpectrum.adicCompletion K v)) [ν.IsAddHaarMeasure] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ A : ℕ,
      ∀ (a : GL (Fin 2) E) (r : ℝ),
        ∫⁻ α in {α : E | ‖Algebra.norm Kv α‖ = r},
          (⨆ β : E, ν {ξ : E | ∃ g ∈ 𝒦 * {a} * 𝒦, (g : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]})
            ∂(ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm Kv b‖⁻¹) ≤
        C * ENNReal.ofReal
          ((‖Algebra.norm Kv ((Matrix.GeneralLinearGroup.det a : Eˣ) : E)‖ *
              (μ' (𝒦 * {a} * 𝒦)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (μ' (𝒦 * {a} * 𝒦)).toReal) ^ A) := by
  classical
  haveI hFT : Fintype (v.Extension (𝓞 L)) :=
    @Fintype.ofFinite _ (HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v)

  letI mL : ∀ w : v.Extension (𝓞 L), MeasurableSpace (w.1.adicCompletion L) := fun w => borel _
  haveI bL : ∀ w : v.Extension (𝓞 L), BorelSpace (w.1.adicCompletion L) := fun w => ⟨rfl⟩
  set νw : ∀ w : v.Extension (𝓞 L), Measure (w.1.adicCompletion L) := fun w => Measure.addHaar with hνw
  haveI hνw' : ∀ w, (νw w).IsAddHaarMeasure := fun w => by simp only [hνw]; infer_instance
  obtain ⟨c, hc0, hctop, hmap⟩ :=
    (AutomorphicForm.mem_semiLocalIntegralSet_iff_and_semiLocalHaar_doubleCoset_localEmbed_eq_localHaar_and_map_baseChangeAlgEquiv_eq_smul_pi
      K L v).2.2.2.2 ν νw

  obtain ⟨π, hπ, hH2⟩ :=
    AutomorphicForm.exists_uniformizers_forall_exists_cartanType_mem_doubleCoset_and_prod_pow_le_semiLocalHaar K L v
  have hπ0 : ∀ w, π w ≠ 0 := fun w => (hπ w).1
  have hq2 : ∀ w : v.Extension (𝓞 L), (2 : ℝ) ≤ (Ideal.absNorm w.1.asIdeal : ℕ) := fun w => by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w.1
  have hπpos : ∀ w, 0 < ‖π w‖ := fun w => norm_pos_iff.mpr (hπ0 w)
  have hπhalf : ∀ w, ‖π w‖ ≤ 1 / 2 := fun w => by
    rw [(hπ w).2, ← one_div]; exact one_div_le_one_div_of_le (by norm_num) (hq2 w)
  have hπ1 : ∀ w, ‖π w‖ < 1 := fun w => (hπhalf w).trans_lt (by norm_num)
  have hπle : ∀ w, ‖π w‖ ≤ 1 := fun w => (hπ1 w).le

  have hpow : ∀ (w : v.Extension (𝓞 L)) (x : w.1.adicCompletion L), x ≠ 0 → ∃ j : ℤ, ‖x‖ = ‖π w‖ ^ j := by
    intro w x hx
    obtain ⟨π', -, -, hq', -, -, hpow'⟩ := exists_uniformizer L w.1
    obtain ⟨j, hj⟩ := hpow' x hx
    refine ⟨j, ?_⟩
    rw [hj, hq', (hπ w).2]; norm_cast

  have hloc := fun w : v.Extension (𝓞 L) =>
    let ϖ := Classical.choose (exists_irreducible L w.1)
    ball_sphere_volume L w.1 (νw w) ϖ (Classical.choose_spec (exists_irreducible L w.1))

  set R : v.Extension (𝓞 L) → ℝ := fun w => (νw w).real (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))
    with hR
  have hRnn : ∀ w, 0 ≤ R w := fun w => by simp only [hR]; exact measureReal_nonneg
  have hball : ∀ (w : v.Extension (𝓞 L)) (n : ℤ),
      (νw w) {u : w.1.adicCompletion L | ‖u‖ ≤ ‖π w‖ ^ n} = ENNReal.ofReal (‖π w‖ ^ n * R w) := by
    intro w n
    obtain ⟨h0, h2, -⟩ := hloc w
    have hϖπ : ‖((Classical.choose (exists_irreducible L w.1) : w.1.adicCompletionIntegers L) : w.1.adicCompletion L)‖ =
        ‖π w‖ := by rw [h0, (hπ w).2]
    have := h2 n
    rw [hϖπ] at this
    rw [← this, measureReal_def, ENNReal.ofReal_toReal (measure_ball_ne_top L w.1 (νw w) _)]
  have hsphere : ∀ (w : v.Extension (𝓞 L)) (n : ℤ),
      (νw w) {u : w.1.adicCompletion L | ‖u‖ = ‖π w‖ ^ n} = ENNReal.ofReal (‖π w‖ ^ n * (1 - ‖π w‖) * R w) := by
    intro w n
    obtain ⟨h0, -, h3⟩ := hloc w
    have hϖπ : ‖((Classical.choose (exists_irreducible L w.1) : w.1.adicCompletionIntegers L) : w.1.adicCompletion L)‖ =
        ‖π w‖ := by rw [h0, (hπ w).2]
    have := h3 n
    rw [hϖπ] at this
    have hne : (νw w) {u : w.1.adicCompletion L | ‖u‖ = ‖π w‖ ^ n} ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_ball_ne_top L w.1 (νw w) (‖π w‖ ^ n)) (measure_mono fun u hu => le_of_eq hu)
    rw [← this, measureReal_def, ENNReal.ofReal_toReal hne]

  set g : ℕ := Fintype.card (v.Extension (𝓞 L)) with hg
  set D : ℝ := ∏ w, (1 - ‖π w‖) * R w with hD
  set P : ℝ := ∏ w, R w with hP
  have hDnn : 0 ≤ D := Finset.prod_nonneg fun w _ => mul_nonneg (by linarith [hπ1 w]) (hRnn w)
  have hPnn : 0 ≤ P := Finset.prod_nonneg fun w _ => hRnn w
  refine ⟨c * c * ENNReal.ofReal (D * P * (Real.log 2)⁻¹ ^ g),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hctop hctop) ENNReal.ofReal_ne_top, g, fun a r => ?_⟩
  obtain ⟨k, m, d, hd, hcell, hvol, hfin⟩ := hH2 a

  set μρ := ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm Kv b‖⁻¹ with hμρ
  set shell : Set E := {α : E | ‖Algebra.norm Kv α‖ = r} with hshell
  set BA : Set E := boxAlpha K L v π k m with hBA
  set BX : Set E := boxXi K L v π k with hBX
  set cell : (v.Extension (𝓞 L) → ℤ) → Set E := fun j => {α : E | ∀ w, ‖bc α w‖ = ‖π w‖ ^ (j w)} with hcelldef
  set Jbox : Finset (v.Extension (𝓞 L) → ℤ) := Fintype.piFinset fun w => Finset.Icc (k w) (k w + m w) with hJbox
  set J : Finset (v.Extension (𝓞 L) → ℤ) := Jbox.filter fun j => ∏ w, ‖π w‖ ^ (j w) = r with hJ

  have hBXmeas : MeasurableSet BX :=
    measurableSet_coordBox K L v (fun w => {u | ‖u‖ ≤ ‖π w‖ ^ (k w)}) fun w => measurableSet_ball L w.1 _
  have hBAmeas : MeasurableSet BA := by
    have : BA = {x : E | ∀ w, bc x w ∈ {u : w.1.adicCompletion L | ‖π w‖ ^ (k w + (m w : ℤ)) ≤ ‖u‖ ∧ ‖u‖ ≤ ‖π w‖ ^ (k w)}} := rfl
    rw [this]
    refine measurableSet_coordBox K L v _ fun w => ?_
    exact (measurableSet_le measurable_const continuous_norm.measurable).inter (measurableSet_ball L w.1 _)
  have hcellmeas : ∀ j, MeasurableSet (cell j) := fun j =>
    measurableSet_coordBox K L v (fun w => {u | ‖u‖ = ‖π w‖ ^ (j w)}) fun w => measurableSet_sphere L w.1 _

  have hBXvol : ν BX = c * ENNReal.ofReal (∏ w, ‖π w‖ ^ (k w) * R w) := by
    rw [show BX = {x : E | ∀ w, bc x w ∈ {u : w.1.adicCompletion L | ‖u‖ ≤ ‖π w‖ ^ (k w)}} from rfl,
      measure_coordBox K L v ν νw c hmap _ (fun w => measurableSet_ball L w.1 _),
      ENNReal.ofReal_prod_of_nonneg (fun w _ => mul_nonneg (zpow_pos (hπpos w) _).le (hRnn w))]
    congr 1; exact Finset.prod_congr rfl fun w _ => hball w (k w)
  have hcellvol : ∀ j, ν (cell j) = c * ENNReal.ofReal (∏ w, ‖π w‖ ^ (j w) * (1 - ‖π w‖) * R w) := by
    intro j
    rw [show cell j = {x : E | ∀ w, bc x w ∈ {u : w.1.adicCompletion L | ‖u‖ = ‖π w‖ ^ (j w)}} from rfl,
      measure_coordBox K L v ν νw c hmap _ (fun w => measurableSet_sphere L w.1 _),
      ENNReal.ofReal_prod_of_nonneg (fun w _ => mul_nonneg (mul_nonneg (zpow_pos (hπpos w) _).le
        (by linarith [hπ1 w])) (hRnn w))]
    congr 1; exact Finset.prod_congr rfl fun w _ => hsphere w (j w)

  have hstep1 : ∫⁻ α in shell, (⨆ β : E, ν {ξ : E | ∃ g ∈ 𝒦 * {a} * 𝒦,
      (g : Matrix (Fin 2) (Fin 2) E) = !![α, ξ; 0, β]}) ∂μρ ≤ ν BX * μρ (BA ∩ shell) := by
    calc _ ≤ ∫⁻ α in shell, BA.indicator (fun _ => ν BX) α ∂μρ :=
          lintegral_mono fun α => iSup_slice_le K L v ν π hπ0 hπle k m d hd a hcell α
      _ = ν BX * (μρ.restrict shell) BA := lintegral_indicator_const hBAmeas _
      _ = ν BX * μρ (BA ∩ shell) := by rw [Measure.restrict_apply hBAmeas]

  have hcover : BA ∩ shell ⊆ ⋃ j ∈ J, cell j := by
    intro α ⟨hαB, hαs⟩
    have hne : ∀ w, bc α w ≠ 0 := fun w h => by
      have := (hαB w).1; rw [h, norm_zero] at this
      exact absurd this (not_le.mpr (zpow_pos (hπpos w) _))
    have hj := fun w => hpow w (bc α w) (hne w)
    choose j hj using hj
    have hjmem : j ∈ J := by
      rw [hJ, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hJbox, Fintype.mem_piFinset]
        intro w
        rw [Finset.mem_Icc]
        have h1 := (hαB w).1; have h2 := (hαB w).2
        rw [hj w] at h1 h2
        exact ⟨(zpow_le_zpow_iff_right_of_lt_one₀ (hπpos w) (hπ1 w)).mp h2,
          (zpow_le_zpow_iff_right_of_lt_one₀ (hπpos w) (hπ1 w)).mp h1⟩
      · rw [← hαs, AutomorphicForm.norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply K L v α]
        exact Finset.prod_congr rfl fun w _ => (hj w).symm
    rw [Set.mem_iUnion₂]
    exact ⟨j, hjmem, fun w => hj w⟩

  have hcellmass : ∀ j ∈ J, μρ (cell j) = c * ENNReal.ofReal D := by
    intro j hj
    rw [hJ, Finset.mem_filter] at hj
    obtain ⟨-, hjr⟩ := hj
    have hrpos : 0 < r := by rw [← hjr]; exact Finset.prod_pos fun w _ => zpow_pos (hπpos w) _
    have hρ : ∀ α ∈ cell j, (fun b : E => ENNReal.ofReal ‖Algebra.norm Kv b‖⁻¹) α = ENNReal.ofReal r⁻¹ := by
      intro α hα
      simp only
      rw [AutomorphicForm.norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply K L v α,
        Finset.prod_congr rfl fun w _ => hα w, hjr]
    rw [hμρ, withDensity_apply _ (hcellmeas j), setLIntegral_congr_fun (hcellmeas j) hρ, setLIntegral_const,
      hcellvol j]

    have hsplit : ∏ w, ‖π w‖ ^ (j w) * (1 - ‖π w‖) * R w = r * D := by
      rw [← hjr, hD, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => by ring
    rw [hsplit, ENNReal.ofReal_mul hrpos.le, ← mul_assoc, ← mul_assoc, mul_comm (ENNReal.ofReal r⁻¹) c,
      mul_assoc c, ← ENNReal.ofReal_mul (inv_nonneg.mpr hrpos.le), inv_mul_cancel₀ hrpos.ne', ENNReal.ofReal_one,
      mul_one]

  have hJcard : (J.card : ℝ≥0∞) ≤ ENNReal.ofReal (∏ w, ((m w : ℝ) + 1)) := by
    have h1 : J.card ≤ Jbox.card := Finset.card_filter_le _ _
    have h2 : Jbox.card = ∏ w, (m w + 1) := by
      rw [hJbox, Fintype.card_piFinset]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [Int.card_Icc]; omega
    rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity)]
    calc (J.card : ℝ≥0∞) ≤ (Jbox.card : ℝ≥0∞) := by exact_mod_cast h1
      _ = ∏ w, ((m w + 1 : ℕ) : ℝ≥0∞) := by rw [h2]; push_cast; rfl
      _ = ∏ w, ENNReal.ofReal ((m w : ℝ) + 1) := Finset.prod_congr rfl fun w _ => by
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  have hstep4 : μρ (BA ∩ shell) ≤ ENNReal.ofReal (∏ w, ((m w : ℝ) + 1)) * (c * ENNReal.ofReal D) := by
    calc μρ (BA ∩ shell) ≤ μρ (⋃ j ∈ J, cell j) := measure_mono hcover
      _ ≤ ∑ j ∈ J, μρ (cell j) := measure_biUnion_finset_le J cell
      _ = ∑ j ∈ J, c * ENNReal.ofReal D := Finset.sum_congr rfl hcellmass
      _ = J.card * (c * ENNReal.ofReal D) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (∏ w, ((m w : ℝ) + 1)) * (c * ENNReal.ofReal D) := mul_le_mul_left hJcard _

  have hdet : ‖Algebra.norm Kv ((Matrix.GeneralLinearGroup.det a : Eˣ) : E)‖ =
      ∏ w, ‖π w‖ ^ (2 * k w + (m w : ℤ)) := by
    rw [AutomorphicForm.norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply K L v]
    refine Finset.prod_congr rfl fun w _ => ?_

    have ha : a ∈ 𝒦 * {a} * 𝒦 := ⟨1 * a, ⟨1, AutomorphicForm.one_mem_semiLocalIntegralSet K L v, a, rfl, rfl⟩, 1,
      AutomorphicForm.one_mem_semiLocalIntegralSet K L v, by simp⟩
    have hm' : k w ≤ k w + (m w : ℤ) := by omega
    obtain ⟨hdetw, -, -⟩ :=
      (AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm L w.1 (π w) (hπ0 w)
        (hπle w) (k w + (m w : ℤ)) (k w) hm' (d w) (hd w) (cw K L v w a)).mp (hcell a ha w)
    have : bc (((Matrix.GeneralLinearGroup.det a : Eˣ) : E)) w =
        ((cw K L v w a : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)).det := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
      simp only [cw_apply, map_sub, map_mul, Pi.sub_apply, Pi.mul_apply]
    rw [this, hdetw]; congr 1; ring
  have hreal : (∏ w, ‖π w‖ ^ (k w) * R w) * (∏ w, ((m w : ℝ) + 1)) * D ≤
      D * P * (Real.log 2)⁻¹ ^ g *
        ((‖Algebra.norm Kv ((Matrix.GeneralLinearGroup.det a : Eˣ) : E)‖ * (μ' (𝒦 * {a} * 𝒦)).toReal) ^ ((1 : ℝ) / 2) *
          (1 + Real.log (μ' (𝒦 * {a} * 𝒦)).toReal) ^ g) := by
    have hM : ∏ w, (‖π w‖)⁻¹ ^ (m w) ≤ (μ' (𝒦 * {a} * 𝒦)).toReal := by
      refine le_trans (le_of_eq ?_) hvol
      exact Finset.prod_congr rfl fun w _ => by rw [(hπ w).2, inv_inv]
    have key := real_bound (fun w => ‖π w‖) hπpos hπhalf k m _ hM
    rw [hdet, Finset.prod_mul_distrib, ← hP]
    have := mul_le_mul_of_nonneg_left key (mul_nonneg hDnn hPnn)
    calc (∏ w, ‖π w‖ ^ k w) * P * (∏ w, ((m w : ℝ) + 1)) * D
        = D * P * ((∏ w, ‖π w‖ ^ k w) * ∏ w, ((m w : ℝ) + 1)) := by ring
      _ ≤ D * P * ((Real.log 2)⁻¹ ^ g * ((( ∏ w, ‖π w‖ ^ (2 * k w + (m w : ℤ))) *
            (μ' (𝒦 * {a} * 𝒦)).toReal) ^ ((1 : ℝ) / 2) * (1 + Real.log (μ' (𝒦 * {a} * 𝒦)).toReal) ^ g)) := this
      _ = _ := by rw [hg]; ring

  calc _ ≤ ν BX * μρ (BA ∩ shell) := hstep1
    _ ≤ (c * ENNReal.ofReal (∏ w, ‖π w‖ ^ (k w) * R w)) *
          (ENNReal.ofReal (∏ w, ((m w : ℝ) + 1)) * (c * ENNReal.ofReal D)) := by
        rw [hBXvol]; exact mul_le_mul_right hstep4 _
    _ = c * c * ENNReal.ofReal ((∏ w, ‖π w‖ ^ (k w) * R w) * (∏ w, ((m w : ℝ) + 1)) * D) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (Finset.prod_nonneg fun w _ =>
          mul_nonneg (zpow_pos (hπpos w) _).le (hRnn w)) (Finset.prod_nonneg fun w _ => by positivity)),
          ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => mul_nonneg (zpow_pos (hπpos w) _).le (hRnn w))]
        ring
    _ ≤ c * c * ENNReal.ofReal (D * P * (Real.log 2)⁻¹ ^ g *
          ((‖Algebra.norm Kv ((Matrix.GeneralLinearGroup.det a : Eˣ) : E)‖ * (μ' (𝒦 * {a} * 𝒦)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (μ' (𝒦 * {a} * 𝒦)).toReal) ^ g)) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hreal) _
    _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hDnn hPnn) (by positivity))]
        ring

end Main

end Ws35H.HT

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ A : ℕ,
      ∀ (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (r : ℝ),
        ∫⁻ α in {α : L ⊗[K] v.adicCompletion K | ‖Algebra.norm (v.adicCompletion K) α‖ = r},
          (⨆ β : L ⊗[K] v.adicCompletion K,
            ν {ξ : L ⊗[K] v.adicCompletion K |
                ∃ g ∈ AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v,
                  (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = !![α, ξ; 0, β]})
            ∂(ν.withDensity fun b => ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) b‖⁻¹) ≤
        C * ENNReal.ofReal
          ((‖Algebra.norm (v.adicCompletion K)
                ((Matrix.GeneralLinearGroup.det a : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)‖ *
              (AutomorphicForm.semiLocalHaar K L v
                (AutomorphicForm.semiLocalIntegralSet K L v * {a} *
                  AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ ((1 : ℝ) / 2) *
            (1 + Real.log (AutomorphicForm.semiLocalHaar K L v
                (AutomorphicForm.semiLocalIntegralSet K L v * {a} *
                  AutomorphicForm.semiLocalIntegralSet K L v)).toReal) ^ A) :=
  Ws35H.HT.h3_main K L v ν

end
end S_AutomorphicForm_exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setLIntegral_withDensity_norm_inv_iSup_measure_setOf_upperTriangular_mem_doubleCoset_le (solution)
