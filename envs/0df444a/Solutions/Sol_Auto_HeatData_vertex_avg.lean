-- Prove2me | solution 1 for Auto.HeatData.vertex_avg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:37:17.955608+00:00
-- url     : https://prove2.me/submissions/1b5df939-5e70-4f54-803b-78a96b1daccb

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_abs_gaussianD_le_const
public import Theorems.Thm_Auto_gaussian_conv_gaussian
public import Theorems.Thm_Auto_gaussianD_conv_gaussianD
public import Theorems.Thm_Auto_matCost_average_le
public import Theorems.Thm_Auto_wGram_posSemidef
public import Theorems.Thm_Auto_wGram_smul
public import Theorems.Thm_Auto_HeatData_T_eq_wGram
public import Theorems.Thm_P2M_Auto_gweight_nonneg__bb3decd414c3
public import Theorems.Thm_Auto_continuous_wGram
public import Theorems.Thm_Auto_gaussian_le_sup
public import Theorems.Thm_P2M_Auto_continuous_gaussian__66693ed17080
public import Theorems.Thm_Auto_lintegral_avgMeasure
public import Theorems.Thm_Auto_matCost_smul_le
public import Theorems.Thm_Auto_integral_avgMeasure_real
public import Theorems.Thm_Auto_integrable_avgMeasure_real
public import Theorems.Thm_Auto_matIntegral_wGram
public import Theorems.Thm_Auto_HeatData_w_update2
public import Theorems.Thm_Auto_HeatData_Brow_update2
public import Theorems.Thm_Auto_HeatData_dw_update2
public import Theorems.Thm_Auto_HeatData_R_insert_eq

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) (v : Fin 3) {j : ℕ} (hj : 1 ≤ j) {Ca : ℝ}
    (hCa : ∀ s, 0 < s → ∀ d, |acoef j s d| ≤ Ca * √s) (p : Fin 3 → ℝ) {s : ℝ} (hs : 0 < s) :
    matCost (Hd.T p (fun _ => 11 / 10 * s) v) ((Hd.R p (fun _ => 11 / 10 * s) v)ᴴ * rdiag (fun i
      => Dfun j s (Hd.u i - p v)) * Hd.R p (fun _ => 11 / 10 * s) v) ≤ ENNReal.ofReal (Ca ^ 2 * s)
      * ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) * matCost (Hd.T (Function.update p v (p v +
      d)) (Function.update (fun _ => 11 / 10 * s) v s) v) (Hd.Ui (Function.update p v (p v + d))
      (Function.update (fun _ => 11 / 10 * s) v s) v) := by
  have : Fact (0 < s) := ⟨hs⟩
  set σB : Fin 3 → ℝ := fun _ => 11 / 10 * s
  have hσB : ∀ k, 0 < σB k := fun k => by simp only [σB]; positivity
  set σV := Function.update σB v s
  have hσV : ∀ k, 0 < σV k := fun k => by
    simp only [σV, Function.update_apply]; split_ifs; exacts [hs, hσB k]
  set Bw := Hd.Brow p σB v
  set ν := avgMeasure s
  have hβ : (0 : ℝ) < 1 / 10 * s := by positivity
  set fT : ℝ → ι → ℝ := fun d i => gweight Hd.u Hd.h s (p v + d) i
  set fK : ℝ → ι → ℝ := fun d i => acoef j s d * -(Hd.h * gaussianD 1 s (Hd.u i - (p v + d)))
  have hT : ∀ d, Hd.T (Function.update p v (p v + d)) σV v = wGram Bw (fT d) := fun d => by
    rw [T_eq_wGram Hd _ _ hh.le (hσV v), Brow_update2, w_update2]
  have hK : ∀ d, ((acoef j s d : ℝ) : ℂ) • Hd.Ui (Function.update p v (p v + d)) σV v =
      wGram Bw (fK d) := fun d => by
    rw [Ui, Brow_update2, dw_update2, ← wGram_smul]
    congr 1
  have hfT : ∀ i, Integrable (fun d => fT d i) ν := by
    intro i
    refine integrable_avgMeasure_real s ?_
    exact (integrable_gaussian' hβ).mul_bdd (c := Hd.h * (√(2 * π * s))⁻¹)
      ((continuous_const.mul ((continuous_gaussian' s).comp
        (continuous_const.sub (continuous_const.add continuous_id)))).aestronglyMeasurable)
      (Eventually.of_forall fun d => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gweight_nonneg' _ hh.le _ _ _)]
        exact mul_le_mul_of_nonneg_left (gaussian_le_sup _ _) hh.le)
  have hgK : ∀ d, gaussian (1 / 10 * s) d * acoef j s d =
      -(√s ^ j * gaussianD (j - 1) (1 / 20 * s) d) := fun d => by
    have hne := (gaussian_pos hβ d).ne'
    simp only [acoef]
    rw [mul_neg, mul_div_assoc', mul_comm (gaussian (1 / 10 * s) d), mul_div_assoc,
      div_self hne, mul_one]
  have hfK : ∀ i, Integrable (fun d => fK d i) ν := by
    intro i
    refine integrable_avgMeasure_real s ?_
    obtain ⟨M, hM⟩ := abs_gaussianD_le_const 1 hs
    have h1 : Integrable (fun d => -(√s ^ j * gaussianD (j - 1) (1 / 20 * s) d)) :=
      ((integrable_gaussianD (j - 1) (by positivity)).const_mul _).neg
    have hc1 : Continuous fun d => -(Hd.h * gaussianD 1 s (Hd.u i - (p v + d))) := by
      have := continuous_gaussianD 1 s
      fun_prop
    have := h1.mul_bdd (c := Hd.h * M) hc1.aestronglyMeasurable
      (Eventually.of_forall fun d => by
        change ‖-(Hd.h * gaussianD 1 s (Hd.u i - (p v + d)))‖ ≤ _
        rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hh]
        exact mul_le_mul_of_nonneg_left (hM _) hh.le)
    refine this.congr (Eventually.of_forall fun d => ?_)
    change -(√s ^ j * gaussianD (j - 1) (1 / 20 * s) d) *
      -(Hd.h * gaussianD 1 s (Hd.u i - (p v + d))) = gaussian (1 / 10 * s) d * fK d i
    simp only [fK]; rw [← mul_assoc, hgK]
  have hIT : ∀ i, ∫ d, fT d i ∂ν = Hd.w p σB v i := by
    intro i
    rw [integral_avgMeasure_real]
    simp only [fT, gweight, w, σB]
    have := gaussian_conv_gaussian hs hβ (Hd.u i - p v)
    rw [show s + 1 / 10 * s = 11 / 10 * s by ring] at this
    rw [← this, ← integral_const_mul]
    congr 1; funext d
    rw [show Hd.u i - (p v + d) = Hd.u i - p v - d by ring]; ring
  have hIK : ∀ i, ∫ d, fK d i ∂ν = Hd.w p σB v i * Dfun j s (Hd.u i - p v) := by
    intro i
    rw [integral_avgMeasure_real]
    have e : ∀ d, gaussian (1 / 10 * s) d * fK d i = Hd.h * √s ^ j *
        (gaussianD 1 s (Hd.u i - p v - d) * gaussianD (j - 1) (1 / 20 * s) d) := fun d => by
      simp only [fK]
      rw [← mul_assoc, hgK, show Hd.u i - (p v + d) = Hd.u i - p v - d by ring]; ring
    simp_rw [e]
    rw [integral_const_mul, gaussianD_conv_gaussianD 1 (j - 1) hs (by positivity),
      show 1 + (j - 1) = j by omega, show s + 1 / 20 * s = 21 / 20 * s by ring]
    have hg := (gaussian_pos (by positivity : (0 : ℝ) < 11 / 10 * s) (Hd.u i - p v)).ne'
    simp only [w, gweight, σB, Dfun]
    rw [show Hd.h * gaussian (11 / 10 * s) (Hd.u i - p v) *
        (√s ^ j * gaussianD j (21 / 20 * s) (Hd.u i - p v) / gaussian (11 / 10 * s) (Hd.u i - p
            v)) =
        Hd.h * (gaussian (11 / 10 * s) (Hd.u i - p v) *
          (√s ^ j * gaussianD j (21 / 20 * s) (Hd.u i - p v)) /
            gaussian (11 / 10 * s) (Hd.u i - p v)) by ring, mul_div_cancel_left₀ _ hg]
    ring
  obtain ⟨iT, mT⟩ := matIntegral_wGram (ν := ν) Bw fT hfT
  obtain ⟨iK, mK⟩ := matIntegral_wGram (ν := ν) Bw fK hfK
  have hTavg : matIntegral ν (fun d => wGram Bw (fT d)) = Hd.T p σB v := by
    rw [mT, T_eq_wGram Hd p σB hh.le (hσB v)]
    simp_rw [hIT]
    rfl
  have hKavg : matIntegral ν (fun d => wGram Bw (fK d)) =
      (Hd.R p σB v)ᴴ * rdiag (fun i => Dfun j s (Hd.u i - p v)) * Hd.R p σB v := by
    rw [mK, R_insert_eq Hd hh.le p σB v _ (hσB v)]
    simp_rw [hIK]
    rfl
  letI : MeasurableSpace (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := borel _
  letI : BorelSpace (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := ⟨rfl⟩
  have hTm : Measurable fun d => wGram Bw (fT d) := by
    have : Continuous fun d => wGram Bw (fT d) := continuous_wGram continuous_const fun i =>
      continuous_const.mul ((continuous_gaussian' s).comp
        (continuous_const.sub (continuous_const.add continuous_id)))
    exact this.measurable
  have hTpsd : ∀ d, (wGram Bw (fT d)).PosSemidef := fun d =>
    wGram_posSemidef _ fun i => gweight_nonneg' _ hh.le _ _ _
  have h03 := matCost_average_le hTm hTpsd iT iK
  rw [hTavg, hKavg] at h03
  refine h03.trans ?_
  rw [lintegral_avgMeasure, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun d => ?_
  rw [← hT d, ← hK d]
  have hc := matCost_smul_le (Hd.T (Function.update p v (p v + d)) σV v)
    (Hd.Ui (Function.update p v (p v + d)) σV v) (acoef j s d)
  have ha2 : acoef j s d ^ 2 ≤ Ca ^ 2 * s := by
    have := hCa s hs d
    have h0 := abs_nonneg (acoef j s d)
    rw [← sq_abs]
    calc |acoef j s d| ^ 2 ≤ (Ca * √s) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = Ca ^ 2 * s := by rw [mul_pow, Real.sq_sqrt hs.le]
  calc ENNReal.ofReal (gaussian (1 / 10 * s) d) *
        matCost (Hd.T (Function.update p v (p v + d)) σV v)
          (((acoef j s d : ℝ) : ℂ) • Hd.Ui (Function.update p v (p v + d)) σV v)
      ≤ ENNReal.ofReal (gaussian (1 / 10 * s) d) * (ENNReal.ofReal (acoef j s d ^ 2) *
          matCost (Hd.T (Function.update p v (p v + d)) σV v)
            (Hd.Ui (Function.update p v (p v + d)) σV v)) := mul_le_mul' le_rfl hc
    _ ≤ ENNReal.ofReal (gaussian (1 / 10 * s) d) * (ENNReal.ofReal (Ca ^ 2 * s) *
          matCost (Hd.T (Function.update p v (p v + d)) σV v)
            (Hd.Ui (Function.update p v (p v + d)) σV v)) :=
        mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal ha2) le_rfl)
    _ = _ := by ring
end Auto.HeatData
