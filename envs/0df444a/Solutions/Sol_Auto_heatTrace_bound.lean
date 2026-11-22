-- Prove2me | solution 1 for Auto.heatTrace_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:39:22.815961+00:00
-- url     : https://prove2.me/submissions/ba9930df-a556-4a4c-b337-6313a0c45843

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_cyclic_trace_control
public import Theorems.Thm_Auto_rdiag_isHermitian
public import Theorems.Thm_P2M_Auto_continuous_gaussian__66693ed17080
public import Theorems.Thm_Auto_HeatData_Gm_eq
public import Theorems.Thm_Auto_HeatData_vertex_avg
public import Theorems.Thm_Auto_lintegral_plane_shift
public import Theorems.Thm_Auto_HeatData_measurable_rowCost
public import Theorems.Thm_Auto_sig_rateAt
public import Theorems.Thm_Auto_constD_spec
public import Theorems.Thm_Auto_constA_spec
public import Theorems.Thm_Auto_sum_shift
public import Theorems.Thm_Auto_sq_smul_one_sub_rdiag_psd

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (hh : 0 < Hd.h) {s : ℝ} (hs : 0 < s) :
    ‖((1 / s : ℝ) : ℂ) * ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s‖ₑ ≤
      ENNReal.ofReal (5 / 3 * constD * constA ^ 2) *
        ∑ v, ∫⁻ p, heatCost Hd (rateAt v) (s, p) := by
  obtain ⟨hcD, hD⟩ := constD_spec
  obtain ⟨hcA, hA⟩ := constA_spec
  set σB : Fin 3 → ℝ := fun _ => 11 / 10 * s
  have hσV : ∀ v k, 0 < Function.update σB v s k := fun v k => by
    simp only [σB, Function.update_apply]; split_ifs <;> positivity
  set Φ : Fin 3 → (Fin 3 → ℝ) → ℝ≥0∞ := fun v p =>
    matCost (Hd.T p (Function.update σB v s) v) (Hd.Ui p (Function.update σB v s) v)
  have hΦ : ∀ v, Measurable (Φ v) := fun v => Hd.measurable_rowCost _ (hσV v) v
  have htr : ∀ q : Fin 2 → ℝ, ‖Hd.baseTrace 3 (planePt q) s‖ₑ ≤
      ENNReal.ofReal (5 / 3 * constD) * ∑ v, ENNReal.ofReal (constA ^ 2 * s) *
        ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) *
          Φ v (Function.update (planePt q) v (planePt q v + d)) := by
    intro q
    set p := planePt q
    have hDh : ∀ v, (Hd.Dmat 3 v p s).IsHermitian := fun v => rdiag_isHermitian _
    have hDb : ∀ v, ((constD ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - Hd.Dmat 3 v p s *
        Hd.Dmat 3 v p s).PosSemidef := fun v =>
      sq_smul_one_sub_rdiag_psd fun i => hD 3 v s hs _
    have h05 := cyclic_trace_control (W0 := Hd.W p σB 0) (W1 := Hd.W p σB 1)
      (W2 := Hd.W p σB 2) (D0 := Hd.Dmat 3 0 p s) (D1 := Hd.Dmat 3 1 p s)
      (D2 := Hd.Dmat 3 2 p s) (hDh 0) (hDh 1) (hDh 2) hcD (hDb 0) (hDb 1) (hDb 2)
    rw [← ofReal_norm]
    refine h05.trans (mul_le_mul' le_rfl ?_)
    rw [Fin.sum_univ_three]
    have hv := fun v : Fin 3 => Hd.vertex_avg hh v (by norm_num [dexp]) (hA 3 v) p hs
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact hv 0
    · exact hv 1
    · exact hv 2
  have hI : ∀ v, AEMeasurable (fun q : Fin 2 → ℝ => ENNReal.ofReal (constA ^ 2 * s) *
      ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) *
        Φ v (Function.update (planePt q) v (planePt q v + d))) volume := by
    intro v
    refine (Measurable.lintegral_prod_right' (ν := (volume : Measure ℝ))
      (f := fun z : (Fin 2 → ℝ) × ℝ => ENNReal.ofReal (gaussian (1 / 10 * s) z.2) *
        Φ v (Function.update (planePt z.1) v (planePt z.1 v + z.2))) ?_).const_mul _
      |>.aemeasurable
    refine (ENNReal.measurable_ofReal.comp ((continuous_gaussian' _).measurable.comp
      measurable_snd)).mul ((hΦ v).comp ?_)
    have : Continuous fun z : (Fin 2 → ℝ) × ℝ =>
        Function.update (planePt z.1) v (planePt z.1 v + z.2) := by
      refine continuous_pi fun k => ?_
      by_cases hk : k = v
      · subst hk; simp only [Function.update_self]
        fin_cases k <;> dsimp [planePt] <;> fun_prop
      · simp only [Function.update_of_ne hk]
        fin_cases k <;> dsimp [planePt] <;> fun_prop
    exact this.measurable
  have hcv : ∀ v, ∫⁻ q : Fin 2 → ℝ, ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) *
      Φ v (Function.update (planePt q) v (planePt q v + d)) ≤
      ∫⁻ p, heatCost Hd (rateAt v) (s, p) := by
    intro v
    have hF : Measurable fun p : Fin 3 → ℝ =>
        ENNReal.ofReal (gaussian (1 / 10 * s) (p 0 + p 1 + p 2)) * Φ v p :=
      (ENNReal.measurable_ofReal.comp ((continuous_gaussian' _).measurable.comp
        (by fun_prop))).mul (hΦ v)
    have := lintegral_plane_shift v hF
    simp only [sum_shift] at this
    rw [this]
    refine lintegral_mono fun p => ?_
    simp only [heatCost, HeatData.Gm_eq, Φ]
    rw [sig_rateAt]
    refine mul_le_mul' le_rfl ?_
    exact Finset.single_le_sum (f := fun v' => matCost (Hd.T p
      (Function.update (fun _ => 11 / 10 * s) v s) v')
      (Hd.Ui p (Function.update (fun _ => 11 / 10 * s) v s) v'))
      (fun _ _ => zero_le) (Finset.mem_univ v)
  calc ‖((1 / s : ℝ) : ℂ) * ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s‖ₑ
      = ENNReal.ofReal (1 / s) * ‖∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s‖ₑ := by
        rw [enorm_mul, ← ofReal_norm (((1 / s : ℝ) : ℂ)), Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ ENNReal.ofReal (1 / s) * ∫⁻ q : Fin 2 → ℝ, ‖Hd.baseTrace 3 (planePt q) s‖ₑ :=
        mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
    _ ≤ ENNReal.ofReal (1 / s) * ∫⁻ q : Fin 2 → ℝ, ENNReal.ofReal (5 / 3 * constD) *
        ∑ v, ENNReal.ofReal (constA ^ 2 * s) * ∫⁻ d, ENNReal.ofReal (gaussian (1 / 10 * s) d) *
          Φ v (Function.update (planePt q) v (planePt q v + d)) :=
        mul_le_mul' le_rfl (lintegral_mono htr)
    _ = ENNReal.ofReal (1 / s) * (ENNReal.ofReal (5 / 3 * constD) *
        ∑ v, ENNReal.ofReal (constA ^ 2 * s) * ∫⁻ q : Fin 2 → ℝ, ∫⁻ d,
          ENNReal.ofReal (gaussian (1 / 10 * s) d) *
            Φ v (Function.update (planePt q) v (planePt q v + d))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum' _
          fun v _ => hI v]
        congr 2
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (1 / s) * (ENNReal.ofReal (5 / 3 * constD) *
        ∑ v, ENNReal.ofReal (constA ^ 2 * s) * ∫⁻ p, heatCost Hd (rateAt v) (s, p)) := by
        gcongr with v
        exact hcv v
    _ = ENNReal.ofReal (5 / 3 * constD * constA ^ 2) * ∑ v, ∫⁻ p, heatCost Hd (rateAt v) (s, p) :=
        by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
end Auto
