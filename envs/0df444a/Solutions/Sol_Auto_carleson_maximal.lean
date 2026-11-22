-- Prove2me | solution 1 for Auto.carleson_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:17:21.896583+00:00
-- url     : https://prove2.me/submissions/0d9dc0d9-f85f-46f8-9cea-a60570a432da

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carleson_rough_bound
public import Theorems.Thm_Auto_measurable_carlesonOp
public import Theorems.Thm_Auto_norm_carlesonOp_le
public import Theorems.Thm_Auto_carlesonForm_indicator
public import Theorems.Thm_Auto_volume_le_of_re_le
public import Theorems.Thm_Auto_carlesonLin_mem
public import Theorems.Thm_Auto_measurable_carlesonLin
public import Theorems.Thm_Auto_lt_norm_carlesonLin
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution (R : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℝ → ℂ) (B lam : ℝ), Measurable h →
    (∀ x, ‖h x‖ ≤ B) → (∀ x, R + 11 < |x| → h x = 0) → 0 < lam →
    volume {x | x ∈ Icc (-R) R ∧ ∃ N : ℕ, lam < ‖carlesonOp h (fun _ => (2 * N + 1) * π) x‖} ≤
      ENNReal.ofReal (4 * (2 * K * B / lam) ^ 3) := by
  obtain ⟨K, hK0, hK⟩ := carleson_rough_bound (R + 11)
  refine ⟨K, hK0, fun h B lam hh hB hhz hlam => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set M : ℕ → ℝ := fun N => (2 * N + 1) * π
  have hM0 : ∀ n, 0 ≤ M n := fun n => by positivity
  have hMmono : Monotone M := fun m n hmn => by
    have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    have := Real.pi_pos
    simp only [M]
    nlinarith
  set T : ℕ → ℝ → ℂ := fun m => carlesonOp h fun _ => M m
  set E : ℕ → Set ℝ := fun n => {x | x ∈ Icc (-R) R ∧ ∃ m ≤ n, lam < ‖T m x‖}
  have hU : {x | x ∈ Icc (-R) R ∧ ∃ N : ℕ, lam < ‖carlesonOp h (fun _ => (2 * N + 1) * π) x‖} =
      ⋃ n, E n := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, E, T, M]
    constructor
    · rintro ⟨hx, N, hN⟩
      exact ⟨N, hx, N, le_rfl, hN⟩
    · rintro ⟨n, hx, m, -, hm⟩
      exact ⟨hx, m, hm⟩
  have hmono : Monotone E := fun m n hmn x ⟨hx, k, hk, hl⟩ => ⟨hx, k, hk.trans hmn, hl⟩
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  set ν := carlesonLin T M lam n
  have hνm : Measurable ν :=
    measurable_carlesonLin (fun m => measurable_carlesonOp hh measurable_const) M lam n
  have hνV : ∀ x, |ν x| ≤ M n := fun x => by
    obtain ⟨m, hm, he⟩ := carlesonLin_mem T M lam n x
    rw [show ν x = M m from he, abs_of_nonneg (hM0 m)]
    exact hMmono hm
  set z := carlesonOp h ν
  have hzm : Measurable z := measurable_carlesonOp hh hνm
  have hE : ∀ x ∈ E n, lam < ‖z x‖ := fun x hx => lt_norm_carlesonLin n hx.2
  set ωs : Fin 4 → ℂ := ![1, -1, -Complex.I, Complex.I]
  set Q : Fin 4 → Set ℝ := fun j => {x | x ∈ Icc (-R) R ∧ lam / 2 ≤ (ωs j * z x).re}
  have hcover : E n ⊆ ⋃ j, Q j := by
    intro x hx
    have h₁ := hE x hx
    have h₂ := Complex.norm_le_abs_re_add_abs_im (z x)
    simp only [mem_iUnion, Q, mem_ofPred_eq]
    by_cases hre : lam / 2 ≤ |(z x).re|
    · rcases le_abs.mp hre with h | h
      · exact ⟨0, hx.1, by simpa [ωs] using h⟩
      · exact ⟨1, hx.1, by simpa [ωs] using h⟩
    · have him : lam / 2 ≤ |(z x).im| := by linarith
      rcases le_abs.mp him with h | h
      · exact ⟨2, hx.1, by simpa [ωs] using h⟩
      · exact ⟨3, hx.1, by simpa [ωs] using h⟩
  have hQ : ∀ j, volume (Q j) ≤ ENNReal.ofReal ((2 * K * B / lam) ^ 3) := by
    intro j
    have hQm : MeasurableSet (Q j) := measurableSet_Icc.inter
      (measurableSet_le measurable_const (Complex.measurable_re.comp (hzm.const_mul _)))
    have hfin : volume (Q j) ≠ ⊤ :=
      ((measure_mono fun x hx => hx.1).trans_lt (by simp [Real.volume_Icc])).ne
    have hform := hK (Q j) ν h R (M n) B hQm (fun x hx => hx.1) hνm hνV hh hB hhz
    rw [carlesonForm_indicator hQm hh hνm hB hνV hfin] at hform
    have hzi : IntegrableOn z (Q j) :=
      Measure.integrableOn_of_bounded hfin hzm.aestronglyMeasurable
        (ae_of_all _ (norm_carlesonOp_le hB hνV))
    have hω : ‖ωs j‖ = 1 := by fin_cases j <;> simp [ωs]
    have hv := volume_le_of_re_le hQm hfin hzi (mul_nonneg hK0 hB0) (half_pos hlam) hform hω
      (fun x hx => hx.2)
    rw [← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal (hv.trans_eq ?_)
    congr 1
    field_simp
  calc volume (E n) ≤ volume (⋃ j, Q j) := measure_mono hcover
    _ ≤ ∑ j, volume (Q j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin 4, ENNReal.ofReal ((2 * K * B / lam) ^ 3) := Finset.sum_le_sum fun j _ => hQ j
    _ = ENNReal.ofReal (4 * (2 * K * B / lam) ^ 3) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_mul (by norm_num),
          nsmul_eq_mul]
        norm_num
end Auto
