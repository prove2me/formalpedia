-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:01.96215+00:00
-- url     : https://prove2.me/theorems/f478232a-0573-521c-a293-fe318caef159
-- title:
--   Cont Diff Fubini Study Ratio Comp Chart0
-- statement:
--   Definitions and structural lemmas for Cont Diff Fubini Study Ratio Comp Chart0, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_continuous_chart1_inv
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_analyticAt_const_apply_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_analyticAt_const_inv_apply_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply


set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
def crd0 (x : OnePoint ℂ) : ℂ := x.elim 0 id
def crd1 (x : OnePoint ℂ) : ℂ := x.elim 0 (fun z => z⁻¹)
@[simp] theorem finiteCoord_coe (z : ℂ) : crd0 (z : OnePoint ℂ) = z := rfl
@[simp] theorem finiteCoord_infty : crd0 ∞ = 0 := rfl
@[simp] theorem infiniteCoord_coe (z : ℂ) : crd1 (z : OnePoint ℂ) = z⁻¹ := rfl
@[simp] theorem infiniteCoord_infty : crd1 ∞ = 0 := rfl
theorem continuousOn_finiteCoord : ContinuousOn crd0 (Set.range ((↑) : ℂ → OnePoint ℂ)) := by
  rintro _ ⟨z, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  rw [← OnePoint.isOpenEmbedding_coe.continuousAt_iff]
  exact continuousAt_id
theorem continuousOn_infiniteCoord : ContinuousOn crd1 {x | x ≠ ((0 : ℂ) : OnePoint ℂ)} := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  induction x with
  | infty =>
    show Tendsto crd1 (𝓝 ∞) (𝓝 (crd1 ∞))
    rw [OnePoint.nhds_infty_eq, tendsto_sup, tendsto_map'_iff]
    refine ⟨?_, tendsto_pure_nhds crd1 ∞⟩
    have h : crd1 ∘ ((↑) : ℂ → OnePoint ℂ) = fun z => z⁻¹ := rfl
    rw [h, infiniteCoord_infty, coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  | coe z =>
    have hz : z ≠ 0 := fun h => hx (by rw [h])
    rw [← OnePoint.isOpenEmbedding_coe.continuousAt_iff]
    exact continuousAt_inv₀ hz
def projectiveLineChartAtZero : OpenPartialHomeomorph (OnePoint ℂ) (Fin 1 → ℂ) where
  toFun x := fun _ => crd0 x
  invFun w := ((w 0 : ℂ) : OnePoint ℂ)
  source := Set.range ((↑) : ℂ → OnePoint ℂ)
  target := Set.univ
  map_source' := by intro x _; exact Set.mem_univ _
  map_target' := by intro w _; exact ⟨w 0, rfl⟩
  left_inv' := by rintro _ ⟨z, rfl⟩; rfl
  right_inv' := by
    intro w _
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  open_source := OnePoint.isOpen_range_coe
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_pi.2 fun _ => continuousOn_finiteCoord
  continuousOn_invFun := (OnePoint.continuous_coe.comp (continuous_apply 0)).continuousOn
open scoped Classical in

def projectiveLineChartAtInfinity : OpenPartialHomeomorph (OnePoint ℂ) (Fin 1 → ℂ) where
  toFun x := fun _ => crd1 x
  invFun w := if w 0 = 0 then ∞ else (((w 0)⁻¹ : ℂ) : OnePoint ℂ)
  source := {x | x ≠ ((0 : ℂ) : OnePoint ℂ)}
  target := Set.univ
  map_source' := by intro x _; exact Set.mem_univ _
  map_target' := by
    intro w _
    simp only [Set.mem_setOf_eq]
    split_ifs with h
    · exact OnePoint.infty_ne_coe _
    · intro e
      exact h (inv_eq_zero.1 (OnePoint.coe_injective e))
  left_inv' := by
    intro x hx
    induction x with
    | infty => simp
    | coe z =>
      have hz : z ≠ 0 := fun h => hx (by rw [h])
      simp [hz]
  right_inv' := by
    intro w _
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    by_cases h : w 0 = 0
    · simp [h]
    · simp [h]
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_pi.2 fun _ => continuousOn_infiniteCoord
  continuousOn_invFun := continuous_chart1_inv.continuousOn
theorem projLineChart0_apply (x : OnePoint ℂ) : projectiveLineChartAtZero x = fun _ => crd0 x := rfl
theorem projLineChart1_apply (x : OnePoint ℂ) : projectiveLineChartAtInfinity x = fun _ => crd1 x := rfl
theorem projLineChart0_symm_apply (w : Fin 1 → ℂ) : projectiveLineChartAtZero.symm w = ((w 0 : ℂ) : OnePoint ℂ) := rfl
theorem projLineChart1_symm_of_eq_zero {w : Fin 1 → ℂ} (h : w 0 = 0) : projectiveLineChartAtInfinity.symm w = ∞ := by
  show projectiveLineChartAtInfinity.invFun w = ∞
  dsimp only [projectiveLineChartAtInfinity]
  rw [if_pos h]
theorem projLineChart1_symm_of_ne_zero {w : Fin 1 → ℂ} (h : w 0 ≠ 0) :
    projectiveLineChartAtInfinity.symm w = (((w 0)⁻¹ : ℂ) : OnePoint ℂ) := by
  show projectiveLineChartAtInfinity.invFun w = _
  dsimp only [projectiveLineChartAtInfinity]
  rw [if_neg h]
@[simp] theorem infiniteCoord_projLineChart1_symm (w : Fin 1 → ℂ) : crd1 (projectiveLineChartAtInfinity.symm w) = w 0 := by
  by_cases h : w 0 = 0
  · rw [projLineChart1_symm_of_eq_zero h, infiniteCoord_infty, h]
  · rw [projLineChart1_symm_of_ne_zero h, infiniteCoord_coe, inv_inv]
@[simp] theorem finiteCoord_projLineChart1_symm (w : Fin 1 → ℂ) : crd0 (projectiveLineChartAtInfinity.symm w) = (w 0)⁻¹ := by
  by_cases h : w 0 = 0
  · rw [projLineChart1_symm_of_eq_zero h, finiteCoord_infty, h, inv_zero]
  · rw [projLineChart1_symm_of_ne_zero h, finiteCoord_coe]
theorem projLineChart1_symm_mem_range {w : Fin 1 → ℂ} :
    projectiveLineChartAtInfinity.symm w ∈ Set.range ((↑) : ℂ → OnePoint ℂ) ↔ w 0 ≠ 0 := by
  by_cases h : w 0 = 0
  · rw [projLineChart1_symm_of_eq_zero h]
    exact ⟨fun ⟨z, hz⟩ => absurd hz (OnePoint.coe_ne_infty z), fun h' => absurd h h'⟩
  · rw [projLineChart1_symm_of_ne_zero h]
    exact ⟨fun _ => h, fun _ => ⟨_, rfl⟩⟩
theorem projLineChart0_symm_ne_zero {w : Fin 1 → ℂ} :
    projectiveLineChartAtZero.symm w ≠ ((0 : ℂ) : OnePoint ℂ) ↔ w 0 ≠ 0 := by
  rw [projLineChart0_symm_apply]
  exact ⟨fun h h' => h (by rw [h']), fun h h' => h (OnePoint.coe_injective h')⟩
def p1 : FinHolAtlas 1 (OnePoint ℂ) where
  n := 2
  chart := ![projectiveLineChartAtZero, projectiveLineChartAtInfinity]
  cover := by
    intro x
    induction x with
    | infty => exact ⟨1, show ∞ ∈ projectiveLineChartAtInfinity.source from OnePoint.infty_ne_coe 0⟩
    | coe z => exact ⟨0, show (z : OnePoint ℂ) ∈ projectiveLineChartAtZero.source from ⟨z, rfl⟩⟩
  holo := by
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · show AnalyticOnNhd ℂ (projectiveLineChartAtZero ∘ projectiveLineChartAtZero.symm) _
      have e : (projectiveLineChartAtZero ∘ projectiveLineChartAtZero.symm) = fun w : Fin 1 → ℂ => fun _ : Fin 1 => w 0 := by
        funext w i; rfl
      rw [e]
      exact fun w _ => projLine_analyticAt_const_apply_zero w
    · show AnalyticOnNhd ℂ (projectiveLineChartAtInfinity ∘ projectiveLineChartAtZero.symm)
        (projectiveLineChartAtZero.target ∩ projectiveLineChartAtZero.symm ⁻¹' projectiveLineChartAtInfinity.source)
      have e : (projectiveLineChartAtInfinity ∘ projectiveLineChartAtZero.symm) = fun w : Fin 1 → ℂ => fun _ : Fin 1 => (w 0)⁻¹ := by
        funext w i; rfl
      rw [e]
      exact fun w hw => projLine_analyticAt_const_inv_apply_zero (projLineChart0_symm_ne_zero.1 hw.2)
    · show AnalyticOnNhd ℂ (projectiveLineChartAtZero ∘ projectiveLineChartAtInfinity.symm)
        (projectiveLineChartAtInfinity.target ∩ projectiveLineChartAtInfinity.symm ⁻¹' projectiveLineChartAtZero.source)
      have e : (projectiveLineChartAtZero ∘ projectiveLineChartAtInfinity.symm) = fun w : Fin 1 → ℂ => fun _ : Fin 1 => (w 0)⁻¹ := by
        funext w i; simp only [Function.comp_apply, projLineChart0_apply, finiteCoord_projLineChart1_symm]
      rw [e]
      exact fun w hw => projLine_analyticAt_const_inv_apply_zero (projLineChart1_symm_mem_range.1 hw.2)
    · show AnalyticOnNhd ℂ (projectiveLineChartAtInfinity ∘ projectiveLineChartAtInfinity.symm) _
      have e : (projectiveLineChartAtInfinity ∘ projectiveLineChartAtInfinity.symm) = fun w : Fin 1 → ℂ => fun _ : Fin 1 => w 0 := by
        funext w i; simp only [Function.comp_apply, projLineChart1_apply, infiniteCoord_projLineChart1_symm]
      rw [e]
      exact fun w _ => projLine_analyticAt_const_apply_zero w
open scoped Classical in

def fsPot : LocPot (OnePoint ℂ) where
  U x := if x = ∞ then projectiveLineChartAtInfinity.source else projectiveLineChartAtZero.source
  isOpen_U := by
    intro x
    split_ifs
    · exact projectiveLineChartAtInfinity.open_source
    · exact projectiveLineChartAtZero.open_source
  mem_U := by
    intro x
    split_ifs with h
    · subst h; exact OnePoint.infty_ne_coe 0
    · obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.1 h
      exact ⟨z, rfl⟩
  φ x y := if x = ∞ then (1 / 2) * Real.log (1 + ‖crd1 y‖ ^ 2)
    else (1 / 2) * Real.log (1 + ‖crd0 y‖ ^ 2)
open scoped Classical in

def projectiveLinePairSection (x y : OnePoint ℂ) : ℂ := if x = ∞ then crd1 y else 1
def fsH (x : OnePoint ℂ) : ℝ := x.elim 1 (fun z => ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2))
theorem fsH_chart0 : fsH ∘ projectiveLineChartAtZero.symm = fun w => fsQ w / (1 + fsQ w) := rfl
theorem fsH_chart1 : fsH ∘ projectiveLineChartAtInfinity.symm = fun w => 1 / (1 + fsQ w) := by
  funext w
  simp only [Function.comp_apply]
  by_cases h : w 0 = 0
  · rw [projLineChart1_symm_of_eq_zero h]
    show (1 : ℝ) = 1 / (1 + ‖w 0‖ ^ 2)
    rw [h]
    simp
  · rw [projLineChart1_symm_of_ne_zero h]
    have hn : ‖w 0‖ ≠ 0 := norm_ne_zero_iff.2 h
    show ‖(w 0)⁻¹‖ ^ 2 / (1 + ‖(w 0)⁻¹‖ ^ 2) = 1 / (1 + ‖w 0‖ ^ 2)
    rw [norm_inv, inv_pow]
    field_simp
    ring
theorem projLine_smooth_of_charts {f : OnePoint ℂ → ℝ}
    (h0 : ContDiff ℝ (⊤ : ℕ∞) (f ∘ projectiveLineChartAtZero.symm)) (h1 : ContDiff ℝ (⊤ : ℕ∞) (f ∘ projectiveLineChartAtInfinity.symm)) :
    p1.Smooth f := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · exact h0.contDiffOn
  · exact h1.contDiffOn
theorem contDiff_fsQ' : ContDiff ℝ (⊤ : ℕ∞) fsQ :=
  (contDiff_norm_sq ℂ).comp (contDiff_apply ℝ ℂ (0 : Fin 1))
theorem contDiff_fubiniStudyRatio_comp_chart0 : ContDiff ℝ (⊤ : ℕ∞) (fsH ∘ projectiveLineChartAtZero.symm) := by
  rw [fsH_chart0]
  exact contDiff_fsQ'.div (contDiff_const.add contDiff_fsQ') fun w => by
    simp only [fsQ]
    positivity
theorem contDiff_fubiniStudyRatio_comp_chart1 : ContDiff ℝ (⊤ : ℕ∞) (fsH ∘ projectiveLineChartAtInfinity.symm) := by
  rw [fsH_chart1]
  exact contDiff_const.div (contDiff_const.add contDiff_fsQ') fun w => by
    simp only [fsQ]
    positivity
def fsχ1 (x : OnePoint ℂ) : ℝ := Real.smoothTransition (4 * fsH x - 1)
theorem smooth_fsχ1 : p1.Smooth fsχ1 := by
  refine projLine_smooth_of_charts ?_ ?_
  · have h := Real.smoothTransition.contDiff.comp (((contDiff_const (c := (4 : ℝ))).mul contDiff_fubiniStudyRatio_comp_chart0).sub
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : Fin 1 → ℂ => (1 : ℝ)))
    exact h
  · have h := Real.smoothTransition.contDiff.comp (((contDiff_const (c := (4 : ℝ))).mul contDiff_fubiniStudyRatio_comp_chart1).sub
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : Fin 1 → ℂ => (1 : ℝ)))
    exact h
theorem smooth_one_sub_fsχ1 : p1.Smooth (fun x => 1 - fsχ1 x) := by
  intro j
  have h := (contDiffOn_const (c := (1 : ℝ))).sub (smooth_fsχ1 j)
  exact h
theorem fsH_eq_one_div_one_add_norm_sq_of_ne_zero {x : OnePoint ℂ} (hx : x ≠ ((0 : ℂ) : OnePoint ℂ)) :
    fsH x = 1 / (1 + ‖crd1 x‖ ^ 2) := by
  induction x with
  | infty =>
    show (1 : ℝ) = 1 / (1 + ‖crd1 ∞‖ ^ 2)
    simp
  | coe z =>
    have hz : z ≠ 0 := fun h => hx (by rw [h])
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    show ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2) = 1 / (1 + ‖z⁻¹‖ ^ 2)
    rw [norm_inv, inv_pow]
    field_simp
    ring
theorem continuous_fsH : Continuous fsH := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  induction x with
  | infty =>
    have hU : {x : OnePoint ℂ | x ≠ ((0 : ℂ) : OnePoint ℂ)} ∈ 𝓝 (∞ : OnePoint ℂ) :=
      isOpen_compl_singleton.mem_nhds (OnePoint.infty_ne_coe 0)
    have hc : ContinuousAt crd1 ∞ :=
      (continuousOn_infiniteCoord ∞ (OnePoint.infty_ne_coe 0)).continuousAt hU
    refine ContinuousAt.congr (f := fun x => 1 / (1 + ‖crd1 x‖ ^ 2)) ?_ ?_
    · exact continuousAt_const.div (continuousAt_const.add (hc.norm.pow 2)) (by positivity)
    · filter_upwards [hU] with x hx using (fsH_eq_one_div_one_add_norm_sq_of_ne_zero hx).symm
  | coe z =>
    have hU : Set.range ((↑) : ℂ → OnePoint ℂ) ∈ 𝓝 (z : OnePoint ℂ) :=
      OnePoint.isOpen_range_coe.mem_nhds ⟨z, rfl⟩
    have hc : ContinuousAt crd0 z := (continuousOn_finiteCoord _ ⟨z, rfl⟩).continuousAt hU
    refine ContinuousAt.congr (f := fun x => ‖crd0 x‖ ^ 2 / (1 + ‖crd0 x‖ ^ 2)) ?_ ?_
    · exact (hc.norm.pow 2).div (continuousAt_const.add (hc.norm.pow 2)) (by positivity)
    · filter_upwards [hU] with x hx
      obtain ⟨w, rfl⟩ := hx
      rfl
def projLinePartition : ChartPartition p1 where
  χ := ![fun x => 1 - fsχ1 x, fsχ1]
  smooth := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact smooth_one_sub_fsχ1
    · exact smooth_fsχ1
  nonneg := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · intro x
      show 0 ≤ 1 - fsχ1 x
      exact sub_nonneg.2 (Real.smoothTransition.le_one _)
    · intro x
      exact Real.smoothTransition.nonneg _
  tsupport_subset := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show tsupport (fun x => 1 - fsχ1 x) ⊆ projectiveLineChartAtZero.source
      have hsub : tsupport (fun x => 1 - fsχ1 x) ⊆ {x | fsH x ≤ 1 / 2} := by
        refine closure_minimal ?_ (isClosed_le continuous_fsH continuous_const)
        intro x hx
        by_contra hc
        apply hx
        simp only [Set.mem_setOf_eq, not_le] at hc
        show 1 - Real.smoothTransition (4 * fsH x - 1) = 0
        rw [Real.smoothTransition.one_of_one_le (by linarith)]
        ring
      intro x hx
      have := hsub hx
      induction x with
      | infty =>
        simp only [Set.mem_setOf_eq] at this
        norm_num [fsH] at this
      | coe z => exact ⟨z, rfl⟩
    · show tsupport fsχ1 ⊆ projectiveLineChartAtInfinity.source
      have hsub : tsupport fsχ1 ⊆ {x | 1 / 4 ≤ fsH x} := by
        refine closure_minimal ?_ (isClosed_le continuous_const continuous_fsH)
        intro x hx
        by_contra hc
        apply hx
        simp only [Set.mem_setOf_eq, not_le] at hc
        exact Real.smoothTransition.zero_of_nonpos (by linarith)
      intro x hx h0
      have := hsub hx
      rw [h0] at this
      norm_num [fsH] at this
  sum_eq_one := by
    intro x
    show ∑ j : Fin 2, ![fun x => 1 - fsχ1 x, fsχ1] j x = 1
    simp [Fin.sum_univ_two]
def ptAtlas (Y : Type*) [TopologicalSpace Y] [Unique Y] : FinHolAtlas 0 Y where
  n := 1
  chart _ :=
    { toFun := fun _ => 0
      invFun := fun _ => default
      source := Set.univ
      target := Set.univ
      map_source' := by intro x _; exact Set.mem_univ _
      map_target' := by intro x _; exact Set.mem_univ _
      left_inv' := by intro x _; exact Subsingleton.elim _ _
      right_inv' := by intro x _; exact Subsingleton.elim _ _
      open_source := isOpen_univ
      open_target := isOpen_univ
      continuousOn_toFun := continuousOn_const
      continuousOn_invFun := continuousOn_const }
  cover := fun _ => ⟨0, Set.mem_univ _⟩
  holo := fun _ _ _ _ => analyticAt_const
def ptPart (Y : Type*) [TopologicalSpace Y] [Unique Y] : ChartPartition (ptAtlas Y) where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := Set.subset_univ _
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp
end
end ReciprocityTheory.AnForm.M


