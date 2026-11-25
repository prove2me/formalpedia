-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_ToPotentialChartsChartFun
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:55.386421+00:00
-- url     : https://prove2.me/theorems/c5c0ce9a-5410-532b-876a-6470b668e370
-- title:
--   To Potential Charts Chart Fun
-- statement:
--   Definitions and structural lemmas for To Potential Charts Chart Fun, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ToPotentialChartsChartFun.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__integral_37214bfa7034
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
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
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
theorem closure_image_subset {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [T2Space Y] (e : OpenPartialHomeomorph X Y) {s : Set X} (hs : closure s ⊆ e.source) :
    IsCompact (e '' closure s) ∧ closure (e.target ∩ e.symm ⁻¹' s) ⊆ e '' closure s := by
  have hK : IsCompact (e '' closure s) :=
    isClosed_closure.isCompact.image_of_continuousOn (e.continuousOn.mono hs)
  refine ⟨hK, closure_minimal ?_ hK.isClosed⟩
  rintro y ⟨hy, hys⟩
  exact ⟨e.symm y, subset_closure hys, e.right_inv hy⟩
theorem closure_preimage_subset {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {s : Set Y} (hc : IsCompact (closure s))
    (hs : closure s ⊆ e.target) :
    closure (e.source ∩ e ⁻¹' s) ⊆ e.symm '' closure s := by
  have hK : IsCompact (e.symm '' closure s) := hc.image_of_continuousOn (e.continuousOn_symm.mono hs)
  refine closure_minimal ?_ hK.isClosed
  rintro x ⟨hx, hxs⟩
  exact ⟨e x, subset_closure hxs, e.left_inv hx⟩
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
namespace RegCharts
def ofPotentialCharts [CompactSpace X] (P : PotentialCharts A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) : RegCharts A where
  n := P.N
  ψ := P.chart
  compat := P.compat
  W j := (P.chart j).target
  W' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
  W'' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.inner j
  isOpen_kappaOpenNeighbourhood j := (P.chart j).open_target
  isOpen_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_mid j)
  isOpen_alt_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_inner j)
  W_subset _ := subset_rfl
  isCompact_closure_middle j :=
    (closure_image_subset (P.chart j) (P.closure_mid j)).1.of_isClosed_subset isClosed_closure
      (closure_image_subset (P.chart j) (P.closure_mid j)).2
  closure_W'_subset j := (closure_image_subset (P.chart j) (P.closure_mid j)).2.trans
    (image_subset_iff.2 fun _ hx => (P.chart j).map_source (P.closure_mid j hx))
  closure_W''_subset j := by
    have hs := (P.closure_inner j).trans (P.mid_subset_source j)
    refine (closure_image_subset (P.chart j) hs).2.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(P.chart j).map_source (hs hx), ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.mid j
    rw [(P.chart j).left_inv (hs hx)]
    exact P.closure_inner j hx
  cover x := by
    obtain ⟨j, hj⟩ := P.cover x
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hj)
    refine ⟨j, hs, (P.chart j).map_source hs, ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.inner j
    rw [(P.chart j).left_inv hs]
    exact hj
  θ := P.th
  θ_pot := P.th_pot
  om := om
  om_pot := om_pot
  om_pos := om_pos
  q := P.q
  q_smooth := P.q_smooth
  q_θ j y hy _ := by
    obtain ⟨V, hV, hyV, G, hG, hq⟩ := P.q_th j y y ⟨P.th.mem_U y, hy⟩
    refine ⟨V, hV, hyV, fun x => -G x, fun k => (hG k).neg, fun x hx _ => ?_⟩
    have := hq x hx
    simp only [Complex.neg_re]
    linarith
variable [CompactSpace X] (P : PotentialCharts A) (om : LocPot X) (om_pot : IsPotential A om)
  (om_pos : IsPosPot A om)
end RegCharts
namespace RegCharts
variable (R : RegCharts A)
def restrChart (j : Fin R.n) : OpenPartialHomeomorph X (Fin D → ℂ) :=
  ((R.ψ j).symm.restrOpen (R.W j) (R.isOpen_kappaOpenNeighbourhood j)).symm
def toPotentialCharts [T2Space X] (hW : ∀ j, R.W j ⊆ ball 0 1) : PotentialCharts A where
  N := R.n
  chart := R.restrChart
  compat j k := ⟨(R.compat j k).1.mono fun _ hy => ⟨hy.1, hy.2.1⟩,
    (R.compat j k).2.mono fun _ hy => ⟨hy.1.1, hy.2⟩⟩
  target_subset j := fun _ hy => hW j hy.2
  mid := R.V'
  inner := R.V''
  isOpen_mid j := (R.ψ j).isOpen_inter_preimage (R.isOpen_alt j)
  isOpen_inner j := (R.ψ j).isOpen_inter_preimage (R.isOpen_alt_alt j)
  closure_inner j := by
    have h1 : closure (R.W'' j) ⊆ R.W' j := R.closure_W''_subset j
    have h2 : closure (R.W' j) ⊆ R.W j := R.closure_W'_subset j
    have hc : IsCompact (closure (R.W'' j)) := (R.isCompact_closure_middle j).of_isClosed_subset
      isClosed_closure (closure_minimal ((subset_closure.trans h1).trans subset_closure) isClosed_closure)
    have ht : closure (R.W'' j) ⊆ (R.ψ j).target :=
      h1.trans (subset_closure.trans (h2.trans (R.W_subset j)))
    refine (closure_preimage_subset (R.ψ j) hc ht).trans ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(R.ψ j).map_target (ht hy), ?_⟩
    show R.ψ j ((R.ψ j).symm y) ∈ R.W' j
    rw [(R.ψ j).right_inv (ht hy)]
    exact h1 hy
  closure_mid j := by
    have h2 : closure (R.W' j) ⊆ R.W j := R.closure_W'_subset j
    have ht : closure (R.W' j) ⊆ (R.ψ j).target := h2.trans (R.W_subset j)
    refine (closure_preimage_subset (R.ψ j) (R.isCompact_closure_middle j) ht).trans ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(R.ψ j).map_target (ht hy), ?_⟩
    show R.ψ j ((R.ψ j).symm y) ∈ R.W j
    rw [(R.ψ j).right_inv (ht hy)]
    exact h2 hy
  cover x := by
    obtain ⟨j, h1, h2⟩ := R.cover x
    exact ⟨j, h1, h2⟩
  th := R.θ
  th_pot := R.θ_pot
  q := R.q
  q_smooth j := (R.q_smooth j).mono inter_subset_right
  q_th j x y hy := by
    obtain ⟨hyx, hys, hyW⟩ := hy
    obtain ⟨V, hV, hyV, G₁, hG₁, h₁⟩ := R.q_θ j y hys hyW
    obtain ⟨V₂, hV₂, hyV₂, G₂, hG₂, h₂⟩ := R.θ_pot.2 x y y ⟨hyx, R.θ.mem_U y⟩
    refine ⟨V ∩ V₂ ∩ R.θ.U y, (hV.inter hV₂).inter (R.θ.isOpen_U y),
      ⟨⟨hyV, hyV₂⟩, R.θ.mem_U y⟩, fun z => -(G₁ z + G₂ z),
      fun k => (((hG₁ k).mono fun _ hz => ⟨hz.1, hz.2.1.1⟩).add
        ((hG₂ k).mono fun _ hz => ⟨hz.1, hz.2.1.2⟩)).neg, ?_⟩
    rintro z ⟨⟨⟨⟨hzV, hzV₂⟩, hzU⟩, hzx⟩, hzs, hzW⟩
    have e1 := h₁ z ⟨⟨hzV, hzU⟩, hzs⟩ hzW
    have e2 := h₂ z ⟨⟨hzV₂, hzx⟩, hzU⟩
    show R.q j (R.ψ j z) - R.θ.φ x z = (-(G₁ z + G₂ z)).re
    simp only [Complex.neg_re, Complex.add_re]
    linarith
variable [T2Space X] (hW : ∀ j, R.W j ⊆ ball 0 1)
end RegCharts
section RoundTrip
variable [CompactSpace X] [T2Space X]
end RoundTrip
namespace PotentialCharts
variable (P : PotentialCharts A)
end PotentialCharts
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular


