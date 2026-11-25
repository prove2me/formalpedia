-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:31.436074+00:00
-- url     : https://prove2.me/theorems/cc4776cc-24d7-4200-9e49-f170a61823fc
-- title:
--   Is Local Homeomorph Add Monoid Hom Of Eventually Eq
-- statement:
--   Definitions and structural lemmas for Is Local Homeomorph Add Monoid Hom Of Eventually Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_analyticAt_doublingLog
import Theorems.Thm_GlobalTheory_exists_addMonoidHom_eventuallyEq
import Theorems.Thm_GlobalTheory_exists_ball_contraction
import Theorems.Thm_GlobalTheory_hasFDerivAt_of_isBigO_sq
import Theorems.Thm_GlobalTheory_isBigO_doublingLog_sub
import Theorems.Thm_GlobalTheory_isBigO_sub_linear_sq_of_analyticAt
import Theorems.Thm_GlobalTheory_map_zero_of_isBigO_sq
import Theorems.Thm_GlobalTheory_norm_iterate_le_of_contraction
import Theorems.Thm_GlobalTheory_tendsto_doublingLog_of_contraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
namespace GlobalTheory
section LocalHomeomorphHom
variable {V A : Type*} [NormedAddCommGroup V] [AddCommGroup A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] {e : V →+ A}
theorem isLocalHomeomorph_addMonoidHom_of_eventuallyEq {ψ : OpenPartialHomeomorph V A}
    (h0 : (0 : V) ∈ ψ.source) (he : e =ᶠ[𝓝 0] ψ) : IsLocalHomeomorph e := by
  obtain ⟨s, hs, hso, hs0⟩ := _root_.eventually_nhds_iff.mp he
  refine IsLocalHomeomorph.mk e fun x => ⟨(Homeomorph.subRight x).toOpenPartialHomeomorph.trans
    ((ψ.restrOpen s hso).trans (Homeomorph.addRight (e x)).toOpenPartialHomeomorph), ?_, ?_⟩
  · simp [h0, hs0]
  · intro y hy
    have hy' : y - x ∈ s := by
      simp at hy
      exact hy.2
    have := hs _ hy'
    simp only [map_sub] at this
    simp [← this]
omit [IsTopologicalAddGroup A] in

theorem discreteTopology_ker_of_isLocalHomeomorph (he : IsLocalHomeomorph e) :
    DiscreteTopology e.ker := by
  obtain ⟨U, hU, hU0, hinj⟩ := he.isLocallyInjective 0
  refine discreteTopology_iff_isOpen_singleton_zero.mpr ⟨U, hU, ?_⟩
  ext x
  refine ⟨fun hx => Subtype.ext (hinj hx hU0 ?_), ?_⟩
  · exact (show e x = 0 from x.2).trans (map_zero e).symm
  · rintro rfl
    exact hU0
theorem span_ker_eq_top_of_isOpenMap_of_compact [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [CompactSpace A] (he : IsOpenMap e) : Submodule.span ℝ (e.ker : Set V) = ⊤ := by
  have hK : IsCompact (range e) := (e.range.isClosed_of_isOpen he.isOpen_range).isCompact
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n : ℕ => e '' ball 0 n)
    (fun n => he _ isOpen_ball) (by
      rintro _ ⟨v, rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_gt ‖v‖
      exact mem_iUnion.mpr ⟨n, v, mem_ball_zero_iff.mpr hn, rfl⟩)
    (Monotone.directed_le fun m n hmn => image_mono (ball_subset_ball (by exact_mod_cast hmn)))
  rw [eq_top_iff]
  intro v _
  rw [← SetLike.mem_coe,
    ← (Submodule.span ℝ (e.ker : Set V)).closed_of_finiteDimensional.closure_eq,
    Metric.mem_closure_iff]
  intro η hη
  have ht : (0 : ℝ) < (n + 1) / η := by positivity
  obtain ⟨b, hb, hbe⟩ := hn (mem_range_self (((n + 1 : ℝ) / η) • v))
  refine ⟨((n + 1 : ℝ) / η)⁻¹ • (((n + 1 : ℝ) / η) • v - b),
    Submodule.smul_mem _ _ (Submodule.subset_span ?_), ?_⟩
  · simp [hbe]
  · rw [dist_eq_norm, smul_sub, inv_smul_smul₀ ht.ne', sub_sub_cancel, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr ht.le), inv_mul_lt_iff₀ ht, div_mul_cancel₀ _ hη.ne']
    linarith [mem_ball_zero_iff.mp hb]
end LocalHomeomorphHom
section Law
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
structure IsLocalCommGroupLaw (m : V × V → V) : Prop where
  analyticAt : AnalyticAt ℂ m 0
  isBigO : (fun p => m p - (p.1 + p.2)) =O[𝓝 0] fun p => ‖p‖ ^ 2
  comm : ∀ᶠ p in 𝓝 (0 : V × V), m (p.1, p.2) = m (p.2, p.1)
  assoc : ∀ᶠ p in 𝓝 (0 : V × V × V), m (m (p.1, p.2.1), p.2.2) = m (p.1, m (p.2.1, p.2.2))
namespace IsLocalCommGroupLaw
variable {m : V × V → V}
theorem of_unit (ha : AnalyticAt ℂ m 0) (hu : ∀ᶠ x in 𝓝 (0 : V), m (x, 0) = x)
    (hc : ∀ᶠ p in 𝓝 (0 : V × V), m (p.1, p.2) = m (p.2, p.1))
    (hs : ∀ᶠ p in 𝓝 (0 : V × V × V), m (m (p.1, p.2.1), p.2.2) = m (p.1, m (p.2.1, p.2.2))) :
    IsLocalCommGroupLaw m := by
  have hd := ha.differentiableAt.hasFDerivAt
  have hu' : ∀ᶠ x in 𝓝 (0 : V), m (0, x) = x := by
    have ht : Tendsto (fun x : V => ((0 : V), x)) (𝓝 0) (𝓝 0) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    filter_upwards [hu, ht.eventually hc] with x h1 h2
    exact h2.trans h1
  have h1 : (fderiv ℂ m 0).comp (ContinuousLinearMap.inl ℂ V V) = ContinuousLinearMap.id ℂ V :=
    (HasFDerivAt.comp (f := ContinuousLinearMap.inl ℂ V V) (0 : V) (by rwa [map_zero])
      (ContinuousLinearMap.inl ℂ V V).hasFDerivAt).unique
      ((hasFDerivAt_id (0 : V)).congr_of_eventuallyEq hu)
  have h2 : (fderiv ℂ m 0).comp (ContinuousLinearMap.inr ℂ V V) = ContinuousLinearMap.id ℂ V :=
    (HasFDerivAt.comp (f := ContinuousLinearMap.inr ℂ V V) (0 : V) (by rwa [map_zero])
      (ContinuousLinearMap.inr ℂ V V).hasFDerivAt).unique
      ((hasFDerivAt_id (0 : V)).congr_of_eventuallyEq hu')
  refine ⟨ha, (isBigO_sub_linear_sq_of_analyticAt ha hu.self_of_nhds hd).congr_left fun p => ?_,
    hc, hs⟩
  have e : p = (p.1, 0) + (0, p.2) := by simp
  have e1 : fderiv ℂ m 0 (p.1, 0) = p.1 := DFunLike.congr_fun h1 p.1
  have e2 : fderiv ℂ m 0 (0, p.2) = p.2 := DFunLike.congr_fun h2 p.2
  conv_lhs => rw [show fderiv ℂ m 0 p = fderiv ℂ m 0 ((p.1, 0) + (0, p.2)) by rw [← e], map_add,
    e1, e2]
variable (h : IsLocalCommGroupLaw m)
include h
theorem map_zero : m 0 = 0 :=
  map_zero_of_isBigO_sq (L := ContinuousLinearMap.fst ℂ V V + ContinuousLinearMap.snd ℂ V V)
    h.isBigO
theorem hasFDerivAt :
    HasFDerivAt m (ContinuousLinearMap.fst ℂ V V + ContinuousLinearMap.snd ℂ V V) 0 :=
  hasFDerivAt_of_isBigO_sq h.isBigO
theorem tendsto : Tendsto m (𝓝 0) (𝓝 0) := by
  simpa [ContinuousAt, h.map_zero] using h.analyticAt.continuousAt
theorem doubling_law :
    ∀ᶠ p in 𝓝 (0 : V × V), m (m p, m p) = m (m (p.1, p.1), m (p.2, p.2)) := by
  have t1 : Tendsto (fun p : V × V => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
  have t2 : Tendsto (fun p : V × V => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
  have t3 : Tendsto (fun p : V × V => m (p.2, p.2)) (𝓝 0) (𝓝 0) :=
    h.tendsto.comp (t2.prodMk_nhds t2)
  filter_upwards [(t1.prodMk_nhds (t2.prodMk_nhds h.tendsto)).eventually h.assoc, h.comm,
    (t2.prodMk_nhds (t2.prodMk_nhds t1)).eventually h.assoc,
    (t3.prodMk_nhds t1).eventually h.comm,
    (t1.prodMk_nhds (t1.prodMk_nhds t3)).eventually h.assoc] with ⟨x, y⟩ h1 h2 h3 h4 h5
  simp only at h1 h2 h3 h4 h5 ⊢
  rw [h1, h2, ← h3, h4, h5]
theorem analyticAt_doubling : AnalyticAt ℂ (fun x => m (x, x)) 0 :=
  AnalyticAt.comp (f := fun x : V => (x, x)) h.analyticAt (analyticAt_id.prod analyticAt_id)
omit h in

noncomputable def twoEquiv (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] : V ≃L[ℂ] V :=
  ContinuousLinearEquiv.equivOfInverse ((2 : ℂ) • ContinuousLinearMap.id ℂ V)
    ((2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ V) (fun x => by simp [smul_smul])
    (fun x => by simp [smul_smul])
theorem hasFDerivAt_doubling :
    HasFDerivAt (fun x => m (x, x)) (twoEquiv V : V →L[ℂ] V) 0 := by
  have := HasFDerivAt.comp (f := fun x : V => (x, x)) (0 : V) h.hasFDerivAt
    ((hasFDerivAt_id (0 : V)).prodMk (hasFDerivAt_id (0 : V)))
  refine this.congr_fderiv ?_
  ext x
  simp [twoEquiv, two_smul]
theorem hasStrictFDerivAt_doubling :
    HasStrictFDerivAt (fun x => m (x, x)) (twoEquiv V : V →L[ℂ] V) 0 :=
  h.hasFDerivAt_doubling.fderiv ▸ h.analyticAt_doubling.hasStrictFDerivAt
variable [CompleteSpace V]
noncomputable def halving : V → V :=
  h.hasStrictFDerivAt_doubling.localInverse _ _ _
theorem halving_doubling : ∀ᶠ x in 𝓝 (0 : V), h.halving (m (x, x)) = x :=
  h.hasStrictFDerivAt_doubling.eventually_left_inverse
section AnyInverse
variable {ε : V → V} (hε : ∀ᶠ x in 𝓝 (0 : V), ε (m (x, x)) = x)
include hε
theorem eventuallyEq_halving : ε =ᶠ[𝓝 0] h.halving := by
  have := h.hasStrictFDerivAt_doubling.localInverse_unique hε
  rwa [show m (0, 0) = 0 from h.map_zero] at this
theorem doubling_inverse : ∀ᶠ x in 𝓝 (0 : V), m (ε x, ε x) = x := by
  have := h.hasStrictFDerivAt_doubling.eventually_right_inverse
  rw [show m (0, 0) = 0 from h.map_zero] at this
  filter_upwards [this, h.eventuallyEq_halving hε] with x h1 h2
  rw [h2]
  exact h1
theorem analyticAt_inverse : AnalyticAt ℂ ε 0 := by
  have := ((h.analyticAt_doubling.contDiffAt (n := ⊤)).to_localInverse h.hasFDerivAt_doubling
    (by simp)).analyticAt
  rw [show m (0, 0) = 0 from h.map_zero] at this
  exact this.congr (h.eventuallyEq_halving hε).symm
omit [CompleteSpace V] in
theorem inverse_zero : ε 0 = 0 := by
  simpa [show m (0, 0) = 0 from h.map_zero] using hε.self_of_nhds
theorem isBigO_inverse : (fun x => ε x - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2 := by
  have := (h.hasStrictFDerivAt_doubling.to_local_left_inverse hε).hasFDerivAt
  rw [show m (0, 0) = 0 from h.map_zero] at this
  exact isBigO_sub_linear_sq_of_analyticAt (h.analyticAt_inverse hε) (h.inverse_zero hε) this
theorem inverse_law : ∀ᶠ p in 𝓝 (0 : V × V), ε (m p) = m (ε p.1, ε p.2) := by
  have t0 : Tendsto ε (𝓝 0) (𝓝 0) := by
    simpa [ContinuousAt, h.inverse_zero hε] using (h.analyticAt_inverse hε).continuousAt
  have t1 : Tendsto (fun p : V × V => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
  have t2 : Tendsto (fun p : V × V => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
  have t3 : Tendsto (fun p : V × V => (ε p.1, ε p.2)) (𝓝 0) (𝓝 0) :=
    (t0.comp t1).prodMk_nhds (t0.comp t2)
  filter_upwards [t3.eventually h.doubling_law, (h.tendsto.comp t3).eventually hε,
    t1.eventually (h.doubling_inverse hε), t2.eventually (h.doubling_inverse hε)]
    with p h1 h2 h3 h4
  simp only [h3, h4, Function.comp] at h1 h2
  rw [← h2, h1]
theorem doublingLog_law :
    ∀ᶠ p in 𝓝 (0 : V × V), doublingLog ε (m p) = doublingLog ε p.1 + doublingLog ε p.2 := by
  obtain ⟨r, hr, C, hC0, hc, hC⟩ := exists_ball_contraction (h.isBigO_inverse hε)
  obtain ⟨D, hD0, hD⟩ := h.isBigO.exists_nonneg
  obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hD.bound.and (h.inverse_law hε))
  filter_upwards [ball_mem_nhds 0 hs, ball_mem_nhds 0 hr,
    h.tendsto.eventually (ball_mem_nhds 0 hr)] with p hps hpr hm
  have hx : p.1 ∈ ball (0 : V) r :=
    mem_ball_zero_iff.mpr ((norm_fst_le p).trans_lt (mem_ball_zero_iff.mp hpr))
  have hy : p.2 ∈ ball (0 : V) r :=
    mem_ball_zero_iff.mpr ((norm_snd_le p).trans_lt (mem_ball_zero_iff.mp hpr))
  have hq : ∀ j : ℕ, ‖(ε^[j] p.1, ε^[j] p.2)‖ ≤ (5 / 8) ^ j * ‖p‖ := fun j =>
    norm_prod_le_iff.mpr
      ⟨(norm_iterate_le_of_contraction hc hx j).trans (by gcongr; exact norm_fst_le p),
        (norm_iterate_le_of_contraction hc hy j).trans (by gcongr; exact norm_snd_le p)⟩
  have hqs : ∀ j : ℕ, (ε^[j] p.1, ε^[j] p.2) ∈ ball (0 : V × V) s := fun j =>
    mem_ball_zero_iff.mpr (((hq j).trans (mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (by norm_num) (by norm_num)))).trans_lt (mem_ball_zero_iff.mp hps))
  have hit : ∀ j : ℕ, ε^[j] (m p) = m (ε^[j] p.1, ε^[j] p.2) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => simp only [Function.iterate_succ_apply', ih, (hball _ (hqs j)).2]
  have h0 : Tendsto (fun j : ℕ => (2 : ℂ) ^ j • ε^[j] (m p) -
      ((2 : ℂ) ^ j • ε^[j] p.1 + (2 : ℂ) ^ j • ε^[j] p.2)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun j : ℕ => D * ‖p‖ ^ 2 * (25 / 32 : ℝ) ^ j) (fun j => ?_) ?_
    · have h1 := (hball _ (hqs j)).1
      rw [norm_pow, norm_norm] at h1
      rw [← smul_add, ← smul_sub, hit, norm_smul, norm_pow, Complex.norm_two]
      calc (2 : ℝ) ^ j * ‖m (ε^[j] p.1, ε^[j] p.2) - (ε^[j] p.1 + ε^[j] p.2)‖
          ≤ 2 ^ j * (D * ((5 / 8) ^ j * ‖p‖) ^ 2) := by
            gcongr
            exact h1.trans (by gcongr; exact hq j)
        _ = D * ‖p‖ ^ 2 * (2 * (5 / 8) ^ 2) ^ j := by
            rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]
            ring
        _ = _ := by norm_num
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (25 / 32 : ℝ)) (by norm_num)
        (by norm_num)).const_mul (D * ‖p‖ ^ 2)
  exact sub_eq_zero.mp (tendsto_nhds_unique
    ((tendsto_doublingLog_of_contraction hc hC0 hC hm).sub
      ((tendsto_doublingLog_of_contraction hc hC0 hC hx).add
        (tendsto_doublingLog_of_contraction hc hC0 hC hy))) h0)
theorem hasFDerivAt_doublingLog : HasFDerivAt (doublingLog ε) (ContinuousLinearMap.id ℂ V) 0 :=
  hasFDerivAt_of_isBigO_sq (isBigO_doublingLog_sub (h.isBigO_inverse hε))
theorem doublingLog_zero : doublingLog ε 0 = 0 :=
  map_zero_of_isBigO_sq (L := ContinuousLinearMap.id ℂ V)
    (isBigO_doublingLog_sub (h.isBigO_inverse hε))
end AnyInverse
noncomputable def log : V → V := doublingLog h.halving
@[simp] theorem log_zero : h.log 0 = 0 := h.doublingLog_zero h.halving_doubling
theorem hasFDerivAt_log : HasFDerivAt h.log (ContinuousLinearMap.id ℂ V) 0 :=
  h.hasFDerivAt_doublingLog h.halving_doubling
theorem log_law : ∀ᶠ p in 𝓝 (0 : V × V), h.log (m p) = h.log p.1 + h.log p.2 :=
  h.doublingLog_law h.halving_doubling
variable [FiniteDimensional ℂ V]
theorem analyticAt_log : AnalyticAt ℂ h.log 0 :=
  analyticAt_doublingLog (h.analyticAt_inverse h.halving_doubling)
    (h.isBigO_inverse h.halving_doubling)
theorem hasStrictFDerivAt_log :
    HasStrictFDerivAt h.log (ContinuousLinearEquiv.refl ℂ V : V →L[ℂ] V) 0 := by
  have := h.analyticAt_log.hasStrictFDerivAt
  rwa [h.hasFDerivAt_log.fderiv] at this
noncomputable def logChart : OpenPartialHomeomorph V V :=
  h.hasStrictFDerivAt_log.toOpenPartialHomeomorph h.log
@[simp] theorem coe_logChart : (h.logChart : V → V) = h.log := rfl
theorem zero_mem_logChart_source : (0 : V) ∈ h.logChart.source :=
  h.hasStrictFDerivAt_log.mem_toOpenPartialHomeomorph_source
theorem zero_mem_logChart_target : (0 : V) ∈ h.logChart.target := by
  simpa using h.logChart.map_source h.zero_mem_logChart_source
@[simp] theorem logChart_symm_zero : h.logChart.symm 0 = 0 := by
  simpa using h.logChart.left_inv h.zero_mem_logChart_source
theorem analyticAt_logChart_symm : AnalyticAt ℂ h.logChart.symm 0 := by
  have := ((h.analyticAt_log.contDiffAt (n := ⊤)).to_localInverse
    h.hasStrictFDerivAt_log.hasFDerivAt (by simp)).analyticAt
  rwa [h.log_zero] at this
theorem logChart_symm_add : ∀ᶠ p in 𝓝 (0 : V × V),
    h.logChart.symm (p.1 + p.2) = m (h.logChart.symm p.1, h.logChart.symm p.2) := by
  have t0 : Tendsto h.logChart.symm (𝓝 0) (𝓝 0) := by
    simpa [ContinuousAt] using h.analyticAt_logChart_symm.continuousAt
  have t1 : Tendsto (fun p : V × V => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
  have t2 : Tendsto (fun p : V × V => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
  have t3 : Tendsto (fun p : V × V => (h.logChart.symm p.1, h.logChart.symm p.2)) (𝓝 0) (𝓝 0) :=
    (t0.comp t1).prodMk_nhds (t0.comp t2)
  have hr := h.logChart.eventually_right_inverse h.zero_mem_logChart_target
  filter_upwards [t3.eventually h.log_law, t1.eventually hr, t2.eventually hr,
    (h.tendsto.comp t3).eventually
      (h.logChart.eventually_left_inverse h.zero_mem_logChart_source)] with p h1 h2 h3 h4
  simp only [coe_logChart, Function.comp] at h1 h2 h3 h4
  rw [← h4, h1, h2, h3]
end IsLocalCommGroupLaw
end Law
section Chart
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [AddCommGroup A]
  [TopologicalSpace A]
def chartLaw (φ : OpenPartialHomeomorph A V) (p : V × V) : V :=
  φ (φ.symm p.1 + φ.symm p.2)
structure IsAnalyticGroupChart (φ : OpenPartialHomeomorph A V) : Prop where
  zero_mem_source : (0 : A) ∈ φ.source
  map_zero : φ 0 = 0
  analyticAt : AnalyticAt ℂ (chartLaw φ) 0
namespace IsAnalyticGroupChart
variable {φ : OpenPartialHomeomorph A V} (h : IsAnalyticGroupChart φ)
include h
theorem zero_mem_target : (0 : V) ∈ φ.target := h.map_zero ▸ φ.map_source h.zero_mem_source
theorem symm_zero : φ.symm 0 = 0 := by simpa [h.map_zero] using φ.left_inv h.zero_mem_source
theorem tendsto : Tendsto φ (𝓝 0) (𝓝 0) := by
  simpa [ContinuousAt, h.map_zero] using φ.continuousAt h.zero_mem_source
theorem tendsto_symm : Tendsto φ.symm (𝓝 0) (𝓝 0) := by
  simpa [ContinuousAt, h.symm_zero] using φ.continuousAt_symm h.zero_mem_target
variable [IsTopologicalAddGroup A]
theorem symm_chartLaw :
    ∀ᶠ p in 𝓝 (0 : V × V), φ.symm (chartLaw φ p) = φ.symm p.1 + φ.symm p.2 := by
  have t1 : Tendsto (fun p : V × V => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
  have t2 : Tendsto (fun p : V × V => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
  have t : Tendsto (fun p : V × V => φ.symm p.1 + φ.symm p.2) (𝓝 0) (𝓝 0) := by
    simpa using (h.tendsto_symm.comp t1).add (h.tendsto_symm.comp t2)
  exact t.eventually (φ.eventually_left_inverse h.zero_mem_source)
theorem isLocalCommGroupLaw : IsLocalCommGroupLaw (chartLaw φ) := by
  refine IsLocalCommGroupLaw.of_unit h.analyticAt ?_
    (Eventually.of_forall fun p => by simp only [chartLaw, add_comm]) ?_
  · filter_upwards [φ.eventually_right_inverse h.zero_mem_target] with x hx
    simp [chartLaw, h.symm_zero, hx]
  · have t1 : Tendsto (fun p : V × V × V => (p.1, p.2.1)) (𝓝 0) (𝓝 0) :=
      (by fun_prop : Continuous fun p : V × V × V => (p.1, p.2.1)).tendsto 0
    have t2 : Tendsto (fun p : V × V × V => (p.2.1, p.2.2)) (𝓝 0) (𝓝 0) :=
      continuous_snd.tendsto 0
    filter_upwards [t1.eventually h.symm_chartLaw, t2.eventually h.symm_chartLaw] with p h1 h2
    change φ (φ.symm (chartLaw φ _) + φ.symm p.2.2) = φ (φ.symm p.1 + φ.symm (chartLaw φ _))
    rw [h1, h2, add_assoc]
variable [FiniteDimensional ℂ V] [CompleteSpace V]
noncomputable abbrev log : V → V := h.isLocalCommGroupLaw.log
noncomputable def localExp : OpenPartialHomeomorph V A :=
  h.isLocalCommGroupLaw.logChart.symm.trans φ.symm
theorem localExp_apply (v : V) :
    h.localExp v = φ.symm (h.isLocalCommGroupLaw.logChart.symm v) := rfl
theorem zero_mem_localExp_source : (0 : V) ∈ h.localExp.source :=
  ⟨h.isLocalCommGroupLaw.zero_mem_logChart_target, by simpa using h.zero_mem_target⟩
theorem localExp_add :
    ∀ᶠ p in 𝓝 (0 : V × V), h.localExp (p.1 + p.2) = h.localExp p.1 + h.localExp p.2 := by
  have t0 : Tendsto h.isLocalCommGroupLaw.logChart.symm (𝓝 0) (𝓝 0) := by
    simpa [ContinuousAt] using h.isLocalCommGroupLaw.analyticAt_logChart_symm.continuousAt
  have t1 : Tendsto (fun p : V × V => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
  have t2 : Tendsto (fun p : V × V => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
  filter_upwards [h.isLocalCommGroupLaw.logChart_symm_add,
    ((t0.comp t1).prodMk_nhds (t0.comp t2)).eventually h.symm_chartLaw] with p h1 h2
  rw [localExp_apply, h1]
  exact h2
noncomputable def exp : V →+ A :=
  (exists_addMonoidHom_eventuallyEq h.localExp_add).choose
theorem exp_eventuallyEq : h.exp =ᶠ[𝓝 0] h.localExp :=
  (exists_addMonoidHom_eventuallyEq h.localExp_add).choose_spec
theorem isLocalHomeomorph_exp : IsLocalHomeomorph h.exp :=
  isLocalHomeomorph_addMonoidHom_of_eventuallyEq h.zero_mem_localExp_source h.exp_eventuallyEq
theorem continuous_exp : Continuous h.exp := h.isLocalHomeomorph_exp.continuous
theorem isOpenMap_exp : IsOpenMap h.exp := h.isLocalHomeomorph_exp.isOpenMap
noncomputable def periodLattice : Submodule ℤ V := AddSubgroup.toIntSubmodule h.exp.ker
instance discreteTopology_ker_exp : DiscreteTopology h.exp.ker :=
  discreteTopology_ker_of_isLocalHomeomorph h.isLocalHomeomorph_exp
instance discreteTopology_periodLattice : DiscreteTopology h.periodLattice :=
  h.discreteTopology_ker_exp
instance isZLattice_periodLattice [CompactSpace A] : IsZLattice ℝ h.periodLattice :=
  ⟨span_ker_eq_top_of_isOpenMap_of_compact h.isOpenMap_exp⟩
noncomputable def quotientKerExpEquiv (hs : Function.Surjective h.exp) : (V ⧸ h.exp.ker) ≃ₜ+ A where
  __ := QuotientAddGroup.quotientKerEquivOfSurjective h.exp hs
  continuous_toFun :=
    (QuotientAddGroup.isQuotientMap_mk h.exp.ker).continuous_iff.mpr h.continuous_exp
  continuous_invFun := by
    refine (h.isOpenMap_exp.isQuotientMap h.continuous_exp hs).continuous_iff.mpr ?_
    refine (QuotientAddGroup.continuous_mk (N := h.exp.ker)).congr fun v => ?_
    exact ((QuotientAddGroup.quotientKerEquivOfSurjective h.exp hs).symm_apply_apply v).symm
end IsAnalyticGroupChart
end Chart
end GlobalTheory


