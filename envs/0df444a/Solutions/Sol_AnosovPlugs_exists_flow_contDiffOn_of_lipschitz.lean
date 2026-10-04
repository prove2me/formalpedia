-- Prove2me | solution 1 for AnosovPlugs.exists_flow_contDiffOn_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:37:14.331509+00:00
-- url     : https://prove2.me/submissions/e56e7185-9c77-41b5-926a-6a9ce6ff700e

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_contDiffOn_fixedPoint_of_contraction
import Theorems.Thm_AnosovPlugs_contDiff_continuousMap_comp_left

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

set_option linter.unusedSectionVars false

local notation "fl_I" => Set.Icc (-1:ℝ) 1

theorem fl_h1 : (-1:ℝ) ≤ 1 := by norm_num

section fl_sec

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem fl_cont_ext (f : C(fl_I, E)) : Continuous (Set.IccExtend fl_h1 f) :=
  f.continuous.Icc_extend'

noncomputable def fl_intOpL : C(fl_I, E) →ₗ[ℝ] C(fl_I, E) where
  toFun f := ⟨fun s => ∫ u in (0:ℝ)..(s:ℝ), Set.IccExtend fl_h1 f u,
    (intervalIntegral.continuous_primitive
      (fun a b => (fl_cont_ext f).intervalIntegrable a b) 0).comp continuous_subtype_val⟩
  map_add' f g := by
    ext s
    simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk]
    rw [← intervalIntegral.integral_add ((fl_cont_ext f).intervalIntegrable _ _)
      ((fl_cont_ext g).intervalIntegrable _ _)]
    rfl
  map_smul' c f := by
    ext s
    simp only [ContinuousMap.smul_apply, ContinuousMap.coe_mk, RingHom.id_apply]
    rw [← intervalIntegral.integral_smul]
    rfl

theorem fl_norm_intOpL_le (f : C(fl_I, E)) : ‖fl_intOpL f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  refine (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun s => ?_
  change ‖∫ u in (0:ℝ)..(s:ℝ), Set.IccExtend fl_h1 f u‖ ≤ ‖f‖
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    fun u _ => ContinuousMap.norm_coe_le_norm f _).trans ?_
  have : |(s:ℝ) - 0| ≤ 1 := by rw [sub_zero, abs_le]; exact s.2
  calc ‖f‖ * |(s:ℝ) - 0| ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg f)
    _ = ‖f‖ := mul_one _

noncomputable def fl_intOp : C(fl_I, E) →L[ℝ] C(fl_I, E) :=
  fl_intOpL.mkContinuous 1 fl_norm_intOpL_le

theorem fl_intOp_apply (f : C(fl_I, E)) (s : fl_I) :
    fl_intOp f s = ∫ u in (0:ℝ)..(s:ℝ), Set.IccExtend fl_h1 f u := rfl

theorem fl_norm_intOp_apply_le (f : C(fl_I, E)) : ‖fl_intOp f‖ ≤ ‖f‖ := by
  have h := fl_norm_intOpL_le f
  rw [one_mul] at h
  exact h

variable (v : E → E) (hv : ContDiff ℝ 1 v) (K : NNReal) (hK : LipschitzWith K v)

def fl_N (β : C(fl_I, E)) : C(fl_I, E) := ⟨v ∘ β, hv.continuous.comp β.continuous⟩

include hK in
theorem fl_lipschitzWith_N : LipschitzWith K (fl_N v hv) := by
  refine LipschitzWith.of_dist_le_mul fun β γ => ?_
  refine (ContinuousMap.dist_le (by positivity)).2 fun s => ?_
  exact (hK.dist_le_mul (β s) (γ s)).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist s) K.coe_nonneg)

noncomputable def fl_T (p : E × ℝ) (β : C(fl_I, E)) : C(fl_I, E) :=
  ContinuousLinearMap.const ℝ fl_I p.1 + p.2 • fl_intOp (fl_N v hv β)

include hK in
theorem fl_contractingWith_T {p : E × ℝ} (hp : ‖p.2‖ * K < 1) :
    ContractingWith (‖p.2‖₊ * K) (fl_T v hv p) := by
  refine ⟨by rw [← NNReal.coe_lt_coe]; push_cast; exact hp,
    LipschitzWith.of_dist_le_mul fun β γ => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  simp only [fl_T]
  rw [add_sub_add_left_eq_sub, ← smul_sub, ← map_sub, norm_smul]
  push_cast
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (fl_norm_intOp_apply_le _).trans ?_
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact (fl_lipschitzWith_N v hv K hK).dist_le_mul β γ

noncomputable def fl_flowAux (p : E × ℝ) : C(fl_I, E) :=
  if hp : ‖p.2‖ * K < 1 then
    ContractingWith.fixedPoint (fl_T v hv p) (fl_contractingWith_T v hv K hK hp)
  else 0

theorem fl_flowAux_isFixedPt {p : E × ℝ} (hp : ‖p.2‖ * K < 1) :
    fl_T v hv p (fl_flowAux v hv K hK p) = fl_flowAux v hv K hK p := by
  simp only [fl_flowAux, dif_pos hp]
  exact (fl_contractingWith_T v hv K hK hp).fixedPoint_isFixedPt

theorem fl_flowAux_eq {p : E × ℝ} (hp : ‖p.2‖ * K < 1) {β : C(fl_I, E)}
    (hβ : fl_T v hv p β = β) : β = fl_flowAux v hv K hK p := by
  simp only [fl_flowAux, dif_pos hp]
  exact (fl_contractingWith_T v hv K hK hp).fixedPoint_unique hβ

theorem fl_flowAux_apply {p : E × ℝ} (hp : ‖p.2‖ * K < 1) (s : fl_I) :
    fl_flowAux v hv K hK p s = p.1 + p.2 • ∫ u in (0:ℝ)..(s:ℝ),
      v (Set.IccExtend fl_h1 (fl_flowAux v hv K hK p) u) := by
  conv_lhs => rw [← fl_flowAux_isFixedPt v hv K hK hp]
  rfl

theorem fl_flowAux_zero (x : E) :
    fl_flowAux v hv K hK (x, 0) = ContinuousLinearMap.const ℝ fl_I x := by
  refine (fl_flowAux_eq v hv K hK (by simp) ?_).symm
  simp [fl_T]

theorem fl_contDiff_T :
    ContDiff ℝ 1 (fun q : (E × ℝ) × C(fl_I, E) => fl_T v hv q.1 q.2) := by
  have hN : ContDiff ℝ 1 (fl_N v hv) :=
    AnosovPlugs.contDiff_continuousMap_comp_left (X := fl_I) v hv
  have h1 : ContDiff ℝ 1 (fun q : (E × ℝ) × C(fl_I, E) => q.1.1) :=
    contDiff_fst.comp contDiff_fst
  have h2 : ContDiff ℝ 1 (fun q : (E × ℝ) × C(fl_I, E) => q.1.2) :=
    contDiff_snd.comp contDiff_fst
  have h3 : ContDiff ℝ 1 (fun q : (E × ℝ) × C(fl_I, E) => q.2) := contDiff_snd
  exact ((ContinuousLinearMap.const ℝ fl_I).contDiff.comp h1).add
    (h2.smul (fl_intOp.contDiff.comp (hN.comp h3)))

theorem fl_contDiffOn_flowAux :
    ContDiffOn ℝ 1 (fl_flowAux v hv K hK) {p : E × ℝ | ‖p.2‖ * K < 1} :=
  AnosovPlugs.contDiffOn_fixedPoint_of_contraction (fl_T v hv) (fl_contDiff_T v hv) _
    (isOpen_lt (f := fun p : E × ℝ => ‖p.2‖ * (K:ℝ)) (by fun_prop) continuous_const)
    (fun p hp => ⟨_, fl_contractingWith_T v hv K hK (p := p) hp⟩) _
    (fun _ hp => fl_flowAux_isFixedPt v hv K hK hp)

theorem fl_flowAux_scale (x : E) {τ c : ℝ} (hτ : ‖τ‖ * K < 1) (hc : c ∈ Icc (-1:ℝ) 1)
    (s : fl_I) :
    fl_flowAux v hv K hK (x, τ * c) s =
      Set.IccExtend fl_h1 (fl_flowAux v hv K hK (x, τ)) (c * s) := by
  have hcs : ∀ s : fl_I, c * (s:ℝ) ∈ fl_I := fun s => by
    rw [mem_Icc, ← abs_le, abs_mul]
    exact mul_le_one₀ (abs_le.2 hc) (abs_nonneg _) (abs_le.2 s.2)
  have hτc : ‖τ * c‖ * K < 1 := by
    calc ‖τ * c‖ * K = ‖τ‖ * |c| * K := by rw [norm_mul, Real.norm_eq_abs c]
      _ ≤ ‖τ‖ * 1 * K := by gcongr; exact abs_le.2 hc
      _ < 1 := by rwa [mul_one]
  let R : C(fl_I, E) := ⟨fun s => Set.IccExtend fl_h1 (fl_flowAux v hv K hK (x, τ)) (c * s),
    (fl_cont_ext _).comp (continuous_const.mul continuous_subtype_val)⟩
  have key : R = fl_flowAux v hv K hK (x, τ * c) := by
    apply fl_flowAux_eq v hv K hK hτc
    ext s
    have e1 : fl_T v hv (x, τ * c) R s = x + (τ * c) • ∫ u in (0:ℝ)..(s:ℝ),
        v (Set.IccExtend fl_h1 (fl_flowAux v hv K hK (x, τ)) (c * u)) := by
      show x + (τ * c) • ∫ u in (0:ℝ)..(s:ℝ), Set.IccExtend fl_h1 (fl_N v hv R) u = _
      congr 2
      refine intervalIntegral.integral_congr fun u hu => ?_
      have hu' : u ∈ fl_I := uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ s.2 hu
      rw [Set.IccExtend_of_mem _ _ hu']
      rfl
    have e2 : R s = x + τ • ∫ u in (0:ℝ)..(c * s),
        v (Set.IccExtend fl_h1 (fl_flowAux v hv K hK (x, τ)) u) := by
      show Set.IccExtend fl_h1 (fl_flowAux v hv K hK (x, τ)) (c * s) = _
      rw [Set.IccExtend_of_mem _ _ (hcs s), fl_flowAux_apply v hv K hK hτ]
    rw [e1, e2, mul_smul, intervalIntegral.smul_integral_comp_mul_left
      (f := fun u => v (Set.IccExtend fl_h1 (fl_flowAux v hv K hK (x, τ)) u)) c, mul_zero]
  rw [← key]
  rfl

theorem fl_eps_mul_lt : (1 / ((K:ℝ) + 1)) * K < 1 := by
  rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
  linarith

end fl_sec

theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v : E → E) (hv : ContDiff ℝ 1 v) (K : NNReal) (hK : LipschitzWith K v) :
    ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E, (∀ x, α x 0 = x) ∧
      (∀ x, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (α x) (v (α x t)) t) ∧
      ContDiffOn ℝ 1 (fun p : E × ℝ => α p.1 p.2) (univ ×ˢ Ioo (-ε) ε) := by
  set ε : ℝ := 1 / ((K:ℝ) + 1) with hε_def
  have hε : 0 < ε := by positivity
  have hεK0 : ε * K < 1 := fl_eps_mul_lt K
  have hε1 : ‖ε‖ * K < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hε]
  have hεK : ∀ t ∈ Ioo (-ε) ε, ‖t‖ * K < 1 := by
    intro t ht
    have h : |t| ≤ ε := (abs_lt.2 ht).le
    calc ‖t‖ * K ≤ ε * K := by rw [Real.norm_eq_abs]; gcongr
      _ < 1 := hεK0
  have hc : ∀ t ∈ Ioo (-ε) ε, t / ε ∈ Icc (-1:ℝ) 1 := fun t ht =>
    ⟨by rw [le_div_iff₀ hε]; linarith [ht.1], by rw [div_le_iff₀ hε]; linarith [ht.2]⟩
  refine ⟨ε, hε, fun x t => fl_flowAux v hv K hK (x, t) ⟨1, by norm_num⟩, ?_, ?_, ?_⟩
  · intro x
    simp only [fl_flowAux_zero]
    rfl
  · intro x t ht
    let g := Set.IccExtend fl_h1 (fl_flowAux v hv K hK (x, ε))
    have hg : Continuous g := fl_cont_ext _
    have hα : ∀ t' ∈ Ioo (-ε) ε, fl_flowAux v hv K hK (x, t') ⟨1, by norm_num⟩ = g (t' / ε) := by
      intro t' ht'
      have h := fl_flowAux_scale v hv K hK x hε1 (hc t' ht') ⟨1, by norm_num⟩
      rw [mul_div_cancel₀ t' hε.ne'] at h
      rw [h, mul_one]
    have hgI : ∀ r ∈ Icc (-1:ℝ) 1, g r = x + ε • ∫ u in (0:ℝ)..r, v (g u) := by
      intro r hr
      show Set.IccExtend fl_h1 (fl_flowAux v hv K hK (x, ε)) r = _
      rw [Set.IccExtend_of_mem _ _ hr, fl_flowAux_apply v hv K hK hε1]
    have heq : (fun t' => fl_flowAux v hv K hK (x, t') ⟨1, by norm_num⟩) =ᶠ[𝓝 t]
        fun t' => x + ε • ∫ u in (0:ℝ)..(t' / ε), v (g u) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with t' ht'
      rw [hα t' ht', hgI _ (hc t' ht')]
    have hd : HasDerivAt (fun t' => x + ε • ∫ u in (0:ℝ)..(t' / ε), v (g u))
        (ε • ((1 / ε) • v (g (t / ε)))) t := by
      have h1 : HasDerivAt (fun r => ∫ u in (0:ℝ)..r, v (g u)) (v (g (t / ε))) (t / ε) :=
        ((hv.continuous.comp hg).integral_hasStrictDerivAt 0 (t / ε)).hasDerivAt
      have h2 : HasDerivAt (fun t' : ℝ => t' / ε) (1 / ε) t := (hasDerivAt_id t).div_const ε
      exact ((h1.scomp t h2).const_smul ε).const_add x
    have h3 := hd.congr_of_eventuallyEq heq
    convert h3 using 1
    rw [smul_smul, mul_one_div_cancel hε.ne', one_smul]
    exact congrArg v (hα t ht)
  · have h := (fl_contDiffOn_flowAux v hv K hK).mono
      (t := univ ×ˢ Ioo (-ε) ε) (fun p hp => hεK p.2 hp.2)
    exact (ContinuousMap.evalCLM ℝ (⟨1, by norm_num⟩ : fl_I)).contDiff.comp_contDiffOn h
