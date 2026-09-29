-- Prove2me | solution 1 for AlgebraicCurve.exists_path_forall_pathIntegral_eq_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e581ecfb-fa84-52e6-80ae-98b0f72f6484

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_path_forall_pathIntegral_eq_sum_mul

open scoped Manifold ContDiff Topology
open AlgebraicCurve Filter Set

namespace LoopRealisation

section Prim

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

theorem sub_eq_sub_of_isPrimitiveAlong {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g g' : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) (hg' : IsPrimitiveAlong θ γ g')
    (t : unitInterval) : g t - g' t = g 0 - g' 0 := by
  have hloc : IsLocallyConstant (fun s => g s - g' s) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t₀ => ?_
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg t₀
    obtain ⟨Φ', hΦ', hgΦ'⟩ := hg' t₀
    set z₀ : ℂ := extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t₀) with hz₀
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hΦ.and hΦ')
    have hconst : ∀ z ∈ Metric.ball z₀ r, Φ z - Φ' z = Φ z₀ - Φ' z₀ := by
      intro z hz
      have hd : ∀ w ∈ Metric.ball z₀ r, HasDerivAt (fun u => Φ u - Φ' u) 0 w := by
        intro w hw
        have h__af := (hball w hw).1.sub (hball w hw).2
        simp at h__af
        exact h__af
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ r).isPreconnected
        (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => (hd w hw).deriv) hz (Metric.mem_ball_self hr)
    have hcont : ContinuousAt (fun s : unitInterval => extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ s)) t₀ :=
      (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) (γ t₀)).comp γ.continuous.continuousAt
    have hin : ∀ᶠ s in 𝓝 t₀, extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ s) ∈ Metric.ball z₀ r :=
      hcont (Metric.ball_mem_nhds z₀ hr)
    filter_upwards [hin, hgΦ, hgΦ'] with s hs hs1 hs2
    have h0 : g t₀ - g' t₀ = Φ z₀ - Φ' z₀ := by
      rw [hgΦ.self_of_nhds, hgΦ'.self_of_nhds]
    rw [hs1, hs2, hconst _ hs, h0]
  exact hloc.apply_eq_of_preconnectedSpace (x := t) (y := 0)

theorem pathIntegral_eq_of_isPrimitiveAlong {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) : pathIntegral θ γ = g 1 - g 0 := by
  classical
  have h : ∃ g, IsPrimitiveAlong θ γ g := ⟨g, hg⟩
  rw [pathIntegral_def, dif_pos h]
  have := sub_eq_sub_of_isPrimitiveAlong h.choose_spec hg 1
  linear_combination this

theorem eventually_sub_eq {Φ₁ Φ₂ f : ℂ → ℂ} {z₀ : ℂ}
    (h₁ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Φ₁ (f z) z) (h₂ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Φ₂ (f z) z) :
    ∀ᶠ z in 𝓝 z₀, Φ₂ z - Φ₁ z = Φ₂ z₀ - Φ₁ z₀ := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h₁.and h₂)
  have hd : ∀ w ∈ Metric.ball z₀ r, HasDerivAt (fun u => Φ₂ u - Φ₁ u) 0 w := fun w hw => by
    have h__af := (hball w hw).2.sub (hball w hw).1
    simp at h__af
    exact h__af
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
  exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ r).isPreconnected
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) hz (Metric.mem_ball_self hr)

theorem isPrimitiveAlong_const_refl {θ : Ω[F⁄ℂ]} {P : Place ℂ F} {g : unitInterval → ℂ}
    (hg : IsPrimitiveAlong θ (Path.refl P) g) (c : ℂ) :
    IsPrimitiveAlong θ (Path.refl P) (fun _ => c) := by
  intro t₀
  obtain ⟨Φ, hΦ, -⟩ := hg t₀
  refine ⟨fun z => Φ z - Φ (extChartAt 𝓘(ℂ, ℂ) P P) + c, ?_, ?_⟩
  · filter_upwards [hΦ] with z hz
    simpa using (hz.sub_const (Φ (extChartAt 𝓘(ℂ, ℂ) P P))).add_const c
  · exact Filter.Eventually.of_forall fun t => by simp

theorem pathIntegral_refl {θ : Ω[F⁄ℂ]} {P : Place ℂ F} (h : ∃ g, IsPrimitiveAlong θ (Path.refl P) g) :
    pathIntegral θ (Path.refl P) = 0 := by
  obtain ⟨g, hg⟩ := h
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_const_refl hg 0), sub_self]

theorem isPrimitiveAlong_symm {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q} {g : unitInterval → ℂ}
    (hg : IsPrimitiveAlong θ γ g) : IsPrimitiveAlong θ γ.symm (fun t => g (unitInterval.symm t)) := by
  intro t₀
  obtain ⟨Φ, hΦ, hgΦ⟩ := hg (unitInterval.symm t₀)
  refine ⟨Φ, hΦ, ?_⟩
  have hc : Tendsto (fun t : unitInterval => unitInterval.symm t) (𝓝 t₀) (𝓝 (unitInterval.symm t₀)) :=
    unitInterval.continuous_symm.continuousAt
  exact hc.eventually hgΦ

theorem pathIntegral_symm {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    (h : ∃ g, IsPrimitiveAlong θ γ g) : pathIntegral θ γ.symm = -pathIntegral θ γ := by
  obtain ⟨g, hg⟩ := h
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_symm hg),
    pathIntegral_eq_of_isPrimitiveAlong hg, unitInterval.symm_one, unitInterval.symm_zero]
  ring

noncomputable def dbl (t : unitInterval) : unitInterval := projIcc 0 1 zero_le_one (2 * t)

noncomputable def dbl' (t : unitInterval) : unitInterval := projIcc 0 1 zero_le_one (2 * t - 1)

theorem continuous_dbl : Continuous (dbl : unitInterval → unitInterval) :=
  continuous_projIcc.comp (continuous_const.mul continuous_subtype_val)

theorem continuous_dbl' : Continuous (dbl' : unitInterval → unitInterval) :=
  continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)

omit [ChartedSpace ℂ (Place ℂ F)] in
theorem trans_apply_of_le {P Q R : Place ℂ F} (γ : Path P Q) (γ' : Path Q R) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) : (γ.trans γ') t = γ (dbl t) := by
  rw [Path.trans_apply, dif_pos ht, dbl, projIcc_of_mem]

omit [ChartedSpace ℂ (Place ℂ F)] in
theorem trans_apply_of_not_le {P Q R : Place ℂ F} (γ : Path P Q) (γ' : Path Q R) (t : unitInterval)
    (ht : ¬ (t : ℝ) ≤ 1 / 2) : (γ.trans γ') t = γ' (dbl' t) := by
  rw [Path.trans_apply, dif_neg ht, dbl', projIcc_of_mem]

theorem dbl_zero : dbl 0 = 0 := by
  apply Subtype.ext; simp [dbl]

theorem dbl'_one : dbl' 1 = 1 := by
  apply Subtype.ext; norm_num [dbl']

theorem dbl_half (t : unitInterval) (ht : (t : ℝ) = 1 / 2) : dbl t = 1 := by
  apply Subtype.ext; rw [dbl, ht]; norm_num

theorem dbl'_half (t : unitInterval) (ht : (t : ℝ) = 1 / 2) : dbl' t = 0 := by
  apply Subtype.ext; rw [dbl', ht]; norm_num

noncomputable def transPrim (g g' : unitInterval → ℂ) (t : unitInterval) : ℂ :=
  if (t : ℝ) ≤ 1 / 2 then g (dbl t) else g 1 - g' 0 + g' (dbl' t)

theorem isPrimitiveAlong_trans {θ : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q} {γ' : Path Q R}
    {g g' : unitInterval → ℂ} (hg : IsPrimitiveAlong θ γ g) (hg' : IsPrimitiveAlong θ γ' g') :
    IsPrimitiveAlong θ (γ.trans γ') (transPrim g g') := by
  intro t₀
  rcases lt_trichotomy (t₀ : ℝ) (1 / 2) with hlt | heq | hgt
  ·
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg (dbl t₀)
    refine ⟨Φ, by rw [trans_apply_of_le γ γ' t₀ hlt.le]; exact hΦ, ?_⟩
    have E1 : ∀ᶠ t : unitInterval in 𝓝 t₀, (t : ℝ) < 1 / 2 :=
      (isOpen_lt continuous_subtype_val continuous_const).mem_nhds hlt
    have E2 := (continuous_dbl.continuousAt (x := t₀)).eventually hgΦ
    filter_upwards [E1, E2] with t h1 h2
    rw [trans_apply_of_le γ γ' t₀ hlt.le, trans_apply_of_le γ γ' t h1.le, transPrim, if_pos h1.le]
    exact h2
  ·
    have ht₀ : (γ.trans γ') t₀ = Q := by
      rw [trans_apply_of_le γ γ' t₀ heq.le, dbl_half t₀ heq, γ.target]
    obtain ⟨Φ₁, hΦ₁, hg₁⟩ := hg 1
    obtain ⟨Φ₂, hΦ₂, hg₂⟩ := hg' 0
    rw [γ.target] at hΦ₁ hg₁
    rw [γ'.source] at hΦ₂ hg₂
    set z₀ := extChartAt 𝓘(ℂ, ℂ) Q Q with hz₀
    have hc := eventually_sub_eq hΦ₁ hΦ₂
    have hv₁ : g 1 = Φ₁ z₀ := by rw [hg₁.self_of_nhds, γ.target]
    have hv₂ : g' 0 = Φ₂ z₀ := by rw [hg₂.self_of_nhds, γ'.source]
    refine ⟨Φ₁, by rw [ht₀]; exact hΦ₁, ?_⟩
    rw [ht₀]
    have hd : Tendsto (dbl : unitInterval → unitInterval) (𝓝 t₀) (𝓝 1) := by
      have h := continuous_dbl.continuousAt (x := t₀)
      rwa [ContinuousAt, dbl_half t₀ heq] at h
    have hd' : Tendsto (dbl' : unitInterval → unitInterval) (𝓝 t₀) (𝓝 0) := by
      have h := continuous_dbl'.continuousAt (x := t₀)
      rwa [ContinuousAt, dbl'_half t₀ heq] at h
    have E1 := hd.eventually hg₁
    have E2 := hd'.eventually hg₂
    have hw : Tendsto (fun t : unitInterval => extChartAt 𝓘(ℂ, ℂ) Q (γ' (dbl' t))) (𝓝 t₀) (𝓝 z₀) := by
      have h1 : Tendsto (fun s : unitInterval => γ' s) (𝓝 0) (𝓝 Q) := by
        have h := γ'.continuous.continuousAt (x := 0)
        rwa [ContinuousAt, γ'.source] at h
      exact ((continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) Q).tendsto.comp (h1.comp hd'))
    have E3 := hw.eventually hc
    filter_upwards [E1, E2, E3] with t e1 e2 e3
    by_cases hle : (t : ℝ) ≤ 1 / 2
    · rw [trans_apply_of_le γ γ' t hle, transPrim, if_pos hle]
      exact e1
    · rw [trans_apply_of_not_le γ γ' t hle, transPrim, if_neg hle, e2, hv₁, hv₂]
      linear_combination e3
  ·
    have hnot : ¬ (t₀ : ℝ) ≤ 1 / 2 := not_le.2 hgt
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg' (dbl' t₀)
    refine ⟨fun z => g 1 - g' 0 + Φ z, ?_, ?_⟩
    · rw [trans_apply_of_not_le γ γ' t₀ hnot]
      filter_upwards [hΦ] with z hz
      exact hz.const_add _
    · have E1 : ∀ᶠ t : unitInterval in 𝓝 t₀, (1 / 2 : ℝ) < t :=
        (isOpen_lt continuous_const continuous_subtype_val).mem_nhds hgt
      have E2 := (continuous_dbl'.continuousAt (x := t₀)).eventually hgΦ
      filter_upwards [E1, E2] with t h1 h2
      rw [trans_apply_of_not_le γ γ' t₀ hnot, trans_apply_of_not_le γ γ' t (not_le.2 h1),
        transPrim, if_neg (not_le.2 h1), h2]

theorem pathIntegral_trans {θ : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q} {γ' : Path Q R}
    (h : ∃ g, IsPrimitiveAlong θ γ g) (h' : ∃ g', IsPrimitiveAlong θ γ' g') :
    pathIntegral θ (γ.trans γ') = pathIntegral θ γ + pathIntegral θ γ' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  rw [pathIntegral_eq_of_isPrimitiveAlong (isPrimitiveAlong_trans hg hg'),
    pathIntegral_eq_of_isPrimitiveAlong hg, pathIntegral_eq_of_isPrimitiveAlong hg']
  have h0 : transPrim g g' 0 = g 0 := by
    rw [transPrim, if_pos (by norm_num), dbl_zero]
  have h1 : transPrim g g' 1 = g 1 - g' 0 + g' 1 := by
    rw [transPrim, if_neg (by norm_num), dbl'_one]
  rw [h0, h1]
  ring

theorem exists_isPrimitiveAlong_trans {θ : Ω[F⁄ℂ]} {P Q R : Place ℂ F} {γ : Path P Q}
    {γ' : Path Q R} (h : ∃ g, IsPrimitiveAlong θ γ g) (h' : ∃ g', IsPrimitiveAlong θ γ' g') :
    ∃ G, IsPrimitiveAlong θ (γ.trans γ') G := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨_, isPrimitiveAlong_trans hg hg'⟩

theorem exists_isPrimitiveAlong_symm {θ : Ω[F⁄ℂ]} {P Q : Place ℂ F} {γ : Path P Q}
    (h : ∃ g, IsPrimitiveAlong θ γ g) : ∃ G, IsPrimitiveAlong θ γ.symm G := by
  obtain ⟨g, hg⟩ := h
  exact ⟨_, isPrimitiveAlong_symm hg⟩

end Prim

section Conn

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X]

theorem isPreconnected_ball_diff_center (c : ℂ) (r : ℝ) :
    IsPreconnected (Metric.ball c r \ {c}) := by
  have hsph : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
    (isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ) zero_le_one).2
  have hprod : IsPreconnected ((Ioo (0 : ℝ) r) ×ˢ (Metric.sphere (0 : ℂ) 1)) :=
    isPreconnected_Ioo.prod hsph
  have himage : (fun q : ℝ × ℂ => c + (q.1 : ℂ) * q.2) '' ((Ioo (0 : ℝ) r) ×ˢ Metric.sphere 0 1) =
      Metric.ball c r \ {c} := by
    ext z
    simp only [mem_image, mem_prod, mem_Ioo, mem_sphere_iff_norm, sub_zero, mem_diff,
      Metric.mem_ball, mem_singleton_iff, Prod.exists]
    constructor
    · rintro ⟨ρ, u, ⟨⟨hρ0, hρr⟩, hu⟩, rfl⟩
      have hn : ‖(ρ : ℂ) * u‖ = ρ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hu, mul_one]
      refine ⟨by rwa [dist_eq_norm, add_sub_cancel_left, hn], fun h => ?_⟩
      have : ‖(ρ : ℂ) * u‖ = 0 := by
        have h' : (ρ : ℂ) * u = 0 := by linear_combination h
        rw [h', norm_zero]
      rw [hn] at this
      exact hρ0.ne' this
    · rintro ⟨hz, hzc⟩
      have hne : z - c ≠ 0 := sub_ne_zero.2 hzc
      have hpos : 0 < ‖z - c‖ := norm_pos_iff.2 hne
      refine ⟨‖z - c‖, (‖z - c‖ : ℂ)⁻¹ * (z - c), ⟨⟨hpos, by rwa [dist_eq_norm] at hz⟩, ?_⟩, ?_⟩
      · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
          inv_mul_cancel₀ hpos.ne']
      · have h0 : (‖z - c‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
        field_simp
        ring
  rw [← himage]
  exact hprod.image _ (by fun_prop)

omit [T2Space X] [ConnectedSpace X] in

theorem exists_open_puncture_preconnected (t : X) {W : Set X} (hW : W ∈ 𝓝 t) :
    ∃ P : Set X, IsOpen P ∧ t ∈ P ∧ P ⊆ W ∧ IsPreconnected (P \ {t}) := by
  set e := chartAt ℂ t with he
  have hsrc : e.source ∈ 𝓝 t := e.open_source.mem_nhds (mem_chart_source ℂ t)

  have hW' : e.target ∩ e.symm ⁻¹' (W ∩ e.source) ∈ 𝓝 (e t) := by
    apply Filter.inter_mem (e.open_target.mem_nhds (mem_chart_target ℂ t))
    refine e.continuousAt_symm (mem_chart_target ℂ t) ?_
    rw [e.left_inv (mem_chart_source ℂ t)]
    exact Filter.inter_mem hW hsrc
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hW'
  refine ⟨e.symm '' Metric.ball (e t) r, ?_, ?_, ?_, ?_⟩
  · apply e.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    exact fun z hz => (hball hz).1
  · exact ⟨e t, Metric.mem_ball_self hr, e.left_inv (mem_chart_source ℂ t)⟩
  · rintro x ⟨z, hz, rfl⟩
    exact (hball hz).2.1
  · have heq : e.symm '' Metric.ball (e t) r \ {t} = e.symm '' (Metric.ball (e t) r \ {e t}) := by
      ext x
      simp only [mem_diff, mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hx⟩
        refine ⟨z, ⟨hz, fun h => hx ?_⟩, rfl⟩
        rw [h, e.left_inv (mem_chart_source ℂ t)]
      · rintro ⟨z, ⟨hz, hzt⟩, rfl⟩
        refine ⟨⟨z, hz, rfl⟩, fun h => hzt ?_⟩
        have := congrArg e h
        rwa [e.right_inv (hball hz).1] at this
    rw [heq]
    exact (isPreconnected_ball_diff_center (e t) r).image _
      (e.continuousOn_symm.mono fun z hz => (hball hz.1).1)

theorem isPreconnected_compl_of_finite {T : Set X} (hT : T.Finite) : IsPreconnected Tᶜ := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub huv

  have hTc : IsOpen Tᶜ := hT.isClosed.isOpen_compl
  set u' := u ∩ Tᶜ with hu'
  set v' := v ∩ Tᶜ with hv'
  have hu'o : IsOpen u' := hu.inter hTc
  have hv'o : IsOpen v' := hv.inter hTc
  have hcov : Tᶜ ⊆ u' ∪ v' := fun x hx => (hsub hx).elim (fun h => Or.inl ⟨h, hx⟩)
    (fun h => Or.inr ⟨h, hx⟩)
  have hdisj : u' ∩ v' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨hxu, hxT⟩, hxv, -⟩
    have : x ∈ Tᶜ ∩ (u ∩ v) := ⟨hxT, hxu, hxv⟩
    rw [huv] at this
    exact this

  have hP : ∀ t ∈ T, ∃ P : Set X, IsOpen P ∧ t ∈ P ∧ P ⊆ (T \ {t})ᶜ ∧ IsPreconnected (P \ {t}) := by
    intro t ht
    refine exists_open_puncture_preconnected t ?_
    exact (hT.subset diff_subset).isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  choose! P hPo hPt hPT hPc using hP

  have hPsub : ∀ t ∈ T, P t \ {t} ⊆ Tᶜ := by
    intro t ht x ⟨hx, hxt⟩ hxT
    exact hPT t ht hx ⟨hxT, hxt⟩
  have hPuv : ∀ t ∈ T, P t \ {t} ⊆ u' ∨ P t \ {t} ⊆ v' := by
    intro t ht
    refine (isPreconnected_iff_subset_of_disjoint.1 (hPc t ht)) u' v' hu'o hv'o
      ((hPsub t ht).trans hcov) ?_
    rw [hdisj, Set.inter_empty]

  set A : Set X := {t | t ∈ T ∧ P t \ {t} ⊆ u'} with hA
  set A' : Set X := {t | t ∈ T ∧ ¬ (P t \ {t} ⊆ u')} with hA'
  have hA'v : ∀ t ∈ A', P t \ {t} ⊆ v' := fun t ht => (hPuv t ht.1).resolve_left ht.2
  set U : Set X := u' ∪ ⋃ t ∈ A, P t with hU
  set V : Set X := v' ∪ ⋃ t ∈ A', P t with hV
  have hUo : IsOpen U := hu'o.union (isOpen_biUnion fun t ht => hPo t ht.1)
  have hVo : IsOpen V := hv'o.union (isOpen_biUnion fun t ht => hPo t ht.1)
  have hu'T : u' ⊆ Tᶜ := fun x hx => hx.2
  have hv'T : v' ⊆ Tᶜ := fun x hx => hx.2
  have hcover : (univ : Set X) ⊆ U ∪ V := by
    intro x _
    by_cases hxT : x ∈ T
    · by_cases hxA : P x \ {x} ⊆ u'
      · exact Or.inl (Or.inr (mem_biUnion (show x ∈ A from ⟨hxT, hxA⟩) (hPt x hxT)))
      · exact Or.inr (Or.inr (mem_biUnion (show x ∈ A' from ⟨hxT, hxA⟩) (hPt x hxT)))
    · rcases hcov hxT with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)

  have hPA : ∀ t ∈ A, ∀ x ∈ P t, x ≠ t → x ∈ u' := fun t ht x hx hxt => ht.2 ⟨hx, hxt⟩
  have hPA' : ∀ t ∈ A', ∀ x ∈ P t, x ≠ t → x ∈ v' := fun t ht x hx hxt => hA'v t ht ⟨hx, hxt⟩
  have hPeq : ∀ t ∈ T, ∀ x ∈ P t, x ∈ T → x = t := by
    intro t ht x hx hxT
    by_contra hne
    exact hPT t ht hx ⟨hxT, hne⟩
  have hnot2 : ∀ x, x ∈ u' → x ∈ v' → False := by
    intro x hxu hxv
    have : x ∈ u' ∩ v' := ⟨hxu, hxv⟩
    rw [hdisj] at this
    exact this
  have hdisjUV : (univ : Set X) ∩ (U ∩ V) = ∅ := by
    rw [Set.univ_inter, Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxU, hxV⟩
    rcases hxU with hxu | hxU
    · have hxT : x ∉ T := hu'T hxu
      rcases hxV with hxv | hxV
      · exact hnot2 x hxu hxv
      · rw [mem_iUnion₂] at hxV
        obtain ⟨t, ht, hx⟩ := hxV
        exact hnot2 x hxu (hPA' t ht x hx fun h => hxT (h ▸ ht.1))
    · rw [mem_iUnion₂] at hxU
      obtain ⟨s, hs, hxs⟩ := hxU
      rcases hxV with hxv | hxV
      · have hxT : x ∉ T := hv'T hxv
        exact hnot2 x (hPA s hs x hxs fun h => hxT (h ▸ hs.1)) hxv
      · rw [mem_iUnion₂] at hxV
        obtain ⟨t, ht, hxt⟩ := hxV
        by_cases hxT : x ∈ T
        · have h1 := hPeq s hs.1 x hxs hxT
          have h2 := hPeq t ht.1 x hxt hxT
          rw [← h1] at hs
          rw [← h2] at ht
          exact ht.2 hs.2
        · exact hnot2 x (hPA s hs x hxs fun h => hxT (h ▸ hs.1))
            (hPA' t ht x hxt fun h => hxT (h ▸ ht.1))
  rcases (isPreconnected_iff_subset_of_disjoint.1 isPreconnected_univ) U V hUo hVo hcover hdisjUV
    with h | h
  · left
    intro x hxT
    rcases h (mem_univ x) with hxu | hxU
    · exact hxu.1
    · rw [mem_iUnion₂] at hxU
      obtain ⟨t, ht, hx⟩ := hxU
      exact (hPA t ht x hx fun h' => hxT (h' ▸ ht.1)).1
  · right
    intro x hxT
    rcases h (mem_univ x) with hxv | hxV
    · exact hxv.1
    · rw [mem_iUnion₂] at hxV
      obtain ⟨t, ht, hx⟩ := hxV
      exact (hPA' t ht x hx fun h' => hxT (h' ▸ ht.1)).1

theorem isPathConnected_compl_of_finite {T : Set X} (hT : T.Finite) (hne : Tᶜ.Nonempty) :
    IsPathConnected Tᶜ := by
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  exact (hT.isClosed.isOpen_compl.isConnected_iff_isPathConnected).1
    ⟨hne, isPreconnected_compl_of_finite hT⟩

end Conn

section LoopsTop

variable {X : Type*} [TopologicalSpace X]

theorem avoid_trans {T : Set X} {P Q R : X} {γ : Path P Q} {γ' : Path Q R}
    (h : ∀ t, γ t ∉ T) (h' : ∀ t, γ' t ∉ T) : ∀ t, (γ.trans γ') t ∉ T := by
  intro t
  have ht : (γ.trans γ') t ∈ range (γ.trans γ') := mem_range_self t
  rw [Path.trans_range] at ht
  rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]; exact h s
  · rw [← hs]; exact h' s

theorem avoid_symm {T : Set X} {P Q : X} {γ : Path P Q} (h : ∀ t, γ t ∉ T) :
    ∀ t, γ.symm t ∉ T := fun t => h (unitInterval.symm t)

noncomputable def npowLoop {P : X} (Z : Path P P) : ℕ → Path P P
  | 0 => Path.refl P
  | n + 1 => (npowLoop Z n).trans Z

noncomputable def zpowLoop {P : X} (Z : Path P P) : ℤ → Path P P
  | Int.ofNat n => npowLoop Z n
  | Int.negSucc n => (npowLoop Z (n + 1)).symm

theorem avoid_npowLoop {T : Set X} {P : X} {Z : Path P P} (h : ∀ t, Z t ∉ T) :
    ∀ n t, npowLoop Z n t ∉ T := by
  intro n
  induction n with
  | zero =>
    intro t
    have h0 := h 0
    rw [Z.source] at h0
    simpa [npowLoop] using h0
  | succ n ih => exact avoid_trans ih h

theorem avoid_zpowLoop {T : Set X} {P : X} {Z : Path P P} (h : ∀ t, Z t ∉ T) :
    ∀ (n : ℤ) t, zpowLoop Z n t ∉ T := by
  rintro (n | n)
  · exact avoid_npowLoop h n
  · exact avoid_symm (avoid_npowLoop h (n + 1))

end LoopsTop

section Loops

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable {T : Set (Place ℂ F)} {θ : Ω[F⁄ℂ]}
  (hP : ∀ {P Q : Place ℂ F} (γ : Path P Q), (∀ t, γ t ∉ T) → ∃ g, IsPrimitiveAlong θ γ g)
include hP

theorem pathIntegral_npowLoop {P : Place ℂ F} {Z : Path P P} (h : ∀ t, Z t ∉ T) (n : ℕ) :
    pathIntegral θ (npowLoop Z n) = n * pathIntegral θ Z := by
  induction n with
  | zero =>
    simp only [npowLoop, Nat.cast_zero, zero_mul]
    exact pathIntegral_refl (hP _ (avoid_npowLoop h 0))
  | succ n ih =>
    simp only [npowLoop]
    rw [pathIntegral_trans (hP _ (avoid_npowLoop h n)) (hP _ h), ih]
    push_cast
    ring

theorem pathIntegral_zpowLoop {P : Place ℂ F} {Z : Path P P} (h : ∀ t, Z t ∉ T) (n : ℤ) :
    pathIntegral θ (zpowLoop Z n) = n * pathIntegral θ Z := by
  rcases n with (n | n)
  · simp only [zpowLoop, Int.ofNat_eq_natCast, Int.cast_natCast]
    exact pathIntegral_npowLoop hP h n
  · simp only [zpowLoop]
    rw [pathIntegral_symm (hP _ (avoid_npowLoop h (n + 1))), pathIntegral_npowLoop hP h (n + 1),
      Int.cast_negSucc]
    push_cast
    ring

theorem pathIntegral_conj {Q₀ P : Place ℂ F} {c : Path Q₀ P} {Z : Path P P} (hc : ∀ t, c t ∉ T)
    (h : ∀ t, Z t ∉ T) (n : ℤ) :
    pathIntegral θ (c.trans ((zpowLoop Z n).trans c.symm)) = n * pathIntegral θ Z := by
  rw [pathIntegral_trans (hP _ hc) (hP _ (avoid_trans (avoid_zpowLoop h n) (avoid_symm hc))),
    pathIntegral_trans (hP _ (avoid_zpowLoop h n)) (hP _ (avoid_symm hc)),
    pathIntegral_symm (hP _ hc), pathIntegral_zpowLoop hP h n]
  ring

end Loops

end LoopRealisation

open LoopRealisation in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {ι : Type*} [Fintype ι] (T : Finset (Place ℂ F)) {Pz : ι → Place ℂ F}
    (Z : ∀ k, Path (Pz k) (Pz k)) (hZ : ∀ k t, Z k t ∉ T) (m : ι → ℤ)
    (Q₀ : Place ℂ F) (hQ₀ : Q₀ ∉ T) :
    ∃ α : Path Q₀ Q₀, (∀ t, α t ∉ T) ∧
      ∀ θ : Ω[F⁄ℂ], (∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ) →
        pathIntegral θ α = ∑ k, (m k : ℂ) * pathIntegral θ (Z k) := by
  classical

  have hprim : ∀ θ : Ω[F⁄ℂ], (∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ) →
      ∀ {P Q : Place ℂ F} (γ : Path P Q), (∀ t, γ t ∉ (↑T : Set (Place ℂ F))) →
        ∃ g, IsPrimitiveAlong θ γ g := by
    intro θ hθ P Q γ hγ
    exact (AlgebraicCurve.exists_isPrimitiveAlong_of_forall_ordDifferential_nonneg F hfg hF θ γ
      (fun t => hθ _ (hγ t))).1

  have hTset : ∀ {x : Place ℂ F}, x ∉ (↑T : Set (Place ℂ F)) ↔ x ∉ T := fun {x} => by
    rw [Finset.mem_coe]
  have hpc : IsPathConnected ((↑T : Set (Place ℂ F))ᶜ) :=
    isPathConnected_compl_of_finite T.finite_toSet ⟨Q₀, hTset.2 hQ₀⟩
  have hc : ∀ k, ∃ c : Path Q₀ (Pz k), ∀ t, c t ∉ (↑T : Set (Place ℂ F)) := by
    intro k
    have hk : Pz k ∈ (↑T : Set (Place ℂ F))ᶜ := by
      have := hZ k 0
      rw [(Z k).source] at this
      exact hTset.2 this
    have hj := hpc.joinedIn Q₀ (hTset.2 hQ₀) (Pz k) hk
    exact ⟨hj.somePath, fun t => hj.somePath_mem t⟩
  choose c hc using hc
  have hZ' : ∀ k t, Z k t ∉ (↑T : Set (Place ℂ F)) := fun k t => hTset.2 (hZ k t)

  suffices h : ∀ s : Finset ι, ∃ α : Path Q₀ Q₀, (∀ t, α t ∉ (↑T : Set (Place ℂ F))) ∧
      ∀ θ : Ω[F⁄ℂ], (∀ v : Place ℂ F, v ∉ T → 0 ≤ v.ordDifferential θ) →
        pathIntegral θ α = ∑ k ∈ s, (m k : ℂ) * pathIntegral θ (Z k) by
    obtain ⟨α, hα, hαi⟩ := h Finset.univ
    exact ⟨α, fun t => hTset.1 (hα t), hαi⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Path.refl Q₀, fun t => by simpa using hTset.2 hQ₀, fun θ hθ => ?_⟩
    rw [Finset.sum_empty]
    exact pathIntegral_refl (hprim θ hθ _ fun t => by simpa using hTset.2 hQ₀)
  | insert k s hk ih =>
    obtain ⟨α, hα, hαi⟩ := ih
    refine ⟨α.trans ((c k).trans ((zpowLoop (Z k) (m k)).trans (c k).symm)), ?_, fun θ hθ => ?_⟩
    · exact avoid_trans hα (avoid_trans (hc k)
        (avoid_trans (avoid_zpowLoop (hZ' k) (m k)) (avoid_symm (hc k))))
    · rw [Finset.sum_insert hk,
        pathIntegral_trans (hprim θ hθ _ hα) (hprim θ hθ _ (avoid_trans (hc k)
          (avoid_trans (avoid_zpowLoop (hZ' k) (m k)) (avoid_symm (hc k))))),
        hαi θ hθ, pathIntegral_conj (hprim θ hθ) (hc k) (hZ' k) (m k)]
      ring

end S_AlgebraicCurve_exists_path_forall_pathIntegral_eq_sum_mul
end P2MW
export P2MW.S_AlgebraicCurve_exists_path_forall_pathIntegral_eq_sum_mul (solution)
