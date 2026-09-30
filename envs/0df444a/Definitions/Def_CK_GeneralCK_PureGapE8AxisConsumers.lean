-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8AxisConsumers
-- name    : CK_GeneralCK_PureGapE8AxisConsumers
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:18:29.792481+00:00
-- url     : https://prove2.me/theorems/cc11cd30-b510-4657-a4e5-d567dbe04641
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8AxisConsumers` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8AxisConsumers` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8AxisConsumers` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8AxisConsumers (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8AxisConsumers.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8RegularizedInverse
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.PureGapE8AxisConsumers =====
section

/-!
# Analytic consumers for the non-origin E8 axis certificates

Only the actual derivative inequalities remain as certificate inputs.  Smooth
extension at zero, intermediate slope-range membership, exact axis zeros, and
all integrations are proved here for the concrete inverse.
-/

namespace GeneralCK

open Set

noncomputable def e8RegularDeltaS (s t : ℝ) : ℝ :=
  deriv (fun u => e8Delta e8RegularQ u t) s

noncomputable def e8RegularDeltaSS (s t : ℝ) : ℝ :=
  deriv (fun u => e8RegularDeltaS u t) s




theorem e8RegularQ_contDiffAt_inputs {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hmax : 2 * s + t ∈ e8SlopeRange) :
    ContDiffAt ℝ 4 e8RegularQ s ∧ ContDiffAt ℝ 4 e8RegularQ t ∧
      ContDiffAt ℝ 4 e8RegularQ (s + t) ∧
      ContDiffAt ℝ 4 e8RegularQ (2 * s + t) := by
  refine ⟨e8RegularQ_contDiffAt_interval hmax ⟨hs, by linarith⟩,
    e8RegularQ_contDiffAt_interval hmax ⟨ht, by linarith⟩,
    e8RegularQ_contDiffAt_interval hmax ⟨by positivity, by linarith⟩,
    e8RegularQ_contDiffAt_of_mem hmax⟩

theorem e8RegularDelta_left_contDiffAt {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hmax : 2 * s + t ∈ e8SlopeRange) :
    ContDiffAt ℝ 4 (fun u => e8Delta e8RegularQ u t) s := by
  obtain ⟨hD, hA, hC, hB⟩ := e8RegularQ_contDiffAt_inputs hs ht hmax
  unfold e8Delta
  fun_prop

theorem e8RegularDelta_right_contDiffAt {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hmax : 2 * s + t ∈ e8SlopeRange) :
    ContDiffAt ℝ 4 (fun v => e8Delta e8RegularQ s v) t := by
  obtain ⟨hD, hA, hC, hB⟩ := e8RegularQ_contDiffAt_inputs hs ht hmax
  unfold e8Delta
  fun_prop

theorem hasDerivAt_e8RegularDelta_left {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hmax : 2 * s + t ∈ e8SlopeRange) :
    HasDerivAt (fun u => e8Delta e8RegularQ u t) (e8RegularDeltaS s t) s :=
  (e8RegularDelta_left_contDiffAt hs ht hmax).differentiableAt (by norm_num)
    |>.hasDerivAt

theorem hasDerivAt_e8RegularDeltaS_left {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hmax : 2 * s + t ∈ e8SlopeRange) :
    HasDerivAt (fun u => e8RegularDeltaS u t) (e8RegularDeltaSS s t) s := by
  have hd := (e8RegularDelta_left_contDiffAt hs ht hmax).derivWithin
    (m := 3) (by norm_num)
  exact hd.differentiableAt (by norm_num) |>.hasDerivAt

theorem hasDerivAt_e8RegularDelta_right {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hmax : 2 * s + t ∈ e8SlopeRange) :
    HasDerivAt (fun v => e8Delta e8RegularQ s v) (e8RegularDeltaT s t) t :=
  (e8RegularDelta_right_contDiffAt hs ht hmax).differentiableAt (by norm_num)
    |>.hasDerivAt















theorem e8RegularDeltaS_zero_left {t : ℝ} (ht : t ∈ e8SlopeRange) :
    e8RegularDeltaS 0 t = 0 := by
  have hQt := (e8RegularQ_contDiffAt_of_mem ht).differentiableAt (by norm_num)
  have hQ0 := hasDerivAt_e8RegularQ_zero.differentiableAt
  unfold e8RegularDeltaS
  rw [deriv_e8Delta_left e8RegularQ 0 t (by simpa using hQt)
    (by simpa using hQt) hQ0]
  unfold e8DeltaDerivS
  rw [e8RegularQ_zero]
  simp only [zero_add]
  ring

private theorem positive_of_first_derivative {f g : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hzero : f 0 = 0)
    (hderiv : ∀ u ∈ Icc 0 x, HasDerivAt f (g u) u)
    (hpos : ∀ u ∈ Ioo 0 x, 0 < g u) : 0 < f x := by
  have hmono : StrictMonoOn f (Icc 0 x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 x)
    · exact fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
    · intro u hu
      have hu' : u ∈ Ioo 0 x := by simpa using hu
      rw [(hderiv u ⟨hu'.1.le, hu'.2.le⟩).deriv]
      exact hpos u hu'
  have h := hmono ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hx
  simpa [hzero] using h

private theorem positive_of_second_derivative {f g k : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hzero : f 0 = 0) (hgzero : g 0 = 0)
    (hf : ∀ u ∈ Icc 0 x, HasDerivAt f (g u) u)
    (hg : ∀ u ∈ Icc 0 x, HasDerivAt g (k u) u)
    (hk : ∀ u ∈ Ioo 0 x, 0 < k u) : 0 < f x := by
  apply positive_of_first_derivative hx hzero hf
  intro u hu
  apply positive_of_first_derivative hu.1 hgzero
  · exact fun v hv => hg v ⟨hv.1, hv.2.trans hu.2.le⟩
  · exact fun v hv => hk v ⟨hv.1, hv.2.trans hu.2⟩

/-- Double integration for a fixed positive `t`, including the analytic
double zero on the left axis. -/
theorem e8Delta_pos_of_second_s_derivative {s t : ℝ}
    (hadm : E8Admissible s t)
    (hss : ∀ u ∈ Ioo 0 s, 0 < e8RegularDeltaSS u t) :
    0 < e8Delta e8Q s t := by
  have hrange (u : ℝ) (hu : u ∈ Icc 0 s) : 2 * u + t ∈ e8SlopeRange :=
    e8SlopeRange_downward hadm.2.2.2.2.2 (by linarith [hadm.2.1, hu.1]) (by linarith [hu.2])
  rw [← e8Delta_regularQ_eq hadm.1.le hadm.2.1.le]
  exact positive_of_second_derivative
    (f := fun u => e8Delta e8RegularQ u t)
    (g := fun u => e8RegularDeltaS u t)
    (k := fun u => e8RegularDeltaSS u t)
    hadm.1 (e8RegularDelta_zero_left t)
    (e8RegularDeltaS_zero_left hadm.2.2.2.1)
    (fun u hu => hasDerivAt_e8RegularDelta_left hu.1 hadm.2.1.le (hrange u hu))
    (fun u hu => hasDerivAt_e8RegularDeltaS_left hu.1 hadm.2.1.le (hrange u hu)) hss

/-- Single integration for a fixed positive `s`, including the exact zero on
the bottom axis. -/
theorem e8Delta_pos_of_first_t_derivative {s t : ℝ}
    (hadm : E8Admissible s t)
    (hdt : ∀ v ∈ Ioo 0 t, 0 < e8RegularDeltaT s v) :
    0 < e8Delta e8Q s t := by
  have hrange (v : ℝ) (hv : v ∈ Icc 0 t) : 2 * s + v ∈ e8SlopeRange :=
    e8SlopeRange_downward hadm.2.2.2.2.2 (by linarith [hadm.1, hv.1]) (by linarith [hv.2])
  rw [← e8Delta_regularQ_eq hadm.1.le hadm.2.1.le]
  exact positive_of_first_derivative hadm.2.1 (e8RegularDelta_zero_right s)
    (fun v hv => hasDerivAt_e8RegularDelta_right hadm.1.le hv.1 (hrange v hv)) hdt

/-- The numerical input for the manuscript's s-axis strip. -/
def E8SAxisDerivativeBound : Prop :=
  ∀ s t : ℝ, E8Admissible s t → s ≤ 1 / 50 →
    (3 / 50 : ℝ) ≤ t → t ≤ 20 → 0 < e8RegularDeltaSS s t

/-- The numerical input for the manuscript's t-axis strip. -/
def E8TAxisDerivativeBound : Prop :=
  ∀ s t : ℝ, E8Admissible s t → (3 / 50 : ℝ) ≤ s →
    s ≤ 63 / 20 → t ≤ 1 / 50 → 0 < e8RegularDeltaT s t

/-- The numerical input for the remaining small-s infinite tail. -/
def E8SmallSTailDerivativeBound : Prop :=
  ∀ s t : ℝ, E8Admissible s t → (20 : ℝ) ≤ t →
    s ≤ 1 / 200 → 0 < e8RegularDeltaSS s t

theorem E8Admissible.mono_s {s t u : ℝ} (h : E8Admissible s t)
    (hu : 0 < u) (hus : u ≤ s) : E8Admissible u t := by
  refine ⟨hu, h.2.1, e8SlopeRange_downward h.2.2.1 hu hus, h.2.2.2.1, ?_, ?_⟩
  · exact e8SlopeRange_downward h.2.2.2.2.1 (by linarith [h.2.1]) (by linarith)
  · exact e8SlopeRange_downward h.2.2.2.2.2 (by linarith [h.2.1]) (by linarith)

theorem E8Admissible.mono_t {s t v : ℝ} (h : E8Admissible s t)
    (hv : 0 < v) (hvt : v ≤ t) : E8Admissible s v := by
  refine ⟨h.1, hv, h.2.2.1, e8SlopeRange_downward h.2.2.2.1 hv hvt, ?_, ?_⟩
  · exact e8SlopeRange_downward h.2.2.2.2.1 (by linarith [h.1]) (by linarith)
  · exact e8SlopeRange_downward h.2.2.2.2.2 (by linarith [h.1]) (by linarith)

theorem e8_sAxis_of_derivative_bound (h : E8SAxisDerivativeBound) :
    E8PositiveOn fun s t => s ≤ 1 / 50 ∧ (3 / 50 : ℝ) ≤ t ∧ t ≤ 20 := by
  intro s t hadm hr
  apply e8Delta_pos_of_second_s_derivative hadm
  intro u hu
  exact h u t (hadm.mono_s hu.1 hu.2.le) (hu.2.le.trans hr.1) hr.2.1 hr.2.2

theorem e8_tAxis_of_derivative_bound (h : E8TAxisDerivativeBound) :
    E8PositiveOn fun s t => (3 / 50 : ℝ) ≤ s ∧ s ≤ 63 / 20 ∧ t ≤ 1 / 50 := by
  intro s t hadm hr
  apply e8Delta_pos_of_first_t_derivative hadm
  intro v hv
  exact h s v (hadm.mono_t hv.1 hv.2.le) hr.1 hr.2.1 (hv.2.le.trans hr.2.2)

theorem e8_smallSTail_of_derivative_bound (h : E8SmallSTailDerivativeBound) :
    E8PositiveOn fun s t => (20 : ℝ) ≤ t ∧ s ≤ 1 / 200 := by
  intro s t hadm hr
  apply e8Delta_pos_of_second_s_derivative hadm
  intro u hu
  exact h u t (hadm.mono_s hu.1 hu.2.le) hr.1 (hu.2.le.trans hr.2)

#print axioms e8Delta_pos_of_second_s_derivative
#print axioms e8Delta_pos_of_first_t_derivative
#print axioms e8_sAxis_of_derivative_bound
#print axioms e8_tAxis_of_derivative_bound
#print axioms e8_smallSTail_of_derivative_bound

end GeneralCK

end


