-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
-- name    : OAI_Analysis_LipschitzEquivalence_SlowAngles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:51:10.222402+00:00
-- url     : https://prove2.me/theorems/fc180f01-94c7-46e7-bb19-a05b390d1607
-- title:
--   Slowly varying rotation angles in the radius
-- statement:
--   Smooth angle functions of a radius $r>0$ that switch from $\pi/2$ to $0$ slowly enough to respect the speed profile $\gamma(r)=c/(r\log(1/r))$ with $c=1/100$.
--
--   1. **Warp.** $\mathrm{warp}(t)=e^{-e^t}$ is strictly decreasing with values in $(0,1)$, inverted by $r\mapsto\log(-\log r)$, whose derivative is $-1/(r\log(1/r))$.
--   2. **Angles.** With $\sigma$ the standard smooth transition from $0$ to $1$ and $|\sigma'|\le C_\sigma$, put $w=\pi C_\sigma\sqrt3/c+1$. The angle $\theta_{A}(r)$ equals $\pi/2$ for $r\le\mathrm{warp}(A+w)$ and $0$ for $r\ge\mathrm{warp}(A)$, and in between
--   $$
--   \theta_A(r)=\frac\pi2\,\sigma\Bigl(\frac{\log(-\log r)-A}{w}\Bigr).
--   $$
--   It is smooth, and for $A\ge3$ it satisfies $|\theta_A'(r)|\le\gamma(r)/(2\sqrt3)$.
--   3. **Stage parameters.** Given bounds $L_k\ge0$, parameters $A_0<A_1<\cdots$ with $A_{k+1}\ge A_k+w+3$ are chosen recursively so that $L_k+L_{k+1}\le\gamma(r)/2$ for $0<r\le\mathrm{warp}(A_k-1)$. The stage transition intervals $[\mathrm{warp}(A_k+w+1),\mathrm{warp}(A_k-1)]$ are then disjoint and shrink to $0$.
--   4. **Pulled-back angles.** For a $\sqrt3$-Lipschitz radius function $R$ on a normed space, $x\mapsto\theta_k(R(x))$ is $C^1$ with derivative at most $\gamma(R(x))/2$ where $R(x)>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SlowAngles.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SlowAngles.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates

namespace OAI

universe uX

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal

namespace LipschitzCounterexample.SlowAngles
open Set Filter
open RadialBudget

def warp (t : ℝ) : ℝ := Real.exp (-Real.exp t)
def inverseWarp (r : ℝ) : ℝ := Real.log (-Real.log r)

theorem warp_pos (t : ℝ) : 0 < warp t := Real.exp_pos _
theorem warp_lt_one (t : ℝ) : warp t < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos _))
theorem warp_strictAnti : StrictAnti warp := by
  intro a b hab
  exact Real.exp_lt_exp.mpr (neg_lt_neg (Real.exp_lt_exp.mpr hab))

@[simp] theorem inverseWarp_warp (t : ℝ) : inverseWarp (warp t) = t := by
  simp [inverseWarp, warp]

theorem inverseWarp_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt inverseWarp (-1 / (r * (-Real.log r))) r := by
  have hlog : Real.log r < 0 := Real.log_neg hr.1 hr.2
  have h := (Real.hasDerivAt_log (neg_ne_zero.mpr hlog.ne)).comp r
    (Real.hasDerivAt_log hr.1.ne').neg
  have he : -1 / (r * (-Real.log r)) = (-Real.log r)⁻¹ * -r⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_neg]
    ring
  rw [he]
  exact h

theorem inverseWarp_le_iff {r t : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    inverseWarp r ≤ t ↔ warp t ≤ r := by
  rw [inverseWarp, Real.log_le_iff_le_exp (neg_pos.mpr (Real.log_neg hr.1 hr.2))]
  rw [warp, ← Real.le_log_iff_exp_le hr.1]
  constructor <;> intro h <;> linarith

theorem le_inverseWarp_iff {r t : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    t ≤ inverseWarp r ↔ r ≤ warp t := by
  rw [inverseWarp, Real.le_log_iff_exp_le (neg_pos.mpr (Real.log_neg hr.1 hr.2))]
  rw [warp, ← Real.log_le_iff_le_exp hr.1]
  constructor <;> intro h <;> linarith

theorem transition_derivative_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds ht] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    rw [he.deriv_eq, deriv_const, abs_zero]
    exact le_max_right _ _
  · exact (hC 0 (by simp)).trans (le_max_left _ _)
  · by_cases ht1 : t ≤ 1
    · exact (hC t ⟨ht.le,ht1⟩).trans (le_max_left _ _)
    · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [eventually_gt_nhds (lt_of_not_ge ht1)] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [he.deriv_eq, deriv_const, abs_zero]
      exact le_max_right _ _

def transitionBound : ℝ := transition_derivative_bound.choose

theorem transitionBound_nonneg : 0 ≤ transitionBound := transition_derivative_bound.choose_spec.1

theorem deriv_transition_le (t : ℝ) : |deriv Real.smoothTransition t| ≤ transitionBound :=
  transition_derivative_bound.choose_spec.2 t

def width : ℝ := Real.pi * transitionBound * Real.sqrt 3 / c + 1

theorem width_pos : 0 < width := by
  have hc := c_pos
  have := transitionBound_nonneg
  dsimp [width]
  positivity

def angleFormula (A B r : ℝ) : ℝ :=
  (Real.pi / 2) * Real.smoothTransition ((inverseWarp r - A) / B)

def angle (A B r : ℝ) : ℝ :=
  if r ≤ warp (A+B+1) then Real.pi/2 else
  if warp (A-1) ≤ r then 0 else angleFormula A B r

theorem angle_small {A B r : ℝ} (hB : 0 < B) (hr : r ≤ warp (A+B)) :
    angle A B r = Real.pi/2 := by
  unfold angle
  split_ifs with hsmall hlarge
  · rfl
  · have : warp (A+B) < warp (A-1) := warp_strictAnti (by linarith)
    linarith
  · have hr0 : 0 < r := (warp_pos _).trans (lt_of_not_ge hsmall)
    have hr1 : r < 1 := hr.trans_lt (warp_lt_one _)
    have hp : A+B ≤ inverseWarp r := (le_inverseWarp_iff ⟨hr0,hr1⟩).mpr hr
    have hs : 1 ≤ (inverseWarp r-A)/B := (le_div_iff₀ hB).mpr (by linarith)
    simp [angleFormula, Real.smoothTransition.one_of_one_le hs]

theorem angle_large {A B r : ℝ} (hB : 0 < B) (hr : warp A ≤ r) :
    angle A B r = 0 := by
  unfold angle
  split_ifs with hsmall hlarge
  · have : warp (A+B+1) < warp A := warp_strictAnti (by linarith)
    linarith
  · rfl
  · have hr0 : 0 < r := (warp_pos A).trans_le hr
    have hr1 : r < 1 := (lt_of_not_ge hlarge).trans (warp_lt_one _)
    have hp : inverseWarp r ≤ A := (inverseWarp_le_iff ⟨hr0,hr1⟩).mpr hr
    have hs : (inverseWarp r-A)/B ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hB.le
    simp [angleFormula, Real.smoothTransition.zero_of_nonpos hs]

end LipschitzCounterexample.SlowAngles

namespace LipschitzCounterexample.SlowAngles
open Set Filter
open RadialBudget

theorem angleFormula_contDiffAt {A B r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) {d : ℕ∞} :
    ContDiffAt ℝ d (angleFormula A B) r := by
  have hi : ContDiffAt ℝ d inverseWarp r :=
    (contDiffAt_id.log hr.1.ne').neg.log (neg_ne_zero.mpr (Real.log_neg hr.1 hr.2).ne)
  exact contDiffAt_const.mul (Real.smoothTransition.contDiffAt.comp r ((hi.sub contDiffAt_const).div_const B))

theorem angle_eventually_formula {A B r : ℝ}
    (ha : warp (A+B+1) < r) (hb : r < warp (A-1)) :
    angle A B =ᶠ[𝓝 r] angleFormula A B := by
  filter_upwards [eventually_gt_nhds ha, eventually_lt_nhds hb] with s hs₁ hs₂
  simp [angle, hs₁.not_ge, hs₂.not_ge]

theorem angle_eventually_small {A B r : ℝ} (hB : 0 < B) (hr : r < warp (A+B)) :
    angle A B =ᶠ[𝓝 r] fun _ => Real.pi/2 := by
  filter_upwards [eventually_lt_nhds hr] with s hs
  exact angle_small hB hs.le

theorem angle_eventually_large {A B r : ℝ} (hB : 0 < B) (hr : warp A < r) :
    angle A B =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
  filter_upwards [eventually_gt_nhds hr] with s hs
  exact angle_large hB hs.le

theorem angle_contDiff (A : ℝ) {B : ℝ} (hB : 0 < B) {d : ℕ∞} :
    ContDiff ℝ d (angle A B) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hs : r < warp (A+B)
  · exact contDiffAt_const.congr_of_eventuallyEq (angle_eventually_small hB hs)
  by_cases hl : warp A < r
  · exact contDiffAt_const.congr_of_eventuallyEq (angle_eventually_large hB hl)
  have ha : warp (A+B+1) < r :=
    (warp_strictAnti (by linarith : A+B < A+B+1)).trans_le (le_of_not_gt hs)
  have hb : r < warp (A-1) :=
    (le_of_not_gt hl).trans_lt (warp_strictAnti (by linarith : A-1 < A))
  have hr : r ∈ Ioo (0 : ℝ) 1 := ⟨(warp_pos _).trans ha, hb.trans (warp_lt_one _)⟩
  exact (angleFormula_contDiffAt hr).congr_of_eventuallyEq (angle_eventually_formula ha hb)

theorem angleFormula_hasDerivAt {A B r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (angleFormula A B)
      ((Real.pi/2) * deriv Real.smoothTransition ((inverseWarp r-A)/B) *
        ((-1 / (r * (-Real.log r)))/B)) r := by
  have hd := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
    ((inverseWarp r-A)/B)).hasDerivAt.comp r ((inverseWarp_hasDerivAt hr).sub_const A |>.div_const B)
  convert hd.const_mul (Real.pi/2) using 1 <;> first | rfl | ring

theorem warp_below_cutoff {A : ℝ} (hA : 3 ≤ A) : warp (A-1) < cutoff := by
  apply Real.exp_lt_exp.mpr
  have hx : 2 < Real.exp (A-1) := by
    have h := Real.add_one_lt_exp (by linarith : A-1 ≠ 0)
    linarith
  linarith

end LipschitzCounterexample.SlowAngles

namespace LipschitzCounterexample.SlowAngles
open Set Filter
open RadialBudget

theorem width_budget : Real.pi * transitionBound / (2 * width) ≤ c / (2 * Real.sqrt 3) := by
  have hw : 0 < 2 * width := mul_pos (by norm_num) width_pos
  have hs : 0 < 2 * Real.sqrt 3 := by positivity
  apply (div_le_div_iff₀ hw hs).mpr
  dsimp [width, c]
  ring_nf
  norm_num

theorem angle_deriv_bound {A : ℝ} (hA : 3 ≤ A) (r : ℝ) :
    |deriv (angle A width) r| ≤ gamma r / (2 * Real.sqrt 3) := by
  by_cases hs : r < warp (A+width)
  · rw [(angle_eventually_small width_pos hs).deriv_eq, deriv_const, abs_zero]
    exact div_nonneg (gamma_nonneg r) (by positivity)
  by_cases hl : warp A < r
  · rw [(angle_eventually_large width_pos hl).deriv_eq, deriv_const, abs_zero]
    exact div_nonneg (gamma_nonneg r) (by positivity)
  have ha : warp (A+width+1) < r :=
    (warp_strictAnti (by linarith : A+width < A+width+1)).trans_le (le_of_not_gt hs)
  have hb : r < warp (A-1) :=
    (le_of_not_gt hl).trans_lt (warp_strictAnti (by linarith : A-1 < A))
  have hr0 : 0 < r := (warp_pos _).trans ha
  have hrc : r < cutoff := hb.trans (warp_below_cutoff hA)
  have hr1 : r < 1 := hrc.trans cutoff_lt_one
  have hden : 0 < r * (-Real.log r) := mul_pos hr0 (neg_pos.mpr (Real.log_neg hr0 hr1))
  rw [(angle_eventually_formula ha hb).deriv_eq, (angleFormula_hasDerivAt ⟨hr0,hr1⟩).deriv]
  calc
    _ = (Real.pi/2) * |deriv Real.smoothTransition ((inverseWarp r-A)/width)| *
        ((1 / (r * (-Real.log r)))/width) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.pi/2),
        abs_div, abs_div, abs_neg, abs_one, abs_of_pos hden, abs_of_pos width_pos]
    _ ≤ (Real.pi/2) * transitionBound * ((1 / (r * (-Real.log r)))/width) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (deriv_transition_le _) (by positivity))
        (div_nonneg (div_nonneg zero_le_one hden.le) width_pos.le)
    _ = (Real.pi * transitionBound / (2 * width)) / (r * (-Real.log r)) := by ring
    _ ≤ (c / (2 * Real.sqrt 3)) / (r * (-Real.log r)) :=
      div_le_div_of_nonneg_right width_budget hden.le
    _ = gamma r / (2 * Real.sqrt 3) := by rw [gamma_formula ⟨hr0,hrc⟩]; ring

end LipschitzCounterexample.SlowAngles

namespace LipschitzCounterexample.SlowAngles
open Set Filter
open RadialBudget

theorem warp_tendsto : Tendsto (fun A : ℝ => warp (A-1)) atTop (𝓝 0) := by
  have hs : Tendsto (fun A : ℝ => A-1) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  have h := Real.tendsto_exp_atTop.comp hs
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h)

theorem warp_denominator_tendsto :
    Tendsto (fun A : ℝ => warp (A-1) * (-Real.log (warp (A-1)))) atTop (𝓝 0) := by
  have h := (Real.continuous_mul_log.tendsto 0).comp warp_tendsto
  simpa only [Function.comp_def, zero_mul, neg_zero, neg_mul_eq_mul_neg] using h.neg

theorem exists_parameter (L : ℝ) (hL : 0 ≤ L) (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 3 ≤ A ∧ R ≤ A ∧ warp (A-1) < δ ∧ L ≤ gamma (warp (A-1))/2 := by
  have hε : 0 < c/(2*L+1) := div_pos c_pos (by linarith)
  have hD := warp_denominator_tendsto.eventually (gt_mem_nhds hε)
  have hb := warp_tendsto.eventually (gt_mem_nhds hδ)
  obtain ⟨A,hD,hb,hA,hR⟩ := (hD.and (hb.and ((eventually_ge_atTop (3 : ℝ)).and (eventually_ge_atTop R)))).exists
  refine ⟨A,hA,hR,hb,?_⟩
  have hd : 0 < warp (A-1) * (-Real.log (warp (A-1))) :=
    mul_pos (warp_pos _) (neg_pos.mpr (Real.log_neg (warp_pos _) (warp_lt_one _)))
  rw [gamma_formula ⟨warp_pos _,warp_below_cutoff hA⟩]
  have hh := (lt_div_iff₀ (by linarith : 0 < 2*L+1)).mp hD
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply (le_div_iff₀ hd).mpr
  nlinarith

def chooseParameter (L R : ℝ) (k : ℕ) (hL : 0 ≤ L) : ℝ :=
  (exists_parameter L hL R (pow_pos (by norm_num : (0 : ℝ) < 1/2) (k+1))).choose

theorem chooseParameter_spec (L R : ℝ) (k : ℕ) (hL : 0 ≤ L) :
    3 ≤ chooseParameter L R k hL ∧ R ≤ chooseParameter L R k hL ∧
    warp (chooseParameter L R k hL-1) < (1/2 : ℝ)^(k+1) ∧
    L ≤ gamma (warp (chooseParameter L R k hL-1))/2 :=
  (exists_parameter L hL R (pow_pos (by norm_num : (0 : ℝ) < 1/2) (k+1))).choose_spec

def parameters (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) : ℕ → ℝ
  | 0 => chooseParameter (L 0+L 1) 3 0 (add_nonneg (hL 0) (hL 1))
  | k+1 => chooseParameter (L (k+1)+L (k+2))
      (parameters L hL k + width + 3) (k+1) (add_nonneg (hL (k+1)) (hL (k+2)))

theorem parameters_ge_three (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) :
    3 ≤ parameters L hL k := by
  cases k with
  | zero => exact (chooseParameter_spec _ _ _ _).1
  | succ k => exact (chooseParameter_spec _ _ _ _).1

theorem parameters_step (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) :
    parameters L hL k + width + 3 ≤ parameters L hL (k+1) :=
  (chooseParameter_spec _ _ _ _).2.1

theorem parameters_budget (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) :
    L k + L (k+1) ≤ gamma (warp (parameters L hL k-1))/2 := by
  cases k with
  | zero => exact (chooseParameter_spec _ _ _ _).2.2.2
  | succ k => exact (chooseParameter_spec _ _ _ _).2.2.2

def lower (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) : ℝ :=
  warp (parameters L hL k + width + 1)
def upper (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) : ℝ :=
  warp (parameters L hL k - 1)
def theta (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) : ℝ → ℝ :=
  angle (parameters L hL k) width

theorem lower_pos (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) : 0 < lower L hL k := warp_pos _

theorem interval_separation (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) :
    upper L hL (k+1) < lower L hL k := by
  apply warp_strictAnti
  linarith [parameters_step L hL k]

theorem stage_budget (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) {r : ℝ}
    (hr : 0 < r) (hr' : r ≤ upper L hL k) : L k + L (k+1) ≤ gamma r / 2 := by
  exact (parameters_budget L hL k).trans
    (div_le_div_of_nonneg_right (gamma_antitone hr (warp_pos _) hr') (by norm_num))

theorem theta_contDiff (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) {d : ℕ∞} :
    ContDiff ℝ d (theta L hL k) := angle_contDiff _ width_pos

theorem theta_deriv_bound (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) (r : ℝ) :
    |deriv (theta L hL k) r| ≤ gamma r / (2 * Real.sqrt 3) :=
  angle_deriv_bound (parameters_ge_three L hL k) r

theorem theta_small_eventually (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) {r : ℝ}
    (hr : r ≤ lower L hL k) : theta L hL k =ᶠ[𝓝 r] fun _ => Real.pi/2 := by
  apply angle_eventually_small width_pos
  exact hr.trans_lt (warp_strictAnti (by linarith : parameters L hL k+width < parameters L hL k+width+1))

theorem theta_large_eventually (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) {r : ℝ}
    (hr : upper L hL k ≤ r) : theta L hL k =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
  apply angle_eventually_large width_pos
  exact (warp_strictAnti (by linarith : parameters L hL k-1 < parameters L hL k)).trans_le hr

end LipschitzCounterexample.SlowAngles

namespace LipschitzCounterexample.SlowAngles
open Set Filter
open scoped Topology
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k)
variable (R : X → ℝ) (hR : ∀ x, 0 ≤ R x) (hcR : Continuous R)
  (hdR : ∀ x, 0 < R x → ContDiffAt ℝ 1 R x)

include hR hcR hdR in

theorem pulledAngle_contDiff (k : ℕ) : ContDiff ℝ 1 (fun x => theta L hL k (R x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hr : 0 < R x
  · exact (theta_contDiff L hL k).contDiffAt.comp x (hdR x hr)
  · have hz : R x = 0 := le_antisymm (le_of_not_gt hr) (hR x)
    have he := (theta_small_eventually L hL k (r := R x) (by rw [hz]; exact (lower_pos L hL k).le)).comp_tendsto hcR.continuousAt
    exact contDiffAt_const.congr_of_eventuallyEq he

include hdR in
theorem pulledAngle_deriv_bound (hLip : LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg _⟩ R)
    (k : ℕ) (x : X) (hr : 0 < R x) :
    ‖fderiv ℝ (fun x => theta L hL k (R x)) x‖ ≤ RadialBudget.gamma (R x)/2 := by
  have hθ := ((theta_contDiff L hL k (d := 1)).differentiable (by norm_num) (R x)).hasDerivAt
  have hD := hθ.comp_hasFDerivAt x ((hdR x hr).differentiableAt (by norm_num)).hasFDerivAt
  change ‖fderiv ℝ (theta L hL k ∘ R) x‖ ≤ _
  rw [hD.fderiv, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (RadialBudget.gamma (R x)/(2*Real.sqrt 3)) * Real.sqrt 3 := by
      exact mul_le_mul (theta_deriv_bound L hL k (R x)) (norm_fderiv_le_of_lipschitz ℝ hLip)
        (norm_nonneg _) (div_nonneg (RadialBudget.gamma_nonneg _) (by positivity))
    _ = _ := by field_simp

end LipschitzCounterexample.SlowAngles

end

end OAI


