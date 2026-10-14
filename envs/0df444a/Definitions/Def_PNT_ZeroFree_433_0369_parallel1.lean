-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0369_parallel1
-- name    : PNT_ZeroFree_433_0369_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:16:31.756245+00:00
-- url     : https://prove2.me/theorems/b02045ae-6d86-4813-818a-a8b71254742d
-- title:
--   Zero-free region foundations: LogarithmicControl [0369_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.LogarithmicControl
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L18-L541

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L18-L541
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.LogarithmicControl
section
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex

namespace SevenEighths.LogarithmicControl

theorem differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U)
    {L g : ℂ → ℂ} (hL : DifferentiableOn ℂ L U)
    (hg : ContinuousOn g U) (he : EqOn (Complex.exp ∘ g) L U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hgc : ContinuousAt g z := (hg z hz).continuousAt (hU.mem_nhds hz)
  have hLc : DifferentiableAt ℂ L z := (hL z hz).differentiableAt (hU.mem_nhds hz)
  have hs := Complex.hasStrictDerivAt_exp (g z)
  let inv := hs.localInverse Complex.exp (Complex.exp (g z)) (g z)
    (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (L z) := by
    rw [← he hz]
    exact (hs.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have heq : (fun w ↦ inv (L w)) =ᶠ[𝓝 z] g := by
    have hlocal := hgc.eventually (hs.eventually_left_inverse (Complex.exp_ne_zero _))
    filter_upwards [hlocal, hU.mem_nhds hz] with w hw hwU
    simpa only [← he hwU, Function.comp_apply] using hw
  exact ((hi.comp z hLc).congr_of_eventuallyEq heq.symm).differentiableWithinAt

theorem exists_holomorphic_log {L : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) := by
  let : ContractibleSpace (ball c R) := contractibleSpace_ball hR
  have hsc : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨g, hg, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc
    isOpen_ball hL.continuousOn (by
      rintro ⟨z, hz, heq⟩
      exact h0 z hz heq)
  exact ⟨g, differentiableOn_of_exp_eq isOpen_ball hL hg he, he⟩

theorem exists_holomorphic_log_normalized {L : ℂ → ℂ} {c m : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) (hm : Complex.exp m = L c) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) ∧ g c = m := by
  obtain ⟨g, hg, he⟩ := exists_holomorphic_log hR hL h0
  refine ⟨fun z ↦ g z + (m - g c), hg.add_const _, ?_, by simp⟩
  intro z hz
  change Complex.exp (g z + (m - g c)) = L z
  have hez : Complex.exp (g z) = L z := he hz
  have hec : Complex.exp (g c) = L c := he (mem_ball_self hR)
  rw [Complex.exp_add, Complex.exp_sub, hm, hez,
    hec, div_self (h0 c (mem_ball_self hR)), mul_one]

theorem log_eqOn_of_eq_center {g h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hh : DifferentiableOn ℂ h (ball c r))
    (he : EqOn (Complex.exp ∘ g) (Complex.exp ∘ h) (ball c r)) (hc : g c = h c) :
    EqOn g h (ball c r) := by
  have hcm : c ∈ ball c r := mem_ball_self hr
  have hgc := (hg.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hhc := (hh.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hs := Complex.hasStrictDerivAt_exp (g c)
  have hleft := hs.eventually_left_inverse (Complex.exp_ne_zero _)
  have hgleft := hgc.eventually hleft
  have hhc' : Tendsto h (𝓝 c) (𝓝 (g c)) := by
    rw [hc]
    exact hhc.tendsto
  have hhleft := hhc'.eventually hleft
  have heq : g =ᶠ[𝓝 c] h := by
    filter_upwards [hgleft, hhleft, isOpen_ball.mem_nhds hcm] with z hz1 hz2 hz
    rw [← hz1, ← hz2]
    exact congrArg _ (he hz)
  exact (hg.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hh.analyticOnNhd isOpen_ball) (convex_ball c r).isPreconnected hcm heq

theorem borel_caratheodory_closedBall {g : ℂ → ℂ} {c : ℂ} {r R M A : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M) (hA : 0 ≤ A)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hRe : ∀ z ∈ ball c R, (g z).re ≤ M) (hc : ‖g c‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * M * r / (R - r) + A * (R + r) / (R - r) := by
  have hzn : ‖z - c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hzR : ‖z - c‖ < R := hzn.trans_lt hrR
  have hRp : 0 < R := hr.trans_lt hrR
  have hg' : DifferentiableOn ℂ (fun w ↦ g (c + w)) (ball 0 R) := by
    apply hg.comp ((differentiable_const c).add differentiable_id).differentiableOn
    intro w hw
    simpa [mem_ball, dist_eq_norm] using hw
  have hb := Complex.borelCaratheodory hM hg' (fun w hw ↦ hRe _ (by
    simpa [mem_ball, dist_eq_norm] using hw)) (hr.trans_lt hrR)
    (show z - c ∈ ball 0 R by simpa using hzR)
  simp only [add_sub_cancel, add_zero] at hb
  refine hb.trans ?_
  apply add_le_add
  · gcongr
  · gcongr

theorem three_circles {g : ℂ → ℂ} {c z : ℂ} {r R S A B : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRS : R < S)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B)
    (hzr : r ≤ ‖z - c‖) (hzR : ‖z - c‖ ≤ R) :
    ‖g z‖ ≤ A ^ (1 - (Real.log ‖z - c‖ - Real.log r) /
      (Real.log R - Real.log r)) *
      B ^ ((Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)) := by
  let F : ℂ → ℂ := fun w ↦ g (c + Complex.exp w)
  have hRp : 0 < R := hr.trans hrR
  have hlog : Real.log r < Real.log R := Real.log_lt_log hr hrR
  have hmap (w : ℂ) (hw : w.re ≤ Real.log R) : c + Complex.exp w ∈ closedBall c R := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw).trans_eq (Real.exp_log hRp)
  have hclosed : closure (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) ⊆
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    apply closure_minimal
    · intro w hw
      exact ⟨hw.1.le, hw.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hd : DiffContOnCl ℂ F
      (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    have hm := hmap w (hclosed hw).2
    have hm' : c + Complex.exp w ∈ ball c S :=
      closedBall_subset_ball hRS hm
    exact ((hg _ hm').differentiableAt (isOpen_ball.mem_nhds hm')).comp w
      ((differentiableAt_const c).add (Complex.differentiable_exp w)) |>.differentiableWithinAt
  have hbound : BddAbove ((norm ∘ F) ''
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hb _ (hmap w hw.2)
  have hzn : 0 < ‖z - c‖ := hr.trans_le hzr
  have hz0 : z - c ≠ 0 := norm_pos_iff.mp hzn
  have hw : Complex.log (z - c) ∈
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    change Real.log r ≤ (Complex.log (z - c)).re ∧
      (Complex.log (z - c)).re ≤ Real.log R
    simp only [Complex.log_re]
    exact ⟨Real.log_le_log hr hzr, Real.log_le_log hzn hzR⟩
  have h := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlog hw hd hbound (a := A) (b := B) ?_ ?_
  · simpa [F, Complex.exp_log hz0, Complex.log_re] using h
  · intro w hw
    apply ha
    simp only [mem_preimage, mem_singleton_iff] at hw
    simp [mem_closedBall, dist_eq_norm, hw, Complex.norm_exp, Real.exp_log hr]
  · intro w hw
    exact hb _ (hmap w (le_of_eq hw))

theorem three_circles_power_bound {g : ℂ → ℂ} {c z : ℂ} {r ρ R S A B T : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R) (hRS : R < S)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B * T)
    (hz : z ∈ closedBall c ρ) :
    ‖g z‖ ≤ A * B * T ^ ((Real.log ρ - Real.log r) /
      (Real.log R - Real.log r)) := by
  let θ := (Real.log ρ - Real.log r) / (Real.log R - Real.log r)
  have hlogR : 0 < Real.log R - Real.log r :=
    sub_pos.mpr (Real.log_lt_log hr (hrρ.trans hρR))
  have hθ0 : 0 ≤ θ := div_nonneg
    (sub_nonneg.mpr (Real.log_le_log hr hrρ.le)) hlogR.le
  have hθ1 : θ ≤ 1 := (div_le_one hlogR).mpr (by
    linarith [Real.log_le_log (hr.trans hrρ) hρR.le])
  have hzn : ‖z - c‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hBp : 0 ≤ B := zero_le_one.trans hB
  have hTp : 0 ≤ T := zero_le_one.trans hT
  have hp1 : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ0
  by_cases hzr : ‖z - c‖ ≤ r
  · have hgz := ha z (by simpa [mem_closedBall, dist_eq_norm] using hzr)
    exact hgz.trans (by nlinarith [mul_le_mul hB hp1 zero_le_one hBp])
  · have hzr' : r ≤ ‖z - c‖ := (lt_of_not_ge hzr).le
    have hzx : 0 < ‖z - c‖ := hr.trans_le hzr'
    let x := (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)
    have hx0 : 0 ≤ x := div_nonneg
      (sub_nonneg.mpr (Real.log_le_log hr hzr')) hlogR.le
    have hxθ : x ≤ θ := (div_le_div_iff_of_pos_right hlogR).mpr (by
      linarith [Real.log_le_log hzx hzn])
    have hx1 : x ≤ 1 := hxθ.trans hθ1
    have h := three_circles hr (hrρ.trans hρR) hRS hg ha hb hzr' (hzn.trans hρR.le)
    have hAa : A ^ (1 - x) ≤ A := by
      simpa using Real.rpow_le_rpow_of_exponent_le hA (show 1 - x ≤ 1 by linarith)
    have hBb : B ^ x ≤ B := by
      simpa using Real.rpow_le_rpow_of_exponent_le hB hx1
    have hTT : T ^ x ≤ T ^ θ := Real.rpow_le_rpow_of_exponent_le hT hxθ
    calc
      ‖g z‖ ≤ A ^ (1 - x) * (B * T) ^ x := h
      _ = A ^ (1 - x) * (B ^ x * T ^ x) := by rw [Real.mul_rpow hBp hTp]
      _ ≤ A * (B * T ^ θ) := mul_le_mul hAa
        (mul_le_mul hBb hTT (Real.rpow_nonneg hTp _) hBp)
        (by positivity) hAp
      _ = A * B * T ^ θ := by ring

def uniformTheta (e : ℝ) : ℝ := 1 - Real.log (1 + e) / Real.log (200 / 49)

theorem uniformTheta_mem {e : ℝ} (he : 0 < e) (he' : e < 1 / 1000) :
    0 < uniformTheta e ∧ uniformTheta e < 1 := by
  have hD : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hn : 0 < Real.log (1 + e) := Real.log_pos (by linarith)
  have hnD : Real.log (1 + e) < Real.log (200 / 49) :=
    Real.log_lt_log (by linarith) (by linarith)
  unfold uniformTheta
  constructor
  · linarith [(div_lt_one hD).mpr hnD]
  · linarith [div_pos hn hD]

theorem three_circles_exponent_uniform {a e : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) :
    (Real.log (2 - a - 6 * e) - Real.log (49 / 100)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) ≤ uniformTheta e := by
  have hr : (0 : ℝ) < 49 / 100 := by norm_num
  have h6 : (49 / 100 : ℝ) < 2 - a - 6 * e := by linarith
  have h4 : (49 / 100 : ℝ) < 2 - a - 4 * e := by linarith
  have h6p : 0 < 2 - a - 6 * e := hr.trans h6
  have h4p : 0 < 2 - a - 4 * e := hr.trans h4
  have hep : 0 < 1 + e := by linarith
  have hD : 0 < Real.log (2 - a - 4 * e) - Real.log (49 / 100) :=
    sub_pos.mpr (Real.log_lt_log hr h4)
  have hU : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hDU : Real.log (2 - a - 4 * e) - Real.log (49 / 100) ≤
      Real.log (200 / 49) := by
    rw [← Real.log_div h4p.ne' hr.ne']
    apply Real.log_le_log (div_pos h4p hr)
    apply (div_le_iff₀ hr).mpr
    norm_num
    linarith
  have hprod : (2 - a - 6 * e) * (1 + e) ≤ 2 - a - 4 * e := by
    have : 2 - a - 6 * e ≤ 2 := by linarith
    nlinarith
  have hdiff : Real.log (1 + e) ≤ Real.log (2 - a - 4 * e) -
      Real.log (2 - a - 6 * e) := by
    have h := Real.log_le_log (mul_pos h6p hep) hprod
    rw [Real.log_mul h6p.ne' hep.ne'] at h
    linarith
  have hfrac : Real.log (1 + e) / Real.log (200 / 49) ≤
      (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
    gcongr
    exact (Real.log_pos (by linarith : 1 < 1 + e)).le.trans hdiff
  calc
    _ = 1 - (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
        (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
      apply eq_sub_iff_add_eq.mpr
      rw [← add_div]
      convert! div_self hD.ne' using 1
      ring
    _ ≤ uniformTheta e := sub_le_sub_left hfrac 1

theorem exp_sublinear_le {θ K ε : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      Real.exp (K * x ^ θ) ≤ D * Real.exp (ε * x) := by
  have ht : Tendsto (fun x : ℝ ↦ K * x ^ (-(1 - θ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).const_mul K
  obtain ⟨X, hX⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let Y := max 1 X
  refine ⟨Real.exp (K * Y ^ θ), Real.exp_pos _, ?_⟩
  intro x hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hYp : 0 < Y := zero_lt_one.trans_le (le_max_left _ _)
  by_cases hxy : x ≤ Y
  · have h1 : Real.exp (K * x ^ θ) ≤ Real.exp (K * Y ^ θ) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxp.le hxy hθ) hK
    exact h1.trans (le_mul_of_one_le_right (Real.exp_pos _).le
      (Real.one_le_exp (by positivity)))
  · have hlarge := hX x ((le_max_right 1 X).trans (lt_of_not_ge hxy).le)
    have heq : K * x ^ θ = (K * x ^ (-(1 - θ))) * x := by
      have hp := Real.rpow_add hxp (-(1 - θ)) 1
      rw [Real.rpow_one] at hp
      rw [mul_assoc, ← hp]
      congr 2
      ring
    have hlin : K * x ^ θ ≤ ε * x := by
      rw [heq]
      exact mul_le_mul_of_nonneg_right hlarge.le hxp.le
    exact (Real.exp_le_exp.mpr hlin).trans (le_mul_of_one_le_left
      (Real.exp_pos _).le (Real.one_le_exp (mul_nonneg hK (Real.rpow_nonneg hYp.le _))))

def outerConstant (e A M : ℝ) : ℝ := (4 * M + 4 * A) / e

theorem outerConstant_ge_one {e A M : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) : 1 ≤ outerConstant e A M := by
  unfold outerConstant
  apply (le_div_iff₀ he).mpr
  nlinarith

theorem outer_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 4 * e)) :
    ‖g z‖ ≤ outerConstant e A M * T := by
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hb := borel_caratheodory_closedBall (by linarith : 0 ≤ 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 3 * e) (mul_pos hMp hTp) hAp
    (hg.mono (ball_subset_ball (by linarith))) hRe hc hz
  have hgap : 2 - a - 3 * e - (2 - a - 4 * e) = e := by ring
  rw [hgap] at hb
  have hfirst : 2 * (M * T) * (2 - a - 4 * e) ≤ 4 * M * T := by
    nlinarith [mul_le_mul_of_nonneg_left
      (show 2 - a - 4 * e ≤ 2 by linarith) (show 0 ≤ 2 * M * T by positivity)]
  have hsecond : A * (2 - a - 3 * e + (2 - a - 4 * e)) ≤ 4 * A * T := by
    have h1 := mul_le_mul_of_nonneg_left
      (show 2 - a - 3 * e + (2 - a - 4 * e) ≤ 4 by linarith) hAp
    nlinarith [mul_le_mul_of_nonneg_left hT (show 0 ≤ 4 * A by positivity)]
  refine hb.trans ?_
  rw [← add_div]
  unfold outerConstant
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right he).mpr (by nlinarith)

theorem inner_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hin : ∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c (2 - a - 6 * e)) :
    ‖g z‖ ≤ A * outerConstant e A M * T ^ uniformTheta e := by
  have hB := outerConstant_ge_one he he' hA hM
  have hb : ∀ w ∈ closedBall c (2 - a - 4 * e), ‖g w‖ ≤ outerConstant e A M * T :=
    fun w hw ↦ outer_log_bound ha ha' he he' hA hM hT hg hRe
      (hin c (mem_closedBall_self (by norm_num))) hw
  have h := three_circles_power_bound (by norm_num : (0 : ℝ) < 49 / 100)
    (by linarith : 49 / 100 < 2 - a - 6 * e)
    (by linarith : 2 - a - 6 * e < 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 2 * e)
    hA hB hT hg hin hb hz
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT (three_circles_exponent_uniform ha ha' he he'))
    (by positivity))

theorem logarithm_derivative_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 8 * e)) :
    ‖deriv g z‖ ≤ (outerConstant e A M / (2 * e)) * T := by
  have hzn : dist z c ≤ 2 - a - 8 * e := hz
  have hsub : closedBall z (2 * e) ⊆ ball c (2 - a - 2 * e) := by
    intro w hw
    have hw' : dist w z ≤ 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c < _
    linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < 2 * e)
    (hg.diffContOnCl_ball hsub) (C := outerConstant e A M * T) ?_
  · exact h.trans_eq (by ring)
  · intro w hw
    apply outer_log_bound ha ha' he he' hA hM hT hg hRe hc
    have hw' : dist w z = 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c ≤ _
    linarith

theorem zero_free_disk_logarithm {L E : ℂ → ℂ} {c : ℂ} {a e A M C : ℝ}
    (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) (hC : 0 < C)
    (hL : DifferentiableOn ℂ L (ball c (2 - a - 2 * e)))
    (h0 : ∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0)
    (hpoly : ∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M)
    (hE : DifferentiableOn ℂ E (ball c (1 / 2)))
    (hEL : EqOn (Complex.exp ∘ E) L (ball c (1 / 2)))
    (hEb : ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c (2 - a - 2 * e)) ∧
      EqOn (Complex.exp ∘ g) L (ball c (2 - a - 2 * e)) ∧
      (∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A) ∧
      (∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * Real.log C) := by
  have hR : (1 / 2 : ℝ) < 2 - a - 2 * e := by linarith
  obtain ⟨g, hg, hge, hgc⟩ := exists_holomorphic_log_normalized
    (by linarith : 0 < 2 - a - 2 * e) hL h0
    (hEL (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
  have hgE : EqOn g E (ball c (1 / 2)) := log_eqOn_of_eq_center (by norm_num)
    (hg.mono (ball_subset_ball hR.le)) hE
    (fun z hz ↦ (hge (ball_subset_ball hR.le hz)).trans (hEL hz).symm) hgc
  refine ⟨g, hg, hge, ?_, ?_⟩
  · intro z hz
    rw [hgE (closedBall_subset_ball (by norm_num : (49 / 100 : ℝ) < 1 / 2) hz)]
    exact hEb z hz
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) := ball_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hp := hpoly z hz
    rw [← hez, Complex.norm_exp, Real.rpow_def_of_pos hC] at hp
    simpa [mul_comm] using Real.exp_le_exp.mp hp

theorem logarithmic_derivative_eq {L g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (he : EqOn (Complex.exp ∘ g) L U)
    {z : ℂ} (hz : z ∈ U) : deriv L z / L z = deriv g z := by
  have hgz := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hd := hgz.hasDerivAt.cexp
  have heq : L =ᶠ[𝓝 z] (fun w ↦ Complex.exp (g w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (he hw).symm
  have hdl := hd.congr_of_eventuallyEq heq
  rw [hdl.deriv]
  have hez : Complex.exp (g z) = L z := he hz
  rw [← hez]
  field_simp

theorem logarithmic_control {e A M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hA : 1 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a C : ℝ) (L E : ℂ → ℂ) (c : ℂ),
      1 / 2 ≤ a → a ≤ 1 → Real.exp 1 ≤ C →
      DifferentiableOn ℂ L (ball c (2 - a - 2 * e)) →
      (∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M) →
      DifferentiableOn ℂ E (ball c (1 / 2)) →
      EqOn (Complex.exp ∘ E) L (ball c (1 / 2)) →
      (∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall c (2 - a - 6 * e), ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall c (2 - a - 8 * e),
        ‖deriv L z / L z‖ ≤ (outerConstant e A M / (2 * e)) * Real.log C) := by
  have hθ := uniformTheta_mem he he'
  have hB := outerConstant_ge_one he he' hA hM
  have hK : 0 ≤ A * outerConstant e A M := by positivity
  obtain ⟨D, hD, hDb⟩ := exp_sublinear_le hθ.1.le hθ.2 hK hε
  refine ⟨2 * D, by positivity, ?_⟩
  intro a C L E c ha ha' hC hL h0 hpoly hE hEL hEb
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hT : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  obtain ⟨g, hg, hge, hgin, hgRe⟩ :=
    zero_free_disk_logarithm ha' he he' hCp hL h0 hpoly hE hEL hEb
  constructor
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) :=
      closedBall_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hb := inner_log_bound ha ha' he he' hA hM hT hg hgRe hgin hz
    have hp : Real.exp (A * outerConstant e A M * Real.log C ^ uniformTheta e) ≤
        D * C ^ ε := by
      convert! hDb (Real.log C) hT using 1
      rw [Real.rpow_def_of_pos hCp, mul_comm ε]
    have hu : ‖L z‖ ≤ D * C ^ ε := by
      rw [← hez, Complex.norm_exp]
      exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hb)).trans hp
    have hl : ‖(L z)⁻¹‖ ≤ D * C ^ ε := by
      rw [← hez, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
      have hre : -(g z).re ≤ ‖g z‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      exact (Real.exp_le_exp.mpr (hre.trans hb)).trans hp
    nlinarith
  · intro z hz
    rw [logarithmic_derivative_eq isOpen_ball hg hge
      (closedBall_subset_ball (by linarith) hz)]
    exact logarithm_derivative_bound ha ha' he he' hA hM hT hg hgRe
      (hgin c (mem_closedBall_self (by norm_num))) hz

theorem conductor_height_scale_ge_exp (Q t : ℝ) (hQ : 1 ≤ Q) :
    Real.exp 1 ≤ 2 * Q * (3 + |t|) ^ 2 := by
  have hs : 9 ≤ (3 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  have hq := mul_le_mul_of_nonneg_right hQ (sq_nonneg (3 + |t|))
  nlinarith [Real.exp_one_lt_three]

theorem absorb_polynomial_constant {K p : ℝ} (hp : 0 ≤ p) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ C : ℝ, Real.exp 1 ≤ C → K * C ^ p ≤ C ^ M := by
  let J := max 1 K
  have hJ : 1 ≤ J := le_max_left _ _
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hlogJ : 0 ≤ Real.log J := Real.log_nonneg hJ
  refine ⟨p + Real.log J + 1, by linarith, ?_⟩
  intro C hC
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hlogC : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  have hJC : J ≤ C ^ Real.log J := by
    rw [Real.rpow_def_of_pos hCp, ← Real.exp_log hJp]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    K * C ^ p ≤ J * C ^ p := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hCp.le _)
    _ ≤ C ^ Real.log J * C ^ p := mul_le_mul_of_nonneg_right hJC
      (Real.rpow_nonneg hCp.le _)
    _ = C ^ (p + Real.log J) := by rw [← Real.rpow_add hCp]; congr 1; ring
    _ ≤ C ^ (p + Real.log J + 1) := Real.rpow_le_rpow_of_exponent_le
      ((show (1 : ℝ) ≤ Real.exp 1 by exact Real.one_le_exp (by norm_num)).trans hC)
      (by linarith)

theorem disk_re_gt {a e t : ℝ} {z : ℂ}
    (hz : z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - a - 2 * e)) :
    a + 2 * e < z.re := by
  have hn : ‖z - (2 + (t : ℂ) * Complex.I)‖ < 2 - a - 2 * e := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z - (2 + (t : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, zero_mul, sub_zero, add_zero] at hr
  norm_num at hr
  linarith [neg_le_abs (z.re - 2)]

theorem same_height_mem_disk {a e t v x : ℝ} (hev : 8 * e ≤ v)
    (hx : a + v ≤ x) (hx' : x ≤ 2) :
    (x : ℂ) + (t : ℂ) * Complex.I ∈
      closedBall (2 + (t : ℂ) * Complex.I) (2 - a - 8 * e) := by
  rw [mem_closedBall, dist_eq_norm]
  have heq : (x : ℂ) + (t : ℂ) * Complex.I - (2 + (t : ℂ) * Complex.I) =
      ((x - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : x - 2 ≤ 0)]
  linarith

theorem principal_regularizer_norm_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  have hn : ‖s - 1‖ ≤ ‖s + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re, Complex.add_im, add_zero]
    nlinarith
  rw [norm_div]
  exact div_le_one_of_le₀ hn (norm_nonneg _)

theorem principal_reciprocal_transfer {s Z L : ℂ} (hs : 0 ≤ s.re)
    (hL : L = ((s - 1) / (s + 1)) * Z) (h0 : L ≠ 0) : ‖Z⁻¹‖ ≤ ‖L⁻¹‖ := by
  have hf0 : (s - 1) / (s + 1) ≠ 0 := by
    intro hf
    apply h0
    rw [hL, hf, zero_mul]
  have heq : Z⁻¹ = ((s - 1) / (s + 1)) * L⁻¹ := by
    rw [hL, mul_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hf0, one_mul]
  rw [heq, norm_mul]
  exact (mul_le_mul_of_nonneg_right (principal_regularizer_norm_le_one hs)
    (norm_nonneg _)).trans_eq (one_mul _)

end SevenEighths.LogarithmicControl

end

end OAI

end


