-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
-- name    : OAI_Analysis_LipschitzEquivalence_RadialBudget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:29:41.800528+00:00
-- url     : https://prove2.me/theorems/19dcea6d-0570-479b-8535-82f5a497b4b5
-- title:
--   A logarithmic speed profile with finite radial budget
-- statement:
--   A scalar speed function $\gamma$ and a potential $\Phi$ controlling sums of the form $\sum(r_n^2-r_{n+1}^2)\gamma(r_n)^2$.
--
--   1. **Definitions.** Let $c=1/100$ and $r_0=e^{-2}$. Define
--   $$
--   \gamma(r)=\frac{c}{r\log(1/r)}\ \ (0<r<r_0),\qquad \gamma(r)=0\ \text{otherwise},
--   $$
--   and $\Phi(r)=-2c^2/\log r$ for $0<r<r_0$, $\Phi(r)=c^2$ for $r\ge r_0$, $\Phi(r)=0$ for $r\le0$.
--   2. **Properties.** $\gamma\ge0$ is antitone on $(0,\infty)$, $0\le\Phi\le c^2$, and on $(0,r_0)$, $2r\gamma(r)^2=\Phi'(r)$. Consequently for $0\le s\le r$,
--   $$
--   (r^2-s^2)\,\gamma(r)^2\le\Phi(r)-\Phi(s).
--   $$
--   3. **Budget.** For any antitone nonnegative sequence $r_n$, the series $\sum_n(r_n^2-r_{n+1}^2)\gamma(r_n)^2$ converges and is at most $c^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/RadialBudget.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/RadialBudget.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace LipschitzCounterexample.RadialBudget
open Set Filter MeasureTheory
open scoped Topology

def c : ℝ := 1/100
def cutoff : ℝ := Real.exp (-2)

def gamma (r : ℝ) : ℝ := if 0 < r ∧ r < cutoff then c / (r * Real.log (1/r)) else 0

def potential (r : ℝ) : ℝ := if 0 < r then if r < cutoff then -2*c^2 / Real.log r else c^2 else 0

theorem c_pos : 0 < c := by norm_num [c]
theorem cutoff_lt_one : cutoff < 1 := by
  rw [cutoff, Real.exp_lt_one_iff]
  norm_num

theorem log_bound {r : ℝ} (hr : r ∈ Ioo 0 cutoff) : Real.log r < -2 := by
  have h := Real.log_lt_log hr.1 hr.2
  simpa [cutoff] using h

theorem gamma_formula {r : ℝ} (hr : r ∈ Ioo 0 cutoff) : gamma r = c / (r * (-Real.log r)) := by
  simp [gamma, hr.1, hr.2, one_div, Real.log_inv]

theorem gamma_nonneg (r : ℝ) : 0 ≤ gamma r := by
  by_cases h : 0 < r ∧ r < cutoff
  · rw [gamma_formula h]
    exact div_nonneg c_pos.le (mul_nonneg h.1.le (by linarith [log_bound h]))
  · simp [gamma, h]

theorem denominator_deriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t => t * (-Real.log t)) (-Real.log r - 1) r := by
  have h : HasDerivAt (fun t : ℝ => t * (-Real.log t))
      (1 * (-Real.log r) + r * (-r⁻¹)) r :=
    (hasDerivAt_id r).mul (Real.hasDerivAt_log hr.ne').neg
  convert h using 1
  simp [hr.ne', sub_eq_add_neg]

theorem denominator_monotone : MonotoneOn (fun r => r * (-Real.log r)) (Ioo 0 cutoff) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun r => -Real.log r - 1) (convex_Ioo _ _) ?_ ?_ ?_
  · intro r hr
    exact (denominator_deriv hr.1).continuousAt.continuousWithinAt
  · intro r hr
    exact (denominator_deriv (interior_subset hr).1).hasDerivWithinAt
  · intro r hr
    have h := log_bound (interior_subset hr)
    linarith

theorem gamma_antitone : AntitoneOn gamma (Ioi 0) := by
  intro r hr s hs hrs
  by_cases hs' : s < cutoff
  · have hr' : r < cutoff := hrs.trans_lt hs'
    rw [gamma_formula ⟨hs, hs'⟩, gamma_formula ⟨hr, hr'⟩]
    have hd : 0 < r * (-Real.log r) := mul_pos hr (by linarith [log_bound ⟨hr, hr'⟩])
    apply div_le_div_of_nonneg_left c_pos.le hd
    exact denominator_monotone ⟨hr, hr'⟩ ⟨hs, hs'⟩ hrs
  · simp only [gamma, hs', and_false, ↓reduceIte]
    exact gamma_nonneg r

theorem potential_nonneg (r : ℝ) : 0 ≤ potential r := by
  by_cases hr : 0 < r
  · by_cases hrc : r < cutoff
    · simp only [potential, hr, hrc, ↓reduceIte]
      exact div_nonneg_of_nonpos (by nlinarith [sq_nonneg c]) (by linarith [log_bound ⟨hr, hrc⟩])
    · simpa [potential, hr, hrc] using sq_nonneg c
  · simp [potential, hr]

theorem potential_le (r : ℝ) : potential r ≤ c^2 := by
  by_cases hr : 0 < r
  · by_cases hrc : r < cutoff
    · simp only [potential, hr, hrc, ↓reduceIte]
      apply (div_le_iff_of_neg (by linarith [log_bound ⟨hr, hrc⟩])).2
      nlinarith [log_bound ⟨hr, hrc⟩, sq_nonneg c]
    · simp [potential, hr, hrc]
  · simpa [potential, hr] using sq_nonneg c

theorem potential_deriv {r : ℝ} (hr : r ∈ Ioo 0 cutoff) :
    HasDerivAt (fun t => -2*c^2 / Real.log t) (2*c^2/(r*(Real.log r)^2)) r := by
  have hn : Real.log r ≠ 0 := by linarith [log_bound hr]
  have h : HasDerivAt (fun t : ℝ => -2*c^2 / Real.log t)
      ((0 * Real.log r - (-2*c^2)*r⁻¹) / (Real.log r)^2) r :=
    (hasDerivAt_const r (-2*c^2)).div (Real.hasDerivAt_log hr.1.ne') hn
  convert h using 1
  field_simp
  ring

theorem weighted_formula {r : ℝ} (hr : r ∈ Ioo 0 cutoff) :
    2*r*gamma r^2 = 2*c^2 / (r * (Real.log r)^2) := by
  rw [gamma_formula hr]
  field_simp

theorem primitive_integral {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hr : r < cutoff) :
    (∫ t in s..r, 2*c^2/(t*(Real.log t)^2)) = potential r - potential s := by
  have hx (t : ℝ) (ht : t ∈ Icc s r) : t ∈ Ioo 0 cutoff := ⟨hs.trans_le ht.1, ht.2.trans_lt hr⟩
  have hc : ContinuousOn (fun t => 2*c^2/(t*(Real.log t)^2)) (Icc s r) := by
    apply continuousOn_const.div (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2))
    · intro t ht
      apply mul_ne_zero (ne_of_gt (hx t ht).1)
      exact pow_ne_zero 2 (by linarith [log_bound (hx t ht)])
    · intro t ht
      exact ne_of_gt (hx t ht).1
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => potential_deriv (hx t (by simpa [uIcc_of_le hsr] using ht)))
    (hc.intervalIntegrable_of_Icc hsr)
  simpa [potential, hs, hs.trans_le hsr, hr, hsr.trans_lt hr] using hi

theorem step_interior {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hr : r < cutoff) :
    (r^2-s^2) * gamma r^2 ≤ potential r - potential s := by
  have hx (t : ℝ) (ht : t ∈ Icc s r) : t ∈ Ioo 0 cutoff := ⟨hs.trans_le ht.1, ht.2.trans_lt hr⟩
  have hc : ContinuousOn (fun t => 2*c^2/(t*(Real.log t)^2)) (Icc s r) := by
    apply continuousOn_const.div (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2))
    · intro t ht
      apply mul_ne_zero (ne_of_gt (hx t ht).1)
      exact pow_ne_zero 2 (by linarith [log_bound (hx t ht)])
    · intro t ht
      exact ne_of_gt (hx t ht).1
  have hle := intervalIntegral.integral_mono_on hsr
    (show IntervalIntegrable (fun t => 2*t*gamma r^2) volume s r from
      (by fun_prop : Continuous (fun t : ℝ => 2*t*gamma r^2)).intervalIntegrable s r)
    (hc.intervalIntegrable_of_Icc hsr) (fun t ht => by
      rw [← weighted_formula (hx t ht)]
      apply mul_le_mul_of_nonneg_left _ (by linarith [(hx t ht).1])
      exact pow_le_pow_left₀ (gamma_nonneg r) (gamma_antitone (hx t ht).1 (hs.trans_le hsr) ht.2) 2)
  have hleft : (∫ t in s..r, 2*t*gamma r^2) = (r^2-s^2)*gamma r^2 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hleft, primitive_integral hs hsr hr] at hle
  exact hle

theorem step_zero {r : ℝ} (hr : 0 < r) (hrc : r < cutoff) :
    r^2 * gamma r^2 ≤ potential r := by
  have hl := log_bound ⟨hr, hrc⟩
  have hn : Real.log r ≠ 0 := by linarith
  have heq : r^2 * gamma r^2 = c^2 / (Real.log r)^2 := by
    rw [gamma_formula ⟨hr, hrc⟩]
    field_simp
  rw [heq]
  simp only [potential, hr, hrc, ↓reduceIte]
  apply (div_le_iff₀ (sq_pos_of_ne_zero hn)).2
  have hp : (-2*c^2 / Real.log r) * (Real.log r)^2 = -2*c^2 * Real.log r := by
    field_simp
  rw [hp]
  nlinarith [sq_nonneg c]

theorem step {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    (r^2-s^2)*gamma r^2 ≤ potential r - potential s := by
  by_cases hr : 0 < r
  · by_cases hrc : r < cutoff
    · rcases hs.eq_or_lt with hsz | hsp
      · subst s
        simpa [potential] using step_zero hr hrc
      · exact step_interior hsp hsr hrc
    · have hg : gamma r = 0 := by simp [gamma, hrc]
      rw [hg]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      have hp : potential r = c^2 := by simp [potential, hr, hrc]
      rw [hp]
      linarith [potential_le s]
  · have hrz : r = 0 := by linarith
    have hsz : s = 0 := by linarith
    subst r s
    simp

theorem partial_budget {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hmono : Antitone r) (N : ℕ) :
    (∑ n ∈ Finset.range N, (r n^2-r (n+1)^2)*gamma (r n)^2) ≤ c^2 := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, (potential (r n) - potential (r (n+1))) := by
      exact Finset.sum_le_sum (fun n _ => step (hr (n+1)) (hmono (Nat.le_succ n)))
    _ = potential (r 0) - potential (r N) := Finset.sum_range_sub' _ _
    _ ≤ c^2 := by linarith [potential_le (r 0), potential_nonneg (r N)]

theorem budget {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hmono : Antitone r) :
    Summable (fun n => (r n^2-r (n+1)^2)*gamma (r n)^2) ∧
      (∑' n, (r n^2-r (n+1)^2)*gamma (r n)^2) ≤ c^2 := by
  have hpos (n : ℕ) : 0 ≤ (r n^2-r (n+1)^2)*gamma (r n)^2 := by
    apply mul_nonneg _ (sq_nonneg _)
    exact sub_nonneg.mpr (pow_le_pow_left₀ (hr (n+1)) (hmono (Nat.le_succ n)) 2)
  exact ⟨summable_of_sum_range_le hpos (partial_budget hr hmono),
    Real.tsum_le_of_sum_range_le hpos (partial_budget hr hmono)⟩

end LipschitzCounterexample.RadialBudget

end

end OAI


