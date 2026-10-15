-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle001
-- name    : ThreeSum1960614_Machine_Bundle001
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T04:55:20.142211+00:00
-- url     : https://prove2.me/theorems/ea70039c-5c99-47e5-89e3-f7e4cc7b9402
-- title:
--   Certified logarithm intervals for the integer schedule
-- statement:
--   For a natural truncation index $n$ and a real number $z$, define the finite odd-power sum
--
--   $$S_n(z)=\sum_{i=0}^{n-1}\frac{z^{2i+1}}{2i+1}.$$
--
--   The supporting interval certificate applies when $0\le z<1$ and $y=(1+z)/(1-z)$. If real endpoints $L,U$ satisfy $L\le2S_n(z)$ and $2(S_n(z)+z^{2n+1}/(1-z^2))\le U$, it yields $L\le\log y\le U$. The bundle instantiates this certificate with explicit rational endpoints of denominator $10^{22}$ for $\log2$, $\log(29/16)$, $\log(232/231)$, $\log(464/463)$, $\log(32\theta)$, and $\log(2(1-\theta))$, where $\theta$ is the fixed rational analysis parameter. It also supplies decidability of the cleared integer switching predicate for natural parameters $J,s,j,q$.
--
--   These finite certificates make the numerical exponent and switching estimates available without floating-point assumptions in the deterministic integer 3SUM runtime proof. The finite-minimum and rounding machinery adapts the pinned upstream Switch formalization.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/Closed3Sum/high_precision_logs.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/Closed3Sum/integer_schedule.lean

-- Finite minimum and rounding arguments adapt the pinned upstream Switch.lean.

import Definitions.Def_ThreeSum1960614_Analysis
import Lean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace Set
end Set
namespace ThreeSum1960614
end ThreeSum1960614
namespace ThreeSum1960614.Machine.ThreeSum1960614
end ThreeSum1960614.Machine.ThreeSum1960614

namespace ThreeSum1960614.Machine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open scoped _root_.BigOperators
open _root_.ThreeSum1960614
open _root_.ThreeSum1960614.Machine.ThreeSum1960614

section
 noncomputable def private_b8deed26f4_logSeries (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * i + 1)
end


section
 theorem private_e85f2b851e_log_interval {y z L U : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hy : (1 + z) / (1 - z) = y) (n : ℕ)
    (hlo : L ≤ 2 * _root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries n z)
    (hhi : 2 * (_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) ≤ U) :
    L ≤ Real.log y ∧ Real.log y ≤ U := by
  have hl := mul_le_mul_of_nonneg_left (Real.sum_range_le_log_div hz0 hz1 n)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hu := mul_le_mul_of_nonneg_left (Real.log_div_le_sum_range_add hz0 hz1 n)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hleft : 2 * _root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries n z ≤ Real.log y := by
    rw [← hy]
    simpa [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hl
  have hright : Real.log y ≤ 2 * (_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
    rw [← hy]
    calc
      Real.log ((1 + z) / (1 - z)) = 2 * (1 / 2 * Real.log ((1 + z) / (1 - z))) := by ring
      _ ≤ 2 * (_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
        simpa [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries] using hu
  exact ⟨hlo.trans hleft, hright.trans hhi⟩
end


theorem ThreeSum1960614.high_precision_logs :
    ((6931471805599453094172 / 10 ^ 22 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 6931471805599453094173 / 10 ^ 22) ∧
    ((5947071077466927895143 / 10 ^ 22 : ℝ) ≤ Real.log (29 / 16) ∧
      Real.log (29 / 16) ≤ 5947071077466927895144 / 10 ^ 22) ∧
    ((43196611445164148724 / 10 ^ 22 : ℝ) ≤ Real.log (232 / 231) ∧
      Real.log (232 / 231) ≤ 43196611445164148725 / 10 ^ 22) ∧
    ((21574981400211907723 / 10 ^ 22 : ℝ) ≤ Real.log (464 / 463) ∧
      Real.log (464 / 463) ≤ 21574981400211907724 / 10 ^ 22) ∧
    ((2570554035235070921259 / 10 ^ 22 : ℝ) ≤ Real.log (32 * _root_.ThreeSum1960614.theta) ∧
      Real.log (32 * _root_.ThreeSum1960614.theta) ≤ 2570554035235070921260 / 10 ^ 22) ∧
    ((6518981167335747474116 / 10 ^ 22 : ℝ) ≤ Real.log (2 * (1 - _root_.ThreeSum1960614.theta)) ∧
      Real.log (2 * (1 - _root_.ThreeSum1960614.theta)) ≤ 6518981167335747474117 / 10 ^ 22) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact _root_.ThreeSum1960614.Machine.private_e85f2b851e_log_interval (z := (1 : ℝ) / 3) (by norm_num) (by norm_num)
      (by norm_num) 26 (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries]) (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries])
  · exact _root_.ThreeSum1960614.Machine.private_e85f2b851e_log_interval (z := (13 : ℝ) / 45) (by norm_num) (by norm_num)
      (by norm_num) 24 (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries]) (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries])
  · exact _root_.ThreeSum1960614.Machine.private_e85f2b851e_log_interval (z := (1 : ℝ) / 463) (by norm_num) (by norm_num)
      (by norm_num) 5 (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries]) (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries])
  · exact _root_.ThreeSum1960614.Machine.private_e85f2b851e_log_interval (z := (1 : ℝ) / 927) (by norm_num) (by norm_num)
      (by norm_num) 5 (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries]) (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries])
  · exact _root_.ThreeSum1960614.Machine.private_e85f2b851e_log_interval (z := (9159899 : ℝ) / 71659899) (by norm_num) (by norm_num)
      (by norm_num [_root_.ThreeSum1960614.theta]) 18 (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries]) (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries])
  · exact _root_.ThreeSum1960614.Machine.private_e85f2b851e_log_interval (z := (459590101 : ℝ) / 1459590101) (by norm_num) (by norm_num)
      (by norm_num [_root_.ThreeSum1960614.theta]) 26 (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries]) (by norm_num [_root_.ThreeSum1960614.Machine.private_b8deed26f4_logSeries])

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
open _root_.ThreeSum1960614
open _root_.ThreeSum1960614.Machine.ThreeSum1960614
open _root_.Set









section
 instance private_9ee78bd37a_switch_decidable (J s j q : ℕ) : Decidable (_root_.ThreeSum1960614.clearedSwitch J s j q) := by
  unfold _root_.ThreeSum1960614.clearedSwitch
  infer_instance
end

end ThreeSum1960614.Machine


