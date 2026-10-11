-- Prove2me | Definitions.Def_CLRS_Chapter4_Master_Rounding
-- name    : CLRS_Chapter4_Master_Rounding
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:02:35.964335+00:00
-- url     : https://prove2.me/theorems/ff09ccac-9a75-4ce0-bf44-b696a9fdfa7a
-- title:
--   Bounded-error natural division for the discrete master theorem
-- statement:
--   RoundedDivision requires a real divisor greater than one and a uniform bound on the distance between the natural child r(n) and n/b. Natural floor and ceiling division have this property. The bundle connects the rounded recurrence interface with the analytic discrete-recurrence framework. Strict child decrease is retained as a separate recurrence-package obligation, rather than inferred solely from bounded rounding error.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module Master.Rounding, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Master/Rounding.lean

import Definitions.Def_CLRS_Chapter4_Master_Basic
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Computability.AkraBazzi.AkraBazzi
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

/-! Rounded subproblem sizes and the bridge to Mathlib's recurrence theorem. -/
namespace Chapter4Master

open Filter Asymptotics Real
open scoped Topology

/-- Bounded rounding error around division by a fixed real divisor. -/
structure RoundedDivision (b : ℝ) (r : ℕ → ℕ) : Prop where
  divisor_gt_one : 1 < b
  bounded_error : ∃ C : ℝ, ∀ n : ℕ, ‖(r n : ℝ) - (n : ℝ) / b‖ ≤ C

theorem constant_littleO_size_div_log_sq :
    (fun _ : ℕ => (1 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log n) ^ 2) := by
  have hlog : (fun n : ℕ => (Real.log n) ^ 2) =o[atTop]
      (fun n : ℕ => (n : ℝ)) := by
    simpa using (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (show (0 : ℝ) < 1 by norm_num)).natCast_atTop
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) / (Real.log n) ^ 2 :=
      div_pos (by linarith) (sq_pos_of_pos (Real.log_pos hn'))
    exact fun h => (ne_of_gt hpos h).elim
  · simpa only [one_div, inv_div] using hlog.tendsto_div_nhds_zero

theorem RoundedDivision.small_error {b : ℝ} {r : ℕ → ℕ}
    (h : RoundedDivision b r) :
    (fun n : ℕ => (r n : ℝ) - b⁻¹ * n) =o[atTop]
      (fun n : ℕ => (n : ℝ) / (Real.log n) ^ 2) := by
  obtain ⟨C, hC⟩ := h.bounded_error
  have hO : (fun n : ℕ => (r n : ℝ) - b⁻¹ * n) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [] with n
    simpa only [norm_one, mul_one, div_eq_mul_inv, mul_comm] using hC n
  exact hO.trans_isLittleO constant_littleO_size_div_log_sq





/-- Reuse Akra--Bazzi only when its additional toll hypotheses are proved. -/
noncomputable def Recurrence.toAkra {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : ℝ} {r : ℕ → ℕ}
    (R : Recurrence T (fun n => g n) a r) (hr : RoundedDivision b r)
    (hg : ∀ x ≥ 0, 0 ≤ g x)
    (hpoly : AkraBazziRecurrence.GrowsPolynomially g) :
    AkraBazziRecurrence T g (fun _ : Unit => a) (fun _ : Unit => b⁻¹)
      (fun _ : Unit => r) where
  n₀ := R.cutoff
  n₀_gt_zero := R.cutoff_pos
  a_pos := fun _ => R.a_pos
  b_pos := fun _ => inv_pos.mpr (by linarith [hr.divisor_gt_one])
  b_lt_one := fun _ => inv_lt_one_of_one_lt₀ hr.divisor_gt_one
  g_nonneg := hg
  g_grows_poly := hpoly
  h_rec := by simpa using R.eqn
  T_gt_zero' := R.base_pos
  r_lt_n := fun _ => R.decreases
  dist_r_b := fun _ => hr.small_error



end Chapter4Master

end CLRS


