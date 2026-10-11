-- Prove2me | Definitions.Def_CLRS_Chapter4_Master_Basic
-- name    : CLRS_Chapter4_Master_Basic
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:02:15.495725+00:00
-- url     : https://prove2.me/theorems/5b010e8e-51af-4340-b773-c5742dc199dd
-- title:
--   Positive-base real recurrences and canonical comparison solutions
-- statement:
--   The real-valued recurrence package fixes a positive real multiplier, a strictly smaller natural child above a positive cutoff, positive base values, a nonnegative toll at every natural size, and the exact recurrence T(n)=a*T(r(n))+f(n). The canonical solve function supplies an actual total solution with base value one for comparison. These definitions keep the original toll assumptions separate from stronger analytic hypotheses imposed only on comparison tolls.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module Master.Basic, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Master/Basic.lean

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

/-!
# Real-valued recurrence comparison

This file keeps the recurrence hypotheses separate from the analytic estimates
used by the master theorem. In particular, the original toll need not have
Mathlib's stronger `GrowsPolynomially` property. Finite base cases may differ
between comparison recurrences.
-/

open Filter Asymptotics
open scoped Topology

namespace Chapter4Master

/-- A positive-base, nonnegative-toll divide-and-conquer recurrence. The child
function is explicit so that floor and ceiling recurrences use the same API. -/
structure Recurrence (T f : ℕ → ℝ) (a : ℝ) (r : ℕ → ℕ) where
  cutoff : ℕ
  cutoff_pos : 0 < cutoff
  a_pos : 0 < a
  base_pos : ∀ n, n < cutoff → 0 < T n
  toll_nonneg : ∀ n, 0 ≤ f n
  decreases : ∀ n, cutoff ≤ n → r n < n
  eqn : ∀ n, cutoff ≤ n → T n = a * T (r n) + f n

namespace Recurrence

variable {T f U g : ℕ → ℝ} {a : ℝ} {r : ℕ → ℕ}





end Recurrence



namespace Recurrence

variable {T f U g : ℕ → ℝ} {a : ℝ} {r : ℕ → ℕ}







end Recurrence

/-- The canonical solution with base value one. This constructs a genuine
recurrence for analytic comparison; existence is not an extra theorem premise. -/
noncomputable def solve (a : ℝ) (r : ℕ → ℕ) (cutoff : ℕ)
    (decreases : ∀ n, cutoff ≤ n → r n < n) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if _hn : n < cutoff then 1
  else a * solve a r cutoff decreases f (r n) + f n
termination_by n
decreasing_by exact decreases n (Nat.le_of_not_lt _hn)

theorem solve_base (a : ℝ) (r : ℕ → ℕ) (cutoff : ℕ)
    (decreases : ∀ n, cutoff ≤ n → r n < n) (f : ℕ → ℝ)
    {n : ℕ} (hn : n < cutoff) : solve a r cutoff decreases f n = 1 := by
  rw [solve, dif_pos hn]

theorem solve_step (a : ℝ) (r : ℕ → ℕ) (cutoff : ℕ)
    (decreases : ∀ n, cutoff ≤ n → r n < n) (f : ℕ → ℝ)
    {n : ℕ} (hn : cutoff ≤ n) :
    solve a r cutoff decreases f n = a * solve a r cutoff decreases f (r n) + f n := by
  rw [solve, dif_neg (Nat.not_lt.mpr hn)]

noncomputable def solve_recurrence (a : ℝ) (r : ℕ → ℕ) (cutoff : ℕ)
    (decreases : ∀ n, cutoff ≤ n → r n < n) (f : ℕ → ℝ)
    (hcutoff : 0 < cutoff) (ha : 0 < a) (hf : ∀ n, 0 ≤ f n) :
    Recurrence (solve a r cutoff decreases f) f a r where
  cutoff := cutoff
  cutoff_pos := hcutoff
  a_pos := ha
  base_pos := fun n hn => by rw [solve_base a r cutoff decreases f hn]; norm_num
  toll_nonneg := hf
  decreases := decreases
  eqn := fun n hn => solve_step a r cutoff decreases f hn

end Chapter4Master

end CLRS


