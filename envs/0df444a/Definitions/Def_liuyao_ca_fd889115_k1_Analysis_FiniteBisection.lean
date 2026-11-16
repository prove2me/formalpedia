-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteBisection
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteBisection
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:49:43.702214+00:00
-- url     : https://prove2.me/theorems/8dca2829-433f-41a1-a2c6-9faa51aa32a8
-- title:
--   Computable analysis · FiniteBisection · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteBisection.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

/-!
# Finite rational bisection

This module records one exact bisection step for a rational interval and a
rational-valued function.  The sign decision is finite: the midpoint is
evaluated exactly and the retained half is chosen by comparison with zero.
No zero is constructed, and no completeness or limiting argument is used.
-/

namespace ComputableAnalysis

open QInterval

/-- Keep the half of `I` selected by the exact sign of the midpoint value. -/
def monotoneBisectionStep (f : Rat -> Rat) (I : QInterval) : QInterval :=
  if 0 ≤ f I.midpoint then
    { lo := I.lo, hi := I.midpoint }
  else
    { lo := I.midpoint, hi := I.hi }

theorem monotoneBisectionStep_ordered {f : Rat -> Rat} {I : QInterval}
    (hI : I.lo ≤ I.hi) :
    (monotoneBisectionStep f I).lo ≤ (monotoneBisectionStep f I).hi := by
  have hm := I.midpoint_mem hI
  by_cases hmid : 0 ≤ f I.midpoint
  · simp [monotoneBisectionStep, hmid]
    exact hm.1
  · simp [monotoneBisectionStep, hmid]
    exact hm.2

theorem monotoneBisectionStep_subinterval {f : Rat -> Rat} {I : QInterval}
    (hI : I.lo ≤ I.hi) :
    (monotoneBisectionStep f I).lo ≥ I.lo /\
      (monotoneBisectionStep f I).hi ≤ I.hi := by
  have hm := I.midpoint_mem hI
  by_cases hmid : 0 ≤ f I.midpoint
  · simp only [monotoneBisectionStep, if_pos hmid]
    exact ⟨by grind, hm.2⟩
  · simp only [monotoneBisectionStep, if_neg hmid]
    exact ⟨hm.1, by grind⟩

theorem monotoneBisectionStep_preserves_bracket
    {f : Rat -> Rat} {I : QInterval}
    (hI : I.lo ≤ I.hi)
    (hf : ∀ ⦃x y : Rat⦄, x ≤ y -> f x ≤ f y)
    (hlo : f I.lo ≤ 0) (hhi : 0 ≤ f I.hi) :
    f (monotoneBisectionStep f I).lo ≤ 0 /\
      0 ≤ f (monotoneBisectionStep f I).hi := by
  have _hvalue :
      f (monotoneBisectionStep f I).lo ≤
        f (monotoneBisectionStep f I).hi :=
    hf (monotoneBisectionStep_ordered hI)
  by_cases hmid : 0 ≤ f I.midpoint
  · simp only [monotoneBisectionStep, if_pos hmid]
    exact ⟨hlo, hmid⟩
  · simp only [monotoneBisectionStep, if_neg hmid]
    exact ⟨by grind, hhi⟩

/-! The target-parametrized step used by inverse searches.  The target is
carried as finite rational data and is never treated as an attained real. -/

def monotoneTargetBisectionStep (f : Rat -> Rat) (y : Rat) (I : QInterval) :
    QInterval :=
  if y ≤ f I.midpoint then
    { lo := I.lo, hi := I.midpoint }
  else
    { lo := I.midpoint, hi := I.hi }

theorem monotoneBisectionStep_preserves_target_bracket
    {f : Rat -> Rat} {I : QInterval} (y : Rat)
    (hI : I.lo ≤ I.hi)
    (hlo : f I.lo ≤ y) (hhi : y ≤ f I.hi) :
    f (monotoneTargetBisectionStep f y I).lo ≤ y /\
      y ≤ f (monotoneTargetBisectionStep f y I).hi := by
  have hm := I.midpoint_mem hI
  by_cases hmid : y ≤ f I.midpoint
  · simp only [monotoneTargetBisectionStep, if_pos hmid]
    exact ⟨hlo, hmid⟩
  · simp only [monotoneTargetBisectionStep, if_neg hmid]
    have hleft : f I.midpoint ≤ y := by
      grind
    exact ⟨hleft, hhi⟩

theorem monotoneTargetBisectionStep_subinterval
    {f : Rat -> Rat} {I : QInterval} (y : Rat)
    (hI : I.lo ≤ I.hi) :
    (monotoneTargetBisectionStep f y I).lo ≥ I.lo /\
      (monotoneTargetBisectionStep f y I).hi ≤ I.hi := by
  have hm := I.midpoint_mem hI
  by_cases hmid : y ≤ f I.midpoint
  · simp only [monotoneTargetBisectionStep, if_pos hmid]
    exact ⟨by grind, hm.2⟩
  · simp only [monotoneTargetBisectionStep, if_neg hmid]
    exact ⟨hm.1, by grind⟩

theorem monotoneTargetBisectionStep_width
    {f : Rat -> Rat} {I : QInterval} (y : Rat) :
    (monotoneTargetBisectionStep f y I).width = I.width / 2 := by
  by_cases hmid : y ≤ f I.midpoint
  · simp [monotoneTargetBisectionStep, QInterval.width,
      QInterval.midpoint]
    grind [Rat.div_def]
  · simp [monotoneTargetBisectionStep, QInterval.width,
      QInterval.midpoint]
    grind [Rat.div_def]

theorem monotoneBisectionStep_width {f : Rat -> Rat} {I : QInterval} :
    (monotoneBisectionStep f I).width = I.width / 2 := by
  by_cases hmid : 0 ≤ f I.midpoint
  · simp [monotoneBisectionStep, QInterval.width, QInterval.midpoint]
    grind [Rat.div_def]
  · simp [monotoneBisectionStep, QInterval.width, QInterval.midpoint]
    grind [Rat.div_def]

end ComputableAnalysis


