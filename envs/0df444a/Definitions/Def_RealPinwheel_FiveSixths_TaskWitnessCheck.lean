-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_TaskWitnessCheck
-- name    : RealPinwheel_FiveSixths_TaskWitnessCheck
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:03:09.094243+00:00
-- url     : https://prove2.me/theorems/fcb42354-d3f5-4d1c-92be-265600878749
-- title:
--   Per-task cycle witness arithmetic
-- statement:
--   For one task of an exact word witness, this Boolean checks the positive rational endpoint, mean execution count, prefix-count recurrence, discrepancy bounds, and monotonic lower tables. Writing $C_i(t)$ for its prefix count, the discrepancy is
--
--   $$D_i(t)=p_i t-q_i C_i(t).$$
--
--   This is precisely one task's portion of the full cycle-witness check, allowing long words to be checked task by task. Validity still follows from the separately proved all-window soundness theorem.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Per-task arithmetic equivalent to the source dominance-box checks.

import Definitions.Def_RealPinwheel_FiveSixths_Witness
namespace RealPinwheel.FiveSixths
/-- The local recurrence and discrepancy conditions for one task. -/
def taskWitnessCheck {n : ℕ} (w : CycleWitness n) (i : Fin n) : Bool :=

    let p := fun t => (w.counts i).eval t
    let lo := fun t => (w.low i).eval t
    let hi := fun t => (w.high i).eval t
    let num := codeNum w.code i
    let den := codeDen w.code i
    let D := fun t => (num : ℤ) * t - (den : ℤ) * p t
    let drift := D w.length
    let cap : ℤ := (den : ℤ) - if codeStrict w.code i then 0 else 1
    decide (0 < num ∧ 0 < den ∧ p 0 = 0 ∧ num * w.length ≤ den * p w.length) &&
    (List.range w.length).all fun t =>
      decide (p (t + 1) = p t + if w.word.eval t % n = i.val then 1 else 0) &&
      decide (lo t ≤ D t ∧ hi t ≤ D t ∧ D t - lo t ≤ cap ∧ D t + drift - hi t ≤ cap) &&
      if t + 1 < w.length then
        decide (lo (t + 1) ≤ lo t ∧ hi t ≤ hi (t + 1))
      else true

end RealPinwheel.FiveSixths


