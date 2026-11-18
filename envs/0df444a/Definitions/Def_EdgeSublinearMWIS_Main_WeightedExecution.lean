-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_WeightedExecution
-- name    : EdgeSublinearMWIS_Main_WeightedExecution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-17T16:18:45.13352+00:00
-- url     : https://prove2.me/theorems/abf34d53-7217-400a-a7ba-be4eafed9ee9
-- title:
--   Rational preprocessing for the weighted independent-set reduction
-- statement:
--   For a signed rational input code representing $w$, retain its positive denominator and replace its numerator by its maximum with zero. The resulting code represents
--   $$w^+=\max\{w,0\}.$$
--   For an accuracy code representing $\varepsilon$, retain its numerator and double its denominator, obtaining a code for
--   $$\varepsilon/2.$$
--   The direct vertex set consists of vertices whose original rational weights are nonnegative. These data specify preprocessing and the empty/singleton boundary cases for the weighted reduction. They contain no program, correctness certificate, running-time field, or algorithmic oracle.
-- source:
--   Bonnet and Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, STOC2027 submission #1044, p.2 rational-weight domain and p.20 proof of Theorem2 (nonnegative reduction, direct cases, and the epsilon/2 unweighted call); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction

namespace EdgeSublinearMWIS.Main

/-- Clipping is performed on the signed numerator, retaining the input denominator. -/
def clippedCode (w : RationalCode) : RationalCode :=
  ⟨max w.numerator 0, w.denominator, w.positive⟩

def clippedValues {n : ℕ} (w : Fin n → RationalCode) : Fin n → ℚ :=
  fun v => (clippedCode (w v)).value

/-- An unreduced representation of half the requested rational accuracy. -/
def halfAccuracy (ε : RationalCode) : RationalCode :=
  ⟨ε.numerator, 2 * ε.denominator, Nat.mul_pos (by decide) ε.positive⟩

/-- The directly handled empty and singleton inputs. -/
noncomputable def directVertices {n : ℕ} (w : Fin n → RationalCode) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => 0 ≤ (w v).value)

end EdgeSublinearMWIS.Main


