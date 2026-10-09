-- Prove2me | Definitions.Def_ZetaNine_AnalyticUniformWeighted
-- name    : ZetaNine_AnalyticUniformWeighted
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T14:53:16.915979+00:00
-- url     : https://prove2.me/theorems/28af307a-1752-475e-9331-1b6aa40715fa
-- title:
--   Actual uniform weighted analytic bounds
-- statement:
--   Definitions of the actual analytic moment functions, explicit uniform constants and error sequence, actual quartic-weighted rational kernel sequence, and its weighted coefficient height. All functions are built from the original CoefficientMap kernel and the same actual phase function. The uniform estimate is a separate theorem; these definitions introduce no integer-output construction or lattice-margin axiom.
-- source:
--   Local zeta(9) research: research/analytic-weighted-uniform-source-delta-2026-10-07.md; complete original factorial, actual-moment, phase and quartic proof chain in the submitted Lean file. Native and fresh platform independent validation completed 2026-10-08.

import Mathlib
import Definitions.Def_ZetaNine_CoefficientMap
import Definitions.Def_ZetaNine_AnalyticPhase
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine

namespace ZetaNine.AnalyticMomentBounds

def actualMomentTerm (n r k : ℕ) : ℝ :=
  (CoefficientMap.actualR n (k : ℚ) : ℝ) *
    ((k : ℝ) * ((k : ℝ) + (n : ℝ))) ^ r

def actualMomentSequence (n r m : ℕ) : ℝ := actualMomentTerm n r (m + 1)

def actualMoment (n r : ℕ) : ℝ := ∑' m : ℕ, actualMomentSequence n r m

def tailPower (n r : ℕ) : ℕ := 7 * n + 9 - 2 * r

def tailCoefficient (n r : ℕ) : ℝ :=
  (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n * (3 / 2 : ℝ) ^ r

end ZetaNine.AnalyticMomentBounds

namespace ZetaNine.AnalyticUniformMomentBound
open AnalyticMomentBounds

def tailWeightConstant (r : ℕ) : ℝ :=
  (9 / 7 : ℝ) * (3 / 2 : ℝ) ^ r / (2 : ℝ) ^ (9 - 2 * r)

def tailMajorant (n r : ℕ) : ℝ :=
  tailCoefficient n r / (2 * (n : ℝ)) ^ tailPower n r * (9 / 7 : ℝ) /
    (n : ℝ) ^ (2 * r)

def tailExponent : ℝ := 7 + 6 * Real.log 2

def momentBoundConstant : ℝ := 5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7

end ZetaNine.AnalyticUniformMomentBound

namespace ZetaNine.AnalyticWeightedBound
open AnalyticMomentBounds AnalyticUniformMomentBound

def actualWeightedSequence (n : ℕ) (W : ℚ[X]) (m : ℕ) : ℝ :=
  (CoefficientMap.weightedR n W ((m + 1 : ℕ) : ℚ) : ℝ)

def weightedCoefficientHeight (n : ℕ) (W : ℚ[X]) : ℝ :=
  ∑ r ∈ range 5, |(W.coeff r : ℝ)| * (n : ℝ) ^ (2 * r)

def analyticPrefactor (n : ℕ) : ℝ :=
  momentBoundConstant * ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n)

def uniformError (n : ℕ) : ℝ :=
  (Real.log momentBoundConstant + 10 * Real.log ((n : ℝ) + 1)) / (n : ℝ)

end ZetaNine.AnalyticWeightedBound


