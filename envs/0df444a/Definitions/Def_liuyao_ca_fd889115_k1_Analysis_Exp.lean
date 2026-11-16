-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Exp
-- name    : liuyao_ca_fd889115_k1_Analysis_Exp
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:23.088703+00:00
-- url     : https://prove2.me/theorems/ada428cf-5357-4d80-8100-6fd1e39fe9dc
-- title:
--   Computable analysis · Exp · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/Exp.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

namespace ComputableAnalysis

/-!
# Exponential algorithms

This file is the public, computation-facing exponential file.  The definitions
below intentionally expose the finite rational calculations directly.
-/

def expPowerSeriesTerms (x : Rat) (n : Nat) : Nat :=
  n + 8 + 2 * x.num.natAbs

def expPowerSeriesTailRatioBound (x : Rat) (n : Nat) : Rat :=
  qabs x / ((expPowerSeriesTerms x n + 1 : Nat) : Rat)

/-- The degree-two Taylor prefix of the exponential series.

This exact rational polynomial is kept public as the first
finite-difference bridge toward the derivative certificate for the full
tail-enclosed evaluator. -/
def expTaylorQuadratic (x : Rat) : Rat :=
  1 + x + x * x / 2

/-- The finite power-series calculation used by `expPowerSeries`.

The first component is the partial sum.  The second component is a rational
tail bound: after enough terms, consecutive term magnitudes are bounded by a
fixed ratio

`ratioBound = |x| / (terms + 1) < 1`,

so the omitted tail is bounded by the geometric series
`firstOmittedAbs / (1 - ratioBound)`. -/
def expPowerSeriesPartialAndTailBound (x : Rat) (n : Nat) : Rat × Rat :=
  Id.run do
    let terms : Nat := expPowerSeriesTerms x n
    let mut sum : Rat := 0
    let mut term : Rat := 1
    for k in List.range terms do
      sum := sum + term
      term := term * x / ((k + 1 : Nat) : Rat)
    let firstOmittedAbs : Rat := qabs term
    let ratioBound : Rat := expPowerSeriesTailRatioBound x n
    return (sum, firstOmittedAbs / (1 - ratioBound))

/-- Exponential from the power series

`exp x = 1 + x + x^2/2! + x^3/3! + ...`.

At stage `n`, we sum a finite number of terms and put a small rational box
around the partial sum using the geometric tail bound computed above.  The
proof that these boxes define the same real as the other exponential
algorithms belongs in the proof/infrastructure files.
-/
def expPowerSeries (x : Rat) : RealCompute where
  compute := fun n =>
    let data := expPowerSeriesPartialAndTailBound x n
    let center : Rat := data.1
    let radius : Rat := data.2
    { lo := center - radius, hi := center + radius }

/-- A candidate exponential from repeated compound interest:

`exp x = lim_m (1 + x/m)^m`.

At stage `n`, we compute the rational power `(1 + x/m)^m` by repeated
multiplication, then display it with a rational box. The fixed radius is
not a justified enclosure for arbitrary `x`: at `x = 2`, stages zero and
one are the disjoint intervals `[2, 4]` and `[73/16, 89/16]`. Thus this
definition is a candidate, not a valid general exponential computation.
Any use as a represented value needs separate validity and identification
evidence on its stated domain. -/
def expEuler (x : Rat) : RealCompute where
  compute := fun n =>
    let m : Nat := (n + 1) * (n + 1)
    let center : Rat := Id.run do
      let mut value : Rat := 1
      for _ in List.range m do
        value := value * (1 + x / (m : Rat))
      return value
    let radius : Rat :=
      if n = 0 then 1 else 1 / (((2 * n : Nat) : Rat))
    { lo := center - radius, hi := center + radius }


/-- A stage of the sharp compound-interest enclosure for `e`.

At external stage `n`, use `m = n + 1` and the classical rational bounds
`(1 + 1/m)^m <= e <= (1 + 1/m)^(m+1)`. -/
def eCompoundInterestStage (n : Nat) : QInterval :=
  let m : Nat := n + 1
  let base : Rat := 1 + 1 / (m : Rat)
  let lo : Rat := base ^ m
  { lo := lo, hi := lo * base }

/-- The number `e`, computed from the sharp compound-interest intervals
`[(1 + 1/m)^m, (1 + 1/m)^(m+1)]`. -/
def eCompoundInterest : RealCompute where
  compute := eCompoundInterestStage

/-- The number `e`, computed from the exponential power series at `1`. -/
def ePowerSeries : RealCompute :=
  expPowerSeries 1

/-- The number `e`, computed from repeated compound interest at `1`. -/
def eEuler : RealCompute :=
  expEuler 1

namespace ExpExamples

#eval! (ePowerSeries.compute 10).display
#eval! (eCompoundInterest.compute 10).display
#eval! (ePowerSeries.compute 100).display
#eval! (eEuler.compute 10).display
#eval! (eEuler.compute 100).display
#eval! ((expPowerSeries (1 / 2)).compute 100).display
#eval! ((expEuler (-1)).compute 100).display

end ExpExamples

end ComputableAnalysis


