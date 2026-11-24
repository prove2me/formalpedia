-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_WeightedGeometricSeries
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_WeightedGeometricSeries
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:14.712206+00:00
-- url     : https://prove2.me/theorems/6b166d1d-c0c8-4949-9a17-47b26bcfad00
-- title:
--   Weighted geometric and prime-rate formal power series
-- statement:
--   For an integer weight w and natural degree d, define a formal power series whose coefficient at n is w^(n/d) when d divides n and is zero otherwise. For positive d, this is the series 1+wX^d+w²X^(2d)+⋯. Define its prime-rate series to be d times the difference between the geometric series and the constant series 1. These definitions provide the factors and rates in the finite Euler product.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/WeightedGeometricSeries.lean lines 14–50; SHA256 b1c97d2323db1a76e8c6ea9dcd7525354ab95ba51973a60071c3d6e31ee927f6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace PowerSeries
end PowerSeries



/-! Weighted geometric factors and their exact formal logarithmic derivatives. -/

open scoped PowerSeries
open PowerSeries Finset

namespace PaleyWeil

noncomputable section

def weightedGeometric (w : ℤ) (d : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n ↦ if d ∣ n then w ^ (n / d) else 0









def weightedPrimeRate (w : ℤ) (d : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.C (d : ℤ) * (weightedGeometric w d - 1)










end
end PaleyWeil


