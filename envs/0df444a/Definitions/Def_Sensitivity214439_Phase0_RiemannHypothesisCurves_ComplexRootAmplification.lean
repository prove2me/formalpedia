-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_ComplexRootAmplification
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_ComplexRootAmplification
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:14:31.266361+00:00
-- url     : https://prove2.me/theorems/ad24188a-d69d-41c9-9eb9-ba1f7846f8ef
-- title:
--   Complex power sums and products of linear factors
-- statement:
--   For a complex number w, define the formal power series with zero constant term and coefficient w^n in each positive degree n. For a finite list of complex numbers, define both the product of the factors 1 − wX and the sum of those positive-power series. These constructions record, respectively, a polynomial through its linear factors and the power sums of the same list, with repetitions retained.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/ComplexRootAmplification.lean lines 68–101; SHA256 11546c08aa7e433be5b2c0c70e879619bc6e1219a9ea26d6dee4de631b473d07; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial



/-!
A finite polynomial with constant coefficient one has an exact logarithmic
derivative given by the power sums of its reciprocal roots. A uniform
exponential bound on those power sums bounds each reciprocal root. This is
the sharpness amplification step; it uses no character-sum assumption.
-/

open Polynomial Finset
open scoped PowerSeries

namespace PaleyWeil

noncomputable section





def complexPositivePowers (w : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.rescale w (PowerSeries.mk 1) - 1







def complexFactorProduct (l : List ℂ) : ℂ⟦X⟧ :=
  (l.map fun w ↦ (1 - PowerSeries.C w * PowerSeries.X : ℂ⟦X⟧)).prod

def complexPowerSums (l : List ℂ) : ℂ⟦X⟧ :=
  (l.map complexPositivePowers).sum












end
end PaleyWeil


