-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659CertificateCheck
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659CertificateCheck
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:08:23.907103+00:00
-- url     : https://prove2.me/theorems/5248576b-2273-4aef-b96a-902e679e09ba
-- title:
--   Executable integer features for Paley moment certificates
-- statement:
--   Define integer evaluators for the signed histogram coefficients, the histogram feature vector, and the lower and upper total-moment endpoints used by the Paley certificate checker. Binomial coefficients are evaluated with the fast natural-number binomial function. A coefficient-weighted feature term is zero when its coefficient is zero; the corresponding endpoint term selects the upper moment endpoint for a nonnegative coefficient and the lower endpoint for a negative coefficient. These definitions specify the exact arithmetic evaluated by the finite certificates.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/Paley2659CertificateCheck.lean lines 14–70; SHA256 b518277d6b881683c5caa30adf93e1330b779668ea13908a33b085168dabde9c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659MomentTotals
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_Paley2659PopulationMajorant
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil



/-! Efficient, kernel-reducible arithmetic for the Paley prefix certificates.

The fast binomial expression is proved equal to `Nat.choose` in mathlib.
Zero coefficients are skipped before evaluating their feature. These changes
only affect proof checking; all semantic inequalities remain those of the
unconditional population majorant.
-/

open Finset
namespace PaleyWeil

/-- The explicit coefficient formula with a polynomial-time binomial evaluator. -/
def signedHistogramMomentFast (n p j : ℕ) : ℤ :=
  if j ≤ n then
    ∑ i ∈ Finset.range (n - j + 1),
      (Nat.fast_choose p i : ℤ) *
        ((-1 : ℤ) ^ (n - p - (n - j - i)) *
          (Nat.fast_choose (n - p) (n - j - i) : ℤ))
  else 0



def paleyHistogramFeatureFast (h inside positives i : ℕ) : ℤ :=
  if i = 0 then 1 - (inside : ℤ)
  else if i = 1 then (inside : ℤ)
  else if i = 2 then (inside : ℤ) * (positives : ℤ)
  else if i ≤ 5 then (Nat.fast_choose positives (i - 2) : ℤ)
  else signedHistogramMomentFast (h - inside) positives (i - 3)



def paleyMomentLowerFast (h i : ℕ) : ℤ :=
  if i = 0 then 2659 - (h : ℤ)
  else if i = 1 then (h : ℤ)
  else if i = 2 then (Nat.fast_choose h 2 : ℤ)
  else if i ≤ 5 then (Nat.fast_choose h (i - 2) : ℤ) * paleyCodegreeLower (i - 2)
  else (Nat.fast_choose h (i - 3) : ℤ) *
    (paleyCharacterCenter (i - 3) - paleyCharacterRadius (i - 3))

def paleyMomentUpperFast (h i : ℕ) : ℤ :=
  if i = 0 then 2659 - (h : ℤ)
  else if i = 1 then (h : ℤ)
  else if i = 2 then (Nat.fast_choose h 2 : ℤ)
  else if i ≤ 5 then (Nat.fast_choose h (i - 2) : ℤ) * paleyCodegreeUpper (i - 2)
  else (Nat.fast_choose h (i - 3) : ℤ) *
    (paleyCharacterCenter (i - 3) + paleyCharacterRadius (i - 3))





def paleyHistogramTermFast (h inside positives i : ℕ) (c : ℤ) : ℤ :=
  if c = 0 then 0 else c * paleyHistogramFeatureFast h inside positives i

def paleyEndpointTermFast (h i : ℕ) (c : ℤ) : ℤ :=
  if c = 0 then 0 else
    signedIntegerEndpoint c (paleyMomentLowerFast h i) (paleyMomentUpperFast h i)









end PaleyWeil


