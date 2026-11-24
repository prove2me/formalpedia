-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitQuadraticWeight
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitQuadraticWeight
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:12.381576+00:00
-- url     : https://prove2.me/theorems/3fa8e399-8811-46b8-9051-8cdc9f0b8426
-- title:
--   The signed quadratic character weight of a polynomial
-- statement:
--   For a finite root set s and a polynomial P over a finite field, define its split quadratic weight to be χ((-1)^(|s| natDegree P) ∏_{a∈s} P(a)), where χ is the quadratic character and natDegree is the natural-valued polynomial degree. The degree-dependent sign fixes the convention relating degree-one polynomial weights to the character sum of the split polynomial with root set s.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitQuadraticWeight.lean lines 7–11; SHA256 8b7f6fc283769826ba78534d830f9bf0706820d9ff02d302bc6ec0b74bdf0ea7; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial



open Polynomial Finset

namespace PaleyWeil

/-- The signed polynomial character whose degree-one sum is the character sum
of the split polynomial with root set `s`. -/
def splitQuadraticWeight {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (s : Finset K) (P : K[X]) : ℤ :=
  quadraticChar K ((-1 : K) ^ (s.card * P.natDegree) * ∏ a ∈ s, P.eval a)










end PaleyWeil


