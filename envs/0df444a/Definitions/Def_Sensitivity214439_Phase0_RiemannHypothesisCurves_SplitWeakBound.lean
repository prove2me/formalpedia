-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitWeakBound
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitWeakBound
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:13.751607+00:00
-- url     : https://prove2.me/theorems/aff01dde-0d76-449e-9d8a-b44e8d0a18e8
-- title:
--   The monic polynomial with a specified finite root set
-- statement:
--   For a finite set s of elements of a field, define the split polynomial ∏_{a∈s}(X−a). The finite-set product includes one linear factor for each distinct element of s and is equal to 1 when s is empty.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitWeakBound.lean lines 8–9; SHA256 a085700b582884c017a4077a03b16064ed535c978747d8cc59a9db8d448fef66; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial



open Polynomial Finset

namespace PaleyWeil

noncomputable def splitPolynomial {K : Type*} [Field K] (s : Finset K) : K[X] :=
  ∏ a ∈ s, (X - C a)















end PaleyWeil


