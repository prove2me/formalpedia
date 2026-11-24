-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovPolynomial
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovPolynomial
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:15.188806+00:00
-- url     : https://prove2.me/theorems/d920480a-a7ec-4adb-9682-926aa1c0227f
-- title:
--   The evaluation set used in the Stepanov argument
-- statement:
--   For a polynomial f over a field, a natural exponent c, and a field element a, define S_a to consist of all x such that f(x)=0 or f(x)^c=a. The definition includes the roots of f along with the points satisfying the specified power-value condition.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovPolynomial.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovPolynomial.lean lines 4–5; SHA256 80a9a4f0c3e2e3d6b4e402005021de097233638fd19ed2f769c11fbdcdf65968.

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
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



noncomputable def S_a (F : Type*) [Field F] (f : Polynomial F) (c : ℕ) (a : F) : Set F :=
  {x | Polynomial.eval x f = 0 ∨ (Polynomial.eval x f) ^ c = a}


