-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitEvenReduction
-- name    : Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitEvenReduction
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:12.842002+00:00
-- url     : https://prove2.me/theorems/7c765be5-bb83-495a-8b3f-a4563bce5cb9
-- title:
--   Split character sums and reciprocal changes of roots
-- statement:
--   For a finite root set s in a finite field, define the quadratic character sum of the split polynomial as the sum over all x of χ(∏_{a∈s}(x−a)). Given a selected field element a, define the reciprocal root set by removing a and mapping every remaining b to (b−a)⁻¹. Define the accompanying scale factor as ∏_{b∈s∖{a}}(a−b). These data specify the reciprocal substitution used in the even-degree reduction.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitEvenReduction.lean lines 13–20; SHA256 5a6c810fae82eeebe6d3371a0784ce36a0927f01247986614079cbfa99224a5a; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil



open Finset

namespace PaleyWeil

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

def splitCharacterSum (s : Finset K) : ℤ :=
  ∑ x : K, quadraticChar K (∏ a ∈ s, (x - a))

def reciprocalRoots (s : Finset K) (a : K) : Finset K :=
  (s.erase a).image (fun b ↦ (b - a)⁻¹)

def reciprocalScale (s : Finset K) (a : K) : K :=
  ∏ b ∈ s.erase a, (a - b)





















end
end PaleyWeil


