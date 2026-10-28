-- Prove2me | Definitions.Def_D1Bound5_PellFiniteCertificate_Definitions
-- name    : D1Bound5_PellFiniteCertificate_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:30:38.033884+00:00
-- url     : https://prove2.me/theorems/7d781bd6-c62a-4c83-b91c-83fef2ae1e8b
-- title:
--   Pell Finite Certificate
-- statement:
--   The matching is linked to the actual computed continued-fraction list. Thus completeness is a proved field of the eventual endpoint, not an external assertion about a supplied list of Pell solutions. The named objects in this bundle include `PellFiniteCertificate`, `PellFiniteCertificate.a0`, `PellFiniteCertificate.graph`, `PellFiniteCertificate.lastIndex`.
-- source:
--   D1Bound5/PellFiniteCertificate.lean, lines 11-21, SHA-256 dcc2fd88b881b2c8eafcbde15c1cb33b51af6fe491a0856432d4dcd395c5e1ed. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions
import Definitions.Def_D1Bound5_UnitPairArithmeticModel_Definitions
import Definitions.Def_D1Bound5_UnitPairPellBounds_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The matching is linked to the actual computed continued-fraction list.
Thus completeness is a proved field of the eventual endpoint, not an
external assertion about a supplied list of Pell solutions. -/
structure PellFiniteCertificate (d X : ℤ) where
  a0 : ℤ
  lastIndex : ℕ
  graph : PellMatchingCertificate d
  prefix_checked : pellCFPrefixCheck d a0 lastIndex = true
  stopping : X < (pellCFAt d a0 (pellCFInit a0) lastIndex).p
  magnitudes_eq :
    (pellCFSolutions d a0 X lastIndex).map (fun uv => uv.1^2-1) = graph.magnitudes









end D1Bound5
end


