-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_Generator
-- name    : OAI_Algebra_FormulaHitting_Generator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:05:33.424877+00:00
-- url     : https://prove2.me/theorems/036ab9c3-268d-4413-afe8-0d03a501190c
-- title:
--   The hitting-set matrices have size 1 for one variable and size 1
-- statement:
--   For natural numbers $n$ (number of variables) and $s$ (formula size bound), the matrix size is $\dim(n,s)=1$ if $n=s=1$ and $\dim(n,s)=2ns^2$ otherwise. This file records the evaluation
--   $$
--   \dim(1,1)=1 .
--   $$
--
--   In the degenerate case of one variable and formulas of size $1$, the hitting matrices are therefore $1\times1$. This case is handled separately from the general construction.
--
--   **Formalization Note** The lemma `dimension_one` is proved by `decide` and tagged as a simplification lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Generator.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Generator.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FormulaHitting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis
import Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity
import Definitions.Def_OAI_Algebra_FormulaHitting_Formula
import Definitions.Def_OAI_Algebra_FormulaHitting_Representation
import Definitions.Def_OAI_Algebra_FormulaHitting_Series
import Definitions.Def_OAI_Algebra_FormulaHitting_System
import Definitions.Def_OAI_Algebra_FormulaHitting_Evaluation
import Definitions.Def_OAI_Algebra_FormulaHitting_FormulaSeries
import Definitions.Def_OAI_Algebra_FormulaHitting_Independence
import Definitions.Def_OAI_Algebra_FormulaHitting_WordIndependence
import Definitions.Def_OAI_Algebra_FormulaHitting_RationalTransfer

namespace OAI

namespace NCHitting

@[simp] theorem dimension_one : dimension 1 1 = 1 := by decide

end NCHitting

end OAI


