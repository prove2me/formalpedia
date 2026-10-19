-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_FormulaSeries
-- name    : OAI_Algebra_FormulaHitting_FormulaSeries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:01:46.065883+00:00
-- url     : https://prove2.me/theorems/8a7a5926-da51-46ac-9093-a77aca3a71d7
-- title:
--   The power series attached to a noncommutative formula
-- statement:
--   Let $F$ be a field and fix $n$. For a word $w$ over $\{0,\dots,n-1\}$, $\Phi(w)\in F[[X]]$ is its word series. It is defined by $\Phi(\varepsilon)=1$ and $\Phi(iw)=\int\Phi(w)\,\frac{1}{X+i+1}$, with formal integration from $0$. For a noncommutative formula $f$ with finitely supported coefficient series $(f_w)_w$, define
--   $$
--   \Sigma(f)=\sum_{w}f_w\,\Phi(w)\in F[[X]],
--   $$
--   a finite sum over the words in the support.
--
--   This linear substitution of words by iterated integrals turns a noncommutative polynomial into a single power series. Distinct words give linearly independent series, so $\Sigma(f)$ vanishes only when all coefficients of $f$ vanish.
--
--   **Formalization Note** The definition is `Formula.series f := f.polynomial.sum (fun w a => C a * wordSeries w)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/FormulaSeries.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/FormulaSeries.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace NCHitting
namespace Formula

variable {F : Type*} {n : ℕ} [Field F]

def series (f : Formula F n) : PowerSeries F :=
  f.polynomial.sum (fun w a => PowerSeries.C a * wordSeries w)

end Formula
end NCHitting

end

end OAI


