-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_JetMatrix
-- name    : OAI_Algebra_FormulaHitting_JetMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:06:29.374874+00:00
-- url     : https://prove2.me/theorems/21bb6c6e-1efb-43f2-98e4-78f72a96ec09
-- title:
--   The integration matrix acting on jets of power series
-- statement:
--   Let $F$ be a field of characteristic zero and let $d,i\in\mathbb{N}$. The integration matrix is the $d\times d$ matrix $M^{(i)}$, indexed by $r,q\in\{0,\dots,d-1\}$, with
--   $$
--   M^{(i)}_{rq}=\begin{cases}\dfrac{(-1)^{r-q-1}}{r\,i^{\,r-q}}, & q<r,\\ 0, & q\ge r,\end{cases}
--   $$
--   with the rational entries viewed in $F$.
--
--   $M^{(i)}$ is strictly lower triangular. It is the matrix of the operator $a\mapsto\int a\,\frac{dX}{X+i}$ on the first $d$ coefficients of a power series: the $r$-th coefficient of the image is $\sum_{q<r}M^{(i)}_{rq}[X^q]a$. The matrices $M^{(i+1)}$ are the generators substituted for the variables $x_i$ in the explicit hitting set.
--
--   **Formalization Note** `integrationMatrix d i` is defined by casting the rational numbers `matrixEntry i r q` into $F$. The characteristic-zero assumption of the enclosing section is not used by the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/JetMatrix.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/JetMatrix.lean by skeleton subtraction
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
import Definitions.Def_OAI_Algebra_FormulaHitting_Generator

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace NCHitting

open Matrix

variable {F : Type*} [Field F] [CharZero F]

def integrationMatrix (d i : ℕ) : Matrix (Fin d) (Fin d) F :=
  fun r q => (matrixEntry i r.val q.val : F)

end NCHitting

end

end OAI


