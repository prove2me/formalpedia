-- Prove2me | Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
-- name    : OAI_Algebra_FormulaHitting_NumeratorRows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T08:55:39.073418+00:00
-- url     : https://prove2.me/theorems/ad68010b-3d9f-4f0f-bb87-522cf3d955ee
-- title:
--   Numerator polynomials for repeated differentiation of a rational linear system
-- statement:
--   Let $F$ be a field and $I$ a finite index set. Fix a polynomial $q\in F[X]$, a matrix $P=(P_{tl})_{t,l\in I}$ of polynomials, and a vector $u\in F^I$. The numerator rows $N_j(l)\in F[X]$ ($j\in\mathbb{N}$, $l\in I$) are defined recursively by $N_0(l)=u_l$ (a constant polynomial) and
--   $$
--   N_{j+1}(l)=q\,N_j(l)'-j\,q'\,N_j(l)+\sum_{t\in I}N_j(t)\,P_{tl}.
--   $$
--
--   Consider a matrix $G$ of power series solving the linear differential system $qG'=PG$. Then $q^j$ times the $j$-th derivative of $\sum_tu_tG_{tl}$ equals $\sum_tN_j(t)G_{tl}$. The rows $N_j$ are the polynomial coefficients in that identity, and their degrees grow at most linearly in $j$.
--
--   **Formalization Note** The definition is `numeratorRow q P u j l`; $j$ in the recursion is cast from $\mathbb{N}$ to $F$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/NumeratorRows.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/NumeratorRows.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace NCHitting

open Polynomial

variable {F : Type*} [Field F]

def numeratorRow {I : Type*} [Fintype I] (q : F[X]) (P : Matrix I I F[X])
    (u : I → F) : ℕ → I → F[X]
  | 0, l => C (u l)
  | j + 1, l => q * (numeratorRow q P u j l).derivative -
      C (j : F) * q.derivative * numeratorRow q P u j l +
      ∑ t : I, numeratorRow q P u j t * P t l

end NCHitting

end

end OAI


