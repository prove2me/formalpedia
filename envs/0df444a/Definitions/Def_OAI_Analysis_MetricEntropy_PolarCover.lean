-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
-- name    : OAI_Analysis_MetricEntropy_PolarCover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:39:34.335978+00:00
-- url     : https://prove2.me/theorems/3f489d5b-548a-4d5f-9586-80e9c3a1f4f6
-- title:
--   Coefficient representatives for approximation-list members
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. The body comes from a real matrix $g(y,x)$ with columns $y\in Y$ and rows $x\in X$, namely $K=3\,\mathrm{conv}\{\pm g(\cdot,x)\}+t\,Q_Y$. Separated rows force $N(K,Q_Y)\ge|X|$. A short list of functions approximating all column combinations $\sum_y\lambda_yg(y,\cdot)$ with $\|\lambda\|_1\le1$ uniformly gives a small dual covering.
--
--   1. **Coefficient representative.** Let $g:Y\times X\to\mathbb R$, $\varepsilon\ge0$, and $f$ a function on $X$. If some $\lambda\in B_1^Y$ has $g^\top\lambda$ $\varepsilon$-close to $f$, the representative of $f$ is a chosen such $\lambda$. Otherwise it is $0$.
--   2. **Use.** Replacing each member of an approximation list $A$ by its representative gives $|A|$ actual centers in $B_1^Y$. Since two $\lambda$'s close to the same $f$ have column combinations within $2\varepsilon$ of each other, these centers serve as covering centers for $B_1^Y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/PolarCover.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/PolarCover.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MetricEntropyDuality mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uX uY

/-!
# Polar covers from arbitrary uniform approximation lists

The functions on the approximation list need not be column combinations.
For every nonempty coefficient fiber we choose an actual vector in the
coefficient ball; empty fibers receive zero. The resulting list has exactly
the original number of slots, with no factor depending on the dimension.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

variable {X : Type uX} {Y : Type uY} [Fintype Y]

/-- An actual coefficient vector in the fiber of a list function, or zero
when this fiber is empty. No inverse of the column-combination map is used. -/
def coefficientRepresentative (g : Y → X → ℝ) (ε : ℝ) (f : RealSpace X) :
    RealSpace Y := by
  classical
  exact if h : ∃ lam ∈ l1Ball Y, UniformClose ε (columnCombination g lam) f then
    Classical.choose h else 0

end MetricEntropyDuality

end

end OAI


