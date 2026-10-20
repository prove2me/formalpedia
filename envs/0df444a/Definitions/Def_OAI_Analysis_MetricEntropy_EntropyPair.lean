-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
-- name    : OAI_Analysis_MetricEntropy_EntropyPair
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:38:12.06275+00:00
-- url     : https://prove2.me/theorems/618fefed-2305-4161-b540-746ecdde2032
-- title:
--   Entropy ratio and the record of a constructed counterexample body
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. Let $R=h(a)$ and $s=s(\theta(a))$ be the compression radius and pivot slots fixed by $a$.
--
--   1. **Entropy ratio.** For a body $K\subset\mathbb R^n$,
--   $$
--   \rho_a(K)=\frac{\log N(Q_n^\circ,a^{-1}K^\circ)}{\log N(K,Q_n)} .
--   $$
--   2. **Entropy budget.** $\beta(a,r,B)=\dfrac{2R^2s}{r+R-1}+\dfrac2B$.
--   3. **Entropy pair.** An entropy pair for $(a,r,B)$ consists of a dimension $n\ge\max(1,r)$ and a symmetric convex body $K\subset\mathbb R^n$ such that both covering problems have finite covers. It also requires $N(K,Q_n)>1$, $N(Q_n^\circ,a^{-1}K^\circ)\ge1$, $\log N(K,Q_n)>0$ and $0\le\rho_a(K)<\beta(a,r,B)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/EntropyPair.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/EntropyPair.lean by skeleton subtraction
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

namespace OAI

universe uι

/-!
# The output of the concrete counterexample construction

Every field below concerns the actual finite-dimensional body, its literal
cube and polar, or their covering numbers. The construction theorem supplies
this record from only the numerical inputs `a`, `r`, and `B`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped Pointwise

/-- The actual quotient of dual covering entropy by primal covering entropy. -/
def entropyRatio {ι : Type uι} [Fintype ι] (a : ℝ)
    (K : Set (RealSpace ι)) : ℝ :=
  Real.log (coveringNumber (polar (cube ι)) (a⁻¹ • polar K) : ℝ) /
    Real.log (coveringNumber K (cube ι) : ℝ)

/-- The scalar upper bound, with radius and pivot count fixed by `a` alone. -/
def entropyBudget (a : ℝ) (r : ℕ) (B : ℝ) : ℝ :=
  2 * (compressionRadius a : ℝ) ^ 2 * (pivotSlots (accuracy a) : ℝ) /
    ((r : ℝ) + (compressionRadius a : ℝ) - 1) + 2 / B

/-- A constructed body with its actual geometric and entropy properties.
No matrix, compression theorem, or abstract entropy function is a field. -/
structure EntropyPair (a : ℝ) (r : ℕ) (B : ℝ) where
  dimension : ℕ
  dimension_pos : 0 < dimension
  rank_le_dimension : r ≤ dimension
  body : Set (RealSpace (Fin dimension))
  body_isSymmetricConvexBody : IsSymmetricConvexBody body
  cube_isSymmetricConvexBody : IsSymmetricConvexBody (cube (Fin dimension))
  primal_coverable : Coverable body (cube (Fin dimension))
  dual_coverable : Coverable (polar (cube (Fin dimension))) (a⁻¹ • polar body)
  primal_one_lt : 1 < coveringNumber body (cube (Fin dimension))
  dual_pos : 0 < coveringNumber (polar (cube (Fin dimension))) (a⁻¹ • polar body)
  primal_log_pos : 0 < Real.log (coveringNumber body (cube (Fin dimension)) : ℝ)
  ratio_nonneg : 0 ≤ entropyRatio a body
  ratio_lt : entropyRatio a body < entropyBudget a r B

end MetricEntropyDuality

end

end OAI


