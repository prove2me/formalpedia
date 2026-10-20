-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
-- name    : OAI_Analysis_MetricEntropy_GreedyPivots
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:57:03.477797+00:00
-- url     : https://prove2.me/theorems/69133170-0df7-4e9d-8584-474b81f3ec24
-- title:
--   Greedy pivot selection by residual mass
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. Let $\mu\ge0$ be weights on a finite set $Y$, $I(x)\subseteq Y$ finite sets indexed by $x\in X$ (nonempty), and $\theta>0$.
--
--   1. **Mass.** $\mu(U)=\sum_{y\in U}\mu_y$.
--   2. **Pivot choice.** Given the current union $U$, choose $x$ with $\mu(I(x)\setminus U)>\theta$ if one exists. Otherwise choose a fixed padding element.
--   3. **Covered sets.** $U_0=\varnothing$ and
--   $$
--   U_{n+1}=U_n\cup I(x_n),
--   $$
--   where $x_n$ is the pivot chosen for $U_n$. If $\sum\mu\le1$, at most $1/\theta$ steps can have gain larger than $\theta$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/GreedyPivots.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/GreedyPivots.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uX uY

/-!
# A bounded greedy family of pivots

At each step, choose a set whose mass outside the current union exceeds the
threshold if such a set exists. Otherwise choose a fixed padding center.
Padding still enlarges the union, so it cannot increase any residual mass.
If the residual bound failed after `s` steps, all preceding steps would have
made a strict gain greater than the threshold, contradicting total mass at
most one and `1 ≤ s * θ`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

namespace GreedyPivots

variable {X : Type uX} {Y : Type uY}

/-- The mass of a finite set of columns. -/
def mass (μ : Y → ℝ) (U : Finset Y) : ℝ := ∑ y ∈ U, μ y

variable [Nonempty X] [DecidableEq Y]

/-- An active greedy pivot, or a fixed center when every residual is small. -/
def choosePivot (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (U : Finset Y) : X := by
  classical
  exact if h : ∃ x, θ < mass μ (I x \ U) then h.choose else Classical.choice inferInstance

/-- The union after exactly `n` selections, including any padding selections. -/
def covered (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) : ℕ → Finset Y
  | 0 => ∅
  | n + 1 => covered μ I θ n ∪ I (choosePivot μ I θ (covered μ I θ n))

@[simp] theorem covered_zero (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) :
    covered μ I θ 0 = ∅ := rfl

end GreedyPivots

end MetricEntropyDuality

end

end OAI


