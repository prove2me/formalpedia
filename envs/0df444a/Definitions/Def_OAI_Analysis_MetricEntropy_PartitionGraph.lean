-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
-- name    : OAI_Analysis_MetricEntropy_PartitionGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:48:59.425881+00:00
-- url     : https://prove2.me/theorems/179a6d51-daa4-4a04-8e0e-3ba1c94e27f5
-- title:
--   Partition graphs defined by agreeing labels
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. Let $L_i:X\to\Lambda_i$ be label maps indexed by $i\in\iota$, and $T\subseteq\iota$ a finite set.
--
--   1. **Graph.** Distinct $x,y\in X$ are adjacent when $L_i(x)=L_i(y)$ for some $i\in T$.
--   2. **Distance.** $d_T(x,y)\in\mathbb N\cup\{\infty\}$ is the extended graph distance. It is $\infty$ between different components, and $d_T(x,y)=0$ iff $x=y$.
--   3. **Balls.** $y$ is $k$-near $x$ if
--   $$
--   d_T(x,y)\le k .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/PartitionGraph.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/PartitionGraph.lean by skeleton subtraction
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

namespace OAI

universe uX uι uLabel

/-!
# Partition graphs and their extended distances

An edge records equality of one selected label. Distances take values in `ℕ∞`,
so vertices in different connected components have infinite distance. The
pivot comparison and finite-walk characterization control the paths
between vertices with common labels.
-/

noncomputable section

namespace MetricEntropyDuality.PartitionGraph

variable {X : Type uX} {ι : Type uι} {Label : ι → Type uLabel}
variable (L : (i : ι) → X → Label i) (T : Finset ι)

/-- Distinct vertices are adjacent when a selected label agrees. -/
def graph : SimpleGraph X where
  Adj x y := x ≠ y ∧ ∃ i ∈ T, L i x = L i y
  symm := by
    constructor
    rintro x y ⟨hxy, i, hi, heq⟩
    exact ⟨hxy.symm, i, hi, heq.symm⟩
  loopless := by
    constructor
    intro x hx
    exact hx.1 rfl

@[simp] theorem adj_iff {x y : X} :
    (graph L T).Adj x y ↔ x ≠ y ∧ ∃ i ∈ T, L i x = L i y := Iff.rfl

/-- The genuine extended shortest-path distance, including infinity. -/
def distance (x y : X) : ℕ∞ := (graph L T).edist x y

/-- Membership in a closed graph ball of finite natural radius. -/
def near (k : ℕ) (x y : X) : Prop := distance L T x y ≤ (k : ℕ∞)

@[simp] theorem distance_self (x : X) : distance L T x x = 0 :=
  SimpleGraph.edist_self

@[simp] theorem distance_eq_zero_iff {x y : X} :
    distance L T x y = 0 ↔ x = y := SimpleGraph.edist_eq_zero_iff

@[simp] theorem near_zero_iff {x y : X} : near L T 0 x y ↔ x = y := by
  simp [near]

@[simp] theorem near_self (k : ℕ) (x : X) : near L T k x x := by
  simp [near]

end MetricEntropyDuality.PartitionGraph

end

end OAI


