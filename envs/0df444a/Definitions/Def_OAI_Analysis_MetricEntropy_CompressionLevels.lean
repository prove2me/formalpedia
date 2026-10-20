-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
-- name    : OAI_Analysis_MetricEntropy_CompressionLevels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:57:56.375659+00:00
-- url     : https://prove2.me/theorems/5e837640-44ba-4fa7-a31a-66a0541391e2
-- title:
--   Ball indicators and pivot-assigned mixtures at one level
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. For a set $T$ of direction indices, two forms are adjacent in the partition graph when they have the same contraction along some $t_i$ with $i\in T$, and $d_T$ is the graph distance (infinite between components). The matrix column $(v,T)$ is $x\mapsto\varphi_h(d_T(x,v))$ with the logarithmic profile $\varphi_h(d)=\max\bigl(0,1-\log(d+1)/\log(h+1)\bigr)$ and $\varphi_h(\infty)=0$. Let $L_i$ be label maps on $X$. Columns $y$ have centres $v_y$, label sets $T_y$ and weights $\mu_y$. Pivot representatives $\mathrm{rep}_k$ and an optional assignment $y\mapsto k$ are given.
--
--   1. **Ball indicator.** $\mathbf 1_{T,j}(x,v)=1$ if $d_T(x,v)\le j$ and $0$ otherwise.
--   2. **Assigned indicator.** An unassigned column contributes $0$. A column assigned to $k$ contributes $\mathbf 1_{T_y,2j+1}(x,\mathrm{rep}_k)$.
--   3. **Level values.**
--   $$
--   \ell_j(x)=\sum_y\mu_y\mathbf 1_{T_y,j}(x,v_y),
--   $$
--   and the assigned value is $\sum_y\mu_y$ times the assigned indicator. The assigned value replaces the centres by few pivots.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/CompressionLevels.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/CompressionLevels.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uX uY uK uι uLabel

/-!
# Graph-ball comparison at one compression level

Columns omitted by the common index and retained columns left uncovered
each contribute at most `θ`. Assigned columns are compared using the actual
partition graph and replacement pivots with the same selected label.
Graph distances remain extended distances throughout.
-/

noncomputable section

namespace MetricEntropyDuality.CompressionLevels

open scoped BigOperators Classical

variable {X : Type uX} {Y : Type uY} {K : Type uK} {ι : Type uι} {Label : ι → Type uLabel}

/-- The real indicator of a finite-radius ball in the actual partition graph. -/
def ballIndicator (L : (i : ι) → X → Label i) (T : Finset ι) (j : ℕ)
    (x v : X) : ℝ := if PartitionGraph.near L T j x v then 1 else 0

/-- Unassigned columns contribute zero; assigned columns use replacement pivots. -/
def assignedIndicator (L : (i : ι) → X → Label i) (T : Y → Finset ι)
    (rep : K → X) (assignment : Y → Option K) (j : ℕ) (x : X) (y : Y) : ℝ :=
  match assignment y with
  | none => 0
  | some k => ballIndicator L (T y) (2 * j + 1) x (rep k)

section Weighted

variable [Fintype Y]

/-- The original mixture at one ball radius. -/
def levelValue (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (μ : Y → ℝ) (j : ℕ) (x : X) : ℝ :=
  ∑ y, μ y * ballIndicator L (T y) j x (v y)

/-- The assigned mixture after pivot replacement. -/
def assignedValue (L : (i : ι) → X → Label i) (T : Y → Finset ι)
    (rep : K → X) (assignment : Y → Option K) (μ : Y → ℝ) (j : ℕ) (x : X) : ℝ :=
  ∑ y, μ y * assignedIndicator L T rep assignment j x y

end Weighted

end MetricEntropyDuality.CompressionLevels

end

end OAI


