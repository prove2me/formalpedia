-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_SignedCompression
-- name    : OAI_Analysis_MetricEntropy_SignedCompression
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T22:05:48.302671+00:00
-- url     : https://prove2.me/theorems/1d3dfaae-4642-49cc-8af1-6b0c4a2e8ef1
-- title:
--   From positive compression to the signed l1 ball
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. The body comes from a real matrix $g(y,x)$ with columns $y\in Y$ and rows $x\in X$, namely $K=3\,\mathrm{conv}\{\pm g(\cdot,x)\}+t\,Q_Y$. Separated rows force $N(K,Q_Y)\ge|X|$. A short list of functions approximating all column combinations $\sum_y\lambda_yg(y,\cdot)$ with $\|\lambda\|_1\le1$ uniformly gives a small dual covering.
--
--   1. **Positive and negative parts.** $\lambda^+_y=\max(\lambda_y,0)$ and $\lambda^-_y=\max(-\lambda_y,0)$, so $\lambda=\lambda^+-\lambda^-$.
--   2. **Difference list.** For a finite list $A$, $A-A=\{a-a':a,a'\in A\}$, which has at most $|A|^2$ members. A code is a pair $(a,a')$, decoded to $a-a'$.
--   3. **Positive approximation.** $A$ is a positive $\theta$-approximation for $g$ if every $\mu\ge0$ with $\sum_y\mu_y\le1$ has some $a\in A$ with
--   $$
--   \sup_x\Bigl|\sum_y\mu_yg(y,x)-a(x)\Bigr|\le3\theta .
--   $$
--   Then $A-A$ is a $6\theta$-approximation of the whole $\ell_1$ ball.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/SignedCompression.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/SignedCompression.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode
import Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionDecoder
import Definitions.Def_OAI_Analysis_MetricEntropy_GroupedWeights

namespace OAI

universe uX uY

/-!
# Signed compression and actual coefficient-ball clusters

A common finite approximation list for nonnegative combinations of mass at
most one gives a difference list for the literal `l1Ball`. A chosen pair of
positive approximants labels each actual coefficient vector; equal labels
give a uniform diameter bound. The list may have centers outside the column
hull, while the fibers consist of actual coefficient vectors.
-/

noncomputable section

namespace MetricEntropyDuality.SignedCompression

open scoped BigOperators

variable {X : Type uX} {Y : Type uY} [Fintype Y]

def positivePart (lam : RealSpace Y) : RealSpace Y := fun y => max (lam y) 0

def negativePart (lam : RealSpace Y) : RealSpace Y := fun y => max (-lam y) 0

/-- The literal difference list, including any duplicated outputs only once. -/
def differenceList (A : Finset (RealSpace X)) : Finset (RealSpace X) := by
  classical
  exact (A.product A).image (fun ab => ab.1 - ab.2)

/-- A pair of members of the positive approximation list. -/
abbrev Code (A : Finset (RealSpace X)) := {a // a ∈ A} × {a // a ∈ A}

def decode {A : Finset (RealSpace X)} (c : Code A) : RealSpace X :=
  c.1.val - c.2.val

variable (g : Y → X → ℝ) (θ : ℝ) (A : Finset (RealSpace X))

/-- The positive compression premise, stated on the actual coefficients. -/
def PositiveApproximation : Prop :=
  ∀ μ : RealSpace Y, (∀ y, 0 ≤ μ y) → (∑ y, μ y) ≤ 1 →
    ∃ a ∈ A, UniformClose (3 * θ) (columnCombination g μ) a

end MetricEntropyDuality.SignedCompression

end

end OAI


