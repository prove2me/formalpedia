-- Prove2me | Definitions.Def_OAI_Analysis_MetricEntropy_Basic
-- name    : OAI_Analysis_MetricEntropy_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:37:28.087441+00:00
-- url     : https://prove2.me/theorems/1fc18158-8ba4-4159-ab82-c223e074407f
-- title:
--   Row hulls, column combinations and uniform approximation lists
-- statement:
--   These notions belong to a counterexample to the duality conjecture for metric entropy. For every $a,b\ge1$ there are $n$ and a symmetric convex body $K\subset\mathbb R^n$ with $\log N(K,Q_n)>b\log N(Q_n^\circ,a^{-1}K^\circ)$. Here $Q_n=[-1,1]^n$ is the cube, $K^\circ=\{y:\langle x,y\rangle\le1\text{ for all }x\in K\}$ is the polar (so $Q_n^\circ$ is the $\ell_1$ ball), and $N(A,B)$ is the least number of translates of $B$ covering $A$. The body comes from a real matrix $g(y,x)$ with columns $y\in Y$ and rows $x\in X$, namely $K=3\,\mathrm{conv}\{\pm g(\cdot,x)\}+t\,Q_Y$. Separated rows force $N(K,Q_Y)\ge|X|$. A short list of functions approximating all column combinations $\sum_y\lambda_yg(y,\cdot)$ with $\|\lambda\|_1\le1$ uniformly gives a small dual covering. For finite sets $X,Y$ and a matrix $g:Y\times X\to\mathbb R$:
--
--   1. **$\ell_1$ ball.** $\|\lambda\|_1=\sum_y|\lambda_y|$ and $B_1^Y=\{\lambda:\|\lambda\|_1\le1\}$.
--   2. **Rows and column combinations.** The row of $x$ is $g(\cdot,x)\in\mathbb R^Y$. For $\lambda\in\mathbb R^Y$ the column combination is $(g^\top\lambda)(x)=\sum_y\lambda_yg(y,x)$, a function on $X$.
--   3. **Uniform approximation.** $f$ and $f'$ are $\varepsilon$-close if $|f(x)-f'(x)|\le\varepsilon$ for all $x$. A finite list $A$ of functions on $X$ is an $\varepsilon$-approximation if every $g^\top\lambda$ with $\lambda\in B_1^Y$ is $\varepsilon$-close to some member of $A$. Members need not be column combinations.
--   4. **Bodies.** The absolute row hull is $\mathrm{conv}\{\pm g(\cdot,x):x\in X\}$, and the matrix body is
--   $$
--   K_{g,t}=3\,\mathrm{conv}\{\pm g(\cdot,x)\}+t\,[-1,1]^Y .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/Basic.lean by skeleton subtraction
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

namespace OAI

universe uι uX uY

/-!
# Literal finite-dimensional convex bodies and covering numbers

The coordinate space carries its ordinary finite product topology and sup norm.
Polar membership uses the actual real coordinate pairing. Covering centers are
unrestricted ambient vectors. `coveringNumber` is the least finite cover size;
the natural-number empty-infimum convention is zero when no finite cover exists.
The geometric applications prove `Coverable` before using attainment, positivity,
or a lower bound, so that convention never substitutes for a genuine minimum.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Pointwise

def l1Norm {ι : Type uι} [Fintype ι] (x : RealSpace ι) : ℝ :=
  ∑ i, |x i|

def l1Ball (ι : Type uι) [Fintype ι] : Set (RealSpace ι) :=
  {x | l1Norm x ≤ 1}

def row {X : Type uX} {Y : Type uY} (g : Y → X → ℝ) (x : X) : RealSpace Y :=
  fun y => g y x

def columnCombination {X : Type uX} {Y : Type uY} [Fintype Y]
    (g : Y → X → ℝ) (lam : RealSpace Y) : RealSpace X :=
  fun x => ∑ y, lam y * g y x

def UniformClose {X : Type uX} (ε : ℝ) (f h : RealSpace X) : Prop :=
  ∀ x, |f x - h x| ≤ ε

/-- The approximation list may contain functions outside the column hull. -/
def UniformApproximation {X : Type uX} {Y : Type uY} [Fintype Y]
    (g : Y → X → ℝ) (ε : ℝ) (A : Finset (RealSpace X)) : Prop :=
  ∀ lam ∈ l1Ball Y, ∃ a ∈ A, UniformClose ε (columnCombination g lam) a

def absRowHull {X : Type uX} {Y : Type uY} (g : Y → X → ℝ) : Set (RealSpace Y) :=
  convexHull ℝ (Set.range (row g) ∪ Set.range (fun x => -row g x))

def matrixBody {X : Type uX} {Y : Type uY} (g : Y → X → ℝ) (t : ℝ) : Set (RealSpace Y) :=
  (3 : ℝ) • absRowHull g + t • cube Y

section Elementary

variable {ι : Type uι} {X : Type uX} {Y : Type uY} [Fintype ι]

@[simp] theorem pairing_zero_left (y : RealSpace ι) : pairing 0 y = 0 := by
  simp [pairing]

@[simp] theorem pairing_zero_right (x : RealSpace ι) : pairing x 0 = 0 := by
  simp [pairing]

@[simp] theorem pairing_neg_left (x y : RealSpace ι) :
    pairing (-x) y = -pairing x y := by
  simp [pairing, Finset.sum_neg_distrib]

@[simp] theorem pairing_neg_right (x y : RealSpace ι) :
    pairing x (-y) = -pairing x y := by
  simp [pairing, Finset.sum_neg_distrib]

@[simp] theorem l1Norm_zero : l1Norm (0 : RealSpace ι) = 0 := by
  simp [l1Norm]

@[simp] theorem l1Norm_neg (x : RealSpace ι) : l1Norm (-x) = l1Norm x := by
  simp [l1Norm]

omit [Fintype ι] in
@[simp] theorem zero_mem_cube : (0 : RealSpace ι) ∈ cube ι := by
  simp [cube]

@[simp] theorem zero_mem_l1Ball : (0 : RealSpace ι) ∈ l1Ball ι := by
  simp [l1Ball]

@[simp] theorem columnCombination_zero [Fintype Y] (g : Y → X → ℝ) :
    columnCombination g 0 = 0 := by
  funext x
  simp [columnCombination]

end Elementary

end MetricEntropyDuality

end

end OAI


