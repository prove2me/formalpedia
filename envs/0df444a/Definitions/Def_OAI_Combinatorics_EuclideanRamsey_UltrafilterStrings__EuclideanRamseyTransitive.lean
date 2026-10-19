-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyTransitive
-- name    : OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyTransitive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T04:16:44.832832+00:00
-- url     : https://prove2.me/theorems/e85b6605-7323-41a9-b8ad-71231b8ee37b
-- title:
--   Ultrafilter monoid, ultrafilter columns and weighted column paths over strings of points
-- statement:
--   Let $M$ be a monoid and let $\beta M$ be the set of ultrafilters on $M$, with the product
--   $$A\in U\cdot V\iff\bigl\{m\in M:\ \{m'\in M:\ mm'\in A\}\in V\bigr\}\in U\qquad(U,V\in\beta M,\ A\subseteq M).$$
--   Write $\delta_x$ for the principal ultrafilter at $x\in M$ (the ultrafilter of all sets containing $x$).
--
--   1. **Translation formulas.** For $x,y\in M$ and $U,V\in\beta M$: $\delta_x\cdot V$ is the image of $V$ under the left multiplication $m\mapsto xm$, and $U\cdot\delta_y$ is the image of $U$ under the right multiplication $m\mapsto my$.
--   2. **Ultrafilter monoid.** $\beta M$ with this (associative) product and the identity element $\delta_1$ is a monoid.
--   3. **Ultrafilter columns.** For an index set $\iota$ (here only the underlying set of $M$ matters), an *ultrafilter column* is either a *common* column $\mathrm{com}(U)$ given by one ultrafilter $U$ on $M$, or a *principal* column $\mathrm{pr}(x)$ given by a tuple $x=(x_i)_{i\in\iota}\in M^\iota$. Its value at $i\in\iota$ is the ultrafilter $U$ for $\mathrm{com}(U)$ and $\delta_{x_i}$ for $\mathrm{pr}(x)$.
--   4. **Realization.** A tuple $y\in M^\iota$ *realizes* $\mathrm{com}(U)$ if $y$ is constant (whatever $U$ is), and realizes $\mathrm{pr}(x)$ if $y=x$.
--   5. **Column paths.** Let $E$ be the real inner product space of finitely supported real sequences $x=(x_0,x_1,x_2,\dots)$ (all but finitely many $x_n$ vanish), with $\langle x,y\rangle=\sum_{n\ge 0}x_ny_n$ and $\|x\|=\langle x,x\rangle^{1/2}$; it contains an isometric copy of every Euclidean space $\mathbb{R}^d$. Let $\mathcal{S}$ be the free monoid of finite strings of points of $E$, fix a configuration $a=(a_i)_{i\in\iota}$ in $E$, and call a family $b=(b_i)_{i\in\iota}$ in $E$ a copy of $a$ of weight $u\in\mathbb{R}$ if $u\ge 0$ and $\|b_i-b_j\|^2=u\,\|a_i-a_j\|^2$ for all $i,j$. The relation $\mathrm{CP}_a(q,u)$ between finite lists $q$ of ultrafilter columns over $\mathcal{S}$ and weights $u\in\mathbb{R}$ is the smallest one such that the empty list has weight $0$; a single common column $[\mathrm{com}(U)]$ has weight $0$ for every ultrafilter $U$ on $\mathcal{S}$; for every copy $b$ of $a$ of weight $u$, the single principal column $[\mathrm{pr}((b_i)_{i\in\iota})]$ formed by the one-letter strings $b_i$ has weight $u$; and concatenating two lists adds their weights.
--
--   These objects connect weighted paths in the free group on the points of $E$ with actual strings of points. The free group is mapped into a group sitting inside $\beta\mathcal{S}$, each generator $z$ going to $p\cdot\delta_z\cdot p$ for a suitable idempotent $p$; expanding a weighted path through this map gives a column path whose coordinatewise products of column values are the images of the path. Choosing tuples of strings that realize all columns of a list (common columns by constant tuples) and multiplying them column by column then turns a column path of weight $u$ into a family of equal-length strings $(x_i)_{i\in\iota}$ whose pairwise energies $\sum_t\|x_{i,t}-x_{j,t}\|^2$ equal $u\,\|a_i-a_j\|^2$ (here $x_{i,t}$ is the $t$-th letter of $x_i$); and if $\iota$ is finite and, for each $i$, the product of the column values at $i$ contains a prescribed set of strings (for instance a colour class), the realizing tuples can be chosen so that each $x_i$ lies in that set.
--
--   **Formalization Note** The product on `Ultrafilter M` is Mathlib's `Ultrafilter.mul` with `Ultrafilter.semigroup`, used as local instances; `ultrafilterMonoid` is a definition (not a global instance), activated with `letI` where needed. The simp lemmas `pure_mul_ultra` and `mul_pure_ultra` are item 1. `UltraColumn ι M` has constructors `common` and `principal`, with `UltraColumn.value` and `UltraColumn.Realizes`. `ColumnPath a` is an inductive predicate on `List (UltraColumn ι Strings) → ℝ`, with `Strings = FreeMonoid FiniteEuclidean`, `FiniteEuclidean = ℕ →₀ ℝ`, and copies of weight $u$ expressed by `CopyPath a u b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyTransitive mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyTransitive

namespace OAI

universe uModule uIndex uAlpha

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

open Filter
namespace EuclideanRamsey
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

section Ultrafilters
variable {M : Type uModule} [Monoid M]
@[simp] lemma pure_mul_ultra (x : M) (V : Ultrafilter M) :
    (pure x : Ultrafilter M)*V = V.map (x*·) := by
  apply Ultrafilter.coe_inj.mp
  apply Filter.ext'
  intro p
  simp [Ultrafilter.eventually_mul]
@[simp] lemma mul_pure_ultra (U : Ultrafilter M) (y : M) :
    U*(pure y : Ultrafilter M) = U.map (·*y) := by
  apply Ultrafilter.coe_inj.mp
  apply Filter.ext'
  intro p
  simp [Ultrafilter.eventually_mul]

@[instance_reducible] def ultrafilterMonoid : Monoid (Ultrafilter M) where
  toSemigroup := Ultrafilter.semigroup
  one := pure 1
  one_mul U := by
    change (pure (1:M) : Ultrafilter M)*U=U
    rw [pure_mul_ultra]
    simp
  mul_one U := by
    change U*(pure (1:M) : Ultrafilter M)=U
    rw [mul_pure_ultra]
    simp

end Ultrafilters

inductive UltraColumn (ι : Type uIndex) (M : Type uModule)
  | common (U : Ultrafilter M)
  | principal (x : ι → M)

namespace UltraColumn
variable {ι : Type uIndex} {M : Type uModule}
def value : UltraColumn ι M → ι → Ultrafilter M
  | .common U,_ => U
  | .principal x,i => pure (x i)
def Realizes : UltraColumn ι M → (ι → M) → Prop
  | .common _,x => ∃ y,∀ i,x i=y
  | .principal y,x => x=y

end UltraColumn
end EuclideanRamsey
namespace EuclideanRamsey
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex}

inductive ColumnPath (a : ι → FiniteEuclidean) : List (UltraColumn ι Strings) → ℝ → Prop
  | nil : ColumnPath a [] 0
  | common (U : Ultrafilter Strings) : ColumnPath a [.common U] 0
  | copy {u : ℝ} (b : ι → FiniteEuclidean) (h : CopyPath a u b) :
      ColumnPath a [.principal (fun i => FreeMonoid.of (b i))] u
  | append {p q u v} : ColumnPath a p u → ColumnPath a q v → ColumnPath a (p++q) (u+v)

end EuclideanRamsey

end

end OAI


