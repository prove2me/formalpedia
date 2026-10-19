-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
-- name    : OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:39:03.950085+00:00
-- url     : https://prove2.me/theorems/8fa2af98-74ef-4165-9403-e99975543088
-- title:
--   Ultrafilter monoid, ultrafilter columns and weighted column paths over strings of points
-- statement:
--   Let $M$ be a monoid and $\beta M$ the set of ultrafilters on $M$, multiplied by the convolution product
--   $$A\in U\cdot V\iff\bigl\{m\in M:\ \{m'\in M:\ mm'\in A\}\in V\bigr\}\in U\qquad(U,V\in\beta M,\ A\subseteq M).$$
--   Write $\delta_x$ for the principal ultrafilter at $x\in M$.
--
--   1. **Translation formulas.** For $x,y\in M$ and $U,V\in\beta M$, $\delta_x\cdot V$ is the image of $V$ under left multiplication $m\mapsto xm$, and $U\cdot\delta_y$ is the image of $U$ under right multiplication $m\mapsto my$.
--   2. **Ultrafilter monoid.** $\beta M$ with the (associative) convolution product and identity $\delta_1$ is a monoid.
--   3. **Ultrafilter columns.** For an index set $\iota$, an *ultrafilter column* is either a *common* column $\mathrm{com}(U)$, given by one ultrafilter $U\in\beta M$, or a *principal* column $\mathrm{pr}(x)$, given by a tuple $x\in M^\iota$. Its value at $i\in\iota$ is $U$ for $\mathrm{com}(U)$ and $\delta_{x_i}$ for $\mathrm{pr}(x)$.
--   4. **Realization.** A tuple $y\in M^\iota$ *realizes* $\mathrm{com}(U)$ if $y$ is constant, and realizes $\mathrm{pr}(x)$ if $y=x$.
--   5. **Column paths.** Let $E_\infty$ denotes the real vector space of finitely supported real sequences $x=(x_0,x_1,x_2,\dots)$ with inner product $\langle x,y\rangle=\sum_n x_ny_n$ and norm $\|x\|=\langle x,x\rangle^{1/2}$, let $\mathcal S$ be the free monoid of finite strings of points of $E_\infty$, and fix a configuration $a=(a_i)_{i\in\iota}$ in $E_\infty$. A family $b$ is a copy of $a$ of weight $u$ if $u\ge 0$ and $\|b_i-b_j\|^2=u\|a_i-a_j\|^2$ for all $i,j$. The relation $\mathrm{CP}_a(q,u)$ between finite lists $q$ of ultrafilter columns over $\mathcal S$ and weights $u\in\mathbb{R}$ is the smallest one such that the empty list has weight $0$; a single common column $[\mathrm{com}(U)]$ has weight $0$; for every copy $b$ of weight $u$ the single principal column $[\mathrm{pr}((b_i)_i)]$ of one-letter strings has weight $u$; and concatenating two lists adds their weights.
--
--   The free group on the points of $E_\infty$ is mapped into a group sitting inside $\beta\mathcal S$, each generator $z$ going to $p\cdot\delta_z\cdot p$ for a suitable idempotent $p$. Expanding a weighted path through this map gives a column path whose coordinatewise products of column values are the images of the path, and realizing all columns at once by actual tuples of strings (common columns by constant tuples) turns a column path of weight $u$ into a string family of weight $u$. This is how finite colourings are transported between strings and ultrafilters.
--
--   **Formalization Note** The product on `Ultrafilter M` is Mathlib's `Ultrafilter.mul` with `Ultrafilter.semigroup`, used as local instances; `ultrafilterMonoid` is a definition, activated with `letI` where needed. `UltraColumn ι M` has constructors `common` and `principal`, with `UltraColumn.value` and `UltraColumn.Realizes`; for a common column, `Realizes` ignores the ultrafilter. `ColumnPath` is an inductive predicate on `List (UltraColumn ι Strings)` using `CopyPath` and `FreeMonoid.of`. The lemmas `pure_mul_ultra` and `mul_pure_ultra` are item 1.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamsey mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords

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


