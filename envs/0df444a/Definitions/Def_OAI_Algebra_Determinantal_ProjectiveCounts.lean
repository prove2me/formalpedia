-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
-- name    : OAI_Algebra_Determinantal_ProjectiveCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:59:32.450636+00:00
-- url     : https://prove2.me/theorems/15c1923c-883e-45fa-bf6a-b5062d4f2355
-- title:
--   Vandermonde bilinear factor pairs and block-separated points in products of projective spaces
-- statement:
--   This module introduces the model bilinear equations and the separation condition used to count isolated solutions of multihomogeneous bilinear systems.
--
--   1. **Vandermonde factor pairs.** Fix a finite set $\iota$ of blocks and $a\in\mathbb N^{\iota}$, and work in $\mathbb C[x_{j,h}: j\in\iota,\ 0\le h\le a_j]$, where block $j$ consists of $x_{j,0},\dots,x_{j,a_j}$ and every variable of block $j$ has multidegree $\mathbf e_j\in\mathbb Z^{\iota}$. For $s\in\mathbb C$ put $\ell_j(s)=\sum_{h=0}^{a_j}s^{h}x_{j,h}$. Given $M\in\mathbb N$, block labels $u,v:\{0,\dots,M-1\}\to\iota$ and complex parameters $t_{i,0},t_{i,1}$ for $0\le i<M$, the $i$-th Vandermonde factor pair is
--   $$
--   \bigl(\ell_{u(i)}(t_{i,0}),\ \ell_{v(i)}(t_{i,1})\bigr),
--   $$
--   with recorded multidegrees $\mathbf e_{u(i)}$ and $\mathbf e_{v(i)}$. Their products $\ell_{u(i)}(t_{i,0})\,\ell_{v(i)}(t_{i,1})$ are model bilinear equations of multidegree $\mathbf e_{u(i)}+\mathbf e_{v(i)}$.
--
--   2. **Block-separated points.** Let $K$ be a field, $g:\sigma\to\iota$ an assignment of variables to blocks and $x,y\in K^{\sigma}$. Then $x$ and $y$ are block-separated if there are variables $v,w$ in the same block, $g(v)=g(w)$, with
--   $$
--   x_v\,y_w\ne x_w\,y_v .
--   $$
--   Equivalently, for some block $j$ the restrictions of $x$ and $y$ to the variables of block $j$ are linearly independent. In particular, when all block restrictions are nonzero, block-separated points represent distinct points of the product $\prod_{j}\mathbb P\bigl(K^{g^{-1}(j)}\bigr)$ of projective spaces.
--
--   Pairwise block-separated points whose designated base coordinates (one variable per block and per point) are nonzero can be interpolated by multihomogeneous polynomials of every multidegree whose entries are at least the number of points; hence the number of such common zeros of an ideal is at most the dimension of a graded piece of the quotient. Combined with the upper bound for quotients by products of Vandermonde forms, this shows that a system of $\sum_ja_j$ equations of multidegrees $\mathbf e_{u(i)}+\mathbf e_{v(i)}$ has at most as many pairwise block-separated simple zeros in affine charts as the coefficient of $X^{a}$ in $\prod_i\bigl(X_{u(i)}+X_{v(i)}\bigr)$.
--
--   **Formalization Note** `vandermondePairs a u v t` is a function on `Fin M` with values in `FactorPair` for the block weight on `BlockVariables a`, where `t : Fin M × Bool → ℂ` (`false` for the left factor, `true` for the right factor). `BlockSeparated group x y` is the existential statement displayed in item 2.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/ProjectiveCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/ProjectiveCounts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SmoothInitialForm mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearPointCount
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

noncomputable def vandermondePairs (a : ι →₀ ℕ) {M : ℕ}
    (u v : Fin M → ι) (t : (Fin M × Bool) → ℂ) :
    Fin M → FactorPair (K := ℂ) (blockWeight (fun v : BlockVariables a => v.1)) :=
  fun i => { left := blockLinearForm a (u i) (t (i,false))
             right := blockLinearForm a (v i) (t (i,true))
             leftDegree := Pi.single (u i) 1
             rightDegree := Pi.single (v i) 1
             left_homogeneous := blockLinearForm_homogeneous a (u i) (t (i,false))
             right_homogeneous := blockLinearForm_homogeneous a (v i) (t (i,true)) }

end BilinearPointCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProductAffineChart
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {L : Type*} [Fintype L] [DecidableEq L]

end ProductAffineChart
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectiveInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def BlockSeparated (group : σ → ι) (x y : σ → K) : Prop :=
  ∃ v w, group v = group w ∧ x v * y w ≠ x w * y v

variable [Fintype L] [DecidableEq L]

end ProjectiveInterpolation
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectivePointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

end ProjectivePointBound
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section MultiChartProductCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end MultiChartProductCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearMultiChartCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end BilinearMultiChartCount
end PermanentBorder.Multigraded

end OAI


