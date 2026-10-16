-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
-- name    : OAI_Analysis_HyperbolicCones_MatrixBasic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:25:33.280863+00:00
-- url     : https://prove2.me/theorems/e112e973-6bbd-4213-98d8-be22180ce0f6
-- title:
--   Additivity and homogeneity of the matrix map $\varphi_y$
-- statement:
--   Let $R$ be a commutative ring and $y=(y_0,y_1,y_2)\in R^3$, with indices read modulo $3$. Let $Q(y)$ be the $3\times3$ matrix with $Q(y)_{ii}=y_i^2+y_{i+1}^2$ and $Q(y)_{ij}=-y_iy_j$ for $i\neq j$. For a $4\times4$ matrix $M$ over $R$ with indices $0,\dots,3$, write $\alpha=M_{00}$, $b^{\mathsf T}=(M_{01},M_{02},M_{03})$ for the rest of the first row, $b'=(M_{10},M_{20},M_{30})^{\mathsf T}$ for the rest of the first column, and $M'$ for the lower-right $3\times3$ block. Define
--
--   $$
--   \varphi_y(M)=\begin{pmatrix}\operatorname{tr}\bigl(Q(y)M'\bigr) & -b^{\mathsf T}Q(y)\\ -Q(y)\,b' & \alpha\,Q(y)\end{pmatrix}.
--   $$
--
--   The file records that $\varphi_y$ is linear in the matrix argument:
--
--   1. **Additivity.** For all $4\times4$ matrices $X,Z$ over $R$, $\varphi_y(X+Z)=\varphi_y(X)+\varphi_y(Z)$.
--   2. **Homogeneity.** For all $s\in R$ and all $4\times4$ matrices $X$ over $R$, $\varphi_y(sX)=s\,\varphi_y(X)$.
--
--   So for fixed $y$, the map $M\mapsto\varphi_y(M)$ is $R$-linear, and its entries are quadratic in $y$. The surrounding development studies the polynomial $p(X,Z,y)=\det\bigl(\det(X)\,Z-\varphi_y(\operatorname{adj}X)\bigr)$, where $\operatorname{adj}X$ is the adjugate. Linearity lets scalars be moved through $\varphi_y$. For instance, $\varphi_y(\operatorname{adj}X)=\det(X)\,\varphi_y(X^{-1})$ for invertible $X$, because $\operatorname{adj}X=\det(X)\,X^{-1}$. It is also the basis for treating $\varphi_y$ as a linear map in all later block-matrix manipulations.
--
--   **Formalization Note** The two identities are `phi_add` and `phi_smul`, stated for an arbitrary commutative ring. The file also contains `sym_isHermitian`, which says that an element of `Sym n` (the self-adjoint real $n\times n$ matrices) is a Hermitian, that is symmetric, matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/MatrixBasic.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/MatrixBasic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem sym_isHermitian {n : ℕ} (X : Sym n) : (X : Mat n ℝ).IsHermitian := X.property

theorem phi_add {R : Type u} [CommRing R] (y : Fin 3 → R) (X Z : Mat 4 R) :
    phi y (X + Z) = phi y X + phi y Z := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [phi, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
      Finset.sum_add_distrib, mul_add, add_mul, add_comm]

theorem phi_smul {R : Type u} [CommRing R] (y : Fin 3 → R) (s : R) (X : Mat 4 R) :
    phi y (s • X) = s • phi y X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [phi, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
      ← Finset.mul_sum, mul_left_comm, mul_assoc]

end Paper256

end

end OAI


