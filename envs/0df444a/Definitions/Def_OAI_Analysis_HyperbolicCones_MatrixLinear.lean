-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
-- name    : OAI_Analysis_HyperbolicCones_MatrixLinear
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:27:15.389767+00:00
-- url     : https://prove2.me/theorems/7cb8155f-b8a2-4ce9-bf67-573424139ac5
-- title:
--   The map $\varphi_y$ as a linear map that preserves symmetric matrices
-- statement:
--   Let $R$ be a commutative ring and $y\in R^3$, with indices $0,1,2$ read modulo $3$. Let $Q(y)$ be the $3\times3$ matrix with $Q(y)_{ii}=y_i^2+y_{i+1}^2$ and $Q(y)_{ij}=-y_iy_j$ for $i\neq j$. For a $4\times4$ matrix $M$ with corner entry $\alpha=M_{00}$, remaining first row $b^{\mathsf T}=(M_{01},M_{02},M_{03})$, remaining first column $b'=(M_{10},M_{20},M_{30})^{\mathsf T}$ and lower-right $3\times3$ block $M'$, set
--
--   $$
--   \varphi_y(M)=\begin{pmatrix}\operatorname{tr}\bigl(Q(y)M'\bigr) & -b^{\mathsf T}Q(y)\\ -Q(y)\,b' & \alpha\,Q(y)\end{pmatrix}.
--   $$
--
--   The file contains two items.
--
--   1. **$\varphi_y$ as a linear map.** The map $M\mapsto\varphi_y(M)$, packaged as an $R$-linear map from $4\times4$ matrices over $R$ to $4\times4$ matrices over $R$. Its additivity and homogeneity are the two linearity identities for $\varphi_y$.
--   2. **Symmetry is preserved.** For real $y\in\mathbb{R}^3$ and every real symmetric $4\times4$ matrix $X$, the matrix $\varphi_y(X)$ is symmetric:
--   $$
--   X^{\mathsf T}=X\implies\varphi_y(X)^{\mathsf T}=\varphi_y(X).
--   $$
--
--   Together these show that, over the reals, $\varphi_y$ restricts to a linear map from symmetric $4\times4$ matrices to symmetric $4\times4$ matrices. This is what allows conditions such as $Z-\varphi_y(X^{-1})\succeq0$ (positive semidefiniteness), for symmetric $Z$ and symmetric invertible $X$, to be stated within the space of symmetric matrices. It also allows $\varphi_y$ to be composed with other linear maps of symmetric matrices.
--
--   **Formalization Note** The linear map is `phiLinear y`, built from `phi_add` and `phi_smul`. Symmetry is stated as `IsHermitian` (`phi_isHermitian`); for real matrices the conjugate transpose is the transpose.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/MatrixLinear.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/MatrixLinear.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder
open Matrix

universe u

namespace Paper256

def phiLinear {R : Type u} [CommRing R] (y : Fin 3 → R) : Mat 4 R →ₗ[R] Mat 4 R where
  toFun := phi y
  map_add' := phi_add y
  map_smul' := phi_smul y

theorem phi_isHermitian (y : Fin 3 → ℝ) (X : Mat 4 ℝ) (hX : X.IsHermitian) :
    (phi y X).IsHermitian := by
  have hQ (i j : Fin 3) : qMatrix y j i = qMatrix y i j := by
    by_cases h : i = j
    · subst j; rfl
    · simp [qMatrix, h, Ne.symm h, mul_comm]
  have hXs (i j : Fin 4) : X j i = X i j := by simpa using hX.apply i j
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · simp only [phi, Fin.cases_zero, Fin.cases_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hQ, hXs 0 k.succ]
    ring
  · simp only [phi, Fin.cases_zero, Fin.cases_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hQ, hXs 0 k.succ]
    ring
  · simp only [phi, Fin.cases_succ]
    rw [hQ]

end Paper256

end

end OAI


