-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
-- name    : OAI_Analysis_HyperbolicCones_ConeMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:55:36.932803+00:00
-- url     : https://prove2.me/theorems/610d43ce-ea70-469b-b433-ed95aba474bc
-- title:
--   The residual matrix $Z+tI-\varphi_y\bigl((X+tI)^{-1}\bigr)$
-- statement:
--   Let $\mathrm{Sym}_n$ be the real symmetric $n\times n$ matrices and $I$ the identity. For $y\in\mathbb{R}^3$ (indices $0,1,2$ read modulo $3$) let $Q(y)$ be the symmetric $3\times3$ matrix with $Q(y)_{ii}=y_i^2+y_{i+1}^2$ and $Q(y)_{ij}=-y_iy_j$ for $i\ne j$. For a $4\times4$ matrix $M$ with corner entry $\alpha=M_{00}$, remaining first row $b^{\mathsf T}=(M_{01},M_{02},M_{03})$, remaining first column $b'=(M_{10},M_{20},M_{30})^{\mathsf T}$ and lower-right $3\times3$ block $M'$, set
--   $$
--   \varphi_y(M)=\begin{pmatrix}\operatorname{tr}\bigl(Q(y)M'\bigr) & -b^{\mathsf T}Q(y)\\ -Q(y)\,b' & \alpha\,Q(y)\end{pmatrix}.
--   $$
--
--   The file defines three maps into symmetric matrices.
--
--   1. **Symmetric inverse.** For $X\in\mathrm{Sym}_n$, the inverse $X^{-1}$ as an element of $\mathrm{Sym}_n$, with the convention $X^{-1}=0$ when $X$ is singular.
--   2. **$\varphi_y$ on symmetric matrices.** For $y\in\mathbb{R}^3$ and $X\in\mathrm{Sym}_4$, the matrix $\varphi_y(X)\in\mathrm{Sym}_4$.
--   3. **Residual matrix.** For $X,Z\in\mathrm{Sym}_4$, $y\in\mathbb{R}^3$ and $t\in\mathbb{R}$,
--   $$
--   R_t(X,Z,y)=Z+tI-\varphi_y\bigl((X+tI)^{-1}\bigr)\in\mathrm{Sym}_4 .
--   $$
--
--   The main theorem concerns the polynomial $p(X,Z,y)=\det\bigl(\det(X)\,Z-\varphi_y(\operatorname{adj}X)\bigr)$, where $\operatorname{adj}$ is the adjugate. If $X+tI$ is invertible, then $\operatorname{adj}(X+tI)=\det(X+tI)\,(X+tI)^{-1}$, and $\varphi_y$ is linear. Hence
--   $$
--   p(X+tI,\,Z+tI,\,y)=\det(X+tI)^4\,\det R_t(X,Z,y).
--   $$
--   So the residual governs the zeros of $p$ along the line through $(X,Z,y)$ in the direction of the base point $(I,I,0)$. It is used to analyse the hyperbolicity cone on the slice where $X$ is positive definite, where membership is expressed through $R_0(X,Z,y)=Z-\varphi_y(X^{-1})$ being positive semidefinite.
--
--   **Formalization Note** The definitions are `symInverse`, `phiSym` and `coneResidual`. `symInverse` uses Lean's total matrix inverse, which is $0$ for singular matrices, so $R_t$ is defined for every $t$. The displayed identity is only meaningful where $X+tI$ is invertible.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/ConeMatrix.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/ConeMatrix.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

def symInverse {n : ℕ} (X : Sym n) : Sym n :=
  ⟨(X : Mat n ℝ)⁻¹, Matrix.IsHermitian.inv X.property⟩

def phiSym (y : Fin 3 → ℝ) (X : Sym 4) : Sym 4 :=
  ⟨phi y (X : Mat 4 ℝ), phi_isHermitian y _ X.property⟩

def coneResidual (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ) : Sym 4 :=
  Z + t • 1 - phiSym y (symInverse (X + t • 1))

end Paper256

end

end OAI


