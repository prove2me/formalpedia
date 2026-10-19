-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Quadratic
-- name    : OAI_Combinatorics_EuclideanRamsey_Quadratic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:01:52.270761+00:00
-- url     : https://prove2.me/theorems/5bdf79bc-e8c2-451f-a769-d9d57da87695
-- title:
--   Quadratic rows of a configuration
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it.
--
--   Let $K\subseteq\mathbb R$ be the field generated over $\mathbb Q$ by all coordinates $a_{ij}$ of a configuration $a_0,\dots,a_{s-1}\in\mathbb R^d$. For each point let $\tilde a_i:\{0,1,\dots,d\}\to K$ be its augmented vector, $\tilde a_i(0)=1$ and $\tilde a_i(j)=a_{ij}$. The quadratic rows are the vectors $\bigl(\tilde a_i(p)\,\tilde a_i(q)\bigr)_{p,q\in\{0,\dots,d\}}\in K^{(d+1)^2}$.
--
--   This module defines the index set $\{0,\dots,d\}\times\{0,\dots,d\}$ of quadratic monomials. It also defines the $s\times(d+1)^2$ matrix over $K$ whose $i$-th row is the quadratic row of $a_i$:
--   $$
--   R_{i,(p,q)}=\tilde a_i(p)\,\tilde a_i(q).
--   $$
--   If the rows of $R$ are linearly independent over $K$, a solution $h$ of $Rh=0$ with identity spatial block lifts to the field criterion. Spherical configurations provide such an $h$, so they are Ramsey under this independence condition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Quadratic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Quadratic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyQuadratic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyQuadratic

namespace OAI

/-! Quadratic row independence gives a tensor lift and the Ramsey property. -/

noncomputable section
open scoped TensorProduct BigOperators RealInnerProductSpace Matrix

namespace EuclideanRamsey.Quadratic

end EuclideanRamsey.Quadratic

namespace EuclideanRamsey

abbrev QuadraticIndex (d : ℕ) := Option (Fin d) × Option (Fin d)

def augmentedQuadraticRows {s d : ℕ} (a : Fin s → Space d) :
    Matrix (Fin s) (QuadraticIndex d) (Coeff a) :=
  fun i q => augmented a i q.1 * augmented a i q.2

end EuclideanRamsey

end

end OAI


