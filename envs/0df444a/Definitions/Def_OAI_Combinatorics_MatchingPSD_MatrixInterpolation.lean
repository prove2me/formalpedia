-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation
-- name    : OAI_Combinatorics_MatchingPSD_MatrixInterpolation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:14:01.440771+00:00
-- url     : https://prove2.me/theorems/38b47da3-8f6d-4cb8-974c-5ea72a87bb57
-- title:
--   Five special points, their coefficients, scaled grid nodes and the total interpolation weight
-- statement:
--   This file names the five special points and coefficients of the interpolation identity, the scaled grid nodes, and the total mass of the interpolation weights.
--
--   **Setting.** Points are elements of $\mathbb{R}^3$, with base point and directions $o=(1,0,0)$, $a=(0,2,0)$, $b=(0,0,2)$, $\star=(2,0,0)$ and $p=(-1,1,1)$. For $d\in\mathbb{N}$ and a grid index $g=(g_0,g_1,g_2)\in\{0,\dots,d\}^3$, let $\ell_{d,k}\in\mathbb{R}[X]$ be the Lagrange basis polynomial for the nodes $0,1,\dots,d$ (so $\ell_{d,k}(j)=1$ if $j=k$ and $0$ otherwise), let $\pi_{d,g,v}(X)=\prod_{c=0}^{2}\ell_{d,g_c}(v_cX)$ for $v\in\mathbb{R}^3$, and let $w_{d,L}(g)=\omega_{d,g}(L^{-1})$ with $\omega_{d,g}=\pi_{d,g,a}+\pi_{d,g,b}-\pi_{d,g,\star}-2\pi_{d,g,p}+\pi_{d,g,0}$.
--
--   1. **Special points.**
--   $$
--   (z_0,z_1,z_2,z_3,z_4)=(o,\ o+p,\ o+\star,\ o+a,\ o+b)=\bigl((1,0,0),(0,1,1),(3,0,0),(1,2,0),(1,0,2)\bigr).
--   $$
--   2. **Special coefficients.** $(\beta_0,\dots,\beta_4)=(1,-2,-1,1,1)$, so that $\sum_j\beta_jP(z_j)=P(o)-2P(o+p)-P(o+\star)+P(o+a)+P(o+b)$.
--   3. **Scaled grid nodes.** For $L\in\mathbb{R}$ and $g\in\{0,\dots,d\}^3$, $o+Lg=(1+Lg_0,\ Lg_1,\ Lg_2)$.
--   4. **Weight mass.**
--   $$
--   \mathrm{mass}(d,L)=\sum_{g\in\{0,\dots,d\}^3}\bigl|w_{d,L}(g)\bigr|.
--   $$
--
--   Read as cross vectors $(e_{AB},e_{AC},e_{BC})$ of a matching of two odd blocks $A,B$ and an even block $C$, the special points are the configurations with one $A$–$B$ edge; one $A$–$C$ and one $B$–$C$ edge; three $A$–$B$ edges; one $A$–$B$ and two $A$–$C$ edges; one $A$–$B$ and two $B$–$C$ edges. The interpolation step compares a matrix-valued function at these five points with its values at the scaled grid nodes, and the error of the resulting matrix inequality is controlled by the weight mass.
--
--   **Formalization Note** The Lean names are `specialPoint : Fin 5 → Point`, `specialCoeff`, `scaledNode L g` and `weightMass d L`; the weights $w_{d,L}(g)$ are `weight d L g`. The section of matrix lemmas in the source contributes no definitions here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatrixInterpolation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatrixInterpolation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation

namespace OAI

universe u_1 u_2

namespace MatchingInterpolation
open MatchingSmoothing Matrix PerfectMatchingPSD
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

noncomputable def specialPoint : Fin 5 → Point :=
  ![origin, origin+dirP, origin+dirStar, origin+dirA, origin+dirB]
def specialCoeff : Fin 5 → ℝ := ![1,-2,-1,1,1]
noncomputable def scaledNode {d : ℕ} (L : ℝ) (g : GridIndex d) : Point :=
  fun a => origin a+L*(g a:ℝ)
noncomputable def weightMass (d : ℕ) (L : ℝ) : ℝ := ∑ g, |weight d L g|

section Matrices
variable {R : Type u_2} [Fintype R] [DecidableEq R]

end Matrices
end MatchingInterpolation

end OAI


