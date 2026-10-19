-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_PolynomialInterpolation__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:53:03.553148+00:00
-- url     : https://prove2.me/theorems/99910589-c7d6-4dcc-b6ac-9805307c3d7d
-- title:
--   Tensor Lagrange weights for a second-difference identity in three variables
-- statement:
--   This file defines the interpolation data used to express a fixed second-order difference of a low-degree polynomial on $\mathbb{R}^3$ through its values on a scaled grid.
--
--   Points are elements $x=(x_0,x_1,x_2)$ of $\mathbb{R}^3$. For $d\in\mathbb{N}$, a grid index is $g=(g_0,g_1,g_2)\in\{0,\dots,d\}^3$.
--
--   1. **Coordinates.** $\operatorname{coord}_c(x)=x_c$ for $c\in\{0,1,2\}$. Products of at most $d$ coordinate functions span the polynomial functions of total degree at most $d$.
--   2. **Lagrange basis.** For $k\in\{0,\dots,d\}$,
--   $$
--   \ell_{d,k}(X)=\prod_{j\in\{0,\dots,d\},\ j\neq k}\frac{X-j}{k-j}\in\mathbb{R}[X],
--   $$
--   the Lagrange basis polynomial for the nodes $0,1,\dots,d$.
--   3. **Tensor basis and grid nodes.** $\Lambda_{d,g}(x)=\prod_{c=0}^{2}\ell_{d,g_c}(x_c)$, and the grid node of $g$ is the point $(g_0,g_1,g_2)\in\mathbb{R}^3$.
--   4. **Line polynomials.** For $v\in\mathbb{R}^3$, $\pi_{d,g,v}(X)=\prod_{c=0}^{2}\ell_{d,g_c}(v_cX)\in\mathbb{R}[X]$, so that $\pi_{d,g,v}(t)=\Lambda_{d,g}(tv)$ for $t\in\mathbb{R}$.
--   5. **Base point and directions.** $o=(1,0,0)$, $a=(0,2,0)$, $b=(0,0,2)$, $\star=(2,0,0)$ and $p=(-1,1,1)$.
--   6. **Weight polynomials and weights.** For $L\in\mathbb{R}$,
--   $$
--   \omega_{d,g}=\pi_{d,g,a}+\pi_{d,g,b}-\pi_{d,g,\star}-2\,\pi_{d,g,p}+\pi_{d,g,0}\in\mathbb{R}[X],\qquad w_{d,L}(g)=\omega_{d,g}\bigl(L^{-1}\bigr).
--   $$
--
--   The weights are designed for the identity
--   $$
--   P(o+a)+P(o+b)-P(o+\star)-2P(o+p)+P(o)=\sum_{g\in\{0,\dots,d\}^3}w_{d,L}(g)\,P(o+Lg),
--   $$
--   valid for every polynomial $P$ of total degree at most $d$ and every $L\neq0$; it comes from exact tensor interpolation of $y\mapsto P(o+Ly)$ on the grid, evaluated at $y=v/L$. Because $a+b-\star-2p=0$ and $1+1-1-2+1=0$, the constant and linear coefficients of $\omega_{d,g}$ cancel, which is reflected in a bound $|w_{d,L}(g)|\le c_d/L^2$ for $L\ge1$. The identity and this bound are proved in separate theorems. They allow a second difference of a function at five nearby points to be controlled by its values on a coarse grid of spacing $L$.
--
--   **Formalization Note** `Point` is `Fin 3 → ℝ` and `GridIndex d` is `Fin 3 → Fin (d+1)`; `lagrange d k` is Mathlib's `Lagrange.basis` on the nodes $0,\dots,d$, `tensorBasis`, `gridNode`, `linePolynomial`, `weightPolynomial` and `weight` are items 3, 4 and 6, and the special data are `origin`, `dirA`, `dirB`, `dirStar`, `dirP`. `weight d L g` evaluates at `L⁻¹`, so by Lean's convention $0^{-1}=0$ its value at $L=0$ is $\omega_{d,g}(0)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PolynomialInterpolation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PolynomialInterpolation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages__MatchingAffineLift

namespace OAI

namespace MatchingInterpolation
open Polynomial
open MatchingSmoothing

abbrev Point := Fin 3 → ℝ
abbrev GridIndex (d : ℕ) := Fin 3 → Fin (d+1)
def coord (i : Fin 3) (x : Point) : ℝ := x i
noncomputable def lagrange (d : ℕ) (k : Fin (d+1)) : ℝ[X] :=
  Lagrange.basis Finset.univ (fun j : Fin (d+1) => (j:ℝ)) k
noncomputable def tensorBasis (d : ℕ) (g : GridIndex d) (x : Point) : ℝ :=
  ∏ a, (lagrange d (g a)).eval (x a)
def gridNode {d : ℕ} (g : GridIndex d) : Point := fun a => (g a:ℝ)

noncomputable def linePolynomial (d : ℕ) (g : GridIndex d) (v : Point) : ℝ[X] :=
  ∏ a, (lagrange d (g a)).comp (Polynomial.C (v a) * Polynomial.X)

def origin : Point := ![1,0,0]
def dirA : Point := ![0,2,0]
def dirB : Point := ![0,0,2]
def dirStar : Point := ![2,0,0]
def dirP : Point := ![-1,1,1]
noncomputable def weightPolynomial (d : ℕ) (g : GridIndex d) : ℝ[X] :=
  linePolynomial d g dirA + linePolynomial d g dirB - linePolynomial d g dirStar -
    (2:ℝ) • linePolynomial d g dirP + linePolynomial d g 0

noncomputable def weight (d : ℕ) (L : ℝ) (g : GridIndex d) : ℝ :=
  (weightPolynomial d g).eval L⁻¹

end MatchingInterpolation

end OAI


