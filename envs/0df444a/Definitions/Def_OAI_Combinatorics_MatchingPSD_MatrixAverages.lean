-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
-- name    : OAI_Combinatorics_MatchingPSD_MatrixAverages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:10:54.14685+00:00
-- url     : https://prove2.me/theorems/4c1311d6-2c9e-4612-b74a-9072ce38545f
-- title:
--   Matrix-valued extension and cell averages of a family of factor matrices
-- statement:
--   This file defines the matrix-valued versions of the extension and cell averages, applied to the family of matrices that a factorisation attaches to the matchings.
--
--   **Setting.** A *pairing* of a set $X$ is a permutation $M$ of $X$ with $M(M(a))=a$ and $M(a)\neq a$ for every $a\in X$, that is, a perfect matching of $X$ in which every $a$ is matched to its partner $M(a)$. Let $A,B,C,I$ be finite sets and $i\in I$. For a pairing $M$ of the local set $(A\sqcup B)\sqcup C$ and a family $N=(N_j)_{j\in I\setminus\{i\}}$ of pairings of $C$, $\operatorname{ext}_i(M,N)$ is the pairing of the global set $(A\sqcup B)\sqcup(I\times C)$ that matches $A\cup B\cup(\{i\}\times C)$ according to $M$ (with $C$ placed as the cell $\{i\}\times C$) and matches every other cell $\{j\}\times C$ internally by $N_j$. The *cross vector* of $M$ is
--   $$
--   x(M)=\bigl(e_{AB}(M),\ e_{AC}(M),\ e_{BC}(M)\bigr)\in\mathbb{R}^3,
--   $$
--   where $e_{XY}(M)$ is the number of vertices of $X$ whose partner lies in $Y$, i.e. the number of edges of $M$ between $X$ and $Y$.
--
--   Let $R$ be an index set and let $\mathcal B$ assign to every pairing of $(A\sqcup B)\sqcup(I\times C)$ a real $R\times R$ matrix.
--
--   1. **Extension matrix.** For a pairing $M$ of $(A\sqcup B)\sqcup C$,
--   $$
--   \bar{\mathcal B}_i(M)=\mathbb{E}_{N}\,\mathcal B\bigl(\operatorname{ext}_i(M,N)\bigr),
--   $$
--   the entrywise uniform average over all families $N=(N_j)_{j\in I\setminus\{i\}}$ of pairings of $C$.
--   2. **Cell matrix.** For $x\in\mathbb{R}^3$,
--   $$
--   \operatorname{cell}_i\mathcal B(x)=\mathbb{E}_{M:\ x(M)=x}\ \bar{\mathcal B}_i(M),
--   $$
--   the uniform average of $\bar{\mathcal B}_i$ over the pairings $M$ of $(A\sqcup B)\sqcup C$ with cross vector $x$.
--
--   Since averages of positive semidefinite matrices are positive semidefinite and traces are linear, the cell matrices of a family of PSD factors are again PSD, and their traces against a fixed matrix are the corresponding scalar cell averages. They are the matrix-valued functions of the cross vector that are approximated by low-degree polynomials and then controlled by interpolation in the lower-bound argument.
--
--   **Formalization Note** The Lean names are `extensionMatrix` and `cellMatrix`, both written with Mathlib's uniform expectation `𝔼` (the second over the subtype of pairings with `crossVector threeColor M = x`). With Lean's convention $0^{-1}=0$, an average over an empty set is the zero matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatrixAverages.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatrixAverages.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace PerfectMatchingPSD
open Matrix MatchingSmoothing
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable
variable {R : Type u_1} {X : Type u_2} [Fintype R] [DecidableEq R] [Fintype X]

section CellMatrices
variable {A : Type u_3} {B : Type u_4} {C : Type u_5} {I : Type u_6} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

noncomputable def extensionMatrix (i : I)
    (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (M : Pairing ((A ⊕ B) ⊕ C)) : Matrix R R ℝ :=
  𝔼 N : {j : I // j ≠ i} → Pairing C, Bf (extendLocal i M N)

noncomputable def cellMatrix (i : I)
    (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (x : Fin 3 → ℝ) : Matrix R R ℝ :=
  𝔼 M : {M : Pairing ((A ⊕ B) ⊕ C) // crossVector threeColor M = x}, extensionMatrix i Bf M.1

end CellMatrices
end PerfectMatchingPSD

end OAI


