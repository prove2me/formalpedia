-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
-- name    : OAI_Combinatorics_MatchingPSD_SequentialTests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:05:52.784055+00:00
-- url     : https://prove2.me/theorems/92ca63a2-977d-4a54-87a2-cfe891047c9f
-- title:
--   Ordered products of two-outcome test matrices along a bit string
-- statement:
--   This file defines the ordered product of a sequence of matrices selected by a bit string.
--
--   Let $R$ be a finite index set and $q\in\mathbb{N}$. Suppose that for every $i\in\{0,\dots,q-1\}$ and every bit $b\in\{\mathrm{false},\mathrm{true}\}$ a real $R\times R$ matrix $F_i(b)$ is given. For a bit string $y=(y_0,\dots,y_{q-1})$ the *sequential product* is
--   $$
--   S_F(y)=F_0(y_0)\,F_1(y_1)\cdots F_{q-1}(y_{q-1})\in\mathbb{R}^{R\times R},
--   $$
--   with $S_F(y)=I$, the identity matrix, when $q=0$. Equivalently $S_F(y)=F_0(y_0)\,S_{F'}(y')$, where $F'$ and $y'$ are obtained by deleting the index $0$ and shifting the remaining indices down by one.
--
--   In the decoding step of the lower bound, $F_i(\mathrm{false})$ and $F_i(\mathrm{true})$ are the two outcomes of a binary test for the $i$-th bit, i.e. positive semidefinite matrices with $F_i(\mathrm{false})+F_i(\mathrm{true})\le I$. The product $S_F(y)$ models running the $q$ tests one after the other and reading the answer $y$. Separate lemmas show that $\sum_y S_F(y)^{\mathsf T}S_F(y)\le I$ and that $S_F(y)$ is close to the identity on states that pass every test with high probability; together these force $|R|\ge 2^q/2$.
--
--   **Formalization Note** The product is `sequentialProduct`, defined by recursion on $q$ using `Fin.tail`; bits are Lean `Bool`s and the matrices are `Matrix R R ℝ` with `R` a `Fintype` with decidable equality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/SequentialTests.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/SequentialTests.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

def sequentialProduct : {q : ℕ} → (Fin q → Bool → Matrix R R ℝ) →
    (Fin q → Bool) → Matrix R R ℝ
  | 0, _, _ => 1
  | _+1, F, y => F 0 (y 0) * sequentialProduct (Fin.tail F) (Fin.tail y)

end PerfectMatchingPSD

end OAI


