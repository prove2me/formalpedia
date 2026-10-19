-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:40:51.79518+00:00
-- url     : https://prove2.me/theorems/20eb4e28-42bb-4cc1-a7fe-3ee37fd15ab5
-- title:
--   The two-block, many-cell global vertex set and its cut colourings
-- statement:
--   This file fixes the global vertex set of the lower-bound construction and the two-colourings that describe its odd cuts.
--
--   1. **Global vertex set.** For $s,q\in\mathbb{N}$,
--   $$
--   \mathcal G_{s,q}=(A\sqcup B)\sqcup\bigl(\{0,\dots,q-1\}\times C\bigr),\qquad A=B=\{0,\dots,2s\},\quad C=\{0,\dots,s-1\}\times\{\mathrm{false},\mathrm{true}\}.
--   $$
--   It consists of two blocks $A$, $B$ of odd size $2s+1$ and $q$ cells $C_i=\{i\}\times C$ of even size $2s$, so it has $2s(q+2)+2$ vertices.
--   2. **Local cut colouring.** For a bit $b$, the map $\lambda_b:\{0,1,2\}\to\{\mathrm{false},\mathrm{true}\}$ is $\lambda_b(0)=\mathrm{true}$, $\lambda_b(1)=\mathrm{false}$, $\lambda_b(2)=b$.
--   3. **Global cut colouring.** For sets $A,B,C,I$ and $y:I\to\{\mathrm{false},\mathrm{true}\}$, the colouring $\gamma_y$ of $(A\sqcup B)\sqcup(I\times C)$ is $\mathrm{true}$ on $A$, $\mathrm{false}$ on $B$, and $y(i)$ on the cell $\{i\}\times C$.
--
--   Composed with the block colouring of a three-block set ($A\mapsto0$, $B\mapsto1$, third block $\mapsto2$), $\lambda_b$ selects the side $A$ (for $b=\mathrm{false}$) or $A\cup C$ (for $b=\mathrm{true}$) of a local cut. On $\mathcal G_{s,q}$, the true side of $\gamma_y$ is $U_y=A\cup\bigcup_{i:\,y(i)=\mathrm{true}}C_i$, which has odd size $2s+1+2s\cdot\#\{i: y(i)=\mathrm{true}\}$. So every bit string $y$ of length $q$ gives an odd cut, and for a perfect matching $M$ the number of true-coloured vertices whose partner is false-coloured is the number of edges of $M$ crossing $U_y$. These $2^q$ odd cuts are the rows of the slack matrix on which the lower-bound argument concentrates.
--
--   **Formalization Note** The Lean names are `GlobalVertices s q`, `localCutColor b` (the vector `![true,false,b]`) and `globalCutColor y`; colours are Lean `Bool`s. The parity and crossing-count facts in the last paragraph are proved in separate lemmas, not in this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/CutGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/CutGeometry.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev GlobalVertices (s q : ℕ) :=
  (Fin (2*s+1) ⊕ Fin (2*s+1)) ⊕ (Fin q × (Fin s × Bool))

def localCutColor (b : Bool) : Fin 3 → Bool := ![true,false,b]
def globalCutColor {A : Type u_1} {B : Type u_2} {C : Type u_3} {I : Type u_4} (y : I → Bool) : (A ⊕ B) ⊕ (I × C) → Bool :=
  Sum.elim (Sum.elim (fun _ => true) (fun _ => false)) (fun v => y v.1)

end MatchingSmoothing

end OAI


