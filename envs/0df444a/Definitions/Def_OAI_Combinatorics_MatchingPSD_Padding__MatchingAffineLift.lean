-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_Padding__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:06:40.593984+00:00
-- url     : https://prove2.me/theorems/b613ac92-0163-4f46-8744-9b08dd6856c9
-- title:
--   Odd cuts from two-colourings with an odd number of marked vertices
-- statement:
--   This file turns a two-colouring of a finite set, identified with $\{0,\dots,n-1\}$, into an odd-cut row of the perfect-matching slack matrix.
--
--   **Odd cuts.** An *odd cut* of $\{0,\dots,n-1\}$ is a subset $U\subseteq\{0,\dots,n-1\}$ with $|U|$ odd. In the slack matrix of the perfect matching problem, the row of $U$ evaluated at a perfect matching is the number of matching edges with exactly one endpoint in $U$, minus one.
--
--   **Colour cut.** Let $V$ be a finite set, $e:V\to\{0,\dots,n-1\}$ a bijection and $z:V\to\{\mathrm{false},\mathrm{true}\}$ a colouring such that $|\{v\in V: z(v)=\mathrm{true}\}|$ is odd. The colour cut is
--   $$
--   U(e,z)=\{u\in\{0,\dots,n-1\}:\ z(e^{-1}(u))=\mathrm{true}\}=e\bigl(z^{-1}(\mathrm{true})\bigr),
--   $$
--   an odd cut, since $e$ preserves cardinalities.
--
--   In the lower-bound argument $V$ is the global vertex set of the construction together with extra padding vertices (coloured false and matched among themselves), $z$ is one of its cut colourings, and $e$ identifies $V$ with the vertex set of $K_n$. The slack of the row $U(e,z)$ at the perfect matching obtained from a pairing $M$ of $V$ by transport along $e$ is the number of true-coloured vertices whose partner is false-coloured, minus one; this is how the abstract cut colourings become genuine rows of the slack matrix.
--
--   **Formalization Note** The Lean name is `colorCut e z hz`, where `hz` is the oddness hypothesis; `OddCut n` is the subtype of `Finset (Fin n)` of odd cardinality, and the oddness of the image is obtained by transporting cardinalities along `e`. The slack formula of the last paragraph is a separate lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Padding.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Padding.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AffineSlacks
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion__MatchingAffineLift

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PerfectMatchingPSD
open MatchingSmoothing Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def colorCut {n : ℕ} {V : Type u_1} [Fintype V]
    (e : V ≃ Fin n) (z : V → Bool) (hz : Odd (Fintype.card {v // z v = true})) : OddCut n := by
  classical
  refine ⟨Finset.univ.filter (fun v => z (e.symm v) = true), ?_⟩
  have he := Fintype.card_congr (Equiv.subtypeEquivOfSubtype' (p := fun v => z v = true) e)
  have ho : Odd (Fintype.card {v : Fin n // z (e.symm v) = true}) := by
    rw [← he]
    exact hz
  simpa only [Fintype.card_subtype] using ho

end PerfectMatchingPSD

end OAI


