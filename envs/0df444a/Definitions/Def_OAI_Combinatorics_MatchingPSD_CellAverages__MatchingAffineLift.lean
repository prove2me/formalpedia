-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:43:19.016757+00:00
-- url     : https://prove2.me/theorems/8ad402e4-5469-4556-9b83-387c1453f293
-- title:
--   Cell averages of functions of matchings over extensions with a prescribed cross vector
-- statement:
--   This file defines the two averaging operations that reduce a function of global matchings to a function of the three-dimensional cross vector of a local matching.
--
--   **Setting.** A *pairing* of a set $X$ is a permutation $M$ of $X$ with $M(M(a))=a$ and $M(a)\neq a$ for every $a\in X$, that is, a perfect matching of $X$ in which every $a$ is matched to its partner $M(a)$. Let $A,B,C,I$ be finite sets and $i\in I$. For a pairing $M$ of the local set $(A\sqcup B)\sqcup C$ and a family $N=(N_j)_{j\in I\setminus\{i\}}$ of pairings of $C$, $\operatorname{ext}_i(M,N)$ is the pairing of the global set $(A\sqcup B)\sqcup(I\times C)$ that matches $A\cup B\cup(\{i\}\times C)$ according to $M$ (with $C$ placed as the cell $\{i\}\times C$) and matches every other cell $\{j\}\times C$ internally by $N_j$. The *cross vector* of $M$ is
--   $$
--   x(M)=\bigl(e_{AB}(M),\ e_{AC}(M),\ e_{BC}(M)\bigr)\in\mathbb{R}^3,
--   $$
--   where $e_{XY}(M)$ is the number of vertices of $X$ whose partner lies in $Y$, i.e. the number of edges of $M$ between $X$ and $Y$. For a property $P$ of the elements of a finite set $X$ and $g:X\to\mathbb{R}$, the *predicate average* is $\operatorname{avg}_P\,g=|\{u\in X: P(u)\}|^{-1}\sum_{u:\,P(u)}g(u)$.
--
--   Let $f$ be a real-valued function on the pairings of $(A\sqcup B)\sqcup(I\times C)$.
--
--   1. **Extension average.** For a pairing $M$ of $(A\sqcup B)\sqcup C$,
--   $$
--   \bar f_i(M)=\mathbb{E}_{N}\,f\bigl(\operatorname{ext}_i(M,N)\bigr),
--   $$
--   the uniform average over all families $N=(N_j)_{j\in I\setminus\{i\}}$ of pairings of $C$.
--   2. **Cell average.** For $x\in\mathbb{R}^3$,
--   $$
--   \operatorname{cell}_i f(x)=\operatorname{avg}_{\{M:\ x(M)=x\}}\ \bar f_i,
--   $$
--   the uniform average of $\bar f_i$ over the pairings $M$ of $(A\sqcup B)\sqcup C$ with cross vector $x$.
--
--   Thus $\operatorname{cell}_i f(x)$ averages $f$ over all global matchings whose restriction to the two blocks and the cell $i$ is a local matching with cross vector $x$ and whose remaining cells are matched internally. These averages turn a function of global matchings into a function on the admissible cross vectors in $\mathbb{R}^3$, to which polynomial approximation and interpolation can then be applied.
--
--   **Formalization Note** `extensionAverage i f M` uses Mathlib's uniform expectation `𝔼` and `cellAverage i f x` uses `predicateAverage`; the extension is `extendLocal` and the cross vector is `crossVector threeColor`. With Lean's convention $0^{-1}=0$, an average over an empty set is $0$; for instance $\operatorname{cell}_i f(x)=0$ when no local pairing has cross vector $x$, and $\bar f_i=0$ when $C$ admits no pairing but $I\setminus\{i\}$ is nonempty. Finiteness of $A$ and $B$ is used only by the cell average.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/CellAverages.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/CellAverages.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable
section CellAverages
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} {I : Type u_4} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

noncomputable def extensionAverage (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ)
    (M : Pairing ((A ⊕ B) ⊕ C)) : ℝ :=
  𝔼 N : {j : I // j ≠ i} → Pairing C, f (extendLocal i M N)

noncomputable def cellAverage (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ)
    (x : Fin 3 → ℝ) : ℝ :=
  predicateAverage (fun M => crossVector threeColor M = x) (extensionAverage i f)

end CellAverages
end MatchingSmoothing

end OAI


