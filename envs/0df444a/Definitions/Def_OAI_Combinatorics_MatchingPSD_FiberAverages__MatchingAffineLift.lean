-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:21:43.640784+00:00
-- url     : https://prove2.me/theorems/7f42ceb3-e937-4ae7-9559-6eea29939b6d
-- title:
--   Average of a function over the fiber of a relation
-- statement:
--   Let $X$ and $Z$ be finite sets, $P$ a relation between them (written $P(x,z)$) and $f : X \to \mathbb{R}$. For $z \in Z$, the **fiber average** of $f$ at $z$ is the mean of $f$ over the fiber $P^{-1}(z) = \{x \in X : P(x,z)\}$:
--
--   $$
--   \bar f_P(z) = \frac{1}{|P^{-1}(z)|} \sum_{x \in X :\, P(x,z)} f(x).
--   $$
--
--   It is the conditional average of $f$ at $z$ (the sum of $f$ over the fiber divided by a normalizing constant) in which the normalization is the actual size of the fiber.
--
--   In the application $X$ is the set of perfect matchings of the $2h$-vertex set $\{0,\dots,h-1\} \times \{0,1\}$, $Z$ the set of 3-colorings with prescribed color counts, and $P(M, z)$ says that the color table of $M$ under $z$ equals a prescribed table; then $\bar f_P(z)$ is the average of $f$ over all matchings with that table. For $h \ge 1$ all these fibers have the same size, so the fiber average coincides with the normalized conditional average and inherits its spectral energy identity.
--
--   **Formalization Note** The definition is `fiberAverage P f z := conditionalAverage P (Fintype.card {x // P x z}) f z`, with decidability supplied classically. By Lean's convention $x / 0 = 0$, the fiber average is $0$ at every $z$ with an empty fiber.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/FiberAverages.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/FiberAverages.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix
attribute [local instance] Classical.propDecidable
section FiberAverages
variable {X : Type u_1} {Z : Type u_2} [Fintype X] [Fintype Z]

noncomputable def fiberAverage (P : X → Z → Prop) (f : X → ℝ) (z : Z) : ℝ :=
  conditionalAverage P (Fintype.card {x // P x z}) f z

end FiberAverages

section TableFibers
variable {H : Type u_3} [Fintype H] [DecidableEq H]

end TableFibers

open scoped RealInnerProductSpace
end MatchingSmoothing

end OAI


