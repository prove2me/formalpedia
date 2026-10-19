-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:24:26.445451+00:00
-- url     : https://prove2.me/theorems/1037e264-0afc-48ac-b2df-413e5b6a25bc
-- title:
--   Orthogonal projection onto low-degree polynomials in the edge indicators of a perfect matching
-- statement:
--   Fix $h, d \in \mathbb{N}$ and let $V_h = \{0,\dots,h-1\} \times \{0,1\}$, a set of $2h$ vertices. Let $\mathcal{M}_h$ be the set of perfect matchings of $V_h$, encoded as permutations $M$ with $M(M(v)) = v$ and $M(v) \neq v$ for all $v$, and let $\mathcal{H}_h = \ell^2(\mathcal{M}_h)$ be the Euclidean space of real functions on $\mathcal{M}_h$ with $\langle f, g\rangle = \sum_{M} f(M) g(M)$. Let $\mathcal{P}_{h,d} \subseteq \mathcal{H}_h$ be the span of all products of at most $d$ edge indicators $x_{(a,b)}(M)$, where $x_{(a,b)}(M) = 1$ if $M(a) = b$ and $0$ otherwise. The module defines the **polynomial projection**
--
--   $$
--   \Pi_{h,d} f = \operatorname{proj}_{\mathcal{P}_{h,d}} f \qquad (f \in \mathcal{H}_h),
--   $$
--
--   the orthogonal projection of $f$ onto $\mathcal{P}_{h,d}$, i.e. the best approximation of $f$ in $\ell^2(\mathcal{M}_h)$ by a polynomial of degree at most $d$ in the edge indicators.
--
--   The residual $f - \Pi_{h,d} f$ is the high-degree part of $f$: it is orthogonal to $\mathcal{P}_{h,d}$ and its norm is at most $\|f\|$. The table smoothing estimate is formulated with this projection: for every $K \in \mathbb{N}$ there are $d \ge 1$ and $h_0$ such that for all $h \ge h_0$, every reference coloring $f_0 : V_h \to \{0,1,2\}$ using all three colors and every $f \in \mathcal{H}_h$, the mean square, over the colorings $z$ with the same color counts as $f_0$, of the average of $f - \Pi_{h,d} f$ over the matchings whose color table under $z$ equals the table of $f_0$, is at most $(2h)^{-2K}$ times the mean square of $f$ over $\mathcal{M}_h$.
--
--   **Formalization Note** The definition is `polynomialProjection h d f := (polynomialSpace h d).starProjection f` on `MatchingSpace h`, where `starProjection` is the orthogonal projection viewed as an endomorphism of the ambient space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/ScalarSmoothing.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/ScalarSmoothing.lean by skeleton subtraction
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

namespace OAI

namespace MatchingSmoothing
open Filter Asymptotics

noncomputable def polynomialProjection (h d : ℕ) (f : MatchingSpace h) : MatchingSpace h :=
  (polynomialSpace h d).starProjection f

end MatchingSmoothing

end OAI


