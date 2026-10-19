-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:31:44.021564+00:00
-- url     : https://prove2.me/theorems/a205db19-2477-4abb-b152-b87b729a8830
-- title:
--   Average of a function over the elements satisfying a predicate
-- statement:
--   Let $X$ be a finite set and $P$ a predicate on $X$ with satisfying set $X_P = \{x \in X : P(x)\}$. The module defines the **predicate average**, the linear functional on $\mathbb{R}^X$ given by
--
--   $$
--   \mathbb{E}_P[f] = \frac{1}{|X_P|} \sum_{x \in X_P} f(x) \qquad (f : X \to \mathbb{R}),
--   $$
--
--   the mean of $f$ over the elements satisfying $P$, i.e. the conditional expectation of $f(x)$ given $P(x)$ for a uniformly random $x \in X$. If $P$ holds for at least one element and $f$ takes the constant value $c$ on $X_P$, then $\mathbb{E}_P[f] = c$.
--
--   Applied with $X$ the perfect matchings of a paired vertex set and $P(M)$ the statement that $M$ has a prescribed color table under a fixed 3-coloring, $\mathbb{E}_P[f]$ is the average of $f$ over a table class. For $f$ a polynomial of degree at most $d$ in the edge indicators, these class averages are given, for every table that actually occurs, by one polynomial of degree at most $d$ evaluated at the three cross-color edge counts of the table.
--
--   **Formalization Note** The definition is `predicateAverage P := (Fintype.card {x // P x})⁻¹ • ∑ x, if P x then LinearMap.proj x else 0`, a linear map `(X → ℝ) →ₗ[ℝ] ℝ`, with classical decidability. Because Lean sets $0^{-1} = 0$, the predicate average is the zero functional when no element satisfies $P$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TablePolynomials.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TablePolynomials.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section PredicateAverage
variable {X : Type u_1} [Fintype X]

noncomputable def predicateAverage (P : X → Prop) : (X → ℝ) →ₗ[ℝ] ℝ :=
  (Fintype.card {x // P x} : ℝ)⁻¹ •
    ∑ x, if P x then LinearMap.proj x else 0

end PredicateAverage
end MatchingSmoothing

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ReynoldsAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

end ReynoldsAverage

section TablePolynomial
variable {H : Type u_4} [Fintype H] [DecidableEq H]

end TablePolynomial
end MatchingSmoothing

end OAI


