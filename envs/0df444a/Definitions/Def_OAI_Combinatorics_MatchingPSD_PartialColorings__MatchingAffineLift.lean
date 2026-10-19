-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:28:13.834216+00:00
-- url     : https://prove2.me/theorems/8252f7c8-a797-4f2f-9bfa-52004e1161f1
-- title:
--   Color-pair edge counts of a matching and candidate edges outside a vertex set
-- statement:
--   Let $V$ be a finite vertex set, $C$ a set of colors and $z : V \to C$ a coloring. Perfect matchings of $V$ are encoded as pairings, permutations $M$ with $M(M(v)) = v$ and $M(v) \neq v$ for all $v$, whose edges are the sets $\{v, M(v)\}$. The module defines:
--
--   1. For an ordered pair of colors $c = (c_1, c_2)$, the **table coordinate**, the function of the matching
--   $$
--   y_{c}(M) = \bigl|\{ v \in V : z(v) = c_1 \text{ and } z(M(v)) = c_2 \}\bigr| ,
--   $$
--   the number of vertices of color $c_1$ whose partner has color $c_2$. For $c_1 \neq c_2$ this is the number of edges of $M$ joining the color classes of $c_1$ and $c_2$; for $c_1 = c_2$ it is twice the number of edges of $M$ inside the class of $c_1$.
--   2. For a finite set $U \subseteq V$ and $c = (c_1,c_2)$, the set of **candidate edges**
--   $$
--   \mathrm{Cand}_z(U, c) = \bigl\{ (a, b) \in V \times V : a \notin U,\ b \notin U,\ a \neq b,\ z(a) = c_1,\ z(b) = c_2 \bigr\},
--   $$
--   the ordered pairs of distinct vertices outside $U$ carrying the prescribed colors.
--
--   The table coordinates are invariant under relabelling by permutations that preserve the coloring. If $\ell$ is a list of edges contained in some matching and $U$ is the set of vertices occurring in $\ell$, then on the matchings containing $\ell$ the table coordinate $y_c$ equals a constant (the contribution of the vertices of $U$) plus the sum of the edge indicators of the candidate edges in $\mathrm{Cand}_z(U, c)$; moreover, all candidate edges $e \in \mathrm{Cand}_z(U, c)$ give the same average of the extended monomial $x_e\, x^{\ell}$ over the permutations preserving the coloring (here $x_e(M) = 1$ if $M$ contains the edge $e$ and $0$ otherwise, and $x^{\ell}$ is the product of the $x_e$ over $e$ in $\ell$). Together these facts drive the induction showing that color averages of low-degree polynomials in the edge indicators are low-degree polynomials in the table coordinates.
--
--   **Formalization Note** The definitions are `tableCoordinate z c`, a real-valued function on `Pairing V`, and `candidateEdges z U c`, a `Finset (V × V)` obtained by filtering `Finset.univ`; decidability is classical.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PartialColorings.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PartialColorings.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ColorCounting
variable {V : Type u_1} {C : Type u_2} [Fintype V]

noncomputable def tableCoordinate (z : V → C) (c : C × C) (M : Pairing V) : ℝ :=
  ∑ v, if z v = c.1 ∧ z (M.1 v) = c.2 then 1 else 0

noncomputable def candidateEdges (z : V → C) (U : Finset V) (c : C × C) : Finset (V × V) :=
  Finset.univ.filter fun e => e.1 ∉ U ∧ e.2 ∉ U ∧ e.1 ≠ e.2 ∧ z e.1 = c.1 ∧ z e.2 = c.2

end ColorCounting
end MatchingSmoothing

end OAI


