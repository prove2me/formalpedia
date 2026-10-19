-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:30:58.30409+00:00
-- url     : https://prove2.me/theorems/056d0292-5401-4400-bd9d-553fcc844c75
-- title:
--   Cross-color edge counts of a perfect matching under a 3-coloring
-- statement:
--   Let $V$ be a finite vertex set and $z : V \to \{0,1,2\}$ a 3-coloring. Perfect matchings of $V$ are encoded as pairings, permutations $M$ with $M(M(v)) = v$ and $M(v) \neq v$ for all $v$. For an ordered color pair $c = (c_1, c_2)$ the table coordinate is $y_c(M) = |\{v \in V : z(v) = c_1,\ z(M(v)) = c_2\}|$. The module defines:
--
--   1. The enumeration $\kappa$ of the three pairs of distinct colors: $\kappa(0) = (0,1)$, $\kappa(1) = (0,2)$, $\kappa(2) = (1,2)$.
--   2. The three **cross coordinates** $u_i = y_{\kappa(i)}$ for $i \in \{0,1,2\}$, that is,
--   $$
--   u_i(M) = \bigl|\{ v \in V : z(v) = a_i \text{ and } z(M(v)) = b_i \}\bigr|, \qquad (a_i, b_i) = \kappa(i).
--   $$
--
--   Since $a_i \neq b_i$, $u_i(M)$ is the number of edges of $M$ with one endpoint of color $a_i$ and the other of color $b_i$: $u_0, u_1, u_2$ count the edges between the color classes $0$ and $1$, $0$ and $2$, and $1$ and $2$, respectively.
--
--   Given the sizes of the color classes, the three cross counts determine all table coordinates: $y_{(a,b)} = y_{(b,a)}$, and $y_{(a,a)}$ equals the size of class $a$ minus the cross coordinates leaving class $a$. Hence every table coordinate is an affine function of $(u_0, u_1, u_2)$, the color average of a polynomial of degree at most $d$ in the edge indicators is a polynomial of degree at most $d$ in $u_0, u_1, u_2$, and on the paired vertex set $H \times \{0,1\}$ the cross coordinates coincide with the entries of the color table of $M$ (the numbers of edges of each unordered color-pair type) for the three non-monochromatic types $\{0,1\}, \{0,2\}, \{1,2\}$.
--
--   **Formalization Note** The definitions are `crossPair : Fin 3 → Fin 3 × Fin 3`, given as `![(0,1), (0,2), (1,2)]`, and `crossCoordinate z i := tableCoordinate z (crossPair i)`, a real-valued function on `Pairing V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TableCoordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TableCoordinates.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section TableCoordinates
variable {V : Type u_1} {C : Type u_2} [Fintype V]

end TableCoordinates

section ThreeCoordinates
variable {V : Type u_3} [Fintype V]

def crossPair : Fin 3 → Fin 3 × Fin 3 := ![(0,1), (0,2), (1,2)]
noncomputable def crossCoordinate (z : V → Fin 3) (i : Fin 3) : Pairing V → ℝ :=
  tableCoordinate z (crossPair i)

end ThreeCoordinates

section TableRelation
variable {H : Type u_4} [Fintype H]

end TableRelation
end MatchingSmoothing

end OAI


