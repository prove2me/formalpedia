-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:03:08.227261+00:00
-- url     : https://prove2.me/theorems/90a694e6-5227-486f-a3fd-027a88aa1a36
-- title:
--   Vertex set of $h$ standard pairs, its initial blocks and the pair transpositions
-- statement:
--   Fix $h \in \mathbb{N}$. The module defines the following objects.
--
--   1. The **vertex set** used for perfect matchings on $2h$ points,
--   $$
--   V_h = \{0, 1, \dots, h-1\} \times \{0, 1\},
--   $$
--   whose elements $(i, 0)$ and $(i, 1)$ form the $i$-th **standard pair**.
--   2. For $t \in \mathbb{N}$, the **initial block** $F_t = \{(i, b) \in V_h : i < t\}$, the vertices of the first $t$ standard pairs. A vertex $(i, b)$ lies in $F_t$ if and only if $i < t$; thus $|F_t| = 2t$ when $t \le h$, and $F_t = V_h$ when $t \ge h$.
--   3. For $i \in \{0, \dots, h-1\}$, the **pair transposition** $s_i$, the permutation of $V_h$ that exchanges $(i, 0)$ and $(i, 1)$ and fixes every other vertex.
--
--   The pair transpositions are commuting involutions. Through the relabelling action on perfect matchings of $V_h$ (conjugation $M \mapsto p M p^{-1}$, acting on functions by $f \mapsto f(p^{-1} M p)$) they give commuting involutive operators on functions of matchings, and prescribing their eigenvalues $\pm 1$ on the first standard pairs, while working with permutations that fix an initial block pointwise, is the mechanism behind a dimension bound: if $4k < h$ and $W$ is a nonzero space of functions on the perfect matchings of $V_h$ that is invariant under all relabellings and meets the space of polynomials of degree at most $(4k)^2$ in the edge indicators only in $0$, then $\dim W \ge \binom{h}{k}$.
--
--   **Formalization Note** `Vertices h` is `Fin h × Bool`, with `false` and `true` in the roles of $0$ and $1$; `firstVertices h t` is a `Finset (Vertices h)` with membership lemma `mem_firstVertices`, and `pairSwap i` is `Equiv.swap (i, false) (i, true)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/RepresentationDimension.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/RepresentationDimension.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1

namespace MatchingSmoothing
section StandardPairs

abbrev Vertices (h : ℕ) := Fin h × Bool

variable {h : ℕ}

def firstVertices (h t : ℕ) : Finset (Vertices h) :=
  (Finset.univ.filter fun i : Fin h => i.val < t) ×ˢ Finset.univ

@[simp] lemma mem_firstVertices (t : ℕ) (v : Vertices h) :
    v ∈ firstVertices h t ↔ v.1.val < t := by simp [firstVertices]

def pairSwap (i : Fin h) : Equiv.Perm (Vertices h) :=
  Equiv.swap (i, false) (i, true)

end StandardPairs
end MatchingSmoothing

end OAI


