-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
-- name    : OAI_Combinatorics_SharpThreshold_BlockOrbits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:21:15.891668+00:00
-- url     : https://prove2.me/theorems/7fd61a77-52d2-478d-9ba3-9d7c23569630
-- title:
--   Edge orbits under block permutations and boundary edges
-- statement:
--   Let $B$ be a set of vertices of $\{0,\dots,n-1\}$.
--
--   1. The block orbit of an edge $e$ is
--   $$
--   \{\pi(e):\ \pi\text{ a permutation fixing every vertex outside }B\} .
--   $$
--   2. For an exterior vertex $w\notin B$ and $u\in B$, the boundary edge is $\{u,w\}$; it has two distinct endpoints since $u\ne w$.
--
--   The boundary edges $\{u,w\}$, $u\in B$, form one block orbit. By symmetry they carry equal influences.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockOrbits.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockOrbits.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- The edge orbit under permutations fixing the complement of `B` pointwise. -/
def blockEdgeOrbit {n : ℕ} (B : Finset (Fin n)) (e : GraphEdge n) :
    Finset (GraphEdge n) := by
  classical
  exact Finset.univ.filter (fun e' => ∃ π : Equiv.Perm (Fin n),
    (∀ u, u ∉ B → π u = u) ∧ permEdge π e = e')

@[simp] theorem mem_blockEdgeOrbit {n : ℕ} {B : Finset (Fin n)}
    {e e' : GraphEdge n} : e' ∈ blockEdgeOrbit B e ↔
    ∃ π : Equiv.Perm (Fin n), (∀ u, u ∉ B → π u = u) ∧ permEdge π e = e' := by
  classical
  simp [blockEdgeOrbit]

/-- The boundary edge joining a vertex of the block to a fixed exterior vertex. -/
def blockBoundaryEdge {n : ℕ} {B : Finset (Fin n)} (w : Fin n) (hw : w ∉ B)
    (u : B) : GraphEdge n :=
  ⟨{u.val, w}, Finset.card_pair (by
    intro h
    exact hw (h ▸ u.property))⟩

end Problem313

end

end OAI


