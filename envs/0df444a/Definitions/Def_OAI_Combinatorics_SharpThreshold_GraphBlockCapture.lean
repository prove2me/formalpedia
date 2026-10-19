-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
-- name    : OAI_Combinatorics_SharpThreshold_GraphBlockCapture
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:12:40.941795+00:00
-- url     : https://prove2.me/theorems/358d3af9-115d-45ed-a428-17fe879dcd33
-- title:
--   A vertex block detecting a Fourier support
-- statement:
--   For a real cutoff $k$, a set $S$ of graph edges on $\{0,\dots,n-1\}$ and a vertex set $B$, the block $B$ detects $S$ if the number of edges of $S$ meeting $B$ satisfies
--   $$
--   1\le\bigl|\{e\in S:\ e\cap B\ne\emptyset\}\bigr|\le k .
--   $$
--
--   A detecting block sees part of the support but only a bounded amount of it. Low Fourier levels are captured by restricting to such blocks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/GraphBlockCapture.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/GraphBlockCapture.lean by skeleton subtraction
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

namespace OAI

/-! The graph-combinatorial input to capture of low Fourier levels. -/

namespace Problem313

noncomputable section

/-- A block detects a support when the restricted Fourier degree is positive
and no larger than the specified real cutoff. -/
def BlockDetects {n : ℕ} (k : ℝ) (S : Finset (GraphEdge n))
    (B : Finset (Fin n)) : Prop :=
  1 ≤ (S.filter (fun e => ¬Disjoint e.val B)).card ∧
    ((S.filter (fun e => ¬Disjoint e.val B)).card : ℝ) ≤ k

instance blockDetects_decidable {n : ℕ} (k : ℝ) (S : Finset (GraphEdge n))
    (B : Finset (Fin n)) : Decidable (BlockDetects k S B) :=
  Classical.propDecidable _

end

end Problem313

end OAI


