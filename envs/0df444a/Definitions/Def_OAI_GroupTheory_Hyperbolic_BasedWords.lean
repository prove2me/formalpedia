-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
-- name    : OAI_GroupTheory_Hyperbolic_BasedWords
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:11:46.971592+00:00
-- url     : https://prove2.me/theorems/b19b3c4b-aecb-4958-a042-ec8acc3ea195
-- title:
--   Base paths, raw edges and power words
-- statement:
--   Auxiliary constructions relating words of a block presentation to its fundamental groupoid.
--
--   1. **Base paths.** The base path to a vertex of the triangle complex is the identity at $o$, the tree path $o\to v$ at $v$, and the tree path $o\to w$ at $w$.
--   2. **Raw edges.** Each oriented edge $e$ is an arrow of the symmetrized quiver from the source of $e$ to its target, and its oriented label is $e$ again.
--   3. **Power words.** For $g\in\Gamma$ and a lifted word $w$, the $n$-th power word concatenates the translates
--   $$
--   w,\ g\cdot w,\ g^2\cdot w,\ \dots,\ g^{n-1}\cdot w ;
--   $$
--   the $0$-th power word is empty.
--   4. **Rewording.** Rewording a full filling along an equality of words does not change its face chain.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/BasedWords.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/BasedWords.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains

namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def basePath : (a : d.Vertex) → (d.vertex .o ⟶ d.vertex a)
  | .o => 𝟙 _
  | .v => d.treePathV
  | .w => d.treePathW

end Release075.BlockPresentation

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-- The original oriented edges really are arrows in the symmetrified quiver. -/
def rawEdge (e : d.OrientedEdge) :
    (show Quiver.Symmetrify d.Vertex from d.edgeTarget (d.flipEdge e)) ⟶
      (show Quiver.Symmetrify d.Vertex from d.edgeTarget e) := by
  rcases e with ⟨e,s⟩
  rcases e with x | l | rr <;> cases s
  · exact Sum.inr (Arrow.x x)
  · exact Sum.inl (Arrow.x x)
  · exact Sum.inr (Arrow.l l)
  · exact Sum.inl (Arrow.l l)
  · exact Sum.inr (Arrow.rr rr)
  · exact Sum.inl (Arrow.rr rr)

@[simp] theorem orientedLabel_rawEdge (e : d.OrientedEdge) :
    d.orientedLabel (d.rawEdge e) = e := by
  rcases e with ⟨e,s⟩
  rcases e with x | l | rr <;> cases s <;> rfl

end Release075.BlockPresentation

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def powerWord (g : d.GroupType) (w : List d.LiftedEdge) : ℕ → List d.LiftedEdge
  | 0 => []
  | n+1 => powerWord g w n ++ w.map (d.shiftEdge (g^n))

@[simp] theorem powerWord_zero (g : d.GroupType) (w : List d.LiftedEdge) :
    d.powerWord g w 0 = [] := rfl

end Release075.BlockPresentation

namespace Release075.FullFilling
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w w' : List d.LiftedEdge}
  (D : FullFilling d.liftedFlip d.liftedTarget d.LiftedFace w)

@[simp] theorem faceChain_reword (h : w = w') : (D.reword h).faceChain = D.faceChain := by
  subst w'; rfl

end Release075.FullFilling

end OAI


