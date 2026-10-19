-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
-- name    : OAI_Combinatorics_HoneycombCorridor_CycleSplice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:42:44.256587+00:00
-- url     : https://prove2.me/theorems/b69181d0-5d7f-4014-93e6-598284ed8c5a
-- title:
--   Stem and reversed-loop germs for splicing cycles
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Stem germ.** For a germ $g=(v,k)$ and a turn $b$, the stem germ is $(v,\mathrm{unusedSlot}(g,b))$: it describes arriving at $v$ through the slot that the walk did not use.
--   2. **Reversed-loop germ.** $(v,\mathrm{outgoingSlot}(g,b))$ describes arriving at $v$ backwards along the edge the walk used to leave.
--   3. **Splicing identities.** From the stem germ, the opposite turn continues along the original walk, and the original turn goes back along the incoming edge:
--   $$
--   \mathrm{advance}(\mathrm{stem}(g,b),\bar b)=\mathrm{advance}(g,b),\qquad\mathrm{advance}(\mathrm{stem}(g,b),b)=\mathrm{reverseGerm}(g).
--   $$
--   Consequently the walk $\bar b::w$ from the stem germ has the same trace and endpoint as $b::w$ from $g$. Reversed-loop germs are involutive and have the same stem, and reversing a germ negates its dart flow.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CycleSplice.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CycleSplice.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def stemGerm (g : Germ) (b : Bool) : Germ := (g.1,unusedSlot g b)

def reverseLoopGerm (g : Germ) (b : Bool) : Germ := (g.1,outgoingSlot g b)

@[simp] theorem stem_forward (g : Germ) (b : Bool) :
    advance (stemGerm g b) (!b) = advance g b := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [stemGerm,unusedSlot,advance,outgoingSlot]

@[simp] theorem stem_reverse (g : Germ) (b : Bool) :
    advance (stemGerm g b) b = reverseGerm g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [stemGerm,unusedSlot,advance,outgoingSlot,reverseGerm]

@[simp] theorem reverseLoop_advance (g : Germ) (b : Bool) :
    advance (reverseLoopGerm g b) (!b) = reverseGerm g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,advance,outgoingSlot,reverseGerm]

@[simp] theorem reverseLoop_reverseLoop (g : Germ) (b : Bool) :
    reverseLoopGerm (reverseLoopGerm g b) (!b) = g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,outgoingSlot]

@[simp] theorem reverseLoop_stem (g : Germ) (b : Bool) :
    stemGerm (reverseLoopGerm g b) (!b) = stemGerm g b := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,stemGerm,unusedSlot,outgoingSlot]

@[simp] theorem reverseGerm_advance_eq (g : Germ) (b : Bool) :
    reverseGerm (advance g b) = reverseLoopGerm g b := by
  simp [reverseGerm,advance,reverseLoopGerm]

@[simp] theorem stem_forward_trace (g : Germ) (b : Bool) (w : List Bool) :
    traced (stemGerm g b) ((!b) :: w) = traced g (b :: w) := by
  change g.1 :: traced (advance (stemGerm g b) (!b)) w = _
  rw [stem_forward]
  rfl

@[simp] theorem stem_forward_terminal (g : Germ) (b : Bool) (w : List Bool) :
    terminalGerm (stemGerm g b) ((!b) :: w) = terminalGerm g (b :: w) := by
  simp [terminalGerm]

@[simp] theorem dartFlow_reverse (g : Germ) : dartFlow (reverseGerm g) = -dartFlow g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [dartFlow,edgeOf,dartSign,reverseGerm,neighbor]

@[simp] theorem reverseLoop_outgoing (g : Germ) (b : Bool) :
    ((reverseLoopGerm g b).1,outgoingSlot (reverseLoopGerm g b) (!b)) = g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [reverseLoopGerm,outgoingSlot]

end PolynomialVacuumBridge.Corridor

end

end OAI


