-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
-- name    : OAI_Combinatorics_HoneycombCorridor_Currents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:32:26.548584+00:00
-- url     : https://prove2.me/theorems/f761fa62-bea0-4456-a637-f90db70048a2
-- title:
--   Directed rational currents and face gradients on the honeycomb
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Directed current.** For a rational edge function $q$, the directed current at a germ $g$ is $\mathrm{sign}(g)\,q(\mathrm{edge}(g))$, where the sign is $+1$ at up vertices and $-1$ at down vertices. It changes sign under reversal of the germ.
--   2. **Conservation.** The current is conserved if at every vertex the outgoing currents through the three slots sum to zero:
--   $$
--   \sum_{k=0}^{2}\mathrm{directedCurrent}(q,(v,k))=0 .
--   $$
--   3. **Face gradients.** For a face function $r$, the face gradient of an edge is $r(\mathrm{left})-r(\mathrm{right})$ along its canonical dart; face gradients are the basic conserved currents.
--   4. The integer oriented flow of an edge chain vanishes at a germ exactly when the chain vanishes on the corresponding edge.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Currents.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Currents.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def directedCurrent (q : EdgeIndex → ℚ) (g : Germ) : ℚ :=
  (dartSign g : ℚ) * q (edgeOf g)

def ConservedCurrent (q : EdgeIndex → ℚ) : Prop :=
  ∀ v : Vertex, ∑ k : Fin 3, directedCurrent q (v,k) = 0

@[simp] theorem directedCurrent_reverse (q : EdgeIndex → ℚ) (g : Germ) :
    directedCurrent q (reverseGerm g) = -directedCurrent q g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [directedCurrent,dartSign,edgeOf,reverseGerm,neighbor]

@[simp] theorem directedCurrent_advance (q : EdgeIndex → ℚ) (g : Germ) (b : Bool) :
    directedCurrent q (advance g b) = -directedCurrent q (g.1,outgoingSlot g b) := by
  have h := directedCurrent_reverse q (advance g b)
  rw [reverseGerm_advance] at h
  linarith

theorem orientedFlow_zero_iff (q : EdgeIndex →₀ ℤ) (g : Germ) :
    orientedFlow q g = 0 ↔ q (edgeOf g) = 0 := by
  rcases g with ⟨v,k⟩
  cases v <;> simp [orientedFlow_up,orientedFlow_down,edgeOf]

def faceGradient (r : FaceIndex → ℚ) (e : EdgeIndex) : ℚ :=
  r (leftFace (canonicalDart e)) - r (rightFace (canonicalDart e))

end PolynomialVacuumBridge.Corridor

end

end OAI


