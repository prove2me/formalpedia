-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
-- name    : OAI_Combinatorics_HoneycombCorridor_CollisionHistories
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:44:59.990673+00:00
-- url     : https://prove2.me/theorems/e6b87c6d-2698-4d5d-b075-973c8f0ddefb
-- title:
--   Reversing a walk at its first collision vertex
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. Neighbours are distinct from the vertex, and outgoing slots differ from the incoming slot.
--   2. **Reversal at a vertex.** $\mathrm{reverseAt}(g,v,w)$ follows $w$ until the walk first stands at $v$, then switches that turn and reverses the remaining turns:
--   $$
--   \mathrm{reverseAt}(g,v,b::w)=\begin{cases}\bar b::\mathrm{reverseTurns}(w),&g\text{ is at }v,\\ b::\mathrm{reverseAt}(\mathrm{advance}(g,b),v,w),&\text{otherwise.}\end{cases}
--   $$
--   It is an involution and preserves length.
--   3. **Stopped walks by traces.** A word is stopped in $D$ iff its trace is duplicate-free and contained in $D$, and the endpoint is outside $D$ or on the trace.
--   4. **Collision reversal.** $\mathrm{collisionReverse}(g,w)=\mathrm{reverseAt}(g,v_{\mathrm{end}},w)$, where $v_{\mathrm{end}}$ is the terminal vertex; for a walk ending by colliding with itself, it reverses the loop closed by the collision.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CollisionHistories.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CollisionHistories.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem neighbor_ne_self (v : Vertex) (k : Fin 3) : neighbor v k ≠ v := by
  cases v <;> fin_cases k <;> simp [neighbor]

@[simp] theorem outgoingSlot_ne (g : Germ) (b : Bool) : outgoingSlot g b ≠ g.2 := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [outgoingSlot]

def reverseAt (g : Germ) (v : Vertex) : List Bool → List Bool
  | [] => []
  | b :: w => if g.1 = v then (!b) :: reverseTurns w
    else b :: reverseAt (advance g b) v w

@[simp] theorem reverseAt_involutive (g : Germ) (v : Vertex) (w : List Bool) :
    reverseAt g v (reverseAt g v w) = w := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      by_cases h : g.1 = v
      · simp [reverseAt,h]
      · simp [reverseAt,h,ih]

@[simp] theorem reverseAt_length (g : Germ) (v : Vertex) (w : List Bool) :
    (reverseAt g v w).length = w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      by_cases h : g.1 = v <;> simp [reverseAt,h,reverseTurns,ih]

theorem stopped_iff_trace (D : Finset Vertex) (g : Germ) (w : List Bool) :
    Stopped D g w ↔ (traced g w).Nodup ∧ (∀ v ∈ traced g w, v ∈ D) ∧
      ((terminalGerm g w).1 ∉ D ∨ (terminalGerm g w).1 ∈ traced g w) := by
  induction w generalizing D g with
  | nil => simp [Stopped,traced,terminalGerm]
  | cons b w ih =>
      simp only [Stopped,ih,traced,List.nodup_cons,List.mem_cons,terminalGerm]
      constructor
      · rintro ⟨hg,hN,hD,ht⟩
        refine ⟨⟨?_,hN⟩,?_,?_⟩
        · intro hm
          exact (Finset.mem_erase.mp (hD _ hm)).1 rfl
        · intro v hv
          rcases hv with rfl | hv
          · exact hg
          · exact Finset.mem_of_mem_erase (hD _ hv)
        · rcases ht with ht | ht
          · by_cases hm : (terminalGerm (advance g b) w).1 ∈ D
            · right; left
              by_contra hn
              exact ht (Finset.mem_erase.mpr ⟨hn,hm⟩)
            · exact Or.inl hm
          · exact Or.inr (Or.inr ht)
      · rintro ⟨⟨hn,hN⟩,hD,ht⟩
        refine ⟨hD _ (Or.inl rfl),hN,?_,?_⟩
        · intro v hv
          exact Finset.mem_erase.mpr ⟨fun he => hn (he ▸ hv),hD _ (Or.inr hv)⟩
        · rcases ht with ht | ht | ht
          · exact Or.inl (fun h => ht (Finset.mem_of_mem_erase h))
          · exact Or.inl (by simp [ht])
          · exact Or.inr ht

@[simp] theorem reverse_advance_vertex (g : Germ) (b : Bool) :
    (reverseGerm (advance g b)).1 = g.1 := by
  simp [reverseGerm, advance]

def collisionReverse (g : Germ) (w : List Bool) : List Bool :=
  reverseAt g (terminalGerm g w).1 w

end PolynomialVacuumBridge.Corridor

end

end OAI


