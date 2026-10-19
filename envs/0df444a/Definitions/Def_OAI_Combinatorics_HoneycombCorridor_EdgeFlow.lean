-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
-- name    : OAI_Combinatorics_HoneycombCorridor_EdgeFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:27:19.014023+00:00
-- url     : https://prove2.me/theorems/4cb6ee72-9202-4fb1-ade5-f242a9f17c67
-- title:
--   Edge chains, boundary map and flows of honeycomb walks
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Edges are indexed by a face index and a slot, $e=((i,j),k)$, with up end $\mathrm{up}(i,j)$ and down end its $k$-th neighbour.
--
--   1. **Boundary map.** The boundary of an integer edge chain is the vertex chain $\partial q=\sum_eq(e)(\delta_{\mathrm{up}(e)}-\delta_{\mathrm{down}(e)})$.
--   2. **Darts and word flows.** A germ determines an edge and a sign ($+1$ at up vertices, $-1$ at down vertices); the dart flow is the corresponding signed unit chain, so its boundary is $\delta_v-\delta_{\mathrm{neighbor}(v,k)}$. The word flow of a walk is the sum of the dart flows of its steps, and
--   $$
--   \partial\,\mathrm{wordFlow}(g,w)=\delta_{g}-\delta_{\mathrm{terminalGerm}(g,w)} .
--   $$
--   3. **Closed walks.** The components of an edge chain along the three slots give a triple of face functions. For a closed walk ($\mathrm{terminalGerm}(g,w)=g$) these components form a conserved finite honeycomb flow, so the word flow has a finite integer face potential.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/EdgeFlow.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/EdgeFlow.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor
abbrev EdgeIndex := FaceIndex × Fin 3

def upEnd (e : EdgeIndex) : Vertex := .up e.1.1 e.1.2

def downEnd (e : EdgeIndex) : Vertex := neighbor (upEnd e) e.2

noncomputable def edgeBoundary : (EdgeIndex →₀ ℤ) →+ (Vertex →₀ ℤ) :=
  Finsupp.liftAddHom fun e => Finsupp.singleAddHom (upEnd e) - Finsupp.singleAddHom (downEnd e)

@[simp] theorem edgeBoundary_single (e : EdgeIndex) (a : ℤ) :
    edgeBoundary (Finsupp.single e a) =
      Finsupp.single (upEnd e) a - Finsupp.single (downEnd e) a := by
  simp [edgeBoundary]

def edgeOf : Germ → EdgeIndex
  | (.up i j, k) => ((i,j),k)
  | (.down i j, k) =>
      if k = 0 then ((i,j+1),k) else if k = 1 then ((i,j),k) else ((i+1,j),k)

def dartSign : Germ → ℤ
  | (.up _ _, _) => 1
  | (.down _ _, _) => -1

noncomputable def dartFlow (g : Germ) : EdgeIndex →₀ ℤ :=
  Finsupp.single (edgeOf g) (dartSign g)

@[simp] theorem edgeBoundary_dartFlow (g : Germ) :
    edgeBoundary (dartFlow g) =
      Finsupp.single g.1 1 - Finsupp.single (neighbor g.1 g.2) 1 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [dartFlow,edgeOf,dartSign,upEnd,downEnd,neighbor]

noncomputable def wordFlow : Germ → List Bool → (EdgeIndex →₀ ℤ)
  | _, [] => 0
  | g, b :: w => dartFlow (g.1,outgoingSlot g b) + wordFlow (advance g b) w

theorem boundary_wordFlow (g : Germ) (w : List Bool) :
    edgeBoundary (wordFlow g w) =
      Finsupp.single g.1 1 - Finsupp.single (terminalGerm g w).1 1 := by
  induction w generalizing g with
  | nil => simp [wordFlow,terminalGerm]
  | cons b w ih =>
      simp only [wordFlow,map_add,edgeBoundary_dartFlow,ih,terminalGerm]
      simp only [advance]
      abel

noncomputable def flowComponent (q : EdgeIndex →₀ ℤ) (k : Fin 3) : FaceIndex →₀ ℤ :=
  Finsupp.comapDomain (fun a => (a,k)) q (by intro a _ b _ h; exact Prod.mk.inj h |>.1)

@[simp] theorem flowComponent_apply (q : EdgeIndex →₀ ℤ) (k : Fin 3) (a : FaceIndex) :
    flowComponent q k a = q (a,k) := rfl

theorem boundary_up (q : EdgeIndex →₀ ℤ) (i j : ℤ) :
    edgeBoundary q (.up i j) = q ((i,j),0) + q ((i,j),1) + q ((i,j),2) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      fin_cases k <;>
        simp [edgeBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm]

theorem boundary_down (q : EdgeIndex →₀ ℤ) (i j : ℤ) :
    edgeBoundary q (.down i j) =
      -(q ((i,j+1),0) + q ((i,j),1) + q ((i+1,j),2)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      have hy : j = y - 1 ↔ y = j + 1 := by omega
      have hx : i = x - 1 ↔ x = i + 1 := by omega
      fin_cases k <;>
        simp [edgeBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm,hy,hx]

noncomputable def closedWordFlow (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) : FiniteHoneycombFlow where
  q0 := flowComponent (wordFlow g w) 0
  q1 := flowComponent (wordFlow g w) 1
  q2 := flowComponent (wordFlow g w) 2
  up_conservation := by
    intro i j
    simp only [flowComponent_apply]
    rw [← boundary_up,boundary_wordFlow,hc,sub_self]
    rfl
  down_conservation := by
    intro i j
    simp only [flowComponent_apply]
    have h := boundary_down (wordFlow g w) i j
    rw [boundary_wordFlow,hc,sub_self] at h
    simp only [Finsupp.zero_apply] at h
    omega

theorem closed_word_has_finite_potential (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) :
    ∃ p : FaceIndex →₀ ℤ, ∀ i j,
      wordFlow g w ((i,j),0) = p (i,j) - p (i-1,j) ∧
      wordFlow g w ((i,j),1) = p (i-1,j+1) - p (i,j) ∧
      wordFlow g w ((i,j),2) = p (i-1,j) - p (i-1,j+1) := by
  exact finite_flow_is_face_boundary (closedWordFlow g w hc)

end PolynomialVacuumBridge.Corridor

end

end OAI


