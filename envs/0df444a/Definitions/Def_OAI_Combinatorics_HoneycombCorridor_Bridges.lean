-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Bridges
-- name    : OAI_Combinatorics_HoneycombCorridor_Bridges
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:45:09.624454+00:00
-- url     : https://prove2.me/theorems/9bb85362-0f01-4214-b1e7-ce3f5ac43543
-- title:
--   Encoding honeycomb bridge paths by turn words
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. A bridge path of height $h$ is a duplicate-free chain of adjacent vertices from $\mathrm{up}(0,0)$ to some $\mathrm{down}(i,h-1)$ inside the layers $0\le j<h$.
--
--   1. **Slots and turns.** Adjacent vertices are related by a slot, and a vertex adjacent to $g_1$ other than the previous one is reached by a left or a right turn.
--   2. **Chains as words.** A duplicate-free chain from $g_1$ avoiding the previous vertex is the trace of a turn word, extended by its terminal vertex.
--   3. **Bridge words.** For $h\ge1$, every bridge path $p$ is traced by a word from the bottom source $(\mathrm{up}(0,0),0)$ whose terminal vertex lies in layer $h$:
--   $$
--   \mathrm{traced}(\mathrm{src},\mathrm{bridgeWord}(p))=p,\qquad|\mathrm{bridgeWord}(p)|=|p| .
--   $$
--   The layer of a vertex is its box index $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Bridges.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Bridges.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripDecay
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Reflection
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralMass
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripWindows
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_SpatialDecay
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralLength

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

 theorem adjacent_exists_slot (v u : Vertex) (h : adjacent v u) :
    ∃ k : Fin 3, neighbor v k = u := by
  cases v <;> cases u <;> simp only [adjacent] at h
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨0,by simp [neighbor]⟩
    · exact ⟨1,by simp [neighbor]⟩
    · exact ⟨2,by simp [neighbor]⟩
  · rcases h with ⟨rfl,hl⟩ | ⟨rfl,rfl⟩ | ⟨hk,rfl⟩
    · exact ⟨0,by simp [neighbor]; omega⟩
    · exact ⟨1,by simp [neighbor]⟩
    · exact ⟨2,by simp [neighbor]; omega⟩

theorem exists_advance_of_adjacent (g : Germ) (v : Vertex) (ha : adjacent g.1 v)
    (hb : v ≠ neighbor g.1 g.2) : ∃ b : Bool, (advance g b).1 = v := by
  obtain ⟨k,hk⟩ := adjacent_exists_slot g.1 v ha
  have hkg : k ≠ g.2 := by
    intro he
    exact hb (he ▸ hk.symm)
  have ho : ∃ b : Bool, outgoingSlot g b = k := by
    obtain ⟨u,j⟩ := g
    fin_cases j <;> fin_cases k <;> simp_all [outgoingSlot]
  obtain ⟨b,hb⟩ := ho
  exact ⟨b,by simpa only [advance,hb] using hk⟩

theorem exists_word_of_chain (g : Germ) (l : List Vertex)
    (hc : (g.1 :: l).IsChain adjacent) (hn : (g.1 :: l).Nodup)
    (hp : neighbor g.1 g.2 ∉ l) :
    ∃ w : List Bool, traced g w ++ [(terminalGerm g w).1] = g.1 :: l := by
  induction l generalizing g with
  | nil => exact ⟨[],rfl⟩
  | cons v l ih =>
    obtain ⟨ha,hc⟩ := List.isChain_cons_cons.mp hc
    obtain ⟨hg,hn⟩ := List.nodup_cons.mp hn
    have hb : v ≠ neighbor g.1 g.2 := by
      intro he
      exact hp (by simp [he])
    obtain ⟨b,hb⟩ := exists_advance_of_adjacent g v ha hb
    have hg' : neighbor (advance g b).1 (advance g b).2 = g.1 := by
      simp only [advance,neighbor_neighbor]
    have hc' : ((advance g b).1 :: l).IsChain adjacent := by simpa only [hb] using hc
    have hn' : ((advance g b).1 :: l).Nodup := by simpa only [hb] using hn
    have hp' : neighbor (advance g b).1 (advance g b).2 ∉ l := by
      rw [hg']
      exact fun hm => hg (List.mem_cons_of_mem _ hm)
    obtain ⟨w,hw⟩ := ih (advance g b) hc' hn' hp'
    refine ⟨b::w,?_⟩
    simp only [traced,terminalGerm,List.cons_append,hw,hb]

@[simp] theorem layer_boxIndex (v : Vertex) : layer v = boxIndex v 0 := by
  cases v <;> simp [layer,boxIndex]

theorem bridge_exists_word (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    ∃ w : List Bool, traced bottomSource w = p.vertices ∧
      layer (terminalGerm bottomSource w).1 = (h : ℤ) := by
  obtain ⟨i,hi⟩ := p.terminal
  let u : Vertex := .up i h
  have hu : layer u = (h : ℤ) := by rfl
  have hnu : u ∉ p.vertices := by
    intro hm
    have h := (p.inStrip u hm).2
    rw [hu] at h
    omega
  have hc : (p.vertices ++ [u]).IsChain adjacent := by
    apply p.connected.append (by simp)
    intro v hv a ha
    have hv' : v = .down i ((h : ℤ)-1) := by symm; simpa only [hi,Option.mem_some_iff] using hv
    have ha' : a = u := by symm; simpa using ha
    subst v; subst a
    simp [u,adjacent]
  have hn : (p.vertices ++ [u]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨p.distinct,by simp,?_⟩
    intro v hv a ha
    have ha' : a = u := by simpa using ha
    subst a
    exact fun he => hnu (he ▸ hv)
  have hp : neighbor bottomSource.1 bottomSource.2 ∉ p.vertices ++ [u] := by
    intro hm
    simp only [List.mem_append,List.mem_singleton] at hm
    rcases hm with hm | hm
    · have hi := (p.inStrip _ hm).1
      norm_num [bottomSource,neighbor,layer,boxIndex] at hi
    · have hidx := congrArg layer hm
      change (-1 : ℤ) = (h : ℤ) at hidx
      have hheight : (1 : ℤ) ≤ h := by exact_mod_cast hh
      exact (ne_of_lt (lt_of_lt_of_le (by norm_num : (-1 : ℤ) < 1) hheight)) hidx
  obtain ⟨l,hl⟩ := List.head?_eq_some_iff.mp p.source
  have hc' : (bottomSource.1 :: (l ++ [u])).IsChain adjacent := by
    simpa only [hl,List.cons_append,bottomSource] using hc
  have hn' : (bottomSource.1 :: (l ++ [u])).Nodup := by
    simpa only [hl,List.cons_append,bottomSource] using hn
  have hp' : neighbor bottomSource.1 bottomSource.2 ∉ l ++ [u] := by
    intro hm
    apply hp
    rw [hl,List.cons_append]
    exact List.mem_cons_of_mem _ hm
  obtain ⟨w,hw⟩ := exists_word_of_chain bottomSource _ hc' hn' hp'
  have heq : traced bottomSource w ++ [(terminalGerm bottomSource w).1] = p.vertices ++ [u] := by
    simpa only [hl,List.cons_append,bottomSource] using hw
  have ht : (terminalGerm bottomSource w).1 = u := by
    have ht := congrArg List.getLast? heq
    simpa using ht
  rw [ht] at heq
  exact ⟨w,List.append_cancel_right heq,ht ▸ hu⟩

noncomputable def bridgeWord (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) : List Bool :=
  (bridge_exists_word h hh p).choose

@[simp] theorem bridgeWord_trace (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    traced bottomSource (bridgeWord h hh p) = p.vertices :=
  (bridge_exists_word h hh p).choose_spec.1

@[simp] theorem bridgeWord_length (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) :
    (bridgeWord h hh p).length = p.vertices.length := by
  rw [← traced_length bottomSource,bridgeWord_trace]

end PolynomialVacuumBridge.Corridor

end

end OAI


