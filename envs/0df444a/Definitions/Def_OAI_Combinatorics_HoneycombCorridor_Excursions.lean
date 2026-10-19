-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
-- name    : OAI_Combinatorics_HoneycombCorridor_Excursions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:25:22.553988+00:00
-- url     : https://prove2.me/theorems/a3716213-fce9-4c9e-abbe-370d86d77c9e
-- title:
--   Reversal of honeycomb walks, excursions and boundary germs
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Reversal.** $\mathrm{reverseGerm}(v,k)=(\mathrm{neighbor}(v,k),k)$ reverses the last edge, and $\mathrm{reverseTurns}(w)$ reverses the word and swaps left and right. Reversal is an involution on germs and words, reverses traces, and conjugates weights: $\mathrm{wordWeight}(\mathrm{reverseTurns}\,w)=\overline{\mathrm{wordWeight}(w)}$.
--   2. **Excursions.** A pair $e=(g,w)$ is an excursion of $D$ if $g$ enters $D$ from outside, $w$ is stopped from $g$, and the walk ends outside $D$. The finite set of excursions is closed under the reversal $e\mapsto(\mathrm{reverseGerm}(\mathrm{terminalGerm}(g,w)),\mathrm{reverseTurns}(w))$, which is an involution.
--   3. **Exit and collision sums.** For a germ $g$, the exit sum adds $\mathrm{wordWeight}(w)$ over stopped words ending outside $D$, and the collision sum over stopped words ending at an already visited vertex of $D$.
--   4. **Boundary data.** The boundary germs of $D$ are the germs $g$ with $g$'s vertex in $D$ and the previous vertex outside $D$. For $v\in D$, the first arrivals at $v$ are walks from boundary germs, stopped in $D\setminus\{v\}$, ending at $v$; the ray exits are walks starting along an edge out of $v$, stopped in $D\setminus\{v\}$ and leaving $D$. Reversing a first arrival gives a ray exit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Excursions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Excursions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def reverseGerm (g : Germ) : Germ := (neighbor g.1 g.2, g.2)

def reverseTurns (w : List Bool) : List Bool := w.reverse.map Bool.not

@[simp] theorem reverseGerm_reverseGerm (g : Germ) :
    reverseGerm (reverseGerm g) = g := by
  rcases g with ⟨v,k⟩
  simp [reverseGerm]

@[simp] theorem reverseTurns_reverseTurns (w : List Bool) :
    reverseTurns (reverseTurns w) = w := by
  simp [reverseTurns, List.map_reverse, List.map_map, Function.comp_def]

@[simp] theorem reverseTurns_nil : reverseTurns [] = [] := rfl

@[simp] theorem reverseTurns_cons (b : Bool) (w : List Bool) :
    reverseTurns (b :: w) = reverseTurns w ++ [!b] := by
  simp [reverseTurns]

@[simp] theorem terminalGerm_append (g : Germ) (u w : List Bool) :
    terminalGerm g (u ++ w) = terminalGerm (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih => simpa [terminalGerm] using ih (advance g b)

@[simp] theorem traced_append (g : Germ) (u w : List Bool) :
    traced g (u ++ w) = traced g u ++ traced (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih => simp [traced, terminalGerm, ih]

@[simp] theorem advance_reverse (g : Germ) (b : Bool) :
    advance (reverseGerm (advance g b)) (!b) = reverseGerm g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [advance, outgoingSlot, reverseGerm]

@[simp] theorem terminalGerm_reverse (g : Germ) (w : List Bool) :
    terminalGerm (reverseGerm (terminalGerm g w)) (reverseTurns w) = reverseGerm g := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    rw [reverseTurns_cons, terminalGerm_append]
    simp only [terminalGerm, ih, advance_reverse]

@[simp] theorem traced_reverse (g : Germ) (w : List Bool) :
    traced (reverseGerm (terminalGerm g w)) (reverseTurns w) = (traced g w).reverse := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    rw [reverseTurns_cons, traced_append]
    simp only [terminalGerm, ih, terminalGerm_reverse, traced, List.reverse_cons]
    simp [reverseGerm, advance]

@[simp] theorem stepWeight_not (b : Bool) :
    stepWeight (!b) = (starRingEnd ℂ) (stepWeight b) := by
  have ha : turnAngle (!b) = -turnAngle b := by cases b <;> simp [turnAngle]
  rw [stepWeight, ha, stepWeight, map_mul, ← Complex.exp_conj]
  simp only [Complex.conj_ofReal, map_mul, Complex.conj_I]
  congr 1
  push_cast
  ring_nf

@[simp] theorem wordWeight_reverse (w : List Bool) :
    wordWeight (reverseTurns w) = (starRingEnd ℂ) (wordWeight w) := by
  unfold wordWeight reverseTurns
  rw [List.map_map]
  simp only [Function.comp_def, stepWeight_not]
  rw [show (fun b => (starRingEnd ℂ) (stepWeight b)) =
    (starRingEnd ℂ) ∘ stepWeight from rfl, ← List.map_map, map_list_prod]
  simp only [List.map_reverse, List.prod_reverse]

theorem stopped_of_trace (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hD : ∀ v ∈ traced g w, v ∈ D)
    (ht : (terminalGerm g w).1 ∉ D) : Stopped D g w := by
  induction w generalizing D g with
  | nil => exact ht
  | cons b w ih =>
    simp only [traced, List.nodup_cons] at hN
    refine ⟨hD _ (by simp [traced]), ih _ _ hN.2 ?_ ?_⟩
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun he => hN.1 (he ▸ hv),
        hD _ (by simp [traced, hv])⟩
    · exact fun hm => ht (Finset.mem_of_mem_erase hm)

def IsExcursion (D : Finset Vertex) (e : Germ × List Bool) : Prop :=
  e.1.1 ∈ D ∧ (reverseGerm e.1).1 ∉ D ∧ Stopped D e.1 e.2 ∧
    (terminalGerm e.1 e.2).1 ∉ D

noncomputable def excursions (D : Finset Vertex) : Finset (Germ × List Bool) := by
  classical
  exact ((D.product Finset.univ).biUnion fun g =>
    (leaves D g).image fun w => (g, w)).filter (IsExcursion D)

@[simp] theorem mem_excursions (D : Finset Vertex) (e : Germ × List Bool) :
    e ∈ excursions D ↔ IsExcursion D e := by
  classical
  rw [excursions, Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨?_, he⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨e.1, Finset.mem_product.mpr ⟨he.1, Finset.mem_univ _⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨e.2, (mem_leaves_iff _ _ _).mpr he.2.2.1, rfl⟩

def reverseExcursion (e : Germ × List Bool) : Germ × List Bool :=
  (reverseGerm (terminalGerm e.1 e.2), reverseTurns e.2)

@[simp] theorem reverseExcursion_reverseExcursion (e : Germ × List Bool) :
    reverseExcursion (reverseExcursion e) = e := by
  rcases e with ⟨g,w⟩
  simp [reverseExcursion]

theorem IsExcursion.nonempty {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : e.2 ≠ [] := by
  intro hw
  exact he.2.2.2 (by simpa [hw, terminalGerm] using he.1)

theorem reverse_first_mem (g : Germ) (w : List Bool) (hw : w ≠ []) :
    (reverseGerm (terminalGerm g w)).1 ∈ traced g w := by
  have hr : reverseTurns w ≠ [] := by
    intro he
    have := congrArg reverseTurns he
    exact hw (by simpa using this)
  obtain ⟨b,u,hu⟩ := List.exists_cons_of_ne_nil hr
  have hm : (reverseGerm (terminalGerm g w)).1 ∈
      traced (reverseGerm (terminalGerm g w)) (reverseTurns w) := by
    simp [hu, traced]
  simpa using hm

theorem IsExcursion.reverse {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : IsExcursion D (reverseExcursion e) := by
  obtain ⟨hN,hD⟩ := stopped_traced D e.1 e.2 he.2.2.1
  refine ⟨hD _ (reverse_first_mem _ _ he.nonempty), ?_, ?_, ?_⟩
  · simpa [reverseExcursion] using he.2.2.2
  · apply stopped_of_trace
    · simpa [reverseExcursion] using hN
    · intro v hv
      apply hD v
      simpa [reverseExcursion] using hv
    · simpa [reverseExcursion] using he.2.1
  · simpa [reverseExcursion] using he.2.1

@[simp] theorem reverseExcursion_mem (D : Finset Vertex) (e : Germ × List Bool) :
    reverseExcursion e ∈ excursions D ↔ e ∈ excursions D := by
  rw [mem_excursions, mem_excursions]
  exact ⟨fun he => by simpa using he.reverse, IsExcursion.reverse⟩

noncomputable def exitSum (D : Finset Vertex) (g : Germ) : ℂ := by
  classical
  exact ∑ w ∈ leaves D g, if (terminalGerm g w).1 ∉ D then wordWeight w else 0

noncomputable def collisionSum (D : Finset Vertex) (g : Germ) : ℂ := by
  classical
  exact ∑ w ∈ leaves D g, if (terminalGerm g w).1 ∈ D then wordWeight w else 0

noncomputable def boundaryGerms (D : Finset Vertex) : Finset Germ := by
  classical
  exact (D.product Finset.univ).filter fun g => (reverseGerm g).1 ∉ D

@[simp] theorem mem_boundaryGerms (D : Finset Vertex) (g : Germ) :
    g ∈ boundaryGerms D ↔ g.1 ∈ D ∧ (reverseGerm g).1 ∉ D := by
  classical
  simp [boundaryGerms]

noncomputable def firstArrivals (D : Finset Vertex) (v : Vertex) :
    Finset (Germ × List Bool) := by
  classical
  exact ((boundaryGerms D).biUnion fun g =>
    (leaves (D.erase v) g).image fun w => (g,w)).filter fun e =>
      (terminalGerm e.1 e.2).1 = v

@[simp] theorem mem_firstArrivals (D : Finset Vertex) (v : Vertex)
    (e : Germ × List Bool) : e ∈ firstArrivals D v ↔
    e.1 ∈ boundaryGerms D ∧ Stopped (D.erase v) e.1 e.2 ∧
      (terminalGerm e.1 e.2).1 = v := by
  classical
  simp only [firstArrivals, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨g,hg,w,hw,he⟩,ht⟩
    subst e
    exact ⟨hg, (mem_leaves_iff _ _ _).mp hw,ht⟩
  · rintro ⟨hg,hw,ht⟩
    exact ⟨⟨e.1,hg,e.2,(mem_leaves_iff _ _ _).mpr hw,rfl⟩,ht⟩

noncomputable def rayExits (D : Finset Vertex) (v : Vertex) :
    Finset (Fin 3 × List Bool) := by
  classical
  exact (Finset.univ.biUnion fun k : Fin 3 =>
    (leaves (D.erase v) (neighbor v k,k)).image fun w => (k,w)).filter fun e =>
      (terminalGerm (neighbor v e.1,e.1) e.2).1 ∉ D

@[simp] theorem mem_rayExits (D : Finset Vertex) (v : Vertex)
    (e : Fin 3 × List Bool) : e ∈ rayExits D v ↔
    Stopped (D.erase v) (neighbor v e.1,e.1) e.2 ∧
      (terminalGerm (neighbor v e.1,e.1) e.2).1 ∉ D := by
  classical
  simp only [rayExits, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨k,hk,w,hw,he⟩,ht⟩
    subst e
    exact ⟨(mem_leaves_iff _ _ _).mp hw,ht⟩
  · rintro ⟨hw,ht⟩
    exact ⟨⟨e.1,Finset.mem_univ _,e.2,(mem_leaves_iff _ _ _).mpr hw,rfl⟩,ht⟩

def reversePrefix (e : Germ × List Bool) : Fin 3 × List Bool :=
  ((terminalGerm e.1 e.2).2, reverseTurns e.2)

def reverseRay (v : Vertex) (e : Fin 3 × List Bool) : Germ × List Bool :=
  (reverseGerm (terminalGerm (neighbor v e.1,e.1) e.2), reverseTurns e.2)

@[simp] theorem reversePrefix_reverseRay (v : Vertex) (e : Fin 3 × List Bool) :
    reversePrefix (reverseRay v e) = e := by
  simp only [reversePrefix,reverseRay, terminalGerm_reverse,
    reverseTurns_reverseTurns]
  rfl

end PolynomialVacuumBridge.Corridor

end

end OAI


