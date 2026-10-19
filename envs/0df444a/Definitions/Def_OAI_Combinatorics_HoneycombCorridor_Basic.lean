-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
-- name    : OAI_Combinatorics_HoneycombCorridor_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:24:38.519982+00:00
-- url     : https://prove2.me/theorems/1aefa8db-ae2e-44f7-accd-521f65c3bcaf
-- title:
--   Honeycomb germs, turn words and parafermionic word weights
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Neighbours and germs.** $\mathrm{neighbor}(v,k)$ is the neighbour of $v$ through slot $k$; it satisfies $\mathrm{neighbor}(\mathrm{neighbor}(v,k),k)=v$. From a germ $g=(v,k)$ a turn $b$ leaves through the outgoing slot $k+2$ (if $b$ is a left turn) or $k+1$ (right turn), and $\mathrm{advance}(g,b)$ is the germ at the next vertex.
--   2. **Stopped walks.** For a finite domain $D$, a word $w$ is stopped from $g$ if the walk stays in $D$, never revisits a vertex (each visited vertex is removed from $D$), and the final vertex is outside the remaining domain. The finite set $\mathrm{leaves}(D,g)$ consists of all such words, and $w\in\mathrm{leaves}(D,g)$ iff $w$ is stopped.
--   3. **Weights.** Turns have angle $\pm\pi/3$, the step weight is
--   $$
--   \mathrm{stepWeight}(b)=\lambda\,e^{i\frac38\,\theta(b)},\qquad\theta(b)=\pm\frac\pi3,
--   $$
--   and $\mathrm{wordWeight}(w)=\prod_b\mathrm{stepWeight}(b)=\lambda^{|w|}e^{i\frac38\sum\theta}$.
--   4. **Traces.** $\mathrm{traced}(g,w)$ lists the vertices visited before the last step (it has length $|w|$) and $\mathrm{terminalGerm}(g,w)$ is the final germ. A stopped walk has a duplicate-free trace contained in $D$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def neighbor (v : Vertex) (k : Fin 3) : Vertex :=
  match v with
  | .up i j => if k = 0 then .down i (j - 1)
      else if k = 1 then .down i j else .down (i - 1) j
  | .down i j => if k = 0 then .up i (j + 1)
      else if k = 1 then .up i j else .up (i + 1) j

abbrev Germ := Vertex × Fin 3

def outgoingSlot (g : Germ) (b : Bool) : Fin 3 :=
  g.2 + (if b then 2 else 1)

def advance (g : Germ) (b : Bool) : Germ :=
  (neighbor g.1 (outgoingSlot g b), outgoingSlot g b)

def Stopped : Finset Vertex → Germ → List Bool → Prop
  | D, g, [] => g.1 ∉ D
  | D, g, b :: w => g.1 ∈ D ∧ Stopped (D.erase g.1) (advance g b) w

def leaves (D : Finset Vertex) (g : Germ) : Finset (List Bool) :=
  if g.1 ∈ D then
    ((leaves (D.erase g.1) (advance g true)).image (List.cons true)) ∪
    ((leaves (D.erase g.1) (advance g false)).image (List.cons false))
  else {[]}
termination_by D.card
decreasing_by all_goals exact Finset.card_erase_lt_of_mem (by assumption)

noncomputable def turnAngle (b : Bool) : ℝ :=
  if b then Real.pi / 3 else -(Real.pi / 3)

noncomputable def stepWeight (b : Bool) : ℂ :=
  (criticalActivity : ℂ) * Complex.exp (((3 / 8 : ℝ) * turnAngle b : ℝ) * Complex.I)

noncomputable def wordWeight (w : List Bool) : ℂ := (w.map stepWeight).prod

def traced : Germ → List Bool → List Vertex
  | _, [] => []
  | g, b :: w => g.1 :: traced (advance g b) w

def terminalGerm : Germ → List Bool → Germ
  | g, [] => g
  | g, b :: w => terminalGerm (advance g b) w

@[simp] theorem neighbor_neighbor (v : Vertex) (k : Fin 3) :
    neighbor (neighbor v k) k = v := by
  cases v <;> fin_cases k <;> simp [neighbor]

theorem adjacent_neighbor (v : Vertex) (k : Fin 3) : adjacent v (neighbor v k) := by
  cases v <;> fin_cases k <;> simp [neighbor, adjacent]

@[simp] theorem advance_adjacent (g : Germ) (b : Bool) :
    adjacent g.1 (advance g b).1 := adjacent_neighbor _ _

@[simp] theorem wordWeight_nil : wordWeight [] = 1 := rfl
@[simp] theorem wordWeight_cons (b : Bool) (w : List Bool) :
    wordWeight (b :: w) = stepWeight b * wordWeight w := rfl

theorem critical_cos_pos : 0 < Real.cos (Real.pi / 8) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

theorem mem_leaves_iff (D : Finset Vertex) (g : Germ) (w : List Bool) :
    w ∈ leaves D g ↔ Stopped D g w := by
  induction w generalizing D g with
  | nil =>
      rw [leaves]
      by_cases h : g.1 ∈ D <;> simp [h, Stopped]
  | cons b w ih =>
      rw [leaves]
      by_cases h : g.1 ∈ D
      · cases b <;> simp [h, Stopped, ih]
      · simp [h, Stopped]

theorem stopped_traced (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : Stopped D g w) :
    (traced g w).Nodup ∧ ∀ v ∈ traced g w, v ∈ D := by
  induction w generalizing D g with
  | nil => simp [traced]
  | cons b w ih =>
      obtain ⟨hg, hw⟩ := hw
      obtain ⟨hn, hD⟩ := ih (D.erase g.1) (advance g b) hw
      constructor
      · simp only [traced, List.nodup_cons]
        refine ⟨?_, hn⟩
        intro hmem
        exact (Finset.mem_erase.mp (hD g.1 hmem)).1 rfl
      · intro v hv
        simp only [traced, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hg
        · exact (Finset.mem_erase.mp (hD v hv)).2

theorem traced_length (g : Germ) (w : List Bool) : (traced g w).length = w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp only [traced, List.length_cons, ih]

theorem wordWeight_physical (w : List Bool) :
    wordWeight w = (criticalActivity : ℂ) ^ w.length *
      Complex.exp (((3 / 8 : ℝ) * (w.map turnAngle).sum : ℝ) * Complex.I) := by
  induction w with
  | nil => simp [wordWeight]
  | cons b w ih =>
      simp only [wordWeight_cons, ih, List.length_cons, List.map_cons, List.sum_cons]
      simp only [stepWeight, mul_add, Complex.ofReal_add, Complex.ofReal_mul]
      rw [add_mul, Complex.exp_add, pow_succ]
      ring

end PolynomialVacuumBridge.Corridor

end

end OAI


