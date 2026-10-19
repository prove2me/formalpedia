-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
-- name    : OAI_Probability_CriticalZ3_BoxGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:59:14.43999+00:00
-- url     : https://prove2.me/theorems/55677b98-8b25-40f0-af2f-75eb1b9e7823
-- title:
--   Boxes in the cubic lattice
-- statement:
--   Axis-parallel boxes $B=[a,b]\subseteq\mathbb Z^3$ with $a\le b$ coordinatewise.
--
--   1. **Vertices and bonds.** The box contains $x$ if $a_i\le x_i\le b_i$ for all $i$; its bonds are those with both endpoints in the box.
--   2. **Expansion and cubes.** Expanding by $j$ moves every face outward by $j$, and expansions compose additively. The cube of radius $m$ around $c$ is the box $[c-m,c+m]$, containing exactly the $x$ with
--   $$
--   \max_i|x_i-c_i|\le m .
--   $$
--   3. **Seed centres.** If the box is wide enough, clamping a point $z$ coordinatewise into $[a_i+m,\,b_i-m]$ gives a centre whose cube of radius $m$ is contained in the box.
--   4. **Translations.** Translation by $c$ acts on vertices and bonds, commutes with lattice steps and moves cubes around $0$ to cubes around $c$. Nearest-neighbour steps within the box are also recorded.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/BoxGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/BoxGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

structure Box where
  lower : Vertex
  upper : Vertex
  ordered : lower ≤ upper

namespace Box

@[ext] theorem ext {B C : Box} (hl : B.lower = C.lower) (hu : B.upper = C.upper) : B = C := by
  cases B; cases C; cases hl; cases hu; rfl

noncomputable def vertices (B : Box) : Finset Vertex := Finset.Icc B.lower B.upper

def Contains (B : Box) (x : Vertex) : Prop := ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i

@[simp] theorem mem_vertices (B : Box) (x : Vertex) : x ∈ B.vertices ↔ B.Contains x := by
  simp only [vertices, Finset.mem_Icc, Pi.le_def, Contains]
  exact ⟨fun h i => ⟨h.1 i,h.2 i⟩,fun h => ⟨fun i => (h i).1,fun i => (h i).2⟩⟩

noncomputable def bonds (B : Box) : Finset Bond :=
  (B.vertices ×ˢ Finset.univ).filter (fun e => B.Contains (step e.1 e.2))

@[simp] theorem mem_bonds (B : Box) (e : Bond) :
    e ∈ B.bonds ↔ B.Contains e.1 ∧ B.Contains (step e.1 e.2) := by
  simp [bonds]

def expand (B : Box) (j : ℕ) : Box where
  lower := fun i => B.lower i-j
  upper := fun i => B.upper i+j
  ordered := fun i => by
    have h : B.lower i ≤ B.upper i := B.ordered i
    dsimp
    omega

def cube (c : Vertex) (m : ℕ) : Box where
  lower := fun i => c i-m
  upper := fun i => c i+m
  ordered := fun i => by dsimp; omega

@[simp] theorem contains_cube (c x : Vertex) (m : ℕ) :
    (cube c m).Contains x ↔ ∀ i, |x i-c i| ≤ (m : ℤ) := by
  simp only [Contains,cube,abs_le]
  constructor <;> intro h i <;> have hi := h i <;> omega

theorem contains_expand (B : Box) (j : ℕ) {x : Vertex} (h : B.Contains x) :
    (B.expand j).Contains x := by
  intro i
  have hi := h i
  change B.lower i-j ≤ x i ∧ x i ≤ B.upper i+j
  omega

@[simp] theorem expand_expand (B : Box) (j k : ℕ) : (B.expand j).expand k = B.expand (j+k) := by
  apply Box.ext <;> funext i <;> simp [expand] <;> omega

def seedCenter (C : Box) (m : ℕ) (z : Vertex) : Vertex :=
  fun i => max (C.lower i+m) (min (C.upper i-m) (z i))

theorem seedCenter_bounds (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) (z : Vertex) (i : Fin 3) :
    C.lower i+m ≤ C.seedCenter m z i ∧ C.seedCenter m z i ≤ C.upper i-m := by
  exact ⟨le_max_left _ _,max_le (hw i) (min_le_left _ _)⟩

theorem seed_contained (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) (z : Vertex) :
    ∀ x, (cube (C.seedCenter m z) m).Contains x → C.Contains x := by
  intro x hx i
  have hb := C.seedCenter_bounds m hw z i
  have hx0 := (contains_cube _ _ _).mp hx i
  rw [abs_le] at hx0
  omega

def translateVertex (c x : Vertex) : Vertex := fun i => x i+c i

def translateBond (c : Vertex) (e : Bond) : Bond := (translateVertex c e.1,e.2)

@[simp] theorem step_translate (c x : Vertex) (i : Fin 3) :
    step (translateVertex c x) i = translateVertex c (step x i) := by
  funext j
  dsimp [step,translateVertex]
  omega

@[simp] theorem cube_contains_translate (c x : Vertex) (m : ℕ) :
    (cube c m).Contains (translateVertex c x) ↔ (cube 0 m).Contains x := by
  simp [contains_cube,translateVertex]

def Within (B : Box) (x y : Vertex) : Prop :=
  NearestNeighbor x y ∧ B.Contains x ∧ B.Contains y

end Box
end CriticalZ3

end OAI


