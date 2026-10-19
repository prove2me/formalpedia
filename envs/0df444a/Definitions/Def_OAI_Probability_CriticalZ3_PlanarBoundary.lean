-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
-- name    : OAI_Probability_CriticalZ3_PlanarBoundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:24:26.547173+00:00
-- url     : https://prove2.me/theorems/bad1d7c4-452f-4e85-b962-c08c9b3db333
-- title:
--   Oriented edge boundaries of finite sets of planar cells
-- statement:
--   The oriented boundary of a finite set $X\subseteq\mathbb Z^2$ of unit cells, with exact conventions.
--
--   1. **Sides.** Each cell has four sides indexed by directions $d\in\{0,1,2,3\}$ (bottom, right, top, left), with outward normals $(0,-1),(1,0),(0,1),(-1,0)$. They are oriented counterclockwise, with tail and head corners given by fixed offsets.
--   2. **Boundary.** The boundary consists of pairs (cell in $X$, direction) whose outward neighbour is not in $X$. At each corner, incoming and outgoing boundary sides correspond, and internal sides pair up with their reverses.
--   3. **Fluxes.** The ray flux counts signed crossings of a dual edge with the positive horizontal ray from $(\frac12,\frac12)$; the line flux counts crossings of the line $y=\frac12$.
--   4. **Codes.** A code of length $n$ is a starting position below $2n$, a starting row and a word of $n$ directions. Following the word from the anchor traces positions and sides:
--   $$
--   \mathrm{pos}_k=\mathrm{anchor}+\sum_{j<k}\bigl(\mathrm{head}(w_j)-\mathrm{tail}(w_j)\bigr).
--   $$
--   Cyclic shifts of indices are also recorded.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Oriented planar edge boundary with exact nearest-neighbor conventions. -/
open Classical
namespace PlanarBoundary
abbrev Point := ℤ × ℤ
abbrev Direction := Fin 4

def tailOffset : Direction → Point := ![(0,0),(1,0),(1,1),(0,1)]
def headOffset : Direction → Point := ![(1,0),(1,1),(0,1),(0,0)]
def outward : Direction → Point := ![(0,-1),(1,0),(0,1),(-1,0)]

abbrev Boundary (X : Finset Point) := {e : Point × Direction // e.1 ∈ X ∧ e.1+outward e.2 ∉ X}

noncomputable instance (X : Finset Point) : Fintype (Boundary X) :=
  Fintype.ofInjective (fun e : Boundary X => (⟨e.val.1,e.property.1⟩,e.val.2) : Boundary X → X × Direction)
    (by intro e e' h; apply Subtype.ext; exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z : X × Direction => z.2) h))

def tail {X : Finset Point} (e : Boundary X) : Point := e.val.1+tailOffset e.val.2
def head {X : Finset Point} (e : Boundary X) : Point := e.val.1+headOffset e.val.2

noncomputable def atVertex (X : Finset Point) (v : Point) (offset : Direction → Point) :
    {e : Boundary X // e.val.1+offset e.val.2 = v} ≃
      {d : Direction // v-offset d ∈ X ∧ v-offset d+outward d ∉ X} where
  toFun e := ⟨e.val.val.2,by
    have he : e.val.val.1 = v-offset e.val.val.2 := eq_sub_iff_add_eq.mpr e.property
    rw [←he]
    exact e.val.property⟩
  invFun d := ⟨⟨(v-offset d.val,d.val),d.property⟩,sub_add_cancel _ _⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (eq_sub_iff_add_eq.mpr e.property).symm
    · rfl
  right_inv d := by rfl

def opposite (d : Direction) : Direction := d+2

theorem opposite_opposite (d : Direction) : opposite (opposite d) = d := by
  fin_cases d <;> decide

theorem outward_opposite (d : Direction) : outward (opposite d) = -outward d := by
  fin_cases d <;> decide

/-- Signed intersections with the positive horizontal ray; dual vertex (a,b)
represents the point (a-1/2,b-1/2). -/
def rayFlux (a b : Point) : ℤ :=
  (if a.2 = 0 ∧ b.2 = 1 ∧ 0 < a.1 then 1 else 0) -
  (if b.2 = 0 ∧ a.2 = 1 ∧ 0 < b.1 then 1 else 0)

def sideFlux (cell : Point) (d : Direction) : ℤ :=
  rayFlux (cell+tailOffset d) (cell+headOffset d)

abbrev FullSide (X : Finset Point) := X × Direction

def isInternal {X : Finset Point} (e : FullSide X) : Prop := e.1.val+outward e.2 ∈ X

noncomputable def internalReverse (X : Finset Point) :
    {e : FullSide X // isInternal e} ≃ {e : FullSide X // isInternal e} := by
  let f : {e : FullSide X // isInternal e} → {e : FullSide X // isInternal e} :=
    fun e => ⟨(⟨e.val.1.val+outward e.val.2,e.property⟩,opposite e.val.2),by
      change e.val.1.val+outward e.val.2+outward (opposite e.val.2) ∈ X
      rw [outward_opposite,add_neg_cancel_right]
      exact e.val.1.property⟩
  have hf : Function.Involutive f := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact by simp [f,outward_opposite]
    · exact opposite_opposite _
  exact ⟨f,f,hf,hf⟩

noncomputable def boundaryEquiv (X : Finset Point) :
    Boundary X ≃ {e : FullSide X // ¬isInternal e} where
  toFun e := ⟨(⟨e.val.1,e.property.1⟩,e.val.2),e.property.2⟩
  invFun e := ⟨(e.val.1.val,e.val.2),e.val.1.property,e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end PlanarBoundary

namespace PlanarBoundary
open Classical

def Neighbor (a b : Point) : Prop := ∃ d : Direction, b = a+outward d

def lineFlux (a b : Point) : ℤ := (if 1 ≤ b.2 then 1 else 0)-(if 1 ≤ a.2 then 1 else 0)

end PlanarBoundary

namespace PlanarBoundary
open Classical

abbrev Code (n : ℕ) := Fin (2*n) × Bool × (Fin n → Direction)

def anchor {n : ℕ} (c : Code n) : Point := (c.1.val,if c.2.1 then 0 else 1)

def wordAt {n : ℕ} (w : Fin n → Direction) (k : ℕ) : Direction :=
  if hk : k < n then w ⟨k,hk⟩ else 0

def displacement (d : Direction) : Point := headOffset d-tailOffset d

def tracePosition {n : ℕ} (c : Code n) (k : ℕ) : Point :=
  anchor c+∑ j ∈ Finset.range k, displacement (wordAt c.2.2 j)

def traceSide {n : ℕ} (c : Code n) (i : Fin n) : Point × Direction :=
  (tracePosition c i.val-tailOffset (c.2.2 i),c.2.2 i)

def shiftIndex {n : ℕ} (hn : 0 < n) (a i : Fin n) : Fin n :=
  ⟨(i.val+a.val)%n,Nat.mod_lt _ hn⟩

end PlanarBoundary

end OAI


