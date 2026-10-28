-- Prove2me | Definitions.Def_OAIQ042S000
-- name    : OAIQ042S000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:30:04.903417+00:00
-- url     : https://prove2.me/theorems/7c96b5eb-c7ed-4a37-837a-a321477fab8f
-- title:
--   Definitions bundle OAIQ042S000 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 550 declarations of OpenAI's Lean: 181 definitions, 9 inductive types or structures, 7 instances and 353 theorems. The definitions and types are `OAI.CriticalStrip.BoundaryPort`, `OAI.CriticalStrip.BoundaryPort.vertex`, `OAI.CriticalStrip.BridgeCut`, `OAI.CriticalStrip.BridgeCut.arch`, `OAI.CriticalStrip.BridgeCut.connector`, `OAI.CriticalStrip.BridgeCut.move`, `OAI.CriticalStrip.BridgePath`, `OAI.CriticalStrip.BridgePath.cut`, `OAI.CriticalStrip.BridgePath.toCutArch`, `OAI.CriticalStrip.CauchyMomentProblem`, `OAI.CriticalStrip.Cell`, `OAI.CriticalStrip.Diagram.C`, `OAI.CriticalStrip.Diagram.ColumnChain.read`, `OAI.CriticalStrip.Diagram.Configuration`, `OAI.CriticalStrip.Diagram.Configuration.padBottom`, `OAI.CriticalStrip.Diagram.Configuration.padTop`, `OAI.CriticalStrip.Diagram.CosineField`, `OAI.CriticalStrip.Diagram.CosineRing`, `OAI.CriticalStrip.Diagram.CutPatch.Shape`, `OAI.CriticalStrip.Diagram.CutPatch.tilePort`, `OAI.CriticalStrip.Diagram.Graph.DrainsAt`, `OAI.CriticalStrip.Diagram.IsPairing`, `OAI.CriticalStrip.Diagram.Laurent`, `OAI.CriticalStrip.Diagram.NonemptyPairing`, `OAI.CriticalStrip.Diagram.Pairing`, `OAI.CriticalStrip.Diagram.Pairing.Adj`, `OAI.CriticalStrip.Diagram.Pairing.BottomOccupiedNonempty`, `OAI.CriticalStrip.Diagram.Pairing.Cross`, `OAI.CriticalStrip.Diagram.Pairing.Occupied`, `OAI.CriticalStrip.Diagram.Pairing.TopOccupiedNonempty`, `OAI.CriticalStrip.Diagram.Pairing.capRemove`, `OAI.CriticalStrip.Diagram.Pairing.capSplice`, `OAI.CriticalStrip.Diagram.Pairing.cutShape`, `OAI.CriticalStrip.Diagram.Pairing.cutToStep`, `OAI.CriticalStrip.Diagram.Pairing.insertCup`, `OAI.CriticalStrip.Diagram.Pairing.map`, `OAI.CriticalStrip.Diagram.Pairing.mapOccupied`, `OAI.CriticalStrip.Diagram.Pairing.moveIntoLowerVacancy`, `OAI.CriticalStrip.Diagram.Pairing.moveIntoVacancy`, `OAI.CriticalStrip.Diagram.Pairing.nonemptyBottomSplit` and 150 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_AugmentedColumn`, `StripMass_AugmentedTail`, `StripMass_Basic`, `StripMass_BottomPadding`, `StripMass_BridgeUnfold`, `StripMass_CauchyMatrices`, `StripMass_CollisionSubstitutions`, `StripMass_CramerBounds`, `StripMass_CutPatch`, `StripMass_CutStateSound`, `StripMass_DeficitBounds`, `StripMass_DiagonalFactors`, `StripMass_FiniteEnds`, `StripMass_FreshGate`, `StripMass_GraphPath`, `StripMass_HalfTurn`, `StripMass_HeightOne`, `StripMass_HoneycombDictionary`, `StripMass_HoneycombTiles`, `StripMass_LastRow`, `StripMass_LaurentBox`, `StripMass_MirrorExterior`, `StripMass_NodalNodes`, `StripMass_NodalRegularity`, `StripMass_PairingDiagrams`, `StripMass_PairingSurgery`, `StripMass_PatchReplacement`, `StripMass_PfaffianSupport`, `StripMass_PhaseAlgebra`, `StripMass_RestrictedDiagrams`, `StripMass_ReversedConvergence`, `StripMass_ScalarBridge`, `StripMass_ScalarFlat`, `StripMass_SewnAssignment`, `StripMass_SidePaths`, `StripMass_Specialization`, `StripMass_SpecializationPolynomial`, `StripMass_StepToCut`, `StripMass_ThreeBoxSplitPolynomial`, `StripMass_TopPadding`, `StripMass_VacuumClosure`, `StripMass_VacuumDegree`.
--
--   **Imports.** It imports the published bundle `Def_CriticalStripMass`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S002`, `OAIQ042S003` and `OAIQ042S004`; the proof of `OAI.CriticalStrip.laguerre_inverseQuarterSum_upper`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_CriticalStripMass

section
-- module Solutions.OAIQ042_SS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory


def omega (x : ℝ) : ℝ := (1 / 2) * Real.sqrt (Real.sqrt ((1 + x) / (2 * x)) - 1)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairingDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset

 
def IsPairing {n : ℕ} (s : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ s, e.1 < e.2) ∧
  (∀ e ∈ s, ∀ f ∈ s, e = f ∨
    (e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)) ∧
  (∀ e ∈ s, ∀ f ∈ s, ¬(e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2))

abbrev Pairing (n : ℕ) := {s : Finset (Fin n × Fin n) // IsPairing s}

instance instFintypePairing (n : ℕ) : Fintype (Pairing n) := by classical exact Subtype.fintype _
instance instDecidableEqPairing (n : ℕ) : DecidableEq (Pairing n) := by classical infer_instance

def empty (n : ℕ) : Pairing n := ⟨∅, by simp [IsPairing]⟩

def Pairing.Adj {n : ℕ} (p : Pairing n) (i j : Fin n) : Prop :=
  (i,j) ∈ p.val ∨ (j,i) ∈ p.val

def Pairing.Occupied {n : ℕ} (p : Pairing n) (i : Fin n) : Prop :=
  ∃ j, p.Adj i j

@[simp] theorem empty_not_adj {n : ℕ} (i j : Fin n) : ¬ (empty n).Adj i j := by
  simp [Pairing.Adj, empty]
@[simp] theorem empty_not_occupied {n : ℕ} (i : Fin n) : ¬ (empty n).Occupied i := by
  simp [Pairing.Occupied]

theorem Pairing.adj_irrefl {n : ℕ} (p : Pairing n) (i : Fin n) : ¬p.Adj i i := by
  rintro (h | h) <;> exact (lt_irrefl i) (p.property.1 _ h)

theorem Pairing.eq_empty_iff {n : ℕ} (p : Pairing n) : p = empty n ↔ ∀ i, ¬p.Occupied i := by
  constructor
  · rintro rfl; simp
  · intro h
    apply Subtype.ext
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact h e.1 ⟨e.2, Or.inl he⟩

inductive Tile where
  | vacant | vertical₀ | vertical₁ | diagonal₀ | diagonal₁
  | cap | cup | verticalPair | capCup
  deriving DecidableEq

instance instFintypeTile : Fintype Tile :=
  ⟨{.vacant, .vertical₀, .vertical₁, .diagonal₀, .diagonal₁, .cap, .cup,
    .verticalPair, .capCup}, by intro t; cases t <;> simp⟩

def Tile.edges : Tile → Finset (Fin 4 × Fin 4)
  | .vacant => ∅
  | .vertical₀ => {(0,2)}
  | .vertical₁ => {(1,3)}
  | .diagonal₀ => {(0,3)}
  | .diagonal₁ => {(1,2)}
  | .cap => {(0,1)}
  | .cup => {(2,3)}
  | .verticalPair => {(0,2),(1,3)}
  | .capCup => {(0,1),(2,3)}

def Tile.Adj (t : Tile) (i j : Fin 4) : Prop := (i,j) ∈ t.edges ∨ (j,i) ∈ t.edges

def Tile.Occupied (t : Tile) (i : Fin 4) : Prop := ∃ j, t.Adj i j

@[simp] theorem Tile.vacant_not_adj (i j : Fin 4) : ¬ Tile.vacant.Adj i j := by
  simp [Tile.Adj, Tile.edges]
@[simp] theorem Tile.vacant_not_occupied (i : Fin 4) : ¬ Tile.vacant.Occupied i := by
  simp [Tile.Occupied]

theorem Tile.eq_vacant_iff (t : Tile) : t = .vacant ↔ ∀ i, ¬t.Occupied i := by
  cases t <;> simp [Tile.Occupied, Tile.Adj, Tile.edges, Fin.forall_fin_succ]

 
structure Weights (𝕜 : Type*) where
  A : 𝕜
  B : 𝕜
  U : 𝕜
  E : 𝕜
  F : 𝕜

def Weights.tile {𝕜 : Type*} [One 𝕜] (w : Weights 𝕜) : Tile → 𝕜
  | .vacant => 1
  | .vertical₀ | .vertical₁ => w.A
  | .diagonal₀ | .diagonal₁ => w.B
  | .cap | .cup => w.U
  | .verticalPair => w.E
  | .capCup => w.F

abbrev Vertex (n : ℕ) := Fin n × Fin 4
abbrev Configuration (n : ℕ) := Fin n → Tile

 

def Wiring {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v w : Vertex n) : Prop :=
  (v.1 = w.1 ∧ (t v.1).Adj v.2 w.2) ∨
  (v.2 = 1 ∧ w.2 = 1 ∧ p.Adj v.1 w.1) ∨
  (v.2 = 3 ∧ w.2 = 0 ∧ v.1.val + 1 = w.1.val ∧ (t v.1).Occupied 3) ∨
  (w.2 = 3 ∧ v.2 = 0 ∧ w.1.val + 1 = v.1.val ∧ (t w.1).Occupied 3)

def Reach {n : ℕ} (p : Pairing n) (t : Configuration n) :=
  Relation.ReflTransGen (Wiring p t)



def deletionWeights {𝕜 : Type*} [Zero 𝕜] [One 𝕜] : Weights 𝕜 := ⟨0,0,1,0,1⟩

def lambda : ℝ := Real.pi / 8


abbrev NonemptyPairing (n : ℕ) := {p : Pairing n // p ≠ empty n}

namespace Pairing

def map {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing n) : Pairing m := by
  classical
  refine ⟨p.val.map (f.toEmbedding.prodMap f.toEmbedding), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_map.mp he with ⟨a, ha, heq⟩
    subst e
    exact f.strictMono (p.property.1 a ha)
  · intro e he g hg
    rcases Finset.mem_map.mp he with ⟨a, ha, heq⟩
    subst e
    rcases Finset.mem_map.mp hg with ⟨b, hb, hgq⟩
    subst g
    rcases p.property.2.1 a ha b hb with h | ⟨h₁,h₂,h₃,h₄⟩
    · exact Or.inl (congrArg _ h)
    · exact Or.inr ⟨by simpa, by simpa, by simpa, by simpa⟩
  · intro e he g hg
    rcases Finset.mem_map.mp he with ⟨a, ha, heq⟩
    subst e
    rcases Finset.mem_map.mp hg with ⟨b, hb, hgq⟩
    subst g
    simpa using p.property.2.2 a ha b hb

def restrict {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing m) : Pairing n := by
  classical
  refine ⟨p.val.preimage (fun e => (f e.1, f e.2))
    (f.toEmbedding.prodMap f.toEmbedding).injective.injOn, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    have h := p.property.1 _ (Finset.mem_preimage.mp he)
    simpa using h
  · intro e he g hg
    have h := p.property.2.1 _ (Finset.mem_preimage.mp he) _ (Finset.mem_preimage.mp hg)
    rcases h with h | ⟨h₁,h₂,h₃,h₄⟩
    · exact Or.inl <| Prod.ext (f.injective (congrArg Prod.fst h))
          (f.injective (congrArg Prod.snd h))
    · exact Or.inr ⟨fun h => h₁ (congrArg f h), fun h => h₂ (congrArg f h),
        fun h => h₃ (congrArg f h), fun h => h₄ (congrArg f h)⟩
  · intro e he g hg
    have h := p.property.2.2 _ (Finset.mem_preimage.mp he) _ (Finset.mem_preimage.mp hg)
    simpa using h

@[simp] theorem restrict_adj {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing m) (i j : Fin n) :
    (p.restrict f).Adj i j ↔ p.Adj (f i) (f j) := by
  classical
  exact or_congr
    (Finset.mem_preimage (hf := (f.toEmbedding.prodMap f.toEmbedding).injective.injOn))
    (Finset.mem_preimage (hf := (f.toEmbedding.prodMap f.toEmbedding).injective.injOn))

@[simp] theorem map_adj_image {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing n) (i j : Fin n) :
    (p.map f).Adj (f i) (f j) ↔ p.Adj i j := by
  classical
  simp [map, Adj, Finset.mem_map]

@[simp] theorem restrict_map {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing n) :
    (p.map f).restrict f = p := by
  classical
  apply Subtype.ext
  ext e
  simp [restrict, map, Finset.mem_map]

 
def padBottom {n : ℕ} (p : Pairing n) : Pairing (n+1) := p.map (Fin.succOrderEmb n)

@[simp] theorem padBottom_adj_succ {n : ℕ} (p : Pairing n) (i j : Fin n) :
    p.padBottom.Adj i.succ j.succ ↔ p.Adj i j := map_adj_image _ _ _ _

@[simp] theorem padBottom_not_adj_zero {n : ℕ} (p : Pairing n) (j : Fin (n+1)) :
    ¬ p.padBottom.Adj 0 j := by
  classical
  simp [padBottom, map, Adj, Finset.mem_map]

@[simp] theorem padBottom_not_adj_zero' {n : ℕ} (p : Pairing n) (j : Fin (n+1)) :
    ¬ p.padBottom.Adj j 0 := by
  classical
  simp [padBottom, map, Adj, Finset.mem_map]

@[simp] theorem padBottom_not_occupied_zero {n : ℕ} (p : Pairing n) :
    ¬ p.padBottom.Occupied 0 := by
  simp [Occupied]

@[simp] theorem padBottom_occupied_succ {n : ℕ} (p : Pairing n) (i : Fin n) :
    p.padBottom.Occupied i.succ ↔ p.Occupied i := by
  simp only [Occupied, Fin.exists_fin_succ, padBottom_adj_succ, padBottom_not_adj_zero',
    false_or]

@[simp] theorem padBottom_empty {n : ℕ} : (empty n).padBottom = empty (n+1) := by
  classical
  apply Subtype.ext
  simp [padBottom, map, empty]

@[simp] theorem padBottom_eq_empty {n : ℕ} (p : Pairing n) :
    p.padBottom = empty (n+1) ↔ p = empty n := by
  simp only [eq_empty_iff, Fin.forall_fin_succ, padBottom_not_occupied_zero,
    padBottom_occupied_succ, not_false_eq_true, true_and]

 
theorem padBottom_restrict {n : ℕ} (p : Pairing (n+1)) (hp : ¬p.Occupied 0) :
    (p.restrict (Fin.succOrderEmb n)).padBottom = p := by
  classical
  apply Subtype.ext
  ext e
  rcases e with ⟨i,j⟩
  induction i using Fin.cases with
  | zero =>
      have hm : (0,j) ∉ p.val := fun h => hp ⟨j, Or.inl h⟩
      simp [padBottom, map, Finset.mem_map, hm]
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          have hm : (i.succ,0) ∉ p.val := fun h => hp ⟨i.succ, Or.inr h⟩
          simp [padBottom, map, Finset.mem_map, hm]
      | succ j => simp [padBottom, map, restrict, Finset.mem_map]

end Pairing

namespace Configuration

def padBottom {n : ℕ} (t : Configuration n) : Configuration (n+1) := Fin.cons .vacant t

@[simp] theorem padBottom_zero {n : ℕ} (t : Configuration n) : t.padBottom 0 = .vacant := rfl
@[simp] theorem padBottom_succ {n : ℕ} (t : Configuration n) (i : Fin n) :
    t.padBottom i.succ = t i := rfl

end Configuration

def vertexSucc {n : ℕ} (v : Vertex n) : Vertex (n+1) := (v.1.succ,v.2)

theorem vertexSucc_injective {n : ℕ} : Function.Injective (@vertexSucc n) := by
  intro v w h
  apply Prod.ext
  · exact Fin.succ_injective n (congrArg (fun v : Vertex (n+1) => v.1) h)
  · exact congrArg (fun v : Vertex (n+1) => v.2) h

theorem wiring_symm {n : ℕ} {p : Pairing n} {t : Configuration n} {v w : Vertex n}
    (h : Wiring p t v w) : Wiring p t w v := by
  rcases h with ⟨h,h'⟩ | ⟨h₁,h₂,h₃⟩ | h | h
  · left
    refine ⟨h.symm, ?_⟩
    simpa only [← h, Tile.Adj, or_comm] using h'
  · right; left
    exact ⟨h₂,h₁,h₃.elim Or.inr Or.inl⟩
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem reach_symm {n : ℕ} {p : Pairing n} {t : Configuration n} {v w : Vertex n}
    (h : Reach p t v w) : Reach p t w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact (Relation.ReflTransGen.single (wiring_symm h)).trans ih

@[simp] theorem wiring_padBottom_zero {n : ℕ} (p : Pairing n) (t : Configuration n)
    (a : Fin 4) (w : Vertex (n+1)) :
    ¬Wiring p.padBottom t.padBottom (0,a) w := by
  simp [Wiring]

@[simp] theorem wiring_padBottom_zero_right {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v : Vertex (n+1)) (b : Fin 4) :
    ¬Wiring p.padBottom t.padBottom v (0,b) :=
  fun h => wiring_padBottom_zero p t b v (wiring_symm h)

@[simp] theorem wiring_padBottom_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v w : Vertex n) :
    Wiring p.padBottom t.padBottom (vertexSucc v) (vertexSucc w) ↔ Wiring p t v w := by
  simp [Wiring, vertexSucc, Nat.add_assoc]

theorem reach_padBottom_image {n : ℕ} (p : Pairing n) (t : Configuration n)
    {v : Vertex n} {w : Vertex (n+1)} (h : Reach p.padBottom t.padBottom (vertexSucc v) w) :
    ∃ z, w = vertexSucc z ∧ Reach p t v z := by
  induction h with
  | refl => exact ⟨v,rfl,Relation.ReflTransGen.refl⟩
  | @tail w z _ hwz ih =>
    obtain ⟨w',rfl,hw'⟩ := ih
    rcases z with ⟨j,b⟩
    induction j using Fin.cases with
    | zero => exact (wiring_padBottom_zero_right p t _ b hwz).elim
    | succ j =>
      exact ⟨(j,b),rfl,hw'.tail ((wiring_padBottom_iff p t _ _).1 hwz)⟩

@[simp] theorem reach_padBottom_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v w : Vertex n) :
    Reach p.padBottom t.padBottom (vertexSucc v) (vertexSucc w) ↔ Reach p t v w := by
  constructor
  · intro h
    obtain ⟨z,hz,hz'⟩ := reach_padBottom_image p t h
    have := vertexSucc_injective hz
    simpa only [this] using hz'
  · exact Relation.ReflTransGen.lift vertexSucc (fun a b h => (wiring_padBottom_iff p t a b).2 h) _ _

@[simp] theorem reach_padBottom_zero_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (a : Fin 4) (w : Vertex (n+1)) :
    Reach p.padBottom t.padBottom (0,a) w ↔ w = (0,a) :=
  Relation.reflTransGen_iff_eq (wiring_padBottom_zero p t a)

@[simp] theorem reach_padBottom_zero_right_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v : Vertex (n+1)) (b : Fin 4) :
    Reach p.padBottom t.padBottom v (0,b) ↔ v = (0,b) := by
  constructor
  · intro h
    exact (reach_padBottom_zero_iff p t b v).1 (reach_symm h)
  · rintro rfl; exact Relation.ReflTransGen.refl

 

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairingSurgery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical
theorem IsPairing.mono {n : ℕ} {s t : Finset (Fin n × Fin n)}
    (h : IsPairing s) (ht : t ⊆ s) : IsPairing t :=
  ⟨fun e he => h.1 e (ht he), fun e he f hf => h.2.1 e (ht he) f (ht hf),
    fun e he f hf => h.2.2 e (ht he) f (ht hf)⟩

namespace Pairing

@[symm] theorem adj_symm {n : ℕ} {p : Pairing n} {i j : Fin n}
    (h : p.Adj i j) : p.Adj j i := h.symm

theorem adj_unique {n : ℕ} {p : Pairing n} {i j k : Fin n}
    (h : p.Adj i j) (g : p.Adj i k) : j = k := by
  rcases h with h | h <;> rcases g with g | g
  · rcases p.property.2.1 _ h _ g with he | ⟨hne, _, _, _⟩
    · exact congrArg Prod.snd he
    · exact (hne rfl).elim
  · rcases p.property.2.1 _ h _ g with he | ⟨_, hne, _, _⟩
    · exact (congrArg Prod.snd he).trans (congrArg Prod.fst he)
    · exact (hne rfl).elim
  · rcases p.property.2.1 _ h _ g with he | ⟨_, _, hne, _⟩
    · exact (congrArg Prod.fst he).trans (congrArg Prod.snd he)
    · exact (hne rfl).elim
  · rcases p.property.2.1 _ h _ g with he | ⟨_, _, _, hne⟩
    · exact congrArg Prod.fst he
    · exact (hne rfl).elim

 
def Cross {α : Type*} [LinearOrder α] (a b c d : α) : Prop :=
  (a < c ∧ c<b ∧ b<d) ∨ (c<a ∧ a<d ∧ d<b) ∨
  (b < c ∧ c<a ∧ a<d) ∨ (c<b ∧ b<d ∧ d<a) ∨
  (a<d ∧ d<b ∧ b < c) ∨ (d<a ∧ a < c ∧ c<b) ∨
  (b<d ∧ d<a ∧ a < c) ∨ (d<b ∧ b < c ∧ c<a)

theorem not_cross {n : ℕ} {p : Pairing n} {a b c d : Fin n}
    (h : p.Adj a b) (g : p.Adj c d) : ¬ Cross a b c d := by
  rcases h with h | h <;> rcases g with g | g
  all_goals
    have hp := p.property.1 _ h
    have hq := p.property.1 _ g
    have hx := p.property.2.2 _ h _ g
    have hy := p.property.2.2 _ g _ h
    dsimp only at hp hq hx hy
    simp only [Cross]
    omega

 
def omitTwo {n : ℕ} (p : Pairing n) (a b : Fin n) : Pairing n :=
  ⟨p.val.filter (fun e => e.1 ≠ a ∧ e.1 ≠ b ∧ e.2 ≠ a ∧ e.2 ≠ b),
    p.property.mono (filter_subset _ _)⟩

@[simp] theorem omitTwo_adj {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    (p.omitTwo a b).Adj i j ↔
      p.Adj i j ∧ i ≠ a ∧ i ≠ b ∧ j ≠ a ∧ j ≠ b := by
  simp only [Adj, omitTwo, mem_filter]
  tauto

theorem not_cross_iff_between {n : ℕ} {a b c d : Fin n}
    (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ¬ Cross a b c d ↔ ((c<a ∧ a<d) ↔ (c<b ∧ b<d)) := by
  simp only [Cross]
  omega

 

theorem cap_no_cross {n : ℕ} {a b x y c d : Fin n}
    (hab : a.val + 1 = b.val) (hcd : c < d) (hc : c ≠ a) (hcb : c ≠ b)
    (hd : d ≠ a) (hdb : d ≠ b)
    (hxc : x ≠ c) (hxd : x ≠ d) (hyc : y ≠ c) (hyd : y ≠ d)
    (hx : ¬ Cross a x c d) (hy : ¬ Cross b y c d) : ¬ Cross x y c d := by
  apply (not_cross_iff_between hcd hxc hxd hyc hyd).mpr
  have hx' := (not_cross_iff_between hcd hc.symm hd.symm hxc hxd).mp hx
  have hy' := (not_cross_iff_between hcd hcb.symm hdb.symm hyc hyd).mp hy
  have h : (c<a ∧ a<d) ↔ (c<b ∧ b<d) := by omega
  exact hx'.symm.trans (h.trans hy')

def orderedEdge {n : ℕ} (x y : Fin n) : Fin n × Fin n := (min x y, max x y)

theorem orderedEdge_lt {n : ℕ} {x y : Fin n} (h : x ≠ y) :
    (orderedEdge x y).1 < (orderedEdge x y).2 := by
  simp only [orderedEdge, min_def, max_def]
  split_ifs <;> omega

theorem occupied_of_mem {n : ℕ} {p : Pairing n} {e : Fin n × Fin n}
    (h : e ∈ p.val) : p.Occupied e.1 ∧ p.Occupied e.2 :=
  ⟨⟨e.2, Or.inl h⟩, ⟨e.1, Or.inr h⟩⟩

theorem cap_new_edge_disjoint {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (hx : p.Adj a x) (hy : p.Adj b y) {e : Fin n × Fin n}
    (he : e ∈ (p.omitTwo a b).val) :
    x ≠ e.1 ∧ x ≠ e.2 ∧ y ≠ e.1 ∧ y ≠ e.2 := by
  have hij : (p.omitTwo a b).Adj e.1 e.2 := Or.inl he
  obtain ⟨he',hca,hcb,hda,hdb⟩ := (omitTwo_adj p a b _ _).mp hij
  refine ⟨?_,?_,?_,?_⟩
  · rintro rfl
    exact hda (adj_unique he' (adj_symm hx))
  · rintro rfl
    exact hca (adj_unique (adj_symm he') (adj_symm hx))
  · rintro rfl
    exact hdb (adj_unique he' (adj_symm hy))
  · rintro rfl
    exact hcb (adj_unique (adj_symm he') (adj_symm hy))

 

def capSplice {n : ℕ} (p : Pairing n) (a b x y : Fin n)
    (hab : a.val + 1 = b.val) (hx : p.Adj a x) (hy : p.Adj b y)
    (hxy : x ≠ y) : Pairing n := by
  refine ⟨insert (orderedEdge x y) (p.omitTwo a b).val, ?_⟩
  refine ⟨?_,?_,?_⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact orderedEdge_lt hxy
    · exact (p.omitTwo a b).property.1 _ he
  · intro e he f hf
    rcases mem_insert.mp he with rfl | he <;>
      rcases mem_insert.mp hf with rfl | hf
    · exact Or.inl rfl
    · right
      have hh := cap_new_edge_disjoint hx hy hf
      simp only [orderedEdge, min_def, max_def]
      split_ifs <;> tauto
    · right
      have hh := cap_new_edge_disjoint hx hy he
      simp only [orderedEdge, min_def, max_def]
      split_ifs <;> tauto
    · exact (p.omitTwo a b).property.2.1 _ he _ hf
  · intro e he f hf
    rcases mem_insert.mp he with rfl | he <;>
      rcases mem_insert.mp hf with rfl | hf
    · simp
    · have hd := cap_new_edge_disjoint hx hy hf
      have hh := (omitTwo_adj p a b _ _).mp (Or.inl hf)
      have hc := cap_no_cross hab ((p.omitTwo a b).property.1 _ hf) hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2
        hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 (not_cross hx hh.1) (not_cross hy hh.1)
      simp only [Cross] at hc
      simp only [orderedEdge, min_def, max_def]
      split_ifs <;> omega
    · have hd := cap_new_edge_disjoint hx hy he
      have hh := (omitTwo_adj p a b _ _).mp (Or.inl he)
      have hc := cap_no_cross hab ((p.omitTwo a b).property.1 _ he) hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2
        hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 (not_cross hx hh.1) (not_cross hy hh.1)
      simp only [Cross] at hc
      simp only [orderedEdge, min_def, max_def]
      split_ifs <;> omega
    · exact (p.omitTwo a b).property.2.2 _ he _ hf


 

 


 

def mapOccupied {n m : ℕ} (p : Pairing n) (f : Fin n ↪ Fin m)
    (hf : ∀ i j, p.Occupied i → p.Occupied j → (f i < f j ↔ i < j)) : Pairing m := by
  refine ⟨p.val.map (f.prodMap f), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a,ha,heq⟩ := mem_map.mp he
    subst e
    apply (hf _ _ (occupied_of_mem ha).1 (occupied_of_mem ha).2).mpr
    exact p.property.1 _ ha
  · intro e he g hg
    obtain ⟨a,ha,heq⟩ := mem_map.mp he
    subst e
    obtain ⟨b,hb,hgq⟩ := mem_map.mp hg
    subst g
    rcases p.property.2.1 _ ha _ hb with rfl | hh
    · exact Or.inl rfl
    · right
      simpa using hh
  · intro e he g hg
    obtain ⟨a,ha,heq⟩ := mem_map.mp he
    subst e
    obtain ⟨b,hb,hgq⟩ := mem_map.mp hg
    subst g
    change ¬ (f a.1 < f b.1 ∧ f b.1 < f a.2 ∧ f a.2 < f b.2)
    rw [hf _ _ (occupied_of_mem ha).1 (occupied_of_mem hb).1,
      hf _ _ (occupied_of_mem hb).1 (occupied_of_mem ha).2,
      hf _ _ (occupied_of_mem ha).2 (occupied_of_mem hb).2]
    exact p.property.2.2 _ ha _ hb

@[simp] theorem mapOccupied_adj {n m : ℕ} (p : Pairing n) (f : Fin n ↪ Fin m)
    (hf : ∀ i j, p.Occupied i → p.Occupied j → (f i < f j ↔ i < j))
    (i j : Fin n) : (mapOccupied p f hf).Adj (f i) (f j) ↔ p.Adj i j := by
  simp [Adj, mapOccupied]

theorem swap_adjacent_order {n : ℕ} {a b i j : Fin n}
    (hab : a.val+1=b.val) (hi : i ≠ b) (hj : j ≠ b) :
    Equiv.swap a b i < Equiv.swap a b j ↔ i<j := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

 
def moveIntoVacancy {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (hb : ¬ p.Occupied b) : Pairing n :=
  p.mapOccupied (Equiv.swap a b).toEmbedding (fun _ _ hi hj =>
    swap_adjacent_order hab (fun h => hb (h ▸ hi)) (fun h => hb (h ▸ hj)))

 

theorem swap_adjacent_order_lower {n : ℕ} {a b i j : Fin n}
    (hab : a.val+1=b.val) (hi : i ≠ a) (hj : j ≠ a) :
    Equiv.swap a b i < Equiv.swap a b j ↔ i<j := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

def moveIntoLowerVacancy {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬ p.Occupied a) : Pairing n :=
  p.mapOccupied (Equiv.swap a b).toEmbedding (fun _ _ hi hj =>
    swap_adjacent_order_lower hab (fun h => ha (h ▸ hi)) (fun h => ha (h ▸ hj)))

 
def insertCup {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val)
    (ha : ¬ p.Occupied a) (hb : ¬ p.Occupied b) : Pairing n := by
  have hlt : a<b := by omega
  have havoid (e : Fin n × Fin n) (he : e ∈ p.val) :
      a ≠ e.1 ∧ a ≠ e.2 ∧ b ≠ e.1 ∧ b ≠ e.2 := by
    have hh := occupied_of_mem he
    exact ⟨fun h => ha (h ▸ hh.1), fun h => ha (h ▸ hh.2),
      fun h => hb (h ▸ hh.1), fun h => hb (h ▸ hh.2)⟩
  refine ⟨insert (a,b) p.val, ?_, ?_, ?_⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact hlt
    · exact p.property.1 _ he
  · intro e he f hf
    rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
    · exact Or.inl rfl
    · exact Or.inr (havoid _ hf)
    · right
      have hh := havoid _ he
      dsimp only
      tauto
    · exact p.property.2.1 _ he _ hf
  · intro e he f hf
    rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
    all_goals try dsimp only
    · omega
    · omega
    · omega
    · exact p.property.2.2 _ he _ hf


 

 


def partner {n : ℕ} (p : Pairing n) (i : Fin n) (hi : p.Occupied i) : Fin n :=
  Classical.choose hi

theorem partner_adj {n : ℕ} (p : Pairing n) (i : Fin n) (hi : p.Occupied i) :
    p.Adj i (p.partner i hi) := Classical.choose_spec hi

theorem adjacent_partners {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y) (hn : ¬ p.Adj a b) :
    x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧ x ≠ y := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro rfl; exact p.adj_irrefl _ hx
  · rintro rfl; exact hn hx
  · rintro rfl; exact hn (adj_symm hy)
  · rintro rfl; exact p.adj_irrefl _ hy
  · rintro rfl
    have := adj_unique (adj_symm hx) (adj_symm hy)
    omega

@[simp] theorem capSplice_adj {n : ℕ} (p : Pairing n) (a b x y : Fin n)
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y) (hxy : x ≠ y)
    (i j : Fin n) :
    (capSplice p a b x y hab hx hy hxy).Adj i j ↔
      (i=x ∧ j=y) ∨ (i=y ∧ j=x) ∨ (p.omitTwo a b).Adj i j := by
  simp only [Adj, capSplice, mem_insert, orderedEdge, min_def, max_def,
    Prod.mk.injEq]
  split_ifs <;> tauto

@[simp] theorem capSplice_occupied {n : ℕ} (p : Pairing n) (a b x y : Fin n)
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y) (hxy : x ≠ y)
    (i : Fin n) :
    (capSplice p a b x y hab hx hy hxy).Occupied i ↔
      i=x ∨ i=y ∨ (p.omitTwo a b).Occupied i := by
  simp only [Occupied, capSplice_adj]
  constructor
  · rintro ⟨j,(⟨h,_⟩|⟨h,_⟩|h)⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j,h⟩)
  · rintro (rfl|rfl|⟨j,h⟩)
    · exact ⟨y,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨x,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · exact ⟨j,Or.inr (Or.inr h)⟩

@[simp] theorem omitTwo_not_occupied_left {n : ℕ} (p : Pairing n) (a b : Fin n) :
    ¬ (p.omitTwo a b).Occupied a := by simp [Occupied]

@[simp] theorem omitTwo_not_occupied_right {n : ℕ} (p : Pairing n) (a b : Fin n) :
    ¬ (p.omitTwo a b).Occupied b := by simp [Occupied]

 

def capRemove {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val)
    (ha : p.Occupied a) (hb : p.Occupied b) (hn : ¬ p.Adj a b) : Pairing n :=
  p.capSplice a b (p.partner a ha) (p.partner b hb) hab
    (p.partner_adj a ha) (p.partner_adj b hb)
    (adjacent_partners hab (p.partner_adj a ha) (p.partner_adj b hb) hn).2.2.2.2

end Pairing
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BottomPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset

namespace Pairing

def nonemptyPadBottom {n : ℕ} (p : NonemptyPairing n) : NonemptyPairing (n+1) :=
  ⟨p.val.padBottom, fun h => p.property ((padBottom_eq_empty _).mp h)⟩

def nonemptyBottomVacantEquiv (n : ℕ) :
    NonemptyPairing n ≃ {p : NonemptyPairing (n+1) // ¬p.val.Occupied 0} where
  toFun p := ⟨nonemptyPadBottom p, p.val.padBottom_not_occupied_zero⟩
  invFun p := ⟨p.val.val.restrict (Fin.succOrderEmb n), by
    intro he
    have hp := padBottom_restrict p.val.val p.property
    rw [he, padBottom_empty] at hp
    exact p.val.property hp.symm⟩
  left_inv p := Subtype.ext (restrict_map _ _)
  right_inv p := Subtype.ext (Subtype.ext (padBottom_restrict _ p.property))

abbrev BottomOccupiedNonempty (n : ℕ) :=
  {p : NonemptyPairing (n+1) // ¬¬p.val.Occupied 0}

def nonemptyBottomSplit (n : ℕ) :
    NonemptyPairing n ⊕ BottomOccupiedNonempty n ≃ NonemptyPairing (n+1) := by
  classical
  exact (Equiv.sumCongr (nonemptyBottomVacantEquiv n) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun p : NonemptyPairing (n+1) => ¬p.val.Occupied 0))

@[simp] theorem nonemptyBottomSplit_inl {n : ℕ} (p : NonemptyPairing n) :
    nonemptyBottomSplit n (.inl p) = nonemptyPadBottom p := rfl

@[simp] theorem nonemptyBottomSplit_inr {n : ℕ} (p : BottomOccupiedNonempty n) :
    nonemptyBottomSplit n (.inr p) = p.val := rfl

end Pairing


namespace Pairing

 
def padTop {n : ℕ} (p : Pairing n) : Pairing (n+1) := p.map Fin.castSuccOrderEmb

@[simp] theorem padTop_adj_castSucc {n : ℕ} (p : Pairing n) (i j : Fin n) :
    p.padTop.Adj i.castSucc j.castSucc ↔ p.Adj i j := map_adj_image _ _ _ _

@[simp] theorem padTop_not_adj_last {n : ℕ} (p : Pairing n) (j : Fin (n+1)) :
    ¬ p.padTop.Adj (Fin.last n) j := by
  classical
  simp [padTop, map, Adj, Finset.mem_map, Fin.castSuccOrderEmb]

@[simp] theorem padTop_not_adj_last' {n : ℕ} (p : Pairing n) (j : Fin (n+1)) :
    ¬ p.padTop.Adj j (Fin.last n) := by
  classical
  simp [padTop, map, Adj, Finset.mem_map, Fin.castSuccOrderEmb]

@[simp] theorem padTop_not_occupied_last {n : ℕ} (p : Pairing n) :
    ¬ p.padTop.Occupied (Fin.last n) := by simp [Occupied]

@[simp] theorem padTop_occupied_castSucc {n : ℕ} (p : Pairing n) (i : Fin n) :
    p.padTop.Occupied i.castSucc ↔ p.Occupied i := by
  simp only [Occupied, Fin.exists_iff_castSucc, padTop_adj_castSucc,
    padTop_not_adj_last', false_or]

@[simp] theorem padTop_empty {n : ℕ} : (empty n).padTop = empty (n+1) := by
  classical
  apply Subtype.ext
  simp [padTop, map, empty]

@[simp] theorem padTop_eq_empty {n : ℕ} (p : Pairing n) :
    p.padTop = empty (n+1) ↔ p = empty n := by
  simp only [eq_empty_iff, Fin.forall_iff_castSucc, padTop_not_occupied_last,
    padTop_occupied_castSucc, not_false_eq_true, true_and]

theorem padTop_restrict {n : ℕ} (p : Pairing (n+1)) (hp : ¬p.Occupied (Fin.last n)) :
    (p.restrict Fin.castSuccOrderEmb).padTop = p := by
  classical
  apply Subtype.ext
  ext e
  rcases e with ⟨i,j⟩
  induction i using Fin.lastCases with
  | last =>
      have hm : (Fin.last n,j) ∉ p.val := fun h => hp ⟨j, Or.inl h⟩
      simp [padTop, map, Finset.mem_map, Fin.castSuccOrderEmb, hm]
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          have hm : (i.castSucc,Fin.last n) ∉ p.val := fun h => hp ⟨i.castSucc, Or.inr h⟩
          simp [padTop, map, Finset.mem_map, Fin.castSuccOrderEmb, hm]
      | cast j => simp [padTop, map, restrict, Finset.mem_map, Fin.castSuccOrderEmb]

end Pairing

namespace Configuration

def padTop {n : ℕ} (t : Configuration n) : Configuration (n+1) := Fin.snoc t .vacant

@[simp] theorem padTop_last {n : ℕ} (t : Configuration n) :
    t.padTop (Fin.last n) = .vacant := Fin.snoc_last _ _
@[simp] theorem padTop_castSucc {n : ℕ} (t : Configuration n) (i : Fin n) :
    t.padTop i.castSucc = t i := Fin.snoc_castSucc _ _ _

end Configuration

def vertexCastSucc {n : ℕ} (v : Vertex n) : Vertex (n+1) := (v.1.castSucc,v.2)

@[simp] theorem wiring_padTop_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v w : Vertex n) :
    Wiring p.padTop t.padTop (vertexCastSucc v) (vertexCastSucc w) ↔ Wiring p t v w := by
  simp [Wiring, vertexCastSucc]


end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TopPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset

namespace Pairing

def nonemptyPadTop {n : ℕ} (p : NonemptyPairing n) : NonemptyPairing (n+1) :=
  ⟨p.val.padTop, fun h => p.property ((padTop_eq_empty _).mp h)⟩

def nonemptyTopVacantEquiv (n : ℕ) :
    NonemptyPairing n ≃ {p : NonemptyPairing (n+1) // ¬p.val.Occupied (Fin.last n)} where
  toFun p := ⟨nonemptyPadTop p, p.val.padTop_not_occupied_last⟩
  invFun p := ⟨p.val.val.restrict Fin.castSuccOrderEmb, by
    intro he
    have hp := padTop_restrict p.val.val p.property
    rw [he, padTop_empty] at hp
    exact p.val.property hp.symm⟩
  left_inv p := Subtype.ext (restrict_map _ _)
  right_inv p := Subtype.ext (Subtype.ext (padTop_restrict _ p.property))

abbrev TopOccupiedNonempty (n : ℕ) :=
  {p : NonemptyPairing (n+1) // ¬¬p.val.Occupied (Fin.last n)}

def nonemptyTopSplit (n : ℕ) :
    NonemptyPairing n ⊕ TopOccupiedNonempty n ≃ NonemptyPairing (n+1) := by
  classical
  exact (Equiv.sumCongr (nonemptyTopVacantEquiv n) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun p : NonemptyPairing (n+1) => ¬p.val.Occupied (Fin.last n)))

@[simp] theorem nonemptyTopSplit_inl {n : ℕ} (p : NonemptyPairing n) :
    nonemptyTopSplit n (.inl p) = nonemptyPadTop p := rfl

@[simp] theorem nonemptyTopSplit_inr {n : ℕ} (p : TopOccupiedNonempty n) :
    nonemptyTopSplit n (.inr p) = p.val := rfl

end Pairing


theorem inlinePrivate0_sin_two_lambda_pos : 0 < Real.sin (2*lambda) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> unfold lambda <;> linarith [Real.pi_pos]

theorem inlinePrivate0_sin_three_lambda_pos : 0 < Real.sin (3*lambda) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> unfold lambda <;> linarith [Real.pi_pos]


def attachEmpty {𝕜 : Type*} [One 𝕜] {n : ℕ}
    (v : NonemptyPairing n → 𝕜) : Pairing n → 𝕜 := by
  classical
  exact fun p => if h : p = empty n then 1 else v ⟨p,h⟩

@[simp] theorem attachEmpty_empty {𝕜 : Type*} [One 𝕜] {n : ℕ}
    (v : NonemptyPairing n → 𝕜) : attachEmpty v (empty n) = 1 := by
  simp [attachEmpty]

@[simp] theorem attachEmpty_nonempty {𝕜 : Type*} [One 𝕜] {n : ℕ}
    (v : NonemptyPairing n → 𝕜) (p : NonemptyPairing n) : attachEmpty v p.val = v p := by
  simp [attachEmpty, p.property]

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RestrictedDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section



abbrev Laurent (n : ℕ) := AddMonoidAlgebra ℂ (Fin n → ℤ)
abbrev SpectralRing (n : ℕ) := Laurent n
abbrev SpectralField (n : ℕ) := FractionRing (SpectralRing n)

def constF (n : ℕ) (z : ℂ) : SpectralField n := algebraMap ℂ (SpectralField n) z

def variableExponent {n : ℕ} (i : Fin n) : Fin n → ℤ :=
  Pi.single i 1

def variableF {n : ℕ} (i : Fin n) : SpectralField n :=
  algebraMap (SpectralRing n) (SpectralField n)
    (AddMonoidAlgebra.single (variableExponent i) 1)

def phase : ℂ := Complex.exp (lambda * Complex.I)
def rho : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)
def d : ℝ := Real.cos (2*lambda)
def C : ℝ := Real.cos lambda

def torusSin {n : ℕ} (z : SpectralField n) : SpectralField n :=
  (z-z⁻¹) / (2*constF n Complex.I)

def torusCos {n : ℕ} (z : SpectralField n) : SpectralField n := (z+z⁻¹)/2

def torusL {n : ℕ} (z : SpectralField n) : SpectralField n :=
  torusSin (constF n phase ^ 2 * z) * torusSin (constF n phase ^ 3 * z)

 
def torusWeights {n : ℕ} (z : SpectralField n) : Weights (SpectralField n) :=
  let q := constF n phase
  let dd := constF n d
  let ell := torusL z
  ⟨dd * torusSin (q^3/z) / ell,
   torusSin z * torusSin (q^3/z) / ell,
   dd * torusSin z / ell,
   torusSin (q^3/z) * torusSin (q^2/z) / ell,
   torusSin (z/q) * torusSin z / ell⟩

 
def spectralWeights (n : ℕ) (i : Fin n) : Weights (SpectralField n) :=
  torusWeights (constF n phase ^ 3 / variableF i)

def spectralA {n : ℕ} (i : Fin n) : SpectralField n :=
  torusCos (variableF i ^ 2 / constF n phase ^ 3)

def discriminant {𝕜 : Type*} [CommRing 𝕜] (dd a b : 𝕜) : 𝕜 :=
  a^2+b^2+2*dd*a*b-dd^2

def pairFirst (n : ℕ) (i : Fin (n/2)) : Fin n := ⟨2*i.val, by have := i.isLt; omega⟩
def pairSecond (n : ℕ) (i : Fin (n/2)) : Fin n := ⟨2*i.val+1, by have := i.isLt; omega⟩

def pfaffian {𝕜 : Type*} [Field 𝕜] {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝕜) : 𝕜 :=
  (2^(n/2) * (Nat.factorial (n/2) : 𝕜))⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) *
      ∏ i : Fin (n/2), M (σ (pairFirst n i)) (σ (pairSecond n i))

 
def augmentedKernel {𝕜 : Type*} [Field 𝕜] {n : ℕ} (dd rr : 𝕜) (a : Fin n → 𝕜) :
    Matrix (Fin (n+n%2)) (Fin (n+n%2)) 𝕜 := fun i j =>
  if hi : i.val < n then
    if hj : j.val < n then
      ((a ⟨i.val,hi⟩ - a ⟨j.val,hj⟩) * (a ⟨i.val,hi⟩ + a ⟨j.val,hj⟩ + rr)) /
        discriminant dd (a ⟨i.val,hi⟩) (a ⟨j.val,hj⟩)
    else 1
  else if j.val < n then -1 else 0


def evalLaurent {n : ℕ} (f : Laurent n) : SpectralField n :=
  algebraMap (SpectralRing n) (SpectralField n) f

def liftLaurent {n : ℕ} (f : Laurent n) : Laurent (n+1) :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain (fun e : Fin n → ℤ => Fin.snoc e 0) f.coeff)

def lastExponent (n : ℕ) (a : ℤ) : Fin (n+1) → ℤ := Fin.snoc (fun _ => 0) a

def lastSine (n : ℕ) : Laurent (n+1) :=
  AddMonoidAlgebra.single (lastExponent n 1) (1/(2*Complex.I)) -
    AddMonoidAlgebra.single (lastExponent n (-1)) (1/(2*Complex.I))



def monomialL {n : ℕ} (e : Fin n → ℤ) (z : ℂ) : Laurent n :=
  AddMonoidAlgebra.single e z

def constantL (n : ℕ) : ℂ →+* Laurent n := AddMonoidAlgebra.singleZeroRingHom

def flatEval (n : ℕ) : Laurent n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) 1

@[simp] theorem flatEval_monomial {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    flatEval n (monomialL e z) = z := by
  simp [flatEval, monomialL, AddMonoidAlgebra.lift_single]

@[simp] theorem flatEval_constant (n : ℕ) (z : ℂ) :
    flatEval n (constantL n z) = z := flatEval_monomial 0 z

@[simp] theorem monomialL_mul {n : ℕ} (e f : Fin n → ℤ) (z w : ℂ) :
    monomialL e z * monomialL f w = monomialL (e+f) (z*w) := by
  exact AddMonoidAlgebra.single_mul_single _ _ _ _

@[simp] theorem monomialL_zero_one (n : ℕ) : monomialL (0 : Fin n → ℤ) 1 = 1 :=
  AddMonoidAlgebra.one_def.symm

theorem map_constantL (n : ℕ) (z : ℂ) :
    algebraMap (SpectralRing n) (SpectralField n) (constantL n z) = constF n z := by
  exact (IsScalarTower.algebraMap_apply ℂ (SpectralRing n) (SpectralField n) z).symm

theorem map_monomialL_inv {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz : z ≠ 0) :
    (algebraMap (SpectralRing n) (SpectralField n) (monomialL e z))⁻¹ =
      algebraMap (SpectralRing n) (SpectralField n) (monomialL (-e) z⁻¹) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul, monomialL_mul]
  simp [hz]

def sineL {n : ℕ} (e : Fin n → ℤ) (z : ℂ) : Laurent n :=
  (monomialL e z - monomialL (-e) z⁻¹) * constantL n ((2*Complex.I)⁻¹)

theorem sineL_map {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz : z ≠ 0) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL e z) =
      torusSin (algebraMap (SpectralRing n) (SpectralField n) (monomialL e z)) := by
  rw [sineL, map_mul, map_sub, map_constantL]
  rw [torusSin, map_monomialL_inv e z hz]
  simp only [constF, map_inv₀, map_mul, map_ofNat, div_eq_mul_inv]

@[simp] theorem flatEval_sine {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    flatEval n (sineL e z) = (z-z⁻¹)/(2*Complex.I) := by
  simp [sineL, div_eq_mul_inv]

theorem phase_ne_zero : phase ≠ 0 := Complex.exp_ne_zero _

theorem phase_pow (k : ℤ) : phase^k = Complex.exp ((k:ℂ)*lambda*Complex.I) := by
  rw [phase, ← Complex.exp_int_mul]
  congr 1
  ring

theorem phase_sine (k : ℤ) : (phase^k-(phase^k)⁻¹)/(2*Complex.I) =
    (Real.sin ((k:ℝ)*lambda) : ℂ) := by
  rw [phase_pow, Complex.ofReal_sin]
  push_cast
  rw [Complex.sin, ← Complex.exp_neg]
  field_simp
  simp [Complex.I_sq]

@[simp] theorem flatEval_sine_phase {n : ℕ} (e : Fin n → ℤ) (k : ℤ) :
    flatEval n (sineL e (phase^k)) = (Real.sin ((k:ℝ)*lambda) : ℂ) := by
  rw [flatEval_sine, phase_sine]

theorem variableF_ne_zero {n : ℕ} (i : Fin n) : variableF i ≠ 0 := by
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  simp [AddMonoidAlgebra.single_eq_zero]

theorem map_monomialL_factor {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    algebraMap (SpectralRing n) (SpectralField n) (monomialL e z) =
      constF n z * algebraMap (SpectralRing n) (SpectralField n) (monomialL e 1) := by
  rw [← map_constantL, ← map_mul]
  congr 1
  change monomialL e z = monomialL 0 z * monomialL e 1
  simp

theorem map_monomialL_variable {n : ℕ} (i : Fin n) (z : ℂ) :
    algebraMap (SpectralRing n) (SpectralField n) (monomialL (variableExponent i) z) =
      constF n z * variableF i := map_monomialL_factor _ z

theorem map_monomialL_neg_variable {n : ℕ} (i : Fin n) (z : ℂ) :
    algebraMap (SpectralRing n) (SpectralField n) (monomialL (-variableExponent i) z) =
      constF n z / variableF i := by
  rw [map_monomialL_factor, div_eq_mul_inv]
  congr 1
  symm
  simpa only [variableF, monomialL, inv_one] using
    map_monomialL_inv (variableExponent i) 1 one_ne_zero

theorem constF_phase_ne_zero (n : ℕ) : constF n phase ≠ 0 := by
  exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr phase_ne_zero

theorem map_sine_variable {n : ℕ} (i : Fin n) (k : ℤ) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL (variableExponent i) (phase^k)) =
      torusSin (constF n phase ^ k * variableF i) := by
  rw [sineL_map _ _ (zpow_ne_zero _ phase_ne_zero), map_monomialL_variable]
  congr 2
  exact map_zpow₀ (algebraMap ℂ (SpectralField n)) phase k

theorem map_sine_neg_variable {n : ℕ} (i : Fin n) (k : ℤ) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL (-variableExponent i) (phase^k)) =
      torusSin (constF n phase ^ k / variableF i) := by
  rw [sineL_map _ _ (zpow_ne_zero _ phase_ne_zero), map_monomialL_neg_variable]
  congr 2
  exact map_zpow₀ (algebraMap ℂ (SpectralField n)) phase k

theorem map_sine_variable_nat {n : ℕ} (i : Fin n) (k : ℕ) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL (variableExponent i) (phase^k)) =
      torusSin (constF n phase ^ k * variableF i) := by
  rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero), map_monomialL_variable]
  congr 2
  exact map_pow (algebraMap ℂ (SpectralField n)) phase k

theorem map_sine_neg_variable_nat {n : ℕ} (i : Fin n) (k : ℕ) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL (-variableExponent i) (phase^k)) =
      torusSin (constF n phase ^ k / variableF i) := by
  rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero), map_monomialL_neg_variable]
  congr 2
  exact map_pow (algebraMap ℂ (SpectralField n)) phase k


 
def rowDenominator {n : ℕ} (i : Fin n) : Laurent n :=
  sineL (-variableExponent i) (phase^(5:ℤ)) *
    sineL (-variableExponent i) (phase^(6:ℤ))

def rowNumerator {n : ℕ} (i : Fin n) : Tile → Laurent n
  | .vacant => rowDenominator i
  | .vertical₀ | .vertical₁ =>
      constantL n d * sineL (variableExponent i) (phase^(0:ℤ))
  | .diagonal₀ | .diagonal₁ =>
      sineL (-variableExponent i) (phase^(3:ℤ)) *
        sineL (variableExponent i) (phase^(0:ℤ))
  | .cap | .cup => constantL n d * sineL (-variableExponent i) (phase^(3:ℤ))
  | .verticalPair =>
      sineL (variableExponent i) (phase^(0:ℤ)) *
        sineL (variableExponent i) (phase^(-1:ℤ))
  | .capCup =>
      sineL (-variableExponent i) (phase^(2:ℤ)) *
        sineL (-variableExponent i) (phase^(3:ℤ))

theorem inlinePrivate0_sin_five_lambda : Real.sin (5*lambda) = Real.sin (3*lambda) := by
  rw [show 5*lambda = Real.pi-3*lambda by unfold lambda; ring, Real.sin_pi_sub]
theorem inlinePrivate0_sin_six_lambda : Real.sin (6*lambda) = Real.sin (2*lambda) := by
  rw [show 6*lambda = Real.pi-2*lambda by unfold lambda; ring, Real.sin_pi_sub]

theorem flatEval_rowDenominator {n : ℕ} (i : Fin n) :
    flatEval n (rowDenominator i) =
      (Real.sin (3*lambda) : ℂ) * (Real.sin (2*lambda) : ℂ) := by
  rw [rowDenominator, map_mul, flatEval_sine_phase, flatEval_sine_phase]
  norm_num only [Int.cast_ofNat]
  rw [inlinePrivate0_sin_five_lambda, inlinePrivate0_sin_six_lambda]

theorem flatEval_rowDenominator_ne_zero {n : ℕ} (i : Fin n) :
    flatEval n (rowDenominator i) ≠ 0 := by
  rw [flatEval_rowDenominator]
  exact mul_ne_zero (by exact_mod_cast ne_of_gt inlinePrivate0_sin_three_lambda_pos)
    (by exact_mod_cast ne_of_gt inlinePrivate0_sin_two_lambda_pos)

theorem rowDenominator_map {n : ℕ} (i : Fin n) :
    algebraMap (SpectralRing n) (SpectralField n) (rowDenominator i) =
      torusL (constF n phase ^ 3 / variableF i) := by
  simp only [rowDenominator, map_mul, zpow_ofNat, map_sine_neg_variable_nat, torusL]
  congr 1 <;> congr 1 <;> ring

theorem rowDenominator_map_ne_zero {n : ℕ} (i : Fin n) :
    algebraMap (SpectralRing n) (SpectralField n) (rowDenominator i) ≠ 0 := by
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro h
  exact flatEval_rowDenominator_ne_zero i (by rw [h, map_zero])

theorem rowNumerator_map {n : ℕ} (i : Fin n) (t : Tile) :
    algebraMap (SpectralRing n) (SpectralField n) (rowNumerator i t) =
      algebraMap (SpectralRing n) (SpectralField n) (rowDenominator i) *
        (spectralWeights n i).tile t := by
  let q : SpectralField n := constF n phase
  let x : SpectralField n := variableF i
  have hq : q ≠ 0 := constF_phase_ne_zero n
  have hx : x ≠ 0 := variableF_ne_zero i
  have h₃ : q^3 / (q^3/x) = x := by field_simp
  have h₂ : q^2 / (q^3/x) = q⁻¹*x := by field_simp
  have h₁ : q^3/x/q = q^2/x := by field_simp
  have hL : torusL (q^3/x) ≠ 0 := by
    simpa only [rowDenominator_map] using rowDenominator_map_ne_zero i
  dsimp only [q, x] at h₃ h₂ h₁ hL
  cases t <;>
    simp only [rowNumerator, map_mul, map_constantL,
      zpow_ofNat, map_sine_variable_nat, map_sine_neg_variable_nat, zpow_neg_one,
      rowDenominator_map, spectralWeights, torusWeights, Weights.tile]
  all_goals try simp only [h₃, h₂, h₁, mul_one]
  all_goals field_simp
  rw [sineL_map _ _ (one_div_ne_zero phase_ne_zero), map_monomialL_variable]
  simp only [constF, one_div, map_inv₀]
  rw [mul_comm ((algebraMap ℂ (SpectralField n)) phase)⁻¹, ← div_eq_mul_inv]



end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LastRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset


def lastValue {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (b s : L) (P : Pairing (n+1) → Polynomial K)
    (p : Pairing (n+1)) : L := by
  classical
  exact if p.Occupied (Fin.last n) then s * (P p).eval₂ f b else (P p).eval₂ f b



end

 

 

noncomputable section

 
def c : ℝ := Real.cos (3*lambda)

theorem phase_cosine (k : ℤ) : (phase^k+(phase^k)⁻¹)/2 =
    (Real.cos ((k:ℝ)*lambda) : ℂ) := by
  rw [phase_pow, Complex.ofReal_cos]
  push_cast
  rw [Complex.cos, ← Complex.exp_neg]
  simp only [neg_mul]

theorem phase_eight : phase^(8:ℕ) = -1 := by
  have h := phase_pow 8
  norm_num only [zpow_ofNat, Int.cast_ofNat] at h
  rw [h]
  convert Complex.exp_pi_mul_I using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  simp [lambda]
  ring

theorem constF_phase_eight (n : ℕ) : constF n phase ^ 8 = -1 := by
  rw [constF, ← map_pow, phase_eight, map_neg, map_one]

@[simp] theorem torusCos_inv {n : ℕ} (z : SpectralField n) :
    torusCos z⁻¹ = torusCos z := by simp [torusCos, add_comm]

@[simp] theorem torusCos_neg {n : ℕ} (z : SpectralField n) :
    torusCos (-z) = -torusCos z := by simp [torusCos]; ring

theorem torusCos_phase_pow (n : ℕ) (k : ℕ) :
    torusCos (constF n phase ^ k) = constF n (Real.cos ((k:ℝ)*lambda)) := by
  have h := congrArg (constF n) (phase_cosine (k:ℤ))
  simpa [torusCos, constF, map_ofNat] using h

theorem torusSin_product {n : ℕ} (z w : SpectralField n) (hz : z ≠ 0) (hw : w ≠ 0) :
    2 * torusSin z * torusSin w = torusCos (z/w) - torusCos (z*w) := by
  have hi : (constF n Complex.I)^2 = -1 := by
    simp only [constF, ← map_pow, Complex.I_sq, map_neg, map_one]
  have hI : constF n Complex.I ≠ 0 := by
    exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero
  unfold torusSin torusCos
  field_simp
  ring_nf
  rw [hi]
  ring

 
theorem spectral_sine_pair {n : ℕ} (i : Fin n) :
    2 * torusSin (variableF i) * torusSin (constF n phase ^ 3 / variableF i) =
      spectralA i - constF n c := by
  rw [torusSin_product _ _ (variableF_ne_zero i)
    (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero i))]
  have h₁ : variableF i / (constF n phase ^ 3 / variableF i) =
      variableF i ^ 2 / constF n phase ^ 3 := by field_simp
  have h₂ : variableF i * (constF n phase ^ 3 / variableF i) = constF n phase ^ 3 := by
    field_simp [variableF_ne_zero i]
  rw [h₁, h₂, torusCos_phase_pow]
  rfl

 
theorem twice_rowDenominator {n : ℕ} (i : Fin n) :
    2 * evalLaurent (rowDenominator i) = spectralA i + constF n C := by
  rw [evalLaurent, rowDenominator_map, torusL]
  have hq := constF_phase_ne_zero n
  have hx := variableF_ne_zero i
  have h₅ : constF n phase ^ 2 * (constF n phase ^ 3 / variableF i) =
      constF n phase ^ 5 / variableF i := by ring
  have h₆ : constF n phase ^ 3 * (constF n phase ^ 3 / variableF i) =
      constF n phase ^ 6 / variableF i := by ring
  rw [h₅, h₆, ← mul_assoc, torusSin_product _ _
    (div_ne_zero (pow_ne_zero _ hq) hx) (div_ne_zero (pow_ne_zero _ hq) hx)]
  have hdiv : (constF n phase ^ 5 / variableF i) / (constF n phase ^ 6 / variableF i) =
      (constF n phase)⁻¹ := by field_simp
  have hmul : (constF n phase ^ 5 / variableF i) * (constF n phase ^ 6 / variableF i) =
      -(variableF i ^ 2 / constF n phase ^ 3)⁻¹ := by
    have h := constF_phase_eight n
    field_simp
    exact h
  rw [hdiv, hmul, torusCos_inv, torusCos_neg, torusCos_inv,
    ← pow_one (constF n phase), torusCos_phase_pow]
  simp only [Nat.cast_one, one_mul, sub_neg_eq_add]
  rw [add_comm]
  simp [spectralA, C]

 
def clearedSpectralRow {n : ℕ} (i : Fin n) (t : Tile) : SpectralField n :=
  (spectralA i + constF n C) * (spectralWeights n i).tile t

theorem clearedSpectralRow_eq {n : ℕ} (i : Fin n) (t : Tile) :
    clearedSpectralRow i t = 2 * evalLaurent (rowNumerator i t) := by
  rw [clearedSpectralRow, ← twice_rowDenominator]
  change (2 * algebraMap (SpectralRing n) (SpectralField n) (rowDenominator i)) * _ = _
  rw [mul_assoc, ← rowNumerator_map]
  rfl

@[simp] theorem clearedSpectralRow_vacant {n : ℕ} (i : Fin n) :
    clearedSpectralRow i .vacant = spectralA i + constF n C := by
  simp [clearedSpectralRow, Weights.tile]

@[simp] theorem clearedSpectralRow_cap {n : ℕ} (i : Fin n) :
    clearedSpectralRow i .cap = 2 * constF n d *
      torusSin (constF n phase ^ 3 / variableF i) := by
  rw [clearedSpectralRow_eq]
  simp only [evalLaurent, rowNumerator, map_mul, map_constantL, zpow_ofNat,
    map_sine_neg_variable_nat, mul_assoc]

@[simp] theorem clearedSpectralRow_vertical₀ {n : ℕ} (i : Fin n) :
    clearedSpectralRow i .vertical₀ = 2 * constF n d * torusSin (variableF i) := by
  rw [clearedSpectralRow_eq]
  simp only [evalLaurent, rowNumerator, map_mul, map_constantL]
  rw [map_sine_variable i (0:ℤ)]
  simp only [zpow_zero, one_mul, mul_assoc]

@[simp] theorem clearedSpectralRow_diagonal₁ {n : ℕ} (i : Fin n) :
    clearedSpectralRow i .diagonal₁ = spectralA i - constF n c := by
  rw [clearedSpectralRow_eq]
  simp only [evalLaurent, rowNumerator, map_mul]
  rw [map_sine_variable i (0:ℤ), map_sine_neg_variable i (3:ℤ)]
  simp only [zpow_ofNat, pow_zero, one_mul]
  rw [mul_comm (torusSin _), ← mul_assoc, spectral_sine_pair]


 

 


 
def appendZero (n : ℕ) : (Fin n → ℤ) →+ (Fin (n+1) → ℤ) where
  toFun e := Fin.snoc e 0
  map_zero' := by
    ext i
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp

def liftLaurentHom (n : ℕ) : Laurent n →+* Laurent (n+1) :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (appendZero n)

@[simp] theorem liftLaurentHom_apply {n : ℕ} (p : Laurent n) :
    liftLaurentHom n p = liftLaurent p := rfl

theorem appendZero_injective (n : ℕ) : Function.Injective (appendZero n) := by
  intro e f h
  funext i
  simpa [appendZero] using congrFun h i.castSucc

theorem liftLaurent_injective (n : ℕ) : Function.Injective (@liftLaurent n) :=
  AddMonoidAlgebra.mapDomain_injective (appendZero_injective n)

 

def liftSpectral (n : ℕ) : SpectralField n →+* SpectralField (n+1) :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))).comp (liftLaurentHom n))
    ((IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))).comp
      (liftLaurent_injective n))

@[simp] theorem liftSpectral_evalLaurent {n : ℕ} (p : Laurent n) :
    liftSpectral n (evalLaurent p) = evalLaurent (liftLaurent p) := by
  exact IsFractionRing.lift_algebraMap _ _

@[simp] theorem liftLaurent_monomial {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    liftLaurent (monomialL e z) = monomialL (Fin.snoc e 0) z := by
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem liftLaurent_const {n : ℕ} (z : ℂ) :
    liftLaurent (constantL n z) = constantL (n+1) z := by
  change liftLaurent (monomialL 0 z) = monomialL 0 z
  rw [liftLaurent_monomial]
  congr 1
  exact (appendZero n).map_zero

@[simp] theorem liftSpectral_const (n : ℕ) (z : ℂ) :
    liftSpectral n (constF n z) = constF (n+1) z := by
  have hc : constF n z = evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc, liftSpectral_evalLaurent, liftLaurent_const]
  exact map_constantL (n+1) z

@[simp] theorem appendZero_variable {n : ℕ} (i : Fin n) :
    Fin.snoc (variableExponent i) 0 = variableExponent i.castSucc := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [variableExponent]
  · simp only [Fin.snoc_castSucc, variableExponent, Pi.single_apply,
      Fin.castSucc_inj]

@[simp] theorem liftSpectral_variable {n : ℕ} (i : Fin n) :
    liftSpectral n (variableF i) = variableF i.castSucc := by
  change liftSpectral n (evalLaurent (monomialL (variableExponent i) 1)) = _
  rw [liftSpectral_evalLaurent, liftLaurent_monomial, appendZero_variable]
  rfl

@[simp] theorem liftSpectral_torusSin {n : ℕ} (z : SpectralField n) :
    liftSpectral n (torusSin z) = torusSin (liftSpectral n z) := by
  simp [torusSin, map_div₀, map_inv₀, map_ofNat]

@[simp] theorem liftSpectral_torusCos {n : ℕ} (z : SpectralField n) :
    liftSpectral n (torusCos z) = torusCos (liftSpectral n z) := by
  simp [torusCos, map_div₀, map_inv₀, map_ofNat]

@[simp] theorem liftSpectral_spectralA {n : ℕ} (i : Fin n) :
    liftSpectral n (spectralA i) = spectralA i.castSucc := by
  simp [spectralA, map_div₀]

@[simp] theorem evalLaurent_lastSine (n : ℕ) :
    evalLaurent (lastSine n) = torusSin (variableF (Fin.last n)) := by
  have he : lastExponent n 1 = variableExponent (Fin.last n) := by
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [lastExponent, variableExponent]
    · simp [lastExponent, variableExponent]
  have he' : lastExponent n (-1) = -variableExponent (Fin.last n) := by
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [lastExponent, variableExponent]
    · simp [lastExponent, variableExponent]
  unfold lastSine
  change evalLaurent (monomialL (lastExponent n 1) _ - monomialL (lastExponent n (-1)) _) = _
  rw [he, he']
  simp only [evalLaurent, map_sub, map_monomialL_variable, map_monomialL_neg_variable]
  simp only [constF, map_div₀, map_mul, map_one, map_ofNat]
  simp only [torusSin, constF, div_eq_mul_inv]
  ring


 

 

open scoped Classical

namespace Weights
variable {K L : Type*} [CommRing K] [CommRing L]
def map (f : K →+* L) (w : Weights K) : Weights L :=
  ⟨f w.A,f w.B,f w.U,f w.E,f w.F⟩
@[simp] lemma map_tile (f : K →+* L) (w : Weights K) (t : Tile) :
    (w.map f).tile t=f (w.tile t) := by cases t <;> simp [map,tile]
end Weights

end

 

 

noncomputable section
open scoped Classical

def permExponent {n : ℕ} (σ : Equiv.Perm (Fin n)) : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun e := e ∘ σ.symm
  map_zero' := rfl
  map_add' _ _ := rfl

lemma permExponent_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permExponent σ) := by
  intro e f he
  funext i
  simpa [permExponent] using congrFun he (σ i)

def permLaurent {n : ℕ} (σ : Equiv.Perm (Fin n)) : Laurent n →+* Laurent n :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (permExponent σ)

lemma permLaurent_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permLaurent σ) :=
  AddMonoidAlgebra.mapDomain_injective (permExponent_injective σ)

def permSpectral {n : ℕ} (σ : Equiv.Perm (Fin n)) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing n) (SpectralField n)).comp (permLaurent σ))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (permLaurent_injective σ))

@[simp] lemma permSpectral_evalLaurent {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Laurent n) :
    permSpectral σ (evalLaurent f)=evalLaurent (permLaurent σ f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma permLaurent_monomial {n : ℕ} (σ : Equiv.Perm (Fin n))
    (e : Fin n → ℤ) (z : ℂ) : permLaurent σ (monomialL e z)=
      monomialL (e ∘ σ.symm) z := AddMonoidAlgebra.mapDomain_single

@[simp] lemma permSpectral_const {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : ℂ) :
    permSpectral σ (constF n z)=constF n z := by
  have hc : constF n z=evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,permSpectral_evalLaurent]
  change evalLaurent (permLaurent σ (monomialL 0 z))=evalLaurent (monomialL 0 z)
  rw [permLaurent_monomial]
  rfl

@[simp] lemma permSpectral_variable {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (variableF i)=variableF (σ i) := by
  change permSpectral σ (evalLaurent (monomialL (variableExponent i) 1))=_
  rw [permSpectral_evalLaurent,permLaurent_monomial]
  congr 2
  funext j
  by_cases hij : j=σ i
  · subst j; simp [variableExponent]
  · have hne : σ.symm j≠i := fun he => hij (by simpa using congrArg σ he)
    simp [variableExponent,Function.comp_apply,hij,hne]

@[simp] lemma permSpectral_torusSin {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : SpectralField n) :
    permSpectral σ (torusSin z)=torusSin (permSpectral σ z) := by
  simp [torusSin,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma permSpectral_torusCos {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : SpectralField n) :
    permSpectral σ (torusCos z)=torusCos (permSpectral σ z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma permSpectral_torusL {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : SpectralField n) :
    permSpectral σ (torusL z)=torusL (permSpectral σ z) := by simp [torusL]

@[simp] lemma permSpectral_torusWeights {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : SpectralField n) :
    (torusWeights z).map (permSpectral σ)=torusWeights (permSpectral σ z) := by
  simp [Weights.map,torusWeights,map_div₀]

@[simp] lemma permSpectral_spectralWeights {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (spectralWeights n i).map (permSpectral σ)=spectralWeights n (σ i) := by
  simp [spectralWeights,map_div₀]

@[simp] lemma permSpectral_spectralA {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (spectralA i)=spectralA (σ i) := by simp [spectralA,map_div₀]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

 

theorem pfaffian_reindex {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (τ : Equiv.Perm (Fin n)) :
    pfaffian (fun i j => M (τ i) (τ j)) =
      (Equiv.Perm.sign τ : ℤ) * pfaffian M := by
  classical
  unfold pfaffian
  have hsign : ((Equiv.Perm.sign τ : ℤ) : K) *
      ((Equiv.Perm.sign τ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> simp [hs]
  have hs : (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : K) *
      ∏ i : Fin (n/2), M (τ (σ (pairFirst n i))) (τ (σ (pairSecond n i)))) =
      ((Equiv.Perm.sign τ : ℤ) : K) *
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : K) *
        ∏ i : Fin (n/2), M (σ (pairFirst n i)) (σ (pairSecond n i)) := by
    rw [mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ ?_
    intro σ
    change _ = ((Equiv.Perm.sign τ : ℤ) : K) *
      (((Equiv.Perm.sign (τ*σ) : ℤ) : K) *
        ∏ i : Fin (n/2), M ((τ*σ) (pairFirst n i)) ((τ*σ) (pairSecond n i)))
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, map_mul, Units.val_mul, Int.cast_mul]
    rw [← mul_assoc, ← mul_assoc, hsign, one_mul]
  rw [hs]
  ring

 
abbrev UpperPair (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

instance instFintypeUpperPair (n : ℕ) : Fintype (UpperPair n) := by classical exact Subtype.fintype _

 
def upperPair {n : ℕ} (i j : Fin n) (h : i ≠ j) : UpperPair n :=
  if hij : i < j then ⟨(i,j),hij⟩ else ⟨(j,i),lt_of_le_of_ne (le_of_not_gt hij) h.symm⟩

theorem pairFirst_ne_pairSecond {n : ℕ} (i j : Fin (n/2)) :
    pairFirst n i ≠ pairSecond n j := by
  intro h
  have := congrArg Fin.val h
  simp only [pairFirst, pairSecond] at this
  omega

def permutationPair {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n/2)) : UpperPair n :=
  upperPair (σ (pairFirst n i)) (σ (pairSecond n i))
    (σ.injective.ne (pairFirst_ne_pairSecond i i))


def selectedPairs {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (UpperPair n) :=
  Finset.univ.image (permutationPair σ)

 

def clearedPfaffianTerm {R : Type*} [CommRing R] {n : ℕ}
    (N D : Matrix (Fin n) (Fin n) R) (σ : Equiv.Perm (Fin n)) : R :=
  (∏ i : Fin (n/2), N (σ (pairFirst n i)) (σ (pairSecond n i))) *
    ∏ e ∈ (selectedPairs σ)ᶜ, D e.val.1 e.val.2

def clearedPfaffian {R : Type*} [CommRing R] {n : ℕ} (t : R)
    (N D : Matrix (Fin n) (Fin n) R) : R :=
  t * ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) * clearedPfaffianTerm N D σ

@[simp] theorem map_clearedPfaffianTerm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (N D : Matrix (Fin n) (Fin n) R) (σ : Equiv.Perm (Fin n)) :
    f (clearedPfaffianTerm N D σ) = clearedPfaffianTerm (N.map f) (D.map f) σ := by
  simp [clearedPfaffianTerm, Matrix.map_apply]

@[simp] theorem map_clearedPfaffian {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (t : R) (N D : Matrix (Fin n) (Fin n) R) :
    f (clearedPfaffian t N D) = clearedPfaffian (f t) (N.map f) (D.map f) := by
  simp [clearedPfaffian]


 

 


 

def augmentedNumerator {R : Type*} [CommRing R] {n : ℕ}
    (rr : R) (a : Fin n → R) : Matrix (Fin (n+n%2)) (Fin (n+n%2)) R := fun i j =>
  if hi : i.val < n then
    if hj : j.val < n then
      (a ⟨i.val,hi⟩-a ⟨j.val,hj⟩)*(a ⟨i.val,hi⟩+a ⟨j.val,hj⟩+rr)
    else 1
  else if j.val < n then -1 else 0

def augmentedDenominator {R : Type*} [CommRing R] {n : ℕ}
    (dd : R) (a : Fin n → R) : Matrix (Fin (n+n%2)) (Fin (n+n%2)) R := fun i j =>
  if hi : i.val < n then
    if hj : j.val < n then discriminant dd (a ⟨i.val,hi⟩) (a ⟨j.val,hj⟩)
    else 1
  else 1

theorem discriminant_symm {R : Type*} [CommRing R] (dd a b : R) :
    discriminant dd a b = discriminant dd b a := by unfold discriminant; ring

theorem augmentedDenominator_symm {R : Type*} [CommRing R] {n : ℕ}
    (dd : R) (a : Fin n → R) (i j : Fin (n+n%2)) :
    augmentedDenominator dd a i j = augmentedDenominator dd a j i := by
  unfold augmentedDenominator
  split_ifs <;> try rfl
  exact discriminant_symm _ _ _

theorem augmentedKernel_eq {K : Type*} [Field K] {n : ℕ}
    (dd rr : K) (a : Fin n → K) (i j : Fin (n+n%2)) :
    augmentedKernel dd rr a i j =
      augmentedNumerator rr a i j / augmentedDenominator dd a i j := by
  unfold augmentedKernel augmentedNumerator augmentedDenominator
  split_ifs <;> simp

@[simp] theorem map_augmentedNumerator {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (rr : R) (a : Fin n → R) :
    (augmentedNumerator rr a).map f = augmentedNumerator (f rr) (fun i => f (a i)) := by
  ext i j
  simp only [Matrix.map_apply, augmentedNumerator]
  split_ifs <;> simp

@[simp] theorem map_augmentedDenominator {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (dd : R) (a : Fin n → R) :
    (augmentedDenominator dd a).map f = augmentedDenominator (f dd) (fun i => f (a i)) := by
  ext i j
  simp only [Matrix.map_apply, augmentedDenominator]
  split_ifs <;> simp [discriminant, map_ofNat]

abbrev CosineRing (n : ℕ) := MvPolynomial (Fin n) ℂ
abbrev CosineField (n : ℕ) := FractionRing (CosineRing n)

def cosineVar {n : ℕ} (i : Fin n) : CosineField n :=
  algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X i)

def cosineConst (n : ℕ) (z : ℂ) : CosineField n :=
  algebraMap (CosineRing n) (CosineField n) (MvPolynomial.C z)

 

def scalarNumerator (n : ℕ) (dd rr : ℂ) : CosineRing n :=
  clearedPfaffian (MvPolynomial.C ((2^((n+n%2)/2) *
    (Nat.factorial ((n+n%2)/2) : ℂ))⁻¹))
      (augmentedNumerator (MvPolynomial.C rr) MvPolynomial.X)
      (augmentedDenominator (MvPolynomial.C dd) MvPolynomial.X)

theorem discriminant_cosineVar_ne {n : ℕ} (dd : ℂ) (hdd : dd ≠ 0) (i j : Fin n) :
    discriminant (cosineConst n dd) (cosineVar i) (cosineVar j) ≠ 0 := by
  change discriminant (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.C dd))
    (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X i))
    (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X j)) ≠ 0
  have hmap : discriminant (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.C dd))
      (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X i))
      (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X j)) =
      algebraMap (CosineRing n) (CosineField n)
        (discriminant (MvPolynomial.C dd) (MvPolynomial.X i) (MvPolynomial.X j)) := by
    simp [discriminant, map_ofNat]
  rw [hmap]
  apply (map_ne_zero_iff _ (IsFractionRing.injective (CosineRing n) (CosineField n))).mpr
  intro h
  have hh := congrArg (MvPolynomial.eval (fun _ : Fin n => (0 : ℂ))) h
  simp [discriminant, hdd] at hh







def upperPairMap {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : UpperPair n) : UpperPair n :=
  upperPair (σ e.val.1) (σ e.val.2) (σ.injective.ne (ne_of_lt e.property))







def augmentedPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+n%2)) :=
  σ.viaEmbedding (Fin.castAddEmb (n%2))

@[simp] theorem augmentedPerm_real {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    augmentedPerm σ (i.castAdd (n%2)) = (σ i).castAdd (n%2) :=
  Equiv.Perm.viaEmbedding_apply σ (Fin.castAddEmb (n%2)) i

theorem augmentedPerm_extra {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin (n+n%2)) (hi : ¬ i.val < n) : augmentedPerm σ i = i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨j,hj⟩
  apply hi
  rw [← hj]
  exact j.isLt

theorem augmentedPerm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n+n%2)) :
    augmentedPerm σ i = if hi : i.val < n then (σ ⟨i.val,hi⟩).castAdd (n%2) else i := by
  split_ifs with hi
  · exact augmentedPerm_real σ ⟨i.val,hi⟩
  · exact augmentedPerm_extra σ i hi

@[simp] theorem augmentedPerm_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (augmentedPerm σ) = Equiv.Perm.sign σ := by
  classical
  unfold augmentedPerm Equiv.Perm.viaEmbedding
  exact @Equiv.Perm.sign_extendDomain _ _ _ _ _ _ σ _
    (fun a => Classical.propDecidable _) _

theorem augmentedNumerator_reindex {R : Type*} [CommRing R] {n : ℕ}
    (rr : R) (a : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    augmentedNumerator rr (a ∘ σ) =
      fun i j => augmentedNumerator rr a (augmentedPerm σ i) (augmentedPerm σ j) := by
  ext i j
  by_cases hi : i.val < n <;> by_cases hj : j.val < n <;>
    simp [augmentedNumerator, augmentedPerm_apply, hi, hj, Function.comp_apply]

theorem augmentedDenominator_reindex {R : Type*} [CommRing R] {n : ℕ}
    (dd : R) (a : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    augmentedDenominator dd (a ∘ σ) =
      fun i j => augmentedDenominator dd a (augmentedPerm σ i) (augmentedPerm σ j) := by
  ext i j
  by_cases hi : i.val < n <;> by_cases hj : j.val < n <;>
    simp [augmentedDenominator, augmentedPerm_apply, hi, hj, Function.comp_apply]

theorem augmentedKernel_reindex {K : Type*} [Field K] {n : ℕ}
    (dd rr : K) (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    augmentedKernel dd rr (a ∘ σ) =
      fun i j => augmentedKernel dd rr a (augmentedPerm σ i) (augmentedPerm σ j) := by
  ext i j
  rw [augmentedKernel_eq, augmentedKernel_eq, augmentedNumerator_reindex,
    augmentedDenominator_reindex]



def cosineCoeff (n : ℕ) : ℂ →+* CosineField n :=
  (algebraMap (CosineRing n) (CosineField n)).comp MvPolynomial.C

@[simp] theorem cosineCoeff_apply (n : ℕ) (z : ℂ) : cosineCoeff n z = cosineConst n z := rfl

theorem eval₂_cosineCoeff (n : ℕ) :
    MvPolynomial.eval₂Hom (cosineCoeff n) cosineVar =
      algebraMap (CosineRing n) (CosineField n) := by
  ext a <;> simp [cosineCoeff, cosineVar]



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DiagonalFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

 

def separateCosine {n : ℕ} (i : Fin n) :
    CosineRing n ≃ₐ[ℂ] Polynomial (MvPolynomial {k : Fin n // k ≠ i} ℂ) :=
  (MvPolynomial.renameEquiv ℂ (Equiv.optionSubtypeNe i).symm).trans
    (MvPolynomial.optionEquivLeft ℂ _)

@[simp] theorem separateCosine_C {n : ℕ} (i : Fin n) (z : ℂ) :
    separateCosine i (MvPolynomial.C z) = Polynomial.C (MvPolynomial.C z) := by
  simp [separateCosine]

@[simp] theorem separateCosine_self {n : ℕ} (i : Fin n) :
    separateCosine i (MvPolynomial.X i) = Polynomial.X := by
  simp [separateCosine]

@[simp] theorem separateCosine_other {n : ℕ} (i j : Fin n) (h : j ≠ i) :
    separateCosine i (MvPolynomial.X j) = Polynomial.C (MvPolynomial.X ⟨j,h⟩) := by
  simp [separateCosine, Equiv.optionSubtypeNe_symm_of_ne h]

def cosineDiagonalEval {n : ℕ} (i j : Fin n) (hji : j ≠ i) :
    CosineRing n →+* MvPolynomial {k : Fin n // k ≠ i} ℂ :=
  (Polynomial.evalRingHom (MvPolynomial.X ⟨j,hji⟩)).comp (separateCosine i).toRingHom

@[simp] theorem cosineDiagonalEval_C {n : ℕ} (i j : Fin n) (hji : j ≠ i) (z : ℂ) :
    cosineDiagonalEval i j hji (MvPolynomial.C z) = MvPolynomial.C z := by
  simp [cosineDiagonalEval]

@[simp] theorem cosineDiagonalEval_self {n : ℕ} (i j : Fin n) (hji : j ≠ i) :
    cosineDiagonalEval i j hji (MvPolynomial.X i) = MvPolynomial.X ⟨j,hji⟩ := by
  simp [cosineDiagonalEval]

@[simp] theorem cosineDiagonalEval_other {n : ℕ} (i j k : Fin n)
    (hji : j ≠ i) (hki : k ≠ i) :
    cosineDiagonalEval i j hji (MvPolynomial.X k) = MvPolynomial.X ⟨k,hki⟩ := by
  simp [cosineDiagonalEval, hki]

theorem cosineDiagonalEval_swap {n : ℕ} (i j : Fin n) (hji : j ≠ i) :
    (cosineDiagonalEval i j hji).comp (MvPolynomial.rename (Equiv.swap i j)).toRingHom =
      cosineDiagonalEval i j hji := by
  ext k
  · simp
  · by_cases hki : k = i
    · subst k; simp [hji]
    · by_cases hkj : k = j
      · subst k; simp [hji]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hki]

theorem prime_cosine_difference {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Prime (MvPolynomial.X i - MvPolynomial.X j : CosineRing n) := by
  apply (MulEquiv.prime_iff (separateCosine i)).mp
  simpa [map_sub, hij.symm] using
    Polynomial.prime_X_sub_C (MvPolynomial.X (⟨j,hij.symm⟩ : {k : Fin n // k ≠ i}) :
      MvPolynomial {k : Fin n // k ≠ i} ℂ)

 
theorem cosine_difference_dvd_of_swap {n : ℕ} (p : CosineRing n)
    (i j : Fin n) (hij : i ≠ j)
    (hp : MvPolynomial.rename (Equiv.swap i j) p = -p) :
    (MvPolynomial.X i - MvPolynomial.X j) ∣ p := by
  let E := cosineDiagonalEval i j hij.symm
  have he : E (MvPolynomial.rename (Equiv.swap i j) p) = E p :=
    congrArg (fun f : CosineRing n →+* _ => f p) (cosineDiagonalEval_swap i j hij.symm)
  have hz : E p = 0 := by
    rw [hp, map_neg] at he
    have hh : (2 : MvPolynomial {k : Fin n // k ≠ i} ℂ) * E p = 0 := by
      linear_combination -he
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  have hd : Polynomial.X - Polynomial.C (MvPolynomial.X ⟨j,hij.symm⟩) ∣
      separateCosine i p := Polynomial.dvd_iff_isRoot.mpr hz
  obtain ⟨q,hq⟩ := hd
  refine ⟨(separateCosine i).symm q, ?_⟩
  apply (separateCosine i).injective
  simpa [map_mul, map_sub, hij.symm] using hq

 

theorem cosine_differences_relPrime {n : ℕ} (e f : UpperPair n) (hef : e ≠ f) :
    IsRelPrime (MvPolynomial.X e.val.1 - MvPolynomial.X e.val.2 : CosineRing n)
      (MvPolynomial.X f.val.1 - MvPolynomial.X f.val.2) := by
  apply (prime_cosine_difference e.val.1 e.val.2 (ne_of_lt e.property)).irreducible.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  let c : Fin n → Fin n := fun k => if k = e.val.1 then e.val.2 else k
  have hc : MvPolynomial.rename c
      (MvPolynomial.X e.val.1 - MvPolynomial.X e.val.2 : CosineRing n) = 0 := by
    simp [c, ne_of_gt e.property]
  have hd := map_dvd (MvPolynomial.rename c : CosineRing n →ₐ[ℂ] CosineRing n) hdiv
  rw [hc, zero_dvd_iff] at hd
  have heq : c f.val.1 = c f.val.2 := by
    apply MvPolynomial.X_injective (R := ℂ)
    exact sub_eq_zero.mp (by simpa only [map_sub, MvPolynomial.rename_X] using hd)
  have he := e.property
  have hf := f.property
  apply hef
  apply Subtype.ext
  dsimp [c] at heq
  split_ifs at heq with h₁ h₂ h₂
  · exact False.elim (ne_of_lt hf (h₁.trans h₂.symm))
  · exact Prod.ext h₁.symm heq
  · exact False.elim (by omega)
  · exact False.elim (ne_of_lt hf heq)


end





noncomputable section
open scoped Classical

 

def insertExponent {n : ℕ} (i : Fin (n+1)) : (Fin n → ℤ) →+ (Fin (n+1) → ℤ) where
  toFun e := Fin.insertNth i 0 e
  map_zero' := by funext j; refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp
  map_add' e f := by funext j; refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp

lemma insertExponent_injective {n : ℕ} (i : Fin (n+1)) : Function.Injective (insertExponent i) := by
  intro e f h
  funext j
  simpa [insertExponent] using congrFun h (i.succAbove j)

def insertLaurent {n : ℕ} (i : Fin (n+1)) : Laurent n →+* Laurent (n+1) :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (insertExponent i)

lemma insertLaurent_injective {n : ℕ} (i : Fin (n+1)) : Function.Injective (insertLaurent i) :=
  AddMonoidAlgebra.mapDomain_injective (insertExponent_injective i)

def insertSpectral {n : ℕ} (i : Fin (n+1)) : SpectralField n →+* SpectralField (n+1) :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))).comp (insertLaurent i))
    ((IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))).comp
      (insertLaurent_injective i))

@[simp] lemma insertSpectral_evalLaurent {n : ℕ} (i : Fin (n+1)) (f : Laurent n) :
    insertSpectral i (evalLaurent f)=evalLaurent (insertLaurent i f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma insertLaurent_monomial {n : ℕ} (i : Fin (n+1)) (e : Fin n → ℤ) (z : ℂ) :
    insertLaurent i (monomialL e z)=monomialL (Fin.insertNth i 0 e) z :=
  AddMonoidAlgebra.mapDomain_single

@[simp] lemma insertSpectral_const {n : ℕ} (i : Fin (n+1)) (z : ℂ) :
    insertSpectral i (constF n z)=constF (n+1) z := by
  have hc : constF n z=evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,insertSpectral_evalLaurent]
  change evalLaurent (insertLaurent i (monomialL 0 z))=evalLaurent (monomialL 0 z)
  rw [insertLaurent_monomial]
  congr 2
  exact (insertExponent i).map_zero

@[simp] lemma insertSpectral_variable {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    insertSpectral i (variableF j)=variableF (i.succAbove j) := by
  change insertSpectral i (evalLaurent (monomialL (variableExponent j) 1))=_
  rw [insertSpectral_evalLaurent,insertLaurent_monomial]
  congr 2
  funext k
  refine Fin.succAboveCases i ?_ (fun l => ?_) k
  · simp [variableExponent]
  · simp [variableExponent,Pi.single_apply]

@[simp] lemma insertSpectral_torusSin {n : ℕ} (i : Fin (n+1)) (z : SpectralField n) :
    insertSpectral i (torusSin z)=torusSin (insertSpectral i z) := by
  simp [torusSin,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma insertSpectral_torusCos {n : ℕ} (i : Fin (n+1)) (z : SpectralField n) :
    insertSpectral i (torusCos z)=torusCos (insertSpectral i z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma insertSpectral_torusL {n : ℕ} (i : Fin (n+1)) (z : SpectralField n) :
    insertSpectral i (torusL z)=torusL (insertSpectral i z) := by simp [torusL]

@[simp] lemma insertSpectral_torusWeights {n : ℕ} (i : Fin (n+1)) (z : SpectralField n) :
    (torusWeights z).map (insertSpectral i)=torusWeights (insertSpectral i z) := by
  simp [Weights.map,torusWeights,map_div₀]

@[simp] lemma insertSpectral_spectralWeights {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    (spectralWeights n j).map (insertSpectral i)=spectralWeights (n+1) (i.succAbove j) := by
  simp [spectralWeights,map_div₀]

@[simp] lemma insertSpectral_spectralA {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    insertSpectral i (spectralA j)=spectralA (i.succAbove j) := by simp [spectralA,map_div₀]

end

 

 

noncomputable section
open scoped LaurentPolynomial

 
def peelExponent {n : ℕ} (i : Fin (n+1)) : (Fin (n+1) → ℤ) ≃+ (ℤ × (Fin n → ℤ)) where
  toFun e := (e i,Fin.removeNth i e)
  invFun p := Fin.insertNth i p.1 p.2
  left_inv e := by simp
  right_inv p := by simp
  map_add' e f := rfl

def peelLaurentEquiv {n : ℕ} (i : Fin (n+1)) :
    Laurent (n+1) ≃+* LaurentPolynomial (Laurent n) :=
  (AddMonoidAlgebra.mapDomainRingEquiv ℂ (peelExponent i)).trans
    AddMonoidAlgebra.curryRingEquiv

@[simp] lemma peelLaurentEquiv_monomial {n : ℕ} (i : Fin (n+1))
    (e : Fin (n+1) → ℤ) (z : ℂ) :
    peelLaurentEquiv i (monomialL e z)=AddMonoidAlgebra.single (e i)
      (monomialL (Fin.removeNth i e) z) := by
  change AddMonoidAlgebra.curryRingEquiv
    (AddMonoidAlgebra.mapDomain (peelExponent i) (AddMonoidAlgebra.single e z))=_
  rw [AddMonoidAlgebra.mapDomain_single]
  exact AddMonoidAlgebra.curryRingEquiv_single _ _ _

 
def peelLaurent {n : ℕ} (i : Fin (n+1)) :
    Laurent (n+1) →+* LaurentPolynomial (SpectralField n) :=
  (AddMonoidAlgebra.mapRingHom ℤ (algebraMap (SpectralRing n) (SpectralField n))).comp
    (peelLaurentEquiv i).toRingHom

@[simp] lemma peelLaurent_monomial {n : ℕ} (i : Fin (n+1)) (e : Fin (n+1) → ℤ) (z : ℂ) :
    peelLaurent i (monomialL e z)=AddMonoidAlgebra.single (e i)
      (evalLaurent (monomialL (Fin.removeNth i e) z)) := by
  change AddMonoidAlgebra.mapRingHom ℤ _ (peelLaurentEquiv i (monomialL e z))=_
  rw [peelLaurentEquiv_monomial]
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

end







end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaurentBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped LaurentPolynomial Classical

def monomialUnit {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz:z≠0) : (Laurent n)ˣ where
  val := monomialL e z
  inv := monomialL (-e) z⁻¹
  val_inv := by simp [monomialL_mul,hz]
  inv_val := by simp [monomialL_mul,hz]

lemma peelLaurentEquiv_insert {n : ℕ} (i : Fin (n+1)) (f : Laurent n) :
    peelLaurentEquiv i (insertLaurent i f)=LaurentPolynomial.C f := by
  have h : (peelLaurentEquiv i).toRingHom.comp (insertLaurent i)=LaurentPolynomial.C := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change peelLaurentEquiv i (insertLaurent i (monomialL _ _))=_
    all_goals
      rw [insertLaurent_monomial,peelLaurentEquiv_monomial]
      simp only [Fin.insertNth_apply_same,Fin.removeNth_insertNth]
      rfl
  exact DFunLike.congr_fun h f

 
def substituteLaurent {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ) :
    Laurent (n+1) →+* Laurent n :=
  (LaurentPolynomial.eval₂ (RingHom.id _) u).comp (peelLaurentEquiv i).toRingHom

@[simp] lemma substituteLaurent_insert {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ)
    (f : Laurent n) : substituteLaurent i u (insertLaurent i f)=f := by
  change LaurentPolynomial.eval₂ (RingHom.id _) u (peelLaurentEquiv i (insertLaurent i f))=f
  rw [peelLaurentEquiv_insert,LaurentPolynomial.eval₂_C]
  rfl


end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PatchReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/







namespace CriticalStrip.Diagram
noncomputable section

instance tileAdjDecidable (t : Tile) : DecidableRel t.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∈ t.edges ∨ _ ∈ t.edges))

instance tileOccupiedDecidable (t : Tile) (i : Fin 4) : Decidable (t.Occupied i) :=
  inferInstanceAs (Decidable (∃ j, t.Adj i j))

@[simp] theorem Tile.adj_symm (t : Tile) {i j : Fin 4} : t.Adj i j ↔ t.Adj j i :=
  or_comm

end
end CriticalStrip.Diagram







end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CutPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.CutPatch
noncomputable section
open Finset

inductive Shape where
  | vacant | single₀ | single₁ | paired | separate
  deriving DecidableEq

def tilePort (i : Fin 4) : Fin 6 := Fin.castLE (by decide) i

end
end CriticalStrip.Diagram.CutPatch

 

 

namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical
namespace Pairing

def partnerOrSelf {n : ℕ} (p : Pairing n) (i : Fin n) : Fin n :=
  if h : p.Occupied i then p.partner i h else i

theorem adj_partnerOrSelf {n : ℕ} (p : Pairing n) (i j : Fin n) :
    p.Adj i j ↔ p.Occupied i ∧ j = p.partnerOrSelf i := by
  by_cases hi : p.Occupied i
  · simp only [partnerOrSelf,hi,dite_eq_left,true_and]
    exact ⟨fun h => adj_unique h (p.partner_adj i hi),fun h => h ▸ p.partner_adj i hi⟩
  · simp only [hi,false_and,iff_false]
    exact fun h => hi ⟨j,h⟩

@[simp] theorem insertCup_adj {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬ p.Occupied a) (hb : ¬ p.Occupied b)
    (i j : Fin n) :
    (p.insertCup a b hab ha hb).Adj i j ↔
      (i=a ∧ j=b) ∨ (i=b ∧ j=a) ∨ p.Adj i j := by
  simp only [Adj,insertCup,mem_insert,Prod.mk.injEq]
  tauto

@[simp] theorem mapOccupied_equiv_adj {n : ℕ} (p : Pairing n) (f : Equiv.Perm (Fin n))
    (hf : ∀ i j, p.Occupied i → p.Occupied j → (f i < f j ↔ i<j))
    (i j : Fin n) :
    (p.mapOccupied f.toEmbedding hf).Adj i j ↔ p.Adj (f.symm i) (f.symm j) := by
  convert (mapOccupied_adj p f.toEmbedding hf (f.symm i) (f.symm j)) using 1
  all_goals try with_reducible_and_instances rfl
  simp

@[simp] theorem moveIntoVacancy_adj {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (hb : ¬ p.Occupied b) (i j : Fin n) :
    (p.moveIntoVacancy a b hab hb).Adj i j ↔
      p.Adj (Equiv.swap a b i) (Equiv.swap a b j) := by
  exact mapOccupied_equiv_adj p (Equiv.swap a b) _ i j

@[simp] theorem moveIntoLowerVacancy_adj {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬ p.Occupied a) (i j : Fin n) :
    (p.moveIntoLowerVacancy a b hab ha).Adj i j ↔
      p.Adj (Equiv.swap a b i) (Equiv.swap a b j) := by
  exact mapOccupied_equiv_adj p (Equiv.swap a b) _ i j

@[simp] theorem capRemove_adj {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : p.Occupied a) (hb : p.Occupied b) (hn : ¬ p.Adj a b)
    (i j : Fin n) :
    (p.capRemove a b hab ha hb hn).Adj i j ↔
      (i=p.partnerOrSelf a ∧ j=p.partnerOrSelf b) ∨
      (i=p.partnerOrSelf b ∧ j=p.partnerOrSelf a) ∨ (p.omitTwo a b).Adj i j := by
  simp only [capRemove,capSplice_adj,partnerOrSelf,ha,hb,dite_eq_left]

 
def cutShape {n : ℕ} (p : Pairing n) (a b : Fin n) : CutPatch.Shape :=
  if p.Occupied a then
    if p.Occupied b then if p.Adj a b then .paired else .separate else .single₀
  else if p.Occupied b then .single₁ else .vacant


end Pairing
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CutStateSound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section





open Finset
open scoped Classical

inductive StepVertex (n : ℕ) where
  | old : Fin n → StepVertex n
  | box : Fin 4 → StepVertex n
  | out : Fin n → StepVertex n
  deriving DecidableEq

namespace Pairing

def cutToStep {n : ℕ} (p : Pairing n) (a b : Fin n) : Sum (Fin 6) (Fin n) → StepVertex n
  | .inl i => ![.box 0,.box 1,.box 2,.box 3,.old (p.partnerOrSelf a),.old (p.partnerOrSelf b)] i
  | .inr i => .out i

end Pairing

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_StepToCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical
namespace Pairing







@[simp] theorem cutToStep_tilePort {n : ℕ} (p : Pairing n) (a b : Fin n) (k : Fin 4) :
    p.cutToStep a b (.inl (CutPatch.tilePort k)) = .box k := by
  fin_cases k <;> rfl

end Pairing
end

 

 

noncomputable section
open scoped Classical

@[simp] theorem Tile.adj_irrefl (t : Tile) (i : Fin 4) : ¬t.Adj i i := by
  cases t <;> fin_cases i <;> decide

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FreshGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace PartialColumn

def support {n : ℕ} (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n)
    (i : Fin (n+1)) : Prop :=
  if hi : i.val<k then (t ⟨i.val,lt_of_lt_of_le hi hk⟩).Occupied 2
  else if h : i.val=k ∧ 0<k then (t ⟨k-1,by omega⟩).Occupied 3
  else p.padBottom.Occupied i

@[simp] theorem support_zero {n : ℕ} (p : Pairing n) (t : Configuration n) (i : Fin (n+1)) :
    support p t 0 (Nat.zero_le n) i ↔ p.padBottom.Occupied i := by simp [support]

section RowTransitions
variable {n : ℕ} (p : Pairing n) (t : Configuration n) (row : Fin n)

@[simp] lemma right_support : support p t row.val (Nat.le_of_lt row.isLt) row.succ ↔ p.Occupied row := by
  simp [support]

end RowTransitions

end PartialColumn
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section

@[simp] theorem cos_six_lambda : Real.cos (6*lambda) = -d := by
  have h : 6*lambda = Real.pi-2*lambda := by simp [lambda]; ring
  rw [h,Real.cos_pi_sub]
  rfl

@[simp] theorem sin_six_lambda : Real.sin (6*lambda) = d := by
  have h : 6*lambda = Real.pi-2*lambda := by simp [lambda]; ring
  rw [h,Real.sin_pi_sub]
  have h2 : 2*lambda = Real.pi/4 := by simp [lambda]; ring
  rw [h2,d,h2,Real.sin_pi_div_four,Real.cos_pi_div_four]

theorem d_sq : d^2 = 1/2 := by
  have h2 : 2*lambda = Real.pi/4 := by simp [lambda]; ring
  rw [d,h2,Real.cos_pi_div_four,div_pow]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem d_ne_zero : d ≠ 0 := by
  intro h
  have := d_sq
  rw [h] at this
  norm_num at this






open Finset
open scoped Classical



end

 

 

noncomputable section
open Finset
open scoped Classical

 

def deletionNode {n : ℕ} (i : Fin n) : SpectralField n :=
  variableF i * constF n phase ^ 3

def deletionBeta {n : ℕ} (i : Fin n) : SpectralField n :=
  torusCos (deletionNode i ^ 2 / constF n phase ^ 3)

def nodalWeights {n : ℕ} (i : Fin n) : Fin (n+1) → Weights (SpectralField n) :=
  Fin.snoc (spectralWeights n) (torusWeights (constF n phase ^ 3 / deletionNode i))



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

 
def cosineL {n : ℕ} (e : Fin n → ℤ) (z : ℂ) : Laurent n :=
  monomialL e (z/2) + monomialL (-e) (z⁻¹/2)

theorem cosineL_map {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz : z ≠ 0) :
    evalLaurent (cosineL e z) = torusCos (evalLaurent (monomialL e z)) := by
  rw [cosineL, evalLaurent, map_add, torusCos, evalLaurent, map_monomialL_inv e z hz]
  rw [map_monomialL_factor e (z/2), map_monomialL_factor (-e) (z⁻¹/2),
    map_monomialL_factor e z, map_monomialL_factor (-e) z⁻¹]
  simp only [constF, map_div₀, map_ofNat]
  ring

theorem map_monomialL_two_variable {n : ℕ} (i : Fin n) (z : ℂ) :
    evalLaurent (monomialL ((2 : ℤ) • variableExponent i) z) =
      constF n z * variableF i ^ 2 := by
  have hh : monomialL ((2 : ℤ) • variableExponent i) (1:ℂ) =
      monomialL (variableExponent i) 1 ^ 2 := by
    simp [pow_two, two_smul]
  rw [evalLaurent, map_monomialL_factor, hh, map_pow]
  rfl

theorem deletionBeta_laurent {n : ℕ} (i : Fin n) :
    deletionBeta i = evalLaurent (cosineL ((2 : ℤ) • variableExponent i) (phase^3)) := by
  rw [cosineL_map _ _ (pow_ne_zero _ phase_ne_zero), map_monomialL_two_variable]
  unfold deletionBeta deletionNode
  congr 1
  simp only [constF, map_pow]
  field_simp [constF_phase_ne_zero]






open scoped LaurentPolynomial Classical

def variableUnit {n : ℕ} (i : Fin n) : (Laurent n)ˣ := monomialUnit (variableExponent i) 1 one_ne_zero

def constantUnit (n : ℕ) (z : ℂ) (hz:z≠0) : (Laurent n)ˣ := monomialUnit 0 z hz

def betaL {n : ℕ} (i : Fin n) : Laurent n := cosineL ((2:ℤ) • variableExponent i) (phase^3)

@[simp] lemma betaL_map {n : ℕ} (i : Fin n) : evalLaurent (betaL i)=deletionBeta i :=
  (deletionBeta_laurent i).symm

@[simp] lemma variableUnit_coe {n : ℕ} (j : Fin n) :
    (variableUnit j : Laurent n)=monomialL (variableExponent j) 1 := rfl
@[simp] lemma variableUnit_inv_coe {n : ℕ} (j : Fin n) :
    ((variableUnit j)⁻¹ : (Laurent n)ˣ).val=monomialL (-variableExponent j) 1 := by
  simp only [variableUnit,monomialUnit,Units.inv_mk,Units.val_mk,inv_one]
@[simp] lemma constantUnit_coe (n : ℕ) (z : ℂ) (hz:z≠0) :
    (constantUnit n z hz : Laurent n)=monomialL 0 z := rfl
@[simp] lemma constantUnit_inv_coe (n : ℕ) (z : ℂ) (hz:z≠0) :
    ((constantUnit n z hz)⁻¹ : (Laurent n)ˣ).val=monomialL 0 z⁻¹ := by
  simp only [constantUnit,monomialUnit,Units.inv_mk,Units.val_mk,neg_zero]

end





noncomputable section

instance spectralFieldCharZero (n : ℕ) : CharZero (SpectralField n) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (SpectralField n)).injective







end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxSplitPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

def deletionTile {K : Type*} [Zero K] [One K] : Tile → K
  | .vacant | .cap | .cup | .capCup => 1
  | _ => 0

def swapTile {K : Type*} [Zero K] [One K] : Tile → K
  | .vacant | .diagonal₀ | .diagonal₁ => 1
  | _ => 0






open Finset



end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhaseAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram
noncomputable section

 
def swapWeights {K : Type*} [Zero K] [One K] : Weights K := ⟨0,1,0,0,0⟩


@[simp] lemma swapWeights_tile {K : Type*} [Zero K] [One K] :
    (swapWeights : Weights K).tile = ThreeBox.swapTile := by funext t; cases t <;> rfl
@[simp] lemma deletionWeights_tile {K : Type*} [Zero K] [One K] :
    (deletionWeights : Weights K).tile = ThreeBox.deletionTile := by funext t; cases t <;> rfl







@[simp] lemma torusSin_inv {n : ℕ} (z : SpectralField n) : torusSin z⁻¹ = -torusSin z := by
  simp only [torusSin,inv_inv]
  ring

@[simp] lemma torusSin_neg {n : ℕ} (z : SpectralField n) : torusSin (-z) = -torusSin z := by
  simp only [torusSin]
  ring

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MirrorExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical






namespace Pairing
variable {n m : ℕ} (f : Fin n ↪o Fin m)

lemma map_adj (p : Pairing n) (x y : Fin m) :
    (p.map f).Adj x y ↔ ∃ i j, p.Adj i j ∧ f i=x ∧ f j=y := by
  simp only [map,Adj,Finset.mem_map,Prod.exists,Function.Embedding.coe_prodMap,Prod.map_apply,Prod.mk.injEq]
  constructor
  · rintro (⟨i,j,h,hi,hj⟩|⟨i,j,h,hj,hi⟩)
    · exact ⟨i,j,Or.inl h,hi,hj⟩
    · exact ⟨j,i,Or.inr h,hi,hj⟩
  · rintro ⟨i,j,(h|h),hi,hj⟩
    · exact Or.inl ⟨i,j,h,hi,hj⟩
    · exact Or.inr ⟨j,i,h,hj,hi⟩

@[simp] lemma map_occupied (p : Pairing n) (i : Fin n) :
    (p.map f).Occupied (f i) ↔ p.Occupied i := by
  simp only [Occupied,map_adj]
  constructor
  · rintro ⟨_,a,b,h,ha,_⟩
    have := f.injective ha
    subst a
    exact ⟨b,h⟩
  · rintro ⟨j,h⟩
    exact ⟨f j,i,j,h,rfl,rfl⟩

@[simp] lemma map_partnerOrSelf (p : Pairing n) (i : Fin n) :
    (p.map f).partnerOrSelf (f i)=f (p.partnerOrSelf i) := by
  by_cases hi : p.Occupied i
  · have hmap : (p.map f).Adj (f i) (f (p.partnerOrSelf i)) :=
      (map_adj_image f p _ _).mpr ((p.adj_partnerOrSelf i _).mpr ⟨hi,rfl⟩)
    exact ((p.map f).adj_partnerOrSelf _ _).mp hmap |>.2.symm
  · simp [partnerOrSelf,hi]

@[simp] lemma map_cutShape (p : Pairing n) (a b : Fin n) :
    (p.map f).cutShape (f a) (f b)=p.cutShape a b := by
  simp only [cutShape,map_occupied,map_adj_image]

end Pairing
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical


@[simp] lemma permSpectral_deletionNode {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (deletionNode i)=deletionNode (σ i) := by simp [deletionNode]

@[simp] lemma permSpectral_deletionBeta {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (deletionBeta i)=deletionBeta (σ i) := by simp [deletionBeta,map_div₀]

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CramerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical

def inlinePrivate155_signMonomial {n : ℕ} (i : Fin n) : Multiplicative (Fin n → ℤ) →* Laurent n where
  toFun e := monomialL e.toAdd ((-1:ℂ) ^ (e.toAdd i))
  map_one' := by simp [monomialL]; rfl
  map_mul' e f := by
    change monomialL (e.toAdd+f.toAdd) ((-1:ℂ) ^ (e.toAdd i+f.toAdd i)) = _
    rw [zpow_add₀ (by norm_num : (-1:ℂ)≠0)]
    exact (AddMonoidAlgebra.single_mul_single _ _ _ _).symm

def signLaurent {n : ℕ} (i : Fin n) : Laurent n →+* Laurent n :=
  (AddMonoidAlgebra.lift ℂ (Laurent n) (Fin n → ℤ) (inlinePrivate155_signMonomial i)).toRingHom

@[simp] lemma signLaurent_monomial {n : ℕ} (i : Fin n) (e : Fin n → ℤ) (z : ℂ) :
    signLaurent i (monomialL e z)=monomialL e (z * (-1:ℂ)^(e i)) := by
  change AddMonoidAlgebra.lift ℂ _ _ (inlinePrivate155_signMonomial i) (AddMonoidAlgebra.single e z)=_
  rw [AddMonoidAlgebra.lift_single]
  change z • AddMonoidAlgebra.single e ((-1:ℂ)^(e i))=AddMonoidAlgebra.single e _
  rw [AddMonoidAlgebra.smul_single,smul_eq_mul]

lemma signLaurent_involutive {n : ℕ} (i : Fin n) : Function.Involutive (signLaurent i) := by
  have h : (signLaurent i).comp (signLaurent i)=RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change signLaurent i (signLaurent i (monomialL _ _))=monomialL _ _
    all_goals rw [signLaurent_monomial,signLaurent_monomial]
    all_goals congr 1; rw [mul_assoc,←mul_zpow]; norm_num
  intro f
  exact DFunLike.congr_fun h f

def signSpectral {n : ℕ} (i : Fin n) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing n) (SpectralField n)).comp (signLaurent i))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (signLaurent_involutive i).injective)

@[simp] lemma signSpectral_evalLaurent {n : ℕ} (i : Fin n) (f : Laurent n) :
    signSpectral i (evalLaurent f)=evalLaurent (signLaurent i f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma signSpectral_const {n : ℕ} (i : Fin n) (z : ℂ) :
    signSpectral i (constF n z)=constF n z := by
  have hc : constF n z=evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,signSpectral_evalLaurent]
  change evalLaurent (signLaurent i (monomialL 0 z))=evalLaurent (monomialL 0 z)
  rw [signLaurent_monomial]
  simp

@[simp] lemma signSpectral_variable {n : ℕ} (i j : Fin n) :
    signSpectral i (variableF j)=if j=i then -variableF j else variableF j := by
  change signSpectral i (evalLaurent (monomialL (variableExponent j) 1))=_
  rw [signSpectral_evalLaurent,signLaurent_monomial]
  by_cases h:j=i
  · subst j
    simp only [variableExponent,Pi.single_apply,ite_true,zpow_one,one_mul]
    change evalLaurent (AddMonoidAlgebra.single _ (-1)) = _
    rw [AddMonoidAlgebra.single_neg]
    simp only [evalLaurent,map_neg]
    rfl
  · have hi : i≠j := Ne.symm h
    simp only [variableExponent,Pi.single_apply,ite_eq_right hi,ite_eq_right h,zpow_zero,mul_one]
    rfl

@[simp] lemma signSpectral_torusSin {n : ℕ} (i : Fin n) (z : SpectralField n) :
    signSpectral i (torusSin z)=torusSin (signSpectral i z) := by
  simp [torusSin,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma signSpectral_torusCos {n : ℕ} (i : Fin n) (z : SpectralField n) :
    signSpectral i (torusCos z)=torusCos (signSpectral i z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma signSpectral_torusL {n : ℕ} (i : Fin n) (z : SpectralField n) :
    signSpectral i (torusL z)=torusL (signSpectral i z) := by simp [torusL]

@[simp] lemma signSpectral_torusWeights {n : ℕ} (i : Fin n) (z : SpectralField n) :
    (torusWeights z).map (signSpectral i)=torusWeights (signSpectral i z) := by
  simp [Weights.map,torusWeights,map_div₀]

end

 

 

noncomputable section
open scoped Classical
open Finset

 
def occupancySign {K : Type*} [Ring K] {n : ℕ} (p : Pairing n) (i : Fin n) : K :=
  if p.Occupied i then -1 else 1

def Weights.signTwist {K : Type*} [Ring K] (w : Weights K) : Weights K :=
  ⟨-w.A,w.B,-w.U,w.E,w.F⟩

@[simp] lemma occupancySign_empty {K : Type*} [Ring K] {n : ℕ} (i : Fin n) :
    occupancySign (K:=K) (empty n) i=1 := by simp [occupancySign]
@[simp] lemma occupancySign_mul_self {K : Type*} [Ring K] {n : ℕ} (p : Pairing n) (i : Fin n) :
    occupancySign (K:=K) p i*occupancySign p i=1 := by
  simp only [occupancySign]; split_ifs <;> simp

end

 

 

noncomputable section
open scoped Classical

@[simp] lemma torusL_neg {n : ℕ} (z : SpectralField n) : torusL (-z)=torusL z := by
  simp only [torusL,mul_neg,torusSin_neg]
  ring

@[simp] lemma torusWeights_neg {n : ℕ} (z : SpectralField n) :
    torusWeights (-z)=(torusWeights z).signTwist := by
  have hinv : (-z)⁻¹ = -z⁻¹ := inv_neg
  simp only [torusWeights,Weights.signTwist,div_eq_mul_inv,hinv,
    mul_neg,torusSin_neg,torusL_neg,neg_mul,neg_neg]

@[simp] lemma signSpectral_spectralA {n : ℕ} (i j : Fin n) :
    signSpectral i (spectralA j)=spectralA j := by
  simp only [spectralA,signSpectral_torusCos,map_div₀,map_pow,signSpectral_const,
    signSpectral_variable]
  split_ifs <;> simp







@[simp] lemma spectral_div_neg {n : ℕ} (x y : SpectralField n) :
    x/(-y)=-(x/y) := div_neg_eq_neg_div _ _

@[simp] lemma signSpectral_deletionNode {n : ℕ} (k i : Fin n) :
    signSpectral k (deletionNode i)=if i=k then -deletionNode i else deletionNode i := by
  simp only [deletionNode,map_mul,signSpectral_variable,map_pow,signSpectral_const]
  split_ifs <;> simp

@[simp] lemma signSpectral_deletionBeta {n : ℕ} (k i : Fin n) :
    signSpectral k (deletionBeta i)=deletionBeta i := by
  simp only [deletionBeta,signSpectral_torusCos,map_div₀,map_pow,signSpectral_const,
    signSpectral_deletionNode]
  split_ifs <;> simp

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_Specialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram





noncomputable section
open Finset

 

def torusCharacter {n k : ℕ} (z : Fin n → SpectralField k) (hz : ∀ i, z i ≠ 0) :
    Multiplicative (Fin n → ℤ) →* SpectralField k where
  toFun e := ∏ i, z i ^ e.toAdd i
  map_one' := by simp
  map_mul' e f := by
    change (∏ i, z i ^ (e.toAdd i + f.toAdd i)) = _
    simp only [zpow_add₀ (hz _), prod_mul_distrib]

def torusEvaluation {n k : ℕ} (z : Fin n → SpectralField k) (hz : ∀ i, z i ≠ 0) :
    Laurent n →ₐ[ℂ] SpectralField k :=
  AddMonoidAlgebra.lift ℂ (SpectralField k) (Fin n → ℤ) (torusCharacter z hz)

@[simp] theorem torusEvaluation_monomial {n k : ℕ} (z : Fin n → SpectralField k)
    (hz : ∀ i, z i ≠ 0) (e : Fin n → ℤ) (c : ℂ) :
    torusEvaluation z hz (monomialL e c) = constF k c * ∏ i, z i ^ e i := by
  simp [torusEvaluation, monomialL, AddMonoidAlgebra.lift_single, torusCharacter, constF, Algebra.smul_def]

@[simp] theorem torusEvaluation_constant {n k : ℕ} (z : Fin n → SpectralField k)
    (hz : ∀ i, z i ≠ 0) (c : ℂ) :
    torusEvaluation z hz (constantL n c) = constF k c := by
  change torusEvaluation z hz (monomialL 0 c) = _
  simp

@[simp] theorem torusEvaluation_variable {n k : ℕ} (z : Fin n → SpectralField k)
    (hz : ∀ i, z i ≠ 0) (i : Fin n) :
    torusEvaluation z hz (monomialL (variableExponent i) 1) = z i := by
  simp [variableExponent, Pi.single_apply, constF]



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CollisionSubstitutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical







def reflectionUnit {n : ℕ} (j : Fin n) : (Laurent n)ˣ :=
  (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero))⁻¹*(variableUnit j)⁻¹

@[simp] lemma reflectionUnit_coe {n : ℕ} (j : Fin n) :
    (reflectionUnit j : Laurent n)=monomialL (-variableExponent j) ((phase^3)⁻¹) := by
  simp only [reflectionUnit,Units.val_mul,constantUnit_inv_coe,variableUnit_inv_coe,
    monomialL_mul,zero_add,mul_one]

@[simp] lemma reflectionUnit_inv_coe {n : ℕ} (j : Fin n) :
    ((reflectionUnit j)⁻¹ : (Laurent n)ˣ).val=monomialL (variableExponent j) (phase^3) := by
  simp only [reflectionUnit,mul_inv_rev,inv_inv,Units.val_mul,constantUnit_coe,variableUnit_coe,
    monomialL_mul,add_zero,one_mul]

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SpecializationPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open Finset
open scoped Classical

@[simp] theorem liftSpectral_weights_tile {n : ℕ} (i : Fin n) (t : Tile) :
    liftSpectral n ((spectralWeights n i).tile t) =
      (spectralWeights (n+1) i.castSucc).tile t := by
  cases t <;> simp [spectralWeights, torusWeights, Weights.tile, torusL, map_div₀]



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarFlat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section








open Finset
open scoped Classical


@[simp] theorem map_deletion_tile {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (t : Tile) :
    f ((deletionWeights : Weights K).tile t) = (deletionWeights : Weights L).tile t := by
  cases t <;> simp [deletionWeights, Weights.tile]



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram




noncomputable section
open scoped Classical BigOperators

namespace Graph

 
def DrainsAt {V : Type*} (r : V → V → Prop) (root : V) : Prop :=
  ∀ v w, r v w → Relation.ReflTransGen r v root



end Graph
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

namespace Tile

def transpose : Tile → Tile
  | .diagonal₀ => .diagonal₁
  | .diagonal₁ => .diagonal₀
  | .cap => .cup
  | .cup => .cap
  | x => x

def transposePort : Fin 4 → Fin 4 := ![2,3,0,1]

@[simp] lemma transpose_transpose (t : Tile) : t.transpose.transpose = t := by cases t <;> rfl
@[simp] lemma transposePort_involutive (i : Fin 4) : transposePort (transposePort i)=i := by
  fin_cases i <;> rfl
@[simp] lemma transpose_adj (t : Tile) (i j : Fin 4) :
    t.transpose.Adj (transposePort i) (transposePort j) ↔ t.Adj i j := by
  cases t <;> fin_cases i <;> fin_cases j <;> decide
@[simp] lemma transpose_occupied (t : Tile) (i : Fin 4) :
    t.transpose.Occupied (transposePort i) ↔ t.Occupied i := by
  cases t <;> fin_cases i <;> decide
@[simp] lemma weight_transpose {K : Type*} [One K] (w : Weights K) (t : Tile) :
    w.tile t.transpose = w.tile t := by cases t <;> rfl

end Tile



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeficitBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators

open Set MeasureTheory _root_.Matrix

 

def boundedCauchy (x y : ℝ) : ℝ := x / (x + y)
def momentBasis (k : ℕ) (x : ℝ) : ℝ := x ^ k * omega x
def transformedBasis (k : ℕ) (x : ℝ) : ℝ :=
  ∫ y in Ioo (0 : ℝ) 1, boundedCauchy x y * momentBasis k y

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CauchyMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
section DeterminantBounds
open scoped BigOperators
open Set MeasureTheory _root_.Matrix



def cauchyDefect (N : ℕ) (D₀ : ℝ) (v : Fin N → ℝ) (x : ℝ) : ℝ :=
  D₀ - ∑ k, v k * transformedBasis k.val x

def CauchyMomentProblem (N : ℕ) (D₀ : ℝ) (v : Fin N → ℝ) : Prop :=
  ∀ j : Fin N, ∫ x in Ioo (0 : ℝ) 1, momentBasis j.val x * cauchyDefect N D₀ v x = 0

end DeterminantBounds

 

open Set MeasureTheory Filter
open scoped Topology

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HeightOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators






def mirrorTriangle (v : Triangle) : Triangle :=
  (-v.1 - (v.2.1 : ℤ) - (if v.2.2 then 0 else 1), v.2.1, v.2.2)

@[simp] theorem mirrorTriangle_band (v : Triangle) : (mirrorTriangle v).2.1 = v.2.1 := rfl

@[simp] theorem mirrorTriangle_up (i : ℤ) (j : ℕ) :
    mirrorTriangle (up i j) = up (-i - j) j := by
  simp [mirrorTriangle, up]

@[simp] theorem mirrorTriangle_down (i : ℤ) (j : ℕ) :
    mirrorTriangle (down i j) = down (-i - j - 1) j := by
  simp [mirrorTriangle, down]

@[simp] theorem mirrorTriangle_mirrorTriangle (v : Triangle) :
    mirrorTriangle (mirrorTriangle v) = v := by
  rcases v with ⟨i, j, b⟩
  cases b <;> simp [mirrorTriangle]
  ring

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/




namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical

 
def PathBetween (N : ℕ) (start finish : Triangle) (p : List Triangle) : Prop :=
  p.head?=some start ∧ p.getLast?=some finish ∧ p.Nodup ∧
    p.IsChain adjacent ∧ ∀ v ∈ p, v.2.1<N

@[simp] lemma pathBetween_source (N : ℕ) (finish : Triangle) (p : List Triangle) :
    PathBetween N (up 0 0) finish p ↔ IsPath N finish p := Iff.rfl

lemma adjacent_symmetric : Std.Symm adjacent := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩


def translateTriangle (i : ℤ) (v : Triangle) : Triangle := (i+v.1,v.2)

@[simp] lemma translateTriangle_up (i j : ℤ) (k : ℕ) :
    translateTriangle i (up j k)=up (i+j) k := rfl
@[simp] lemma translateTriangle_down (i j : ℤ) (k : ℕ) :
    translateTriangle i (down j k)=down (i+j) k := rfl
@[simp] lemma translateTriangle_band (i : ℤ) (v : Triangle) :
    (translateTriangle i v).2.1=v.2.1 := rfl
@[simp] lemma translateTriangle_zero (v : Triangle) : translateTriangle 0 v=v := by
  cases v; simp [translateTriangle]
@[simp] lemma translateTriangle_add (i j : ℤ) (v : Triangle) :
    translateTriangle i (translateTriangle j v)=translateTriangle (i+j) v := by
  simp [translateTriangle,add_assoc]

end




end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_GraphPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram.PathGraph
noncomputable section
open scoped Classical

 
def AtMostTwo {V : Type*} (r : V → V → Prop) : Prop :=
  ∀ ⦃v x y z⦄, r v x → r v y → r v z → x ≠ y → z = x ∨ z = y

def AtMostOne {V : Type*} (r : V → V → Prop) (v : V) : Prop :=
  ∀ ⦃x y⦄, r v x → r v y → x = y

 
def Trace {V : Type*} (r : V → V → Prop) (a b : V) (p : List V) : Prop :=
  p.head? = some a ∧ p.getLast? = some b ∧ p.Nodup ∧ p.IsChain r

 
def Consecutive {V : Type*} (p : List V) (v w : V) : Prop :=
  ∃ (i : ℕ) (hi : i+1 < p.length),
    (p[i] = v ∧ p[i+1] = w) ∨ (p[i] = w ∧ p[i+1] = v)

lemma consecutive_symm {V : Type*} {p : List V} {v w : V} :
    Consecutive p v w → Consecutive p w v := by
  rintro ⟨i,hi,h⟩
  exact ⟨i,hi,h.symm⟩

lemma consecutive_mem {V : Type*} {p : List V} {v w : V}
    (h : Consecutive p v w) : v ∈ p ∧ w ∈ p := by
  obtain ⟨i,hi,h⟩ := h
  rcases h with ⟨hv,hw⟩ | ⟨hw,hv⟩ <;>
    exact ⟨List.mem_of_getElem hv,List.mem_of_getElem hw⟩

lemma Trace.length_two_le {V : Type*} {r : V → V → Prop} {a b : V} {p : List V}
    (h : Trace r a b p) (hab : a ≠ b) : 2 ≤ p.length := by
  rcases p with _ | ⟨x,p⟩
  · simp [Trace] at h
  · cases p with
    | nil => simp [Trace] at h; exact (hab (h.1.symm.trans h.2)).elim
    | cons => simp

lemma Trace.first {V : Type*} {r : V → V → Prop} {a b : V} {p : List V}
    (h : Trace r a b p) (hi : 0 < p.length) : p[0] = a := by
  have hh := h.1
  simpa only [List.head?_eq_getElem?,List.getElem?_eq_getElem hi,Option.some.injEq] using hh

lemma Trace.last {V : Type*} {r : V → V → Prop} {a b : V} {p : List V}
    (h : Trace r a b p) (hi : p.length-1 < p.length) : p[p.length-1] = b := by
  have hh := h.2.1
  simpa only [List.getLast?_eq_getElem?,List.getElem?_eq_getElem hi,Option.some.injEq] using hh

 

theorem Trace.edge_consecutive {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) (hb : AtMostOne r b) {p : List V}
    (hp : Trace r a b p) (hab : a ≠ b) {v w : V}
    (hv : v ∈ p) (hvw : r v w) : Consecutive p v w := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  have hlen := hp.length_two_le hab
  have hc := List.isChain_iff_getElem.mp hp.2.2.2
  by_cases hz : i=0
  · subst i
    have he : p[1] = w := ha (by simpa only [hp.first (by omega)] using hc 0 (by omega))
      (by simpa only [hp.first (by omega)] using hvw)
    exact ⟨0,by omega,Or.inl ⟨rfl,he⟩⟩
  · by_cases ht : i+1=p.length
    · have hi' : i=p.length-1 := by omega
      have hpi : p[i] = b := by simpa only [hi'] using hp.last (by omega)
      have hw : p[i-1] = w := hb
        (by have hh := hs.symm _ _ (hc (i-1) (by omega));
            have he : i-1+1=i := by omega
            simpa only [he,hpi] using hh)
        (by simpa only [hpi] using hvw)
      refine ⟨i-1,by omega,Or.inr ⟨hw,?_⟩⟩
      have he : i-1+1=i := by omega
      simp only [he]
    · have he : i-1+1=i := by omega
      have hm : r p[i] p[i-1] := by
        have hh := hs.symm _ _ (hc (i-1) (by omega))
        simpa only [he] using hh
      have hp' : r p[i] p[i+1] := hc i (by omega)
      have hne : p[i-1] ≠ p[i+1] := by
        intro hh
        have hi' := hp.2.2.1.getElem_inj_iff.mp hh
        omega
      rcases h₂ hm hp' hvw hne with hw | hw
      · exact ⟨i-1,by omega,Or.inr ⟨hw.symm,by simp only [he]⟩⟩
      · exact ⟨i,by omega,Or.inl ⟨rfl,hw.symm⟩⟩

lemma Trace.reach_mem {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) (hb : AtMostOne r b) {p : List V}
    (hp : Trace r a b p) (hab : a ≠ b) {v : V}
    (hr : Relation.ReflTransGen r v a) : v ∈ p := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    have hl := hp.length_two_le hab
    exact List.mem_of_getElem (hp.first (by omega))
  | @head v w hvw hr ih =>
    exact (consecutive_mem (hp.edge_consecutive hs h₂ ha hb hab ih (hs.symm _ _ hvw))).2

 

theorem Trace.edges_iff {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) (hb : AtMostOne r b) {p : List V}
    (hp : Trace r a b p) (hab : a ≠ b)
    (hd : ∀ v w, r v w → Relation.ReflTransGen r v a) (v w : V) :
    r v w ↔ Consecutive p v w := by
  constructor
  · intro hvw
    exact hp.edge_consecutive hs h₂ ha hb hab (hp.reach_mem hs h₂ ha hb hab (hd v w hvw)) hvw
  · rintro ⟨i,hi,he⟩
    have hc := List.isChain_iff_getElem.mp hp.2.2.2 i hi
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hc
    · exact hs.symm _ _ hc

lemma exists_trace {V : Type*} {r : V → V → Prop} (hs : Std.Symm r)
    (hirr : ∀ v, ¬r v v) {a b : V} (hr : Relation.ReflTransGen r a b) :
    ∃ p : List V, Trace r a b p := by
  let G : SimpleGraph V := ⟨r,hs,⟨hirr⟩⟩
  obtain ⟨w,hw⟩ := ((SimpleGraph.reachable_iff_reflTransGen (G := G) a b).mpr hr).exists_isPath
  refine ⟨w.support,?_,?_,hw.support_nodup,w.isChain_adj_support⟩
  · rw [List.head?_eq_some_head w.support_ne_nil]; simp
  · rw [List.getLast?_eq_some_getLast w.support_ne_nil]; simp

lemma Trace.eq_singleton {V : Type*} {r : V → V → Prop} {a : V} {p : List V}
    (hp : Trace r a a p) : p = [a] := by
  have hpos : 0 < p.length := by
    cases p with
    | nil => simp [Trace] at hp
    | cons => simp
  have hf := hp.first hpos
  have hl := hp.last (by omega)
  have he : 0 = p.length-1 := hp.2.2.1.getElem_inj_iff.mp (hf.trans hl.symm)
  obtain ⟨l,rfl⟩ := List.head?_eq_some_iff.mp hp.1
  have hlen : l.length=0 := by simp only [List.length_cons] at he; omega
  simp only [List.length_eq_zero_iff.mp hlen]

lemma Trace.avoid {V : Type*} {r : V → V → Prop} {x a b : V} {p : List V}
    (hp : Trace r a b p) (hx : x ∉ p) :
    Trace (fun v w => r v w ∧ v ≠ x ∧ w ≠ x) a b p := by
  refine ⟨hp.1,hp.2.1,hp.2.2.1,?_⟩
  rw [List.isChain_iff_getElem]
  intro i hi
  exact ⟨List.isChain_iff_getElem.mp hp.2.2.2 i hi,
    fun he => hx (List.mem_of_getElem he), fun he => hx (List.mem_of_getElem he)⟩

 

theorem Trace.unique {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) {p q : List V}
    (hp : Trace r a b p) (hq : Trace r a b q) : p = q := by
  induction p generalizing r a b q with
  | nil => simp [Trace] at hp
  | cons x p ih =>
    have hxa : x=a := by simpa using hp.1
    subst x
    by_cases hab : a=b
    · subst b
      exact hp.eq_singleton.trans hq.eq_singleton.symm
    have hl := hp.length_two_le hab
    obtain ⟨q,rfl⟩ := List.head?_eq_some_iff.mp hq.1
    have hlq := hq.length_two_le hab
    cases p with
    | nil => simp at hl
    | cons v p =>
      cases q with
      | nil => simp at hlq
      | cons w q =>
        have hav : r a v := (List.isChain_cons_cons.mp hp.2.2.2).1
        have haw : r a w := (List.isChain_cons_cons.mp hq.2.2.2).1
        have hvw := ha hav haw
        subst w
        let s : V → V → Prop := fun v w => r v w ∧ v ≠ a ∧ w ≠ a
        have hsp : Trace s v b (v::p) := by
          apply Trace.avoid (r := r)
          · refine ⟨rfl,?_,hp.2.2.1.of_cons,(List.isChain_cons_cons.mp hp.2.2.2).2⟩
            simpa only [List.getLast?_cons_cons] using hp.2.1
          · exact (List.nodup_cons.mp hp.2.2.1).1
        have hsq : Trace s v b (v::q) := by
          apply Trace.avoid (r := r)
          · refine ⟨rfl,?_,hq.2.2.1.of_cons,(List.isChain_cons_cons.mp hq.2.2.2).2⟩
            simpa only [List.getLast?_cons_cons] using hq.2.1
          · exact (List.nodup_cons.mp hq.2.2.1).1
        have hss : Std.Symm s := ⟨fun x y h => ⟨hs.symm _ _ h.1,h.2.2,h.2.1⟩⟩
        have hs₂ : AtMostTwo s := by
          intro v x y z hx hy hz hn
          exact h₂ hx.1 hy.1 hz.1 hn
        have hs₁ : AtMostOne s v := by
          intro x y hx hy
          rcases h₂ (hs.symm _ _ hav) hx.1 hy.1 hx.2.2.symm with hy' | hy'
          · exact (hy.2.2 hy').elim
          · exact hy'.symm
        exact congrArg (List.cons a) (ih hss hs₂ hs₁ hsp hsq)

 

theorem existsUnique_trace {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) (hirr : ∀ v, ¬r v v) (h₂ : AtMostTwo r) {a b : V}
    (ha : AtMostOne r a) (hr : Relation.ReflTransGen r a b) :
    ∃! p : List V, Trace r a b p := by
  obtain ⟨p,hp⟩ := exists_trace hs hirr hr
  exact ⟨p,hp,fun q hq => hq.unique hs h₂ ha hp⟩

lemma consecutive_iff_neighbors {V : Type*} {p : List V} (hp : p.Nodup)
    (i : ℕ) (hi : i < p.length) (v : V) :
    Consecutive p p[i] v ↔
      (∃ h : 0 < i, v = p[i-1]) ∨ (∃ h : i+1 < p.length, v = p[i+1]) := by
  constructor
  · rintro ⟨j,hj,⟨he,hv⟩ | ⟨hv,he⟩⟩
    · have hji : j=i := hp.getElem_inj_iff.mp he
      subst j
      exact Or.inr ⟨hj,hv.symm⟩
    · have hji : j+1=i := hp.getElem_inj_iff.mp he
      have hj' : j=i-1 := by omega
      exact Or.inl ⟨by omega,by simpa only [hj'] using hv.symm⟩
  · rintro (⟨_,hv⟩ | ⟨hv,hv'⟩)
    · refine ⟨i-1,by omega,Or.inr ⟨hv.symm,?_⟩⟩
      have he : i-1+1=i := by omega
      simp only [he]
    · exact ⟨i,hv,Or.inl ⟨rfl,hv'.symm⟩⟩

lemma consecutive_irrefl {V : Type*} {p : List V} (hp : p.Nodup) (v : V) :
    ¬Consecutive p v v := by
  rintro ⟨i,hi,⟨h₁,h₂⟩ | ⟨h₂,h₁⟩⟩ <;>
    have hh := hp.getElem_inj_iff.mp (h₁.trans h₂.symm) <;> omega

lemma consecutive_two {V : Type*} {p : List V} (hp : p.Nodup) :
    AtMostTwo (Consecutive p) := by
  intro v x y z hx hy hz hxy
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem (consecutive_mem hx).1
  rw [consecutive_iff_neighbors hp i hi] at hx hy hz
  rcases hx with ⟨hx,rfl⟩ | ⟨hx,rfl⟩ <;>
    rcases hy with ⟨hy,rfl⟩ | ⟨hy,rfl⟩ <;>
    rcases hz with ⟨hz,rfl⟩ | ⟨hz,rfl⟩ <;> simp_all

lemma consecutive_first_one {V : Type*} {p : List V} (hp : p.Nodup)
    (hpos : 0 < p.length) : AtMostOne (Consecutive p) p[0] := by
  intro x y hx hy
  rw [consecutive_iff_neighbors hp 0 hpos] at hx hy
  simpa only [Nat.lt_irrefl,exists_false,exists_prop,and_true,false_or,exists_and_left] using
    (show x=y from by rcases hx with ⟨h,h'⟩ | ⟨h,rfl⟩; · omega
                      rcases hy with ⟨h,h'⟩ | ⟨h,rfl⟩; · omega
                      rfl)

lemma consecutive_last_one {V : Type*} {p : List V} (hp : p.Nodup)
    (hpos : 0 < p.length) : AtMostOne (Consecutive p) p[p.length-1] := by
  intro x y hx hy
  rw [consecutive_iff_neighbors hp (p.length-1) (by omega)] at hx hy
  rcases hx with ⟨h,rfl⟩ | ⟨h,h'⟩
  · rcases hy with ⟨h,rfl⟩ | ⟨h,h'⟩
    · rfl
    · omega
  · omega

lemma consecutive_chain {V : Type*} (p : List V) : p.IsChain (Consecutive p) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  exact ⟨i,hi,Or.inl ⟨rfl,rfl⟩⟩

lemma Trace.used_of_mem {V : Type*} {r : V → V → Prop}
    (hs : Std.Symm r) {a b : V} {p : List V} (hp : Trace r a b p)
    (hab : a ≠ b) {v : V} (hv : v ∈ p) : ∃ w, r v w := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  have hl := hp.length_two_le hab
  have hc := List.isChain_iff_getElem.mp hp.2.2.2
  by_cases hi' : i+1 < p.length
  · exact ⟨p[i+1],hc i hi'⟩
  · have hi0 : 0 < i := by omega
    have he : i-1+1=i := by omega
    exact ⟨p[i-1],by simpa only [he] using hs.symm _ _ (hc (i-1) (by omega))⟩

lemma Trace.reach_of_mem {V : Type*} {r : V → V → Prop} {a b : V}
    {p : List V} (hp : Trace r a b p) {v : V} (hv : v ∈ p) :
    Relation.ReflTransGen r a v := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  induction i with
  | zero => rw [hp.first (by omega)]
  | succ i ih =>
    exact (ih (by omega) (by simp)).tail (List.isChain_iff_getElem.mp hp.2.2.2 i hi)

end
end CriticalStrip.Diagram.PathGraph

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram.PathGraph

 

structure WireConfiguration (N : ℕ) (finish : Triangle) where
  graph : SimpleGraph Triangle
  allowed : ∀ v w, graph.Adj v w → adjacent v w ∧ v.2.1 < N ∧ w.2.1 < N
  two : AtMostTwo graph.Adj
  source_one : AtMostOne graph.Adj (up 0 0)
  finish_one : AtMostOne graph.Adj finish
  source_used : ∃ w, graph.Adj (up 0 0) w
  finish_used : ∃ w, graph.Adj finish w
  drains : ∀ v w, graph.Adj v w → Relation.ReflTransGen graph.Adj v (up 0 0)

namespace WireConfiguration
variable {N : ℕ} {finish : Triangle}

@[ext] theorem ext {x y : WireConfiguration N finish} (h : x.graph = y.graph) : x=y := by
  cases x; cases y; cases h; rfl

lemma reach (D : WireConfiguration N finish) :
    Relation.ReflTransGen D.graph.Adj (up 0 0) finish := by
  obtain ⟨w,hw⟩ := D.finish_used
  have : Std.Symm D.graph.Adj := D.graph.symm
  exact symm (D.drains finish w hw)

lemma existsUniqueTrace (D : WireConfiguration N finish) :
    ∃! p : List Triangle, Trace D.graph.Adj (up 0 0) finish p :=
  existsUnique_trace D.graph.symm (fun v => D.graph.loopless.irrefl v) D.two D.source_one D.reach

 

def path (D : WireConfiguration N finish) : List Triangle :=
  Classical.choose D.existsUniqueTrace

lemma path_trace (D : WireConfiguration N finish) :
    Trace D.graph.Adj (up 0 0) finish D.path :=
  (Classical.choose_spec D.existsUniqueTrace).1

lemma path_isPath (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    IsPath N finish D.path := by
  have h := D.path_trace
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.imp (fun {_ _} hvw => (D.allowed _ _ hvw).1),?_⟩
  intro v hv
  obtain ⟨w,hw⟩ := h.used_of_mem D.graph.symm hf.symm hv
  exact (D.allowed _ _ hw).2.1

lemma edges_iff (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) (v w : Triangle) :
    D.graph.Adj v w ↔ Consecutive D.path v w :=
  D.path_trace.edges_iff D.graph.symm D.two D.source_one D.finish_one hf.symm D.drains v w


lemma ofPath_trace {p : List Triangle} (hp : IsPath N finish p) :
    Trace (Consecutive p) (up 0 0) finish p :=
  ⟨hp.1,hp.2.1,hp.2.2.1,consecutive_chain p⟩

 

def ofPath {p : List Triangle} (hf : finish ≠ up 0 0) (hp : IsPath N finish p) :
    WireConfiguration N finish := by
  have h : Trace (Consecutive p) (up 0 0) finish p := ofPath_trace hp
  have hs : Std.Symm (Consecutive p) := ⟨fun _ _ => consecutive_symm⟩
  have hl : 0 < p.length := lt_of_lt_of_le (by omega) (h.length_two_le hf.symm)
  refine ⟨⟨Consecutive p,hs,⟨consecutive_irrefl hp.2.2.1⟩⟩,?_,consecutive_two hp.2.2.1,?_,?_,?_,?_,?_⟩
  · intro v w hvw
    obtain ⟨hv,hw⟩ := consecutive_mem hvw
    refine ⟨?_,hp.2.2.2.2 v hv,hp.2.2.2.2 w hw⟩
    obtain ⟨i,hi,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := hvw
    · exact List.isChain_iff_getElem.mp hp.2.2.2.1 i hi
    · exact adjacent_symmetric.symm _ _ (List.isChain_iff_getElem.mp hp.2.2.2.1 i hi)
  · simpa only [h.first hl] using consecutive_first_one hp.2.2.1 hl
  · simpa only [h.last (by omega)] using consecutive_last_one hp.2.2.1 hl
  · exact h.used_of_mem hs hf.symm (List.mem_of_getElem (h.first hl))
  · exact h.used_of_mem hs hf.symm (List.mem_of_getElem (h.last (by omega)))
  · intro v w hvw
    have : Std.Symm (Consecutive p) := hs
    exact symm (h.reach_of_mem (consecutive_mem hvw).1)

@[simp] lemma ofPath_graph {p : List Triangle} (hf : finish ≠ up 0 0)
    (hp : IsPath N finish p) (v w : Triangle) :
    (ofPath hf hp).graph.Adj v w ↔ Consecutive p v w := Iff.rfl

@[simp] theorem ofPath_path {p : List Triangle} (hf : finish ≠ up 0 0)
    (hp : IsPath N finish p) : (ofPath hf hp).path = p := by
  exact (ofPath hf hp).path_trace.unique (ofPath hf hp).graph.symm
    (ofPath hf hp).two (ofPath hf hp).source_one (ofPath_trace hp)

@[simp] theorem ofPath_path_isPath (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    ofPath hf (D.path_isPath hf) = D := by
  apply ext
  apply SimpleGraph.ext
  funext v w
  exact propext (D.edges_iff hf v w).symm



end WireConfiguration
end





noncomputable section
open scoped Classical BigOperators
open Diagram.PathGraph

lemma Diagram.PathGraph.Trace.two_neighbors {V : Type*} {r : V → V → Prop} (hs : Std.Symm r)
    {a b : V} {p : List V} (hp : Trace r a b p) {v : V}
    (hv : v ∈ p) (ha : v ≠ a) (hb : v ≠ b) :
    ∃ x y, r v x ∧ r v y ∧ x ≠ y := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  have hz : 0 < i := by
    by_contra h
    have he : i=0 := by omega
    exact ha (by simpa only [he] using hp.first (by omega))
  have ht : i+1 < p.length := by
    by_contra h
    have he : i=p.length-1 := by omega
    exact hb (by simpa only [he] using hp.last (by omega))
  have hc := List.isChain_iff_getElem.mp hp.2.2.2
  refine ⟨p[i-1],p[i+1],?_,hc i ht,?_⟩
  · have he : i-1+1=i := by omega
    simpa only [he] using hs.symm _ _ (hc (i-1) (by omega))
  · intro he
    have := hp.2.2.1.getElem_inj_iff.mp he
    omega

namespace WireConfiguration
variable {N : ℕ} {finish : Triangle}

lemma another_neighbor (D : WireConfiguration N finish) (hf : finish ≠ up 0 0)
    {v w : Triangle} (hvw : D.graph.Adj v w) (ha : v ≠ up 0 0) (hb : v ≠ finish) :
    ∃ z, D.graph.Adj v z ∧ z ≠ w := by
  obtain ⟨x,y,hx,hy,hxy⟩ := D.path_trace.two_neighbors D.graph.symm
    (consecutive_mem ((D.edges_iff hf v w).mp hvw)).1 ha hb
  by_cases h : x=w
  · exact ⟨y,hy,by simpa only [←h] using hxy.symm⟩
  · exact ⟨x,hx,h⟩

end WireConfiguration

lemma adjacent_up_iff (i : ℤ) (j : ℕ) (w : Triangle) :
    adjacent (up i j) w ↔ w=down i j ∨ w=down (i-1) j ∨
      (0<j ∧ w=down i (j-1)) := by
  rcases w with ⟨k,l,b⟩
  cases b <;> simp only [adjacent,upDownAdjacent,up,down,Prod.mk.injEq,Bool.false_eq_true,
    Bool.true_eq_false,true_and,false_and,or_false,and_true,and_false]
  all_goals omega

lemma adjacent_down_iff (i : ℤ) (j : ℕ) (w : Triangle) :
    adjacent (down i j) w ↔ w=up i j ∨ w=up (i+1) j ∨ w=up i (j+1) := by
  rcases w with ⟨k,l,b⟩
  cases b <;> simp only [adjacent,upDownAdjacent,up,down,Prod.mk.injEq,Bool.false_eq_true,
    Bool.true_eq_false,true_and,false_and,false_or,or_false,and_true,and_false]
  all_goals omega

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical
namespace ColumnChain
variable {n : ℕ}

 

def read (ts : List (Configuration n)) (k : ℕ) : Configuration n :=
  (ts[k]?).getD (fun _=>.vacant)

@[simp] lemma read_nil (k : ℕ) : read ([] : List (Configuration n)) k=fun _=>.vacant := by
  simp [read]
@[simp] lemma read_cons_zero (t : Configuration n) (ts : List (Configuration n)) :
    read (t::ts) 0=t := rfl
@[simp] lemma read_cons_succ (t : Configuration n) (ts : List (Configuration n)) (k : ℕ) :
    read (t::ts) (k+1)=read ts k := rfl

end ColumnChain
end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombTiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators

 
def ValidTriangle (a b m : Prop) : Prop :=
  (¬a ∧ ¬b ∧ ¬m) ∨ (a ∧ b ∧ ¬m) ∨ (a ∧ ¬b ∧ m) ∨ (¬a ∧ b ∧ m)

lemma ValidTriangle.of_not_three_not_one {a b m : Prop}
    (h₃ : ¬(a ∧ b ∧ m)) (ha : a → b ∨ m) (hb : b → a ∨ m) (hm : m → a ∨ b) :
    ValidTriangle a b m := by
  unfold ValidTriangle
  tauto

namespace Tile

 

def middle : Tile → Bool
  | .vertical₀ | .vertical₁ | .diagonal₀ | .diagonal₁ => true
  | _ => false

lemma physical_ext {t u : Tile} (ht : t ≠ .verticalPair) (hu : u ≠ .verticalPair)
    (h : ∀ i, t.Occupied i ↔ u.Occupied i) (hm : t.middle=u.middle) : t=u := by
  revert t u
  decide

 

theorem existsUnique_physical (s w e n m : Bool)
    (hu : ValidTriangle s w m) (hd : ValidTriangle e n m) :
    ∃! t : Tile, t ≠ .verticalPair ∧
      (t.Occupied 0 ↔ s) ∧ (t.Occupied 1 ↔ w) ∧
      (t.Occupied 2 ↔ e) ∧ (t.Occupied 3 ↔ n) ∧ t.middle=m := by
  have hex : ∃ t : Tile, t ≠ .verticalPair ∧
      (t.Occupied 0 ↔ s) ∧ (t.Occupied 1 ↔ w) ∧
      (t.Occupied 2 ↔ e) ∧ (t.Occupied 3 ↔ n) ∧ t.middle=m := by
    cases s <;> cases w <;> cases e <;> cases n <;> cases m <;>
      simp_all only [ValidTriangle, Bool.false_eq_true, not_false_eq_true, not_true,
        and_false, and_true, or_false, false_or]
    all_goals first
      | exact ⟨.vacant, by decide⟩
      | exact ⟨.vertical₀, by decide⟩
      | exact ⟨.vertical₁, by decide⟩
      | exact ⟨.diagonal₀, by decide⟩
      | exact ⟨.diagonal₁, by decide⟩
      | exact ⟨.cap, by decide⟩
      | exact ⟨.cup, by decide⟩
      | exact ⟨.capCup, by decide⟩
  obtain ⟨t,ht⟩ := hex
  refine ⟨t,ht,?_⟩
  intro u hu
  apply physical_ext hu.1 ht.1 ?_ (hu.2.2.2.2.2.trans ht.2.2.2.2.2.symm)
  intro i
  fin_cases i
  · exact hu.2.1.trans ht.2.1.symm
  · exact hu.2.2.1.trans ht.2.2.1.symm
  · exact hu.2.2.2.1.trans ht.2.2.2.1.symm
  · exact hu.2.2.2.2.1.trans ht.2.2.2.2.1.symm


end Tile
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram Diagram.PathGraph

abbrev Cell := ℤ × ℕ

 

def upDownWire (t : Cell → Tile) (v w : Triangle) : Prop :=
  v.2.2=true ∧ w.2.2=false ∧
  ((v.2.1=w.2.1 ∧
     ((w.1=v.1 ∧ (t (v.1,v.2.1)).middle) ∨
      (w.1+1=v.1 ∧ (t (v.1,v.2.1)).Occupied 1))) ∨
   (v.2.1=w.2.1+1 ∧ v.1=w.1 ∧ (t (v.1,v.2.1)).Occupied 0))

def tileGraph (N : ℕ) (t : Cell → Tile) : SimpleGraph Triangle where
  Adj v w := v.2.1<N ∧ w.2.1<N ∧ (upDownWire t v w ∨ upDownWire t w v)
  symm := ⟨fun v w h => ⟨h.2.1,h.1,h.2.2.symm⟩⟩
  loopless := ⟨by
    intro v h
    rcases h.2.2 with h | h <;> exact Bool.noConfusion (h.1.symm.trans h.2.1)⟩

lemma tileGraph_allowed (N : ℕ) (t : Cell → Tile) {v w : Triangle}
    (h : (tileGraph N t).Adj v w) : adjacent v w ∧ v.2.1<N ∧ w.2.1<N := by
  refine ⟨?_,h.1,h.2.1⟩
  have hu : ∀ v w, upDownWire t v w → upDownAdjacent v w := by
    intro v w ⟨hv,hw,h⟩
    refine ⟨hv,hw,?_⟩
    rcases h with ⟨hj,hk⟩ | ⟨hj,hk,ho⟩
    · exact Or.inl ⟨hj,hk.imp And.left And.left⟩
    · exact Or.inr ⟨hj,hk⟩
  exact h.2.2.imp (hu v w) (hu w v)

lemma tileGraph_middle (N : ℕ) (t : Cell → Tile) (i : ℤ) (j : ℕ) :
    (tileGraph N t).Adj (up i j) (down i j) ↔ j<N ∧ (t (i,j)).middle := by
  simp [tileGraph,upDownWire,up,down]

lemma tileGraph_west (N : ℕ) (t : Cell → Tile) (i : ℤ) (j : ℕ) :
    (tileGraph N t).Adj (up i j) (down (i-1) j) ↔ j<N ∧ (t (i,j)).Occupied 1 := by
  simp [tileGraph,upDownWire,up,down]

lemma tileGraph_south (N : ℕ) (t : Cell → Tile) (i : ℤ) (j : ℕ) (hj : 0<j) :
    (tileGraph N t).Adj (up i j) (down i (j-1)) ↔ j<N ∧ (t (i,j)).Occupied 0 := by
  have hn : j ≠ j-1 := by omega
  have hpred : j-1+1=j := by omega
  have hbound : j<N → j-1<N := by omega
  simp [tileGraph,upDownWire,up,down,hn,hpred,and_left_comm]
  exact fun hj _ => hbound hj

lemma tileGraph_up (N : ℕ) (t : Cell → Tile) (i : ℤ) (j : ℕ) (w : Triangle) :
    (tileGraph N t).Adj (up i j) w ↔ j<N ∧
      ((w=down i j ∧ (t (i,j)).middle) ∨
       (w=down (i-1) j ∧ (t (i,j)).Occupied 1) ∨
       (0<j ∧ w=down i (j-1) ∧ (t (i,j)).Occupied 0)) := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    rcases (adjacent_up_iff i j w).mp (tileGraph_allowed N t h).1 with rfl | rfl | ⟨hj,rfl⟩
    · exact Or.inl ⟨rfl,((tileGraph_middle N t i j).mp h).2⟩
    · exact Or.inr (Or.inl ⟨rfl,((tileGraph_west N t i j).mp h).2⟩)
    · exact Or.inr (Or.inr ⟨hj,rfl,((tileGraph_south N t i j hj).mp h).2⟩)
  · rintro ⟨hj,⟨rfl,hm⟩ | ⟨rfl,hm⟩ | ⟨hpos,rfl,hm⟩⟩
    · exact (tileGraph_middle N t i j).mpr ⟨hj,hm⟩
    · exact (tileGraph_west N t i j).mpr ⟨hj,hm⟩
    · exact (tileGraph_south N t i j hpos).mpr ⟨hj,hm⟩

 
structure HoneycombAssignment (N : ℕ) where
  tile : Cell → Tile
  physical : ∀ q, tile q ≠ .verticalPair
  outside : ∀ i j, N≤j → tile (i,j)=.vacant
  horizontal : ∀ i j, (tile (i,j)).Occupied 2 ↔ (tile (i+1,j)).Occupied 1
  vertical : ∀ i j, j+1<N → ((tile (i,j)).Occupied 3 ↔ (tile (i,j+1)).Occupied 0)

namespace HoneycombAssignment
variable {N : ℕ}

def graph (D : HoneycombAssignment N) : SimpleGraph Triangle := tileGraph N D.tile

lemma up_neighbors (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) (w : Triangle) :
    D.graph.Adj (up i j) w ↔ j<N ∧
      ((w=down i j ∧ (D.tile (i,j)).middle) ∨
       (w=down (i-1) j ∧ (D.tile (i,j)).Occupied 1) ∨
       (0<j ∧ w=down i (j-1) ∧ (D.tile (i,j)).Occupied 0)) :=
  tileGraph_up N D.tile i j w

end HoneycombAssignment






lemma validTriangle_of_neighbors {V : Type*} {r : V → V → Prop} {v a b c : V}
    (h₂ : AtMostTwo r) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (he : ∀ w, r v w → w=a ∨ w=b ∨ w=c)
    (ho : ∀ w, r v w → ∃ z, r v z ∧ z≠w) :
    ValidTriangle (r v a) (r v b) (r v c) := by
  apply ValidTriangle.of_not_three_not_one
  · rintro ⟨ha,hb,hc⟩
    exact (h₂ ha hb hc hab).elim hac.symm hbc.symm
  · intro ha
    obtain ⟨z,hz,hza⟩ := ho a ha
    rcases he z hz with rfl | rfl | rfl
    · exact (hza rfl).elim
    · exact Or.inl hz
    · exact Or.inr hz
  · intro hb
    obtain ⟨z,hz,hzb⟩ := ho b hb
    rcases he z hz with rfl | rfl | rfl
    · exact Or.inl hz
    · exact (hzb rfl).elim
    · exact Or.inr hz
  · intro hc
    obtain ⟨z,hz,hzc⟩ := ho c hc
    rcases he z hz with rfl | rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
    · exact (hzc rfl).elim

lemma validTriangle_with_port {V : Type*} {r : V → V → Prop} {v a b : V} {P : Prop}
    (hab : a≠b) (he : ∀ w, r v w → w=a ∨ w=b)
    (h₁ : P → AtMostOne r v) (hu : P → ∃ w, r v w)
    (ho : ¬P → ∀ w, r v w → ∃ z, r v z ∧ z≠w) :
    ValidTriangle P (r v a) (r v b) := by
  apply ValidTriangle.of_not_three_not_one
  · exact fun ⟨hp,ha,hb⟩ => hab (h₁ hp ha hb)
  · intro hp
    obtain ⟨w,hw⟩ := hu hp
    rcases he w hw with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  · intro ha
    by_cases hp : P
    · exact Or.inl hp
    obtain ⟨w,hw,hwa⟩ := ho hp a ha
    rcases he w hw with rfl | rfl
    · exact (hwa rfl).elim
    · exact Or.inr hw
  · intro hb
    by_cases hp : P
    · exact Or.inl hp
    obtain ⟨w,hw,hwb⟩ := ho hp b hb
    rcases he w hw with rfl | rfl
    · exact Or.inr hw
    · exact (hwb rfl).elim

 
inductive BoundaryPort where
  | bottom (index : ℤ)
  | top (index : ℤ)
  deriving DecidableEq

namespace BoundaryPort

def vertex (N : ℕ) : BoundaryPort → Triangle
  | .bottom k => up k 0
  | .top k => down k (N-1)

lemma vertex_ne_source {N : ℕ} (b : BoundaryPort) (hb : b ≠ .bottom 0) :
    b.vertex N ≠ up 0 0 := by
  cases b with
  | bottom k => simpa [vertex,up] using hb
  | top k => simp [vertex,up,down]

lemma up_eq_iff {N j : ℕ} {i : ℤ} {b : BoundaryPort} :
    up i j=b.vertex N ↔ b=.bottom i ∧ j=0 := by
  cases b <;> simp [vertex,up,down,eq_comm]

lemma down_eq_iff {N j : ℕ} {i : ℤ} {b : BoundaryPort} :
    down i j=b.vertex N ↔ b=.top i ∧ j=N-1 := by
  cases b <;> simp [vertex,up,down,eq_comm]

end BoundaryPort

namespace WireConfiguration
variable {N : ℕ} {b : BoundaryPort}

def south (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  if j=0 then i=0 ∨ b=.bottom i else D.graph.Adj (up i j) (down i (j-1))

def west (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  D.graph.Adj (up i j) (down (i-1) j)

def middle (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  D.graph.Adj (up i j) (down i j)

def east (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  D.graph.Adj (down i j) (up (i+1) j)

def north (D : WireConfiguration N (b.vertex N)) (i : ℤ) (j : ℕ) : Prop :=
  if j+1=N then b=.top i else D.graph.Adj (down i j) (up i (j+1))

lemma up_nonterminal (_D : WireConfiguration N (b.vertex N)) {i : ℤ} {j : ℕ}
    (hj : 0<j) : up i j ≠ up 0 0 ∧ up i j ≠ b.vertex N := by
  constructor
  · simp [up,show j≠0 by omega]
  · simp [BoundaryPort.up_eq_iff,show j≠0 by omega]

lemma down_nonterminal (_D : WireConfiguration N (b.vertex N)) {i : ℤ} {j : ℕ}
    (hj : j+1<N) : down i j ≠ up 0 0 ∧ down i j ≠ b.vertex N := by
  constructor
  · simp [up,down]
  · simp [BoundaryPort.down_eq_iff,show j≠N-1 by omega]

lemma up_valid (D : WireConfiguration N (b.vertex N)) (_hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) (j : ℕ) :
    ValidTriangle (D.south i j) (D.west i j) (D.middle i j) := by
  have hf := b.vertex_ne_source (N := N) hb
  by_cases hj : j=0
  · subst j
    simp only [south,west,middle]
    apply validTriangle_with_port (a := down (i-1) 0) (b := down i 0)
      (by simp [down])
    · intro w hw
      have ha := (adjacent_up_iff i 0 w).mp (D.allowed _ _ hw).1
      simpa only [lt_self_iff_false,false_and,or_false,false_or,or_comm] using ha
    · rintro (rfl | ht)
      · exact D.source_one
      · subst b; exact D.finish_one
    · rintro (rfl | ht)
      · exact D.source_used
      · subst b; exact D.finish_used
    · intro hn w hw
      apply D.another_neighbor hf hw
      · have h : i≠0 := fun h => hn (Or.inl h)
        simpa [up] using h
      · intro he
        exact hn (Or.inr (BoundaryPort.up_eq_iff.mp he).1)
  · have hpos : 0<j := by omega
    simp only [south,ite_eq_right hj,west,middle]
    apply validTriangle_of_neighbors D.two
      (a := down i (j-1)) (b := down (i-1) j) (c := down i j)
      (by simp [down]; omega) (by simp [down,show j-1≠j by omega]) (by simp [down])
    · intro w hw
      have ha := (adjacent_up_iff i j w).mp (D.allowed _ _ hw).1
      tauto
    · intro w hw
      exact D.another_neighbor hf hw (D.up_nonterminal hpos).1 (D.up_nonterminal hpos).2

lemma down_valid (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) (j : ℕ) :
    ValidTriangle (D.east i j) (D.north i j) (D.middle i j) := by
  have hf := b.vertex_ne_source (N := N) hb
  have hm : D.middle i j ↔ D.graph.Adj (down i j) (up i j) :=
    ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩
  by_cases hj : j<N
  · by_cases ht : j+1=N
    · have he : j=N-1 := by omega
      subst j
      simp only [east,north,ite_eq_left ht,hm]
      have h := validTriangle_with_port (r := D.graph.Adj) (v := down i (N-1))
        (a := up (i+1) (N-1)) (b := up i (N-1)) (P := b=.top i)
        (by simp [up]) ?_ ?_ ?_ ?_
      · unfold ValidTriangle at h ⊢; tauto
      · intro w hw
        have ha := (adjacent_down_iff i (N-1) w).mp (D.allowed _ _ hw).1
        rcases ha with ha | ha | rfl
        · exact Or.inr ha
        · exact Or.inl ha
        · have := (D.allowed _ _ hw).2.2; simp only [up] at this; omega
      · intro hb'; subst b; exact D.finish_one
      · intro hb'; subst b; exact D.finish_used
      · intro hn w hw
        exact D.another_neighbor hf hw (by simp [down,up])
          (by intro he; exact hn (BoundaryPort.down_eq_iff.mp he).1)
    · have hnext : j+1<N := by omega
      simp only [east,north,ite_eq_right ht,hm]
      apply validTriangle_of_neighbors D.two
        (a := up (i+1) j) (b := up i (j+1)) (c := up i j)
        (by simp [up]) (by simp [up]) (by simp [up])
      · intro w hw
        have ha := (adjacent_down_iff i j w).mp (D.allowed _ _ hw).1
        tauto
      · intro w hw
        exact D.another_neighbor hf hw (D.down_nonterminal hnext).1 (D.down_nonterminal hnext).2
  · have he : ∀ w, ¬ D.graph.Adj (down i j) w := by
      intro w hw; exact hj (D.allowed _ _ hw).2.1
    have hn : j+1≠N := by omega
    simp only [east,north,ite_eq_right hn,hm,he,ValidTriangle,not_false_eq_true,and_self,true_or]

 
lemma flags_outside (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (i : ℤ) (j : ℕ) (hj : N≤j) :
    ¬ D.south i j ∧ ¬ D.west i j ∧ ¬ D.east i j ∧ ¬ D.north i j ∧ ¬ D.middle i j := by
  have he : ∀ w, ¬ D.graph.Adj (up i j) w := by
    intro w hw; have := (D.allowed _ _ hw).2.1; exact (by omega : ¬j<N) this
  have he' : ∀ w, ¬ D.graph.Adj (down i j) w := by
    intro w hw; have := (D.allowed _ _ hw).2.1; exact (by omega : ¬j<N) this
  simp [south,west,east,north,middle,show j≠0 by omega,show j+1≠N by omega,he,he']

end WireConfiguration
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombDictionary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram Diagram.PathGraph

namespace HoneycombAssignment
variable {N : ℕ}

@[ext] lemma ext {D E : HoneycombAssignment N} (h : D.tile=E.tile) : D=E := by
  cases D; cases E; cases h; rfl



end HoneycombAssignment

namespace WireConfiguration
variable {N : ℕ} {b : BoundaryPort}

def physicalTile (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (q : Cell) : Tile :=
  Classical.choose (Tile.existsUnique_physical
    (decide (D.south q.1 q.2)) (decide (D.west q.1 q.2))
    (decide (D.east q.1 q.2)) (decide (D.north q.1 q.2)) (decide (D.middle q.1 q.2))
    (by simpa only [decide_eq_true_eq] using D.up_valid hN hb q.1 q.2)
    (by simpa only [decide_eq_true_eq] using D.down_valid hN hb q.1 q.2))

lemma physicalTile_spec (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) (j : ℕ) :
    D.physicalTile hN hb (i,j) ≠ .verticalPair ∧
    ((D.physicalTile hN hb (i,j)).Occupied 0 ↔ D.south i j) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 1 ↔ D.west i j) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 2 ↔ D.east i j) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 3 ↔ D.north i j) ∧
    ((D.physicalTile hN hb (i,j)).middle ↔ D.middle i j) := by
  have h := (Classical.choose_spec (Tile.existsUnique_physical
    (decide (D.south i j)) (decide (D.west i j))
    (decide (D.east i j)) (decide (D.north i j)) (decide (D.middle i j))
    (by simpa only [decide_eq_true_eq] using D.up_valid hN hb i j)
    (by simpa only [decide_eq_true_eq] using D.down_valid hN hb i j))).1
  change D.physicalTile hN hb (i,j) ≠ .verticalPair ∧
    ((D.physicalTile hN hb (i,j)).Occupied 0 ↔ decide (D.south i j) = true) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 1 ↔ decide (D.west i j) = true) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 2 ↔ decide (D.east i j) = true) ∧
    ((D.physicalTile hN hb (i,j)).Occupied 3 ↔ decide (D.north i j) = true) ∧
    (D.physicalTile hN hb (i,j)).middle=decide (D.middle i j) at h
  refine ⟨h.1,?_,?_,?_,?_,?_⟩
  · simpa only [decide_eq_true_eq] using h.2.1
  · simpa only [decide_eq_true_eq] using h.2.2.1
  · simpa only [decide_eq_true_eq] using h.2.2.2.1
  · simpa only [decide_eq_true_eq] using h.2.2.2.2.1
  · rw [h.2.2.2.2.2,decide_eq_true_eq]

 

def toAssignment (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : HoneycombAssignment N where
  tile := D.physicalTile hN hb
  physical q := (D.physicalTile_spec hN hb q.1 q.2).1
  outside i j hj := by
    apply (Tile.eq_vacant_iff _).mpr
    intro p
    have h := D.physicalTile_spec hN hb i j
    have hf := D.flags_outside hN i j hj
    fin_cases p
    · exact fun hp => hf.1 (h.2.1.mp hp)
    · exact fun hp => hf.2.1 (h.2.2.1.mp hp)
    · exact fun hp => hf.2.2.1 (h.2.2.2.1.mp hp)
    · exact fun hp => hf.2.2.2.1 (h.2.2.2.2.1.mp hp)
  horizontal i j := by
    rw [(D.physicalTile_spec hN hb i j).2.2.2.1,
      (D.physicalTile_spec hN hb (i+1) j).2.2.1]
    simp only [east,west,add_sub_cancel_right]
    exact ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩
  vertical i j hj := by
    rw [(D.physicalTile_spec hN hb i j).2.2.2.2.1,
      (D.physicalTile_spec hN hb i (j+1)).2.1]
    simp only [north,south,show j+1≠N by omega,show j+1≠0 by omega,
      add_tsub_cancel_right]
    exact ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩

lemma toAssignment_up (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) (j : ℕ) (w : Triangle) :
    (D.toAssignment hN hb).graph.Adj (up i j) w ↔ D.graph.Adj (up i j) w := by
  rw [HoneycombAssignment.up_neighbors]
  change (j<N ∧ ((w=down i j ∧ (D.physicalTile hN hb (i,j)).middle) ∨
    (w=down (i-1) j ∧ (D.physicalTile hN hb (i,j)).Occupied 1) ∨
    (0<j ∧ w=down i (j-1) ∧ (D.physicalTile hN hb (i,j)).Occupied 0))) ↔ _
  rw [(D.physicalTile_spec hN hb i j).2.2.2.2.2,
    (D.physicalTile_spec hN hb i j).2.2.1,(D.physicalTile_spec hN hb i j).2.1]
  constructor
  · rintro ⟨_,⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨hj,rfl,h⟩⟩
    · exact h
    · exact h
    · simpa only [south,ite_eq_right (show j≠0 by omega)] using h
  · intro h
    refine ⟨(D.allowed _ _ h).2.1,?_⟩
    rcases (adjacent_up_iff i j w).mp (D.allowed _ _ h).1 with rfl | rfl | ⟨hj,rfl⟩
    · exact Or.inl ⟨rfl,h⟩
    · exact Or.inr (Or.inl ⟨rfl,h⟩)
    · exact Or.inr (Or.inr ⟨hj,rfl,by simpa only [south,ite_eq_right (show j≠0 by omega)] using h⟩)

@[simp] theorem toAssignment_graph (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : (D.toAssignment hN hb).graph = D.graph := by
  apply SimpleGraph.ext
  funext v w
  apply propext
  rcases v with ⟨i,j,bv⟩
  cases bv
  · rcases w with ⟨k,l,bw⟩
    cases bw
    · constructor
      · intro h
        have ha := (tileGraph_allowed N (D.toAssignment hN hb).tile h).1
        simp [adjacent,upDownAdjacent] at ha
      · intro h
        have ha := (D.allowed _ _ h).1
        simp [adjacent,upDownAdjacent] at ha
    · exact (show (D.toAssignment hN hb).graph.Adj (down i j) (up k l) ↔
          (D.toAssignment hN hb).graph.Adj (up k l) (down i j) from
          ⟨(D.toAssignment hN hb).graph.symm.symm _ _,(D.toAssignment hN hb).graph.symm.symm _ _⟩).trans
          ((D.toAssignment_up hN hb k l (down i j)).trans
          ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩)
  · exact D.toAssignment_up hN hb i j w

end WireConfiguration

 

structure HoneycombConfiguration (N : ℕ) (b : BoundaryPort) extends HoneycombAssignment N where
  bottom : ∀ i, (tile (i,0)).Occupied 0 ↔ i=0 ∨ b=.bottom i
  top : ∀ i, (tile (i,N-1)).Occupied 3 ↔ b=.top i
  drains : ∀ v w, toHoneycombAssignment.graph.Adj v w →
    Relation.ReflTransGen toHoneycombAssignment.graph.Adj v (up 0 0)

namespace HoneycombConfiguration
variable {N : ℕ} {b : BoundaryPort}

@[ext] lemma ext {D E : HoneycombConfiguration N b}
    (h : D.toHoneycombAssignment=E.toHoneycombAssignment) : D=E := by
  cases D; cases E; cases h; rfl


end HoneycombConfiguration






end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ReversedConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical
namespace Tile

 

def horizontalPort : Equiv.Perm (Fin 4) := Equiv.swap 1 2

def horizontal : Tile → Tile
  | .vertical₀ => .cap
  | .vertical₁ => .cup
  | .cap => .vertical₀
  | .cup => .vertical₁
  | .verticalPair => .capCup
  | .capCup => .verticalPair
  | t => t

@[simp] lemma horizontal_involutive (t : Tile) : t.horizontal.horizontal=t := by cases t <;> rfl

lemma horizontal_occupied (t : Tile) (a : Fin 4) :
    t.horizontal.Occupied (horizontalPort a) ↔ t.Occupied a := by
  revert t a
  decide

end Tile
end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SewnAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Tile
@[simp] lemma horizontal_occupied_zero (t : Tile) : t.horizontal.Occupied 0 ↔ t.Occupied 0 := by
  revert t; decide
@[simp] lemma horizontal_occupied_one (t : Tile) : t.horizontal.Occupied 1 ↔ t.Occupied 2 := by
  simpa [horizontalPort] using horizontal_occupied t 2
@[simp] lemma horizontal_occupied_two (t : Tile) : t.horizontal.Occupied 2 ↔ t.Occupied 1 := by
  simpa [horizontalPort] using horizontal_occupied t 1
@[simp] lemma horizontal_occupied_three (t : Tile) : t.horizontal.Occupied 3 ↔ t.Occupied 3 := by
  revert t; decide
end Diagram.Tile

namespace SewnRectangle
variable {n : ℕ}

 

def tile (l r : List (Configuration n)) (v : Cell) : Tile :=
  if hj : v.2<n then
    if v.1<0 then ColumnChain.read l (-v.1-1).toNat ⟨v.2,hj⟩
    else (ColumnChain.read r v.1.toNat ⟨v.2,hj⟩).horizontal
  else .vacant

@[simp] lemma tile_left (l r : List (Configuration n)) (k : ℕ) (j : Fin n) :
    tile l r (-1-(k:ℤ),j.val)=ColumnChain.read l k j := by
  have hk : -1-(k:ℤ)<0 := by omega
  have he : -(-1-(k:ℤ))-1=(k:ℤ) := by omega
  simp only [tile,j.isLt,dite_eq_left,hk,ite_true,he,Int.toNat_natCast]
@[simp] lemma tile_right (l r : List (Configuration n)) (k : ℕ) (j : Fin n) :
    tile l r ((k:ℤ),j.val)=(ColumnChain.read r k j).horizontal := by
  simp [tile,j.isLt,show ¬(k:ℤ)<0 by omega]
@[simp] lemma tile_outside (l r : List (Configuration n)) (i : ℤ) (j : ℕ) (hj : n≤j) :
    tile l r (i,j)=.vacant := by simp [tile,show ¬j<n by omega]

end SewnRectangle
end
end CriticalStrip





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FiniteEnds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram Diagram.PathGraph

namespace HoneycombAssignment
variable {N M : ℕ}

 

def restrict (D : HoneycombAssignment N) (M : ℕ) (hM : M≤N) : HoneycombAssignment M where
  tile q := if q.2<M then D.tile q else .vacant
  physical q := by split <;> first | exact D.physical q | decide
  outside i j hj := ite_eq_right (by omega)
  horizontal i j := by
    by_cases hj : j<M
    · simp only [hj,ite_true]; exact D.horizontal i j
    · simp only [hj,ite_false,Tile.vacant_not_occupied]
  vertical i j hj := by
    have hj' : j<M := by omega
    simp only [hj,hj',ite_true]
    exact D.vertical i j (by omega)

@[simp] lemma restrict_tile (D : HoneycombAssignment N) (M : ℕ) (hM : M≤N)
    (i : ℤ) (j : ℕ) (hj : j<M) : (D.restrict M hM).tile (i,j)=D.tile (i,j) := by
  simp [restrict,hj]

end HoneycombAssignment
end





end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HalfTurn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Tile

 
def turn : Tile → Tile
  | .vertical₀ => .vertical₁
  | .vertical₁ => .vertical₀
  | .cap => .cup
  | .cup => .cap
  | t => t

@[simp] lemma turn_turn (t : Tile) : t.turn.turn=t := by cases t <;> rfl
@[simp] lemma turn_vacant : Tile.vacant.turn=.vacant := rfl
@[simp] lemma turn_physical (t : Tile) : t.turn≠.verticalPair ↔ t≠.verticalPair := by
  cases t <;> decide
@[simp] lemma turn_occupied_zero (t : Tile) : t.turn.Occupied 0 ↔ t.Occupied 3 := by
  revert t; decide
@[simp] lemma turn_occupied_one (t : Tile) : t.turn.Occupied 1 ↔ t.Occupied 2 := by
  revert t; decide
@[simp] lemma turn_occupied_two (t : Tile) : t.turn.Occupied 2 ↔ t.Occupied 1 := by
  revert t; decide
@[simp] lemma turn_occupied_three (t : Tile) : t.turn.Occupied 3 ↔ t.Occupied 0 := by
  revert t; decide
@[simp] lemma turn_middle (t : Tile) : t.turn.middle=t.middle := by cases t <;> rfl

end Diagram.Tile



end
end CriticalStrip





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SidePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical

 

def rotateTriangle (H : ℕ) (v : Triangle) : Triangle :=
  if v.2.1 < H then (-v.1,H-1-v.2.1,!v.2.2) else v

@[simp] lemma rotateTriangle_up {H : ℕ} (i : ℤ) (j : ℕ) (hj : j<H) :
    rotateTriangle H (up i j)=down (-i) (H-1-j) := by simp [rotateTriangle,up,down,hj]
@[simp] lemma rotateTriangle_down {H : ℕ} (i : ℤ) (j : ℕ) (hj : j<H) :
    rotateTriangle H (down i j)=up (-i) (H-1-j) := by simp [rotateTriangle,up,down,hj]

end




end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BridgeUnfold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators

 
def raiseTriangle (v : Triangle) : Triangle := (v.1,v.2.1+1,v.2.2)

lemma raiseTriangle_injective : Function.Injective raiseTriangle := by
  rintro ⟨i,j,b⟩ ⟨k,l,c⟩ h
  simp only [raiseTriangle,Prod.mk.injEq,Nat.add_right_cancel_iff] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

lemma adjacent_raise (v w : Triangle) :
    adjacent (raiseTriangle v) (raiseTriangle w) ↔ adjacent v w := by
  simp only [adjacent,upDownAdjacent,raiseTriangle,Nat.add_right_cancel_iff]

lemma PathBetween.raise {H : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) :
    PathBetween (H+1) (raiseTriangle a) (raiseTriangle b) (p.map raiseTriangle) := by
  refine ⟨?_,?_,hp.2.2.1.map raiseTriangle_injective,?_,?_⟩
  · rw [List.head?_map,hp.1]; rfl
  · rw [List.getLast?_map,hp.2.1]; rfl
  · exact (List.isChain_map _).mpr (hp.2.2.2.1.imp (fun v w h=>(adjacent_raise v w).mpr h))
  · intro v hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    exact Nat.succ_lt_succ (hp.2.2.2.2 w hw)

lemma PathBetween.prepend_vertex {H : ℕ} {a b v : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) (hv : v.2.1<H) (hn : v∉p) (hva : adjacent v a) :
    PathBetween H v b (v::p) := by
  refine ⟨rfl,?_,List.nodup_cons.mpr ⟨hn,hp.2.2.1⟩,?_,?_⟩
  · have hne : p≠[] := by intro h; simpa only [h,List.getLast?_nil,reduceCtorEq] using hp.2.1
    simp only [List.getLast?_cons,hp.2.1,Option.getD_some]
  · apply List.isChain_cons.mpr
    refine ⟨?_,hp.2.2.2.1⟩
    intro y hy
    have he : a=y := by simpa only [hp.1,Option.mem_some_iff] using hy
    exact he ▸ hva
  · intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact hv
    · exact hp.2.2.2.2 w hw

 

def prepareBridge (p : List Triangle) : List Triangle :=
  up 0 0 :: down 0 0 :: p.map raiseTriangle

lemma prepareBridge_spec {H : ℕ} (hH : 1≤H) {k : ℤ} {p : List Triangle}
    (hp : IsPath H (down k (H-1)) p) :
    IsPath (H+1) (down k H) (prepareBridge p) := by
  have hh := (show PathBetween H (up 0 0) (down k (H-1)) p from hp).raise
  have he : raiseTriangle (down k (H-1))=down k H := by
    have he : H-1+1=H := by omega
    simp only [raiseTriangle,down,he]
  rw [he] at hh
  have hn (b : Bool) : (0,0,b) ∉ p.map raiseTriangle := by
    intro h
    obtain ⟨v,_,hv⟩:=List.mem_map.mp h
    have hx:=congrArg (fun x : Triangle=>x.2.1) hv
    change v.2.1+1=0 at hx
    omega
  have hu : up (0:ℤ) 0 ≠ down 0 0 := by decide
  exact (hh.prepend_vertex (by change 0<H+1; omega) (hn false)
    (by simp [adjacent,upDownAdjacent,raiseTriangle,up])).prepend_vertex
      (by change 0<H+1; omega) (by simpa only [List.mem_cons,up,down,Prod.mk.injEq,Bool.true_eq_false,and_false,
        false_or] using (hn true))
      (by simp [adjacent,upDownAdjacent,up])

@[simp] lemma prepareBridge_length (p : List Triangle) :
    (prepareBridge p).length=p.length+2 := by simp [prepareBridge]

lemma adjacent_up_other_column {i : ℤ} {j : ℕ} {w : Triangle}
    (h : adjacent (up i j) w) (hne : w.1≠i) : w=down (i-1) j := by
  rcases w with ⟨k,l,b⟩
  cases b <;> simp [adjacent,upDownAdjacent,up,down] at h ⊢
  all_goals omega

 

lemma exists_rightmost_down {H : ℕ} {k : ℤ} {p : List Triangle}
    (hp : IsPath H (down k (H-1)) p) (hzero : down 0 0∈p) :
    ∃ M : ℤ, ∃ j : ℕ, down M j∈p ∧ 0≤M ∧ ∀ v∈p,v.1≤M := by
  let F:=p.toFinset.image Prod.fst
  have h0 : (0:ℤ)∈F := Finset.mem_image.mpr ⟨down 0 0,List.mem_toFinset.mpr hzero,rfl⟩
  have hne : F.Nonempty:=⟨0,h0⟩
  let M:=F.max' hne
  have hM (v : Triangle) (hv : v∈p) : v.1≤M :=
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨v,List.mem_toFinset.mpr hv,rfl⟩)
  have hM0 : 0≤M := Finset.le_max' F 0 h0
  by_contra hh
  have hn (j : ℕ) : down M j∉p := by
    intro h; exact hh ⟨M,j,h,hM0,hM⟩
  have hMp : ∃v∈p,v.1=M := by
    obtain ⟨v,hv,he⟩:=Finset.mem_image.mp (Finset.max'_mem F hne)
    exact ⟨v,List.mem_toFinset.mp hv,he⟩
  obtain ⟨⟨i,j,b⟩,hv,hi⟩:=hMp
  change i=M at hi
  subst i
  cases b with
  | false => exact hn j hv
  | true =>
    obtain ⟨a,ha,hv⟩:=List.getElem_of_mem hv
    have hfirst : p[0]'(by omega)=up 0 0 := by
      simpa only [List.head?_eq_getElem?,List.getElem?_eq_getElem (by omega : 0<p.length),
        Option.some.injEq] using hp.1
    have hlast : p[p.length-1]'(by omega)=down k (H-1) := by
      simpa only [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by omega : p.length-1<p.length),
        Option.some.injEq] using hp.2.1
    have haz : a≠0 := by
      intro hz; subst a
      have he := hfirst.symm.trans hv
      have hcol:=congrArg Prod.fst he
      change 0=M at hcol
      exact hn 0 (hcol ▸ hzero)
    have hat : a+1<p.length := by
      by_contra ht
      have he : a=p.length-1 := by omega
      have hb := hlast.symm.trans (by simpa only [he] using hv)
      have hb':=congrArg (fun v : Triangle=>v.2.2) hb
      contradiction
    have ha' : a-1+1=a := by omega
    have hc:=List.isChain_iff_getElem.mp hp.2.2.2.1
    have hprev : adjacent (up M j) p[a-1] := by
      have he:=adjacent_symmetric.symm _ _ (hc (a-1) (by omega))
      simpa only [ha',hv,up] using he
    have hnext : adjacent (up M j) p[a+1] := by simpa only [hv,up] using hc a hat
    have other {w : Triangle} (hw : w∈p) (had : adjacent (up M j) w) : w=down (M-1) j := by
      apply adjacent_up_other_column had
      intro he
      have hb : w.2.2=false := by
        rcases had with h|h
        · exact h.2.1
        · exact (by have he := h.2.1; change true=false at he; contradiction)
      have hw' : w=down M w.2.1 := by
        rcases w with ⟨i,l,b⟩
        exact Prod.ext he (Prod.ext rfl hb)
      exact hn w.2.1 (hw' ▸ hw)
    have he := (other (List.getElem_mem _) hprev).trans (other (List.getElem_mem _) hnext).symm
    have hi := hp.2.2.1.getElem_inj_iff.mp he
    omega

 
def ladderVertex (i : ℤ) (r : ℕ) : Triangle := (i,r/2,r%2=0)

lemma ladderVertex_injective (i : ℤ) : Function.Injective (ladderVertex i) := by
  intro a b h
  have hr:=congrArg (fun v : Triangle=>v.2.1) h
  have hp:=congrArg (fun v : Triangle=>v.2.2) h
  simp only [ladderVertex] at hr hp
  have ha:=Nat.mod_lt a (by omega : 0<2)
  have hb:=Nat.mod_lt b (by omega : 0<2)
  simp only [decide_eq_decide] at hp
  omega

lemma ladderVertex_adjacent (i : ℤ) (r : ℕ) :
    adjacent (ladderVertex i r) (ladderVertex i (r+1)) := by
  have hmod:=Nat.mod_lt r (by omega : 0<2)
  by_cases he : r%2=0
  · have he' : (r+1)%2≠0 := by omega
    have hd : (r+1)/2=r/2 := by omega
    simp [ladderVertex,he,he',hd,adjacent,upDownAdjacent]
  · have he' : (r+1)%2=0 := by omega
    have hd : (r+1)/2=r/2+1 := by omega
    simp [ladderVertex,he,he',hd,adjacent,upDownAdjacent]

lemma exists_column_connector (H : ℕ) (i : ℤ) (j l : ℕ) (hj : j<H) (hl : l<H) :
    ∃ p : List Triangle, PathBetween H (up i j) (down i l) p ∧
      (∀ v∈p,v.1=i) ∧ p.length≤2*H := by
  let a : Fin (2*H):=⟨2*j,by omega⟩
  let b : Fin (2*H):=⟨2*l+1,by omega⟩
  obtain ⟨w,hw⟩:=((SimpleGraph.pathGraph_preconnected (2*H)) a b).exists_isPath
  let f : Fin (2*H)→Triangle:=fun r=>ladderVertex i r.val
  have hf : Function.Injective f := (ladderVertex_injective i).comp Fin.val_injective
  refine ⟨w.support.map f,⟨?_,?_,hw.support_nodup.map hf,?_,?_⟩,?_,?_⟩
  · simp only [List.head?_map,List.head?_eq_some_head w.support_ne_nil,w.head_support,Option.map_some]
    simp [f,a,ladderVertex,up]
  · simp only [List.getLast?_map,List.getLast?_eq_some_getLast w.support_ne_nil,w.getLast_support,Option.map_some]
    simp only [f,b,ladderVertex,down,Option.some.injEq,Prod.mk.injEq,true_and]
    have he : (2*l+1)/2=l := by omega
    have hm : (2*l+1)%2≠0 := by omega
    simp only [he,hm,decide_false,and_self]
  · apply (List.isChain_map _).mpr
    apply w.isChain_adj_support.imp
    intro v w h
    have hh:=SimpleGraph.pathGraph_adj.mp h
    rcases hh with hh|hh
    · change adjacent (ladderVertex i v.val) (ladderVertex i w.val)
      rw [←hh]
      exact ladderVertex_adjacent i _
    · change adjacent (ladderVertex i v.val) (ladderVertex i w.val)
      rw [←hh]
      exact adjacent_symmetric.symm _ _ (ladderVertex_adjacent i _)
  · intro v hv
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hv
    change r.val/2<H
    have :=r.isLt
    omega
  · intro v hv
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hv
    rfl
  · rw [List.length_map]
    have := List.Nodup.length_le_card hw.support_nodup
    simpa only [Fintype.card_fin] using this







lemma PathBetween.split {H : ℕ} {a b v : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) (hv : v∈p) :
    ∃ r t, PathBetween H a v r ∧ PathBetween H v b t ∧
      p=r++t.tail ∧ (∀w∈r,w∈p) ∧ (∀w∈t,w∈p) := by
  obtain ⟨x,y,rfl⟩:=List.append_of_mem hv
  have hpre : x++[v] <+: x++v::y := ⟨y,by simp only [List.append_assoc,List.singleton_append]⟩
  have hsuf : v::y <:+ x++v::y := List.suffix_append _ _
  have hmem₁ : ∀w∈x++[v],w∈x++v::y:=fun _ h=>hpre.sublist.subset h
  have hmem₂ : ∀w∈v::y,w∈x++v::y:=fun _ h=>hsuf.sublist.subset h
  refine ⟨x++[v],v::y,⟨?_,by simp,hp.2.2.1.sublist hpre.sublist,
    hp.2.2.2.1.prefix hpre,fun w hw=>hp.2.2.2.2 w (hmem₁ w hw)⟩,
    ⟨rfl,?_,hp.2.2.1.sublist hsuf.sublist,hp.2.2.2.1.suffix hsuf,
      fun w hw=>hp.2.2.2.2 w (hmem₂ w hw)⟩,?_,hmem₁,hmem₂⟩
  · have he : (x++[v]).head?=(x++v::y).head? := by cases x <;> rfl
    exact he.trans hp.1
  · have he:=hp.2.1
    rw [List.getLast?_append_of_ne_nil x (by simp)] at he
    exact he
  · simp only [List.tail_cons,List.append_assoc,List.singleton_append]

 

structure BridgeCut (H : ℕ) (k : ℤ) (p : List Triangle) where
  column : ℤ
  row : ℕ
  left : List Triangle
  right : List Triangle
  column_nonneg : 0 ≤ column
  row_lt : row<H
  left_path : PathBetween H (up 0 0) (down column row) left
  right_path : PathBetween H (down column row) (down k (H-1)) right
  left_le : ∀v∈left,v.1 ≤ column
  right_le : ∀v∈right,v.1 ≤ column
  reconstruct : p=left++right.tail

lemma exists_bridgeCut {H : ℕ} {k : ℤ} {p : List Triangle}
    (hp : IsPath H (down k (H-1)) p) (hzero : down 0 0∈p) :
    Nonempty (BridgeCut H k p) := by
  obtain ⟨M,j,hv,hM,hmax⟩:=exists_rightmost_down hp hzero
  obtain ⟨r,t,hr,ht,he,hm₁,hm₂⟩:=
    (show PathBetween H (up 0 0) (down k (H-1)) p from hp).split hv
  exact ⟨⟨M,j,r,t,hM,hp.2.2.2.2 _ hv,hr,ht,
    fun v hv=>hmax v (hm₁ v hv),fun v hv=>hmax v (hm₂ v hv),he⟩⟩

namespace BridgeCut
section TraceRealizations
variable {H : ℕ} {k : ℤ} {p : List Triangle}



def move (D : BridgeCut H k p) (v : Triangle) : Triangle :=
  translateTriangle (2*D.column+2) (rotateTriangle H v)

lemma connector_exists (D : BridgeCut H k p) :
    ∃ q : List Triangle, PathBetween H (up (D.column+1) D.row)
        (down (D.column+1) (H-1-D.row)) q ∧
      (∀v∈q,v.1=D.column+1) ∧ q.length≤2*H :=
  exists_column_connector H (D.column+1) D.row (H-1-D.row) D.row_lt
    (by have :=D.row_lt; omega)

def connector (D : BridgeCut H k p) : List Triangle := D.connector_exists.choose


def arch (D : BridgeCut H k p) : List Triangle := D.left++D.connector++D.right.map D.move

end TraceRealizations






end BridgeCut

 
def BridgePath (N : ℕ) := {x : ℤ×List Triangle // IsPath N (down x.1 (N-1)) x.2}

namespace BridgePath
variable {N : ℕ}

def cut (hN : 1≤N) (x : BridgePath N) :
    BridgeCut (N+1) x.val.1 (prepareBridge x.val.2) := by
  apply Classical.choice
  apply exists_bridgeCut (by simpa only [Nat.add_sub_cancel] using prepareBridge_spec hN x.property)
  simp [prepareBridge]

 

def toCutArch (hN : 1≤N) (x : BridgePath N) : (ℕ×ℕ)×List Triangle :=
  let D:=x.cut hN
  ((D.column.toNat,(D.column+1-x.val.1).toNat),D.arch.map (translateTriangle (-D.column)))

end BridgePath

end
end CriticalStrip

end OAI
end


