-- Prove2me | Definitions.Def_OAIQ042S005
-- name    : OAIQ042S005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:39:32.680114+00:00
-- url     : https://prove2.me/theorems/6886f62b-5337-46bb-b350-5b6aad47d55b
-- title:
--   Definitions bundle OAIQ042S005 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 221 declarations of OpenAI's Lean: 44 definitions, 2 inductive types or structures, 4 instances and 171 theorems. The definitions and types are `OAI.CriticalStrip.CrossTopArch.sigmaEquiv`, `OAI.CriticalStrip.CrossTopArch.weight`, `OAI.CriticalStrip.CrossTopArch.window`, `OAI.CriticalStrip.Diagram.ArcColumn.label`, `OAI.CriticalStrip.Diagram.BoundaryInsert.pairing`, `OAI.CriticalStrip.Diagram.BoundarySew.equivalence`, `OAI.CriticalStrip.Diagram.Circuit.CompactVertex`, `OAI.CriticalStrip.Diagram.Circuit.compactBoundary`, `OAI.CriticalStrip.Diagram.Circuit.compactWiring`, `OAI.CriticalStrip.Diagram.ColumnChain.mass`, `OAI.CriticalStrip.Diagram.ColumnNonnegative`, `OAI.CriticalStrip.Diagram.Graph.boundaryClosure`, `OAI.CriticalStrip.Diagram.IsNormalizedStationary`, `OAI.CriticalStrip.Diagram.LastMatrix`, `OAI.CriticalStrip.Diagram.PairExchangeRegular`, `OAI.CriticalStrip.Diagram.Pairing.ArcAddition`, `OAI.CriticalStrip.Diagram.Pairing.GateCompatible`, `OAI.CriticalStrip.Diagram.Pairing.GatePotentials`, `OAI.CriticalStrip.Diagram.Pairing.closedStep`, `OAI.CriticalStrip.Diagram.Pairing.turnPotential`, `OAI.CriticalStrip.Diagram.PartialColumn.choicesEquiv`, `OAI.CriticalStrip.Diagram.PartialColumn.program`, `OAI.CriticalStrip.Diagram.Position.gate`, `OAI.CriticalStrip.Diagram.Position.pairCircuit`, `OAI.CriticalStrip.Diagram.Program.circuit`, `OAI.CriticalStrip.Diagram.Program.matrix`, `OAI.CriticalStrip.Diagram.Program.weight`, `OAI.CriticalStrip.Diagram.ThreeBox.profile`, `OAI.CriticalStrip.Diagram.TriplePosition.rightCircuit`, `OAI.CriticalStrip.Diagram.fullPeel`, `OAI.CriticalStrip.Diagram.localR`, `OAI.CriticalStrip.Diagram.matrixPolynomial`, `OAI.CriticalStrip.Diagram.twoPair`, `OAI.CriticalStrip.HoneycombAssignment.weight`, `OAI.CriticalStrip.HoneycombBranch.factor`, `OAI.CriticalStrip.NorthHistory.equivCross`, `OAI.CriticalStrip.NorthHistory.leftState`, `OAI.CriticalStrip.NorthHistory.ls`, `OAI.CriticalStrip.NorthHistory.ofCross`, `OAI.CriticalStrip.NorthHistory.rightState` and 6 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_ArchTrig`, `StripMass_AugmentedColumn`, `StripMass_BoundaryTree`, `StripMass_CollisionLeaf`, `StripMass_ColumnSweep`, `StripMass_FiniteEnds`, `StripMass_HalfTurn`, `StripMass_HoneycombClip`, `StripMass_HoneycombDictionary`, `StripMass_LastRow`, `StripMass_LocalPadding`, `StripMass_MergePairCandidate`, `StripMass_MirrorExterior`, `StripMass_NodalEmpty`, `StripMass_NodalExchange`, `StripMass_NorthBijection`, `StripMass_NorthMass`, `StripMass_PairSelfNode`, `StripMass_PhysicalStationarity`, `StripMass_ResidualParityCoefficients`, `StripMass_ReversedConvergence`, `StripMass_ScalarFlat`, `StripMass_SewnAssignment`, `StripMass_SpecializationPolynomial`, `StripMass_StepComplete`, `StripMass_SwapVacancy`, `StripMass_ThreeBoxProfiles`, `StripMass_ThreeBoxWeights`, `StripMass_TopPadding`, `StripMass_TripleCircuit`, `StripMass_TurnDisk`, `StripMass_TurnGate`, `StripMass_VacuumClosure`, `StripMass_VacuumDegree`, `StripMass_WireContraction`.
--
--   **Imports.** It imports the published bundle `Def_CriticalStripMass`; the bundles `OAIQ042S002` and `OAIQ042S003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S010`, `OAIQ042S011` and `OAIQ042S012`; the statement `OAI.CriticalStrip.HoneycombBranch.finite_split`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_CriticalStripMass
import Definitions.Def_OAIQ042S002
import Definitions.Def_OAIQ042S003

section
-- module Solutions.OAIQ042_SS.StripMass_TopPadding
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset

def IsNormalizedStationary {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (v : Pairing n → 𝕜) : Prop :=
  v (empty n) = 1 ∧ (column w).mulVec v = v

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LastRow
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset


theorem Realizes.last_eq {n : ℕ} {p q : Pairing (n+1)} {t : Configuration (n+1)}
    (h : Realizes p q t) : t (Fin.last n) = lastTile p q := by
  classical
  have hn := h.north (Fin.last n) rfl
  have hw := h.west (Fin.last n)
  have he := h.east (Fin.last n)
  unfold lastTile
  generalize t (Fin.last n) = a at hn hw he ⊢
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges]



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_StepComplete
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
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

def Position.gate {n : ℕ} (a : Position n) (t : Tile) : Gate n :=
  ⟨a.left,a.right,a.adjacent,t⟩

variable {K : Type*} [CommRing K]

def localR {n : ℕ} (a : Position n) (w : Weights K) : Matrix (Pairing n) (Pairing n) K :=
  ∑ t : Tile, w.tile t • optionMatrix (fun p => p.tileStep a.left a.right a.adjacent t)

namespace Program
variable {n : ℕ}

def circuit : (p : Program n K) → p.Choices → Circuit n
  | .nil,_ => .nil
  | .snoc p a _,(c,t) => .snoc (p.circuit c) (a.gate t)

def weight : (p : Program n K) → p.Choices → K
  | .nil,_ => 1
  | .snoc p _ w,(c,t) => p.weight c * w.tile t

def matrix : Program n K → Matrix (Pairing n) (Pairing n) K
  | .nil => 1
  | .snoc p a w => localR a w * p.matrix

lemma matrix_expansion (p : Program n K) : p.matrix =
    ∑ c : p.Choices, p.weight c • optionMatrix (fun q => Circuit.eval q (p.circuit c)) := by
  induction p with
  | nil =>
    change (1 : Matrix (Pairing n) (Pairing n) K) =
      ∑ _ : PUnit, (1:K) • optionMatrix (fun q : Pairing n => some q)
    rw [Fintype.sum_unique]
    ext q r
    simp [optionMatrix,Matrix.one_apply,eq_comm]
  | snoc p a w ih =>
    simp only [matrix,localR,ih,mul_sum,sum_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    change (∑ c : p.Choices, ∑ t : Tile,
        (p.weight c * w.tile t) • (optionMatrix (fun q : Pairing n => q.tileStep a.left a.right a.adjacent t) *
          optionMatrix (fun q => Circuit.eval q (p.circuit c)))) = _
    simp_rw [optionMatrix_mul]
    change _ = ∑ c : p.Choices × Tile, _
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro t _
    simp only [weight,circuit,Circuit.eval,Position.gate]

lemma matrix_apply (p : Program n K) (q r : Pairing n) : p.matrix q r =
    ∑ c : p.Choices, if Circuit.eval r (p.circuit c)=some q then p.weight c else 0 := by
  rw [matrix_expansion]
  simp only [Matrix.sum_apply,Matrix.smul_apply,optionMatrix,smul_eq_mul,mul_ite,mul_one,mul_zero]

end Program
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_WireContraction
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section





open scoped Classical

namespace Circuit
variable {n : ℕ}

def CompactVertex : Circuit n → Type
  | .nil => Fin n
  | .snoc c _ => Sum c.CompactVertex (Fin 4)

def compactBoundary : (c : Circuit n) → Fin n → c.CompactVertex
  | .nil => id
  | .snoc c g => CompactGate.boundary c.compactBoundary g.left g.right

def compactWiring (p : Pairing n) : (c : Circuit n) → c.CompactVertex → c.CompactVertex → Prop
  | .nil => p.Adj
  | .snoc c g => CompactGate.wiring (compactWiring p c) c.compactBoundary
      (support p c) g.left g.right g.tile

theorem compactBoundary_injective (c : Circuit n) : Function.Injective c.compactBoundary := by
  induction c with
  | nil => exact Function.injective_id
  | snoc c g ih => exact CompactGate.boundary_injective _ ih _ _

instance compactWiring_symm (p : Pairing n) (c : Circuit n) : Std.Symm (compactWiring p c) := by
  induction c with
  | nil => exact ⟨fun _ _ h => Pairing.adj_symm h⟩
  | snoc c g ih =>
    let := ih
    exact inferInstanceAs (Std.Symm (CompactGate.wiring _ _ _ _ _ _))

theorem compact_eval_sound (p : Pairing n) (c : Circuit n) (q : Pairing n)
    (h : eval p c=some q) : GraphRealizes (compactWiring p c) c.compactBoundary q := by
  induction c generalizing q with
  | nil => have he : p=q := Option.some.inj h; subst q; exact p.graphRealizes
  | snoc c g ih =>
    cases hr : eval p c with
    | none => simp [eval,hr] at h
    | some r =>
      have hstep : r.tileStep g.left g.right g.adjacent g.tile = some q := by
        simpa only [eval,hr,Option.bind_some] using h
      have hp := ih r hr
      have hs := (eval_sound p c r hr).2.2
      have hne : g.left≠g.right := by have := g.adjacent; intro hh; have := congrArg Fin.val hh; omega
      change GraphRealizes (CompactGate.wiring _ _ _ _ _ _) _ q
      rw [hs]
      exact (CompactGate.realizes_iff hp c.compactBoundary_injective g.left g.right hne g.tile q).mp
        ((graph_gate_step_iff hp g.left g.right g.adjacent g.tile q).mpr hstep).2

theorem compact_eval_exists (p : Pairing n) (c : Circuit n) (hc : Compatible p c)
    (hd : Graph.DrainsBoundary (compactWiring p c) c.compactBoundary) :
    ∃ q, eval p c=some q := by
  induction c with
  | nil => exact ⟨p,rfl⟩
  | snoc c g ih =>
    obtain ⟨hc,hl,hright⟩ := hc
    obtain ⟨r,hr⟩ := ih hc (CompactGate.drains_local
      (compactWiring p c) c.compactBoundary (support p c) g.left g.right g.tile hd)
    have hp := compact_eval_sound p c r hr
    have hs := (eval_sound p c r hr).2.2
    have hne : g.left≠g.right := by have := g.adjacent; intro hh; have := congrArg Fin.val hh; omega
    have hcomp : CutPatch.Compatible (r.cutShape g.left g.right) g.tile := by
      rw [r.cutShape_compatible]
      exact ⟨by simpa only [hs] using hl,by simpa only [hs] using hright⟩
    change Graph.DrainsBoundary (CompactGate.wiring _ _ _ _ _ _) _ at hd
    rw [hs] at hd
    have hfull := (CompactGate.contraction hp c.compactBoundary_injective g.left g.right hne g.tile).drains_inv hd
    obtain ⟨q,hq⟩ := graph_gate_step_exists hp g.left g.right g.adjacent g.tile hcomp hfull
    exact ⟨q,by simpa only [eval,hr,Option.bind_some] using hq⟩

theorem compact_eval_iff (p : Pairing n) (c : Circuit n) (q : Pairing n) :
    eval p c=some q ↔ Compatible p c ∧ GraphRealizes (compactWiring p c) c.compactBoundary q := by
  constructor
  · intro h; exact ⟨(eval_sound p c q h).1,compact_eval_sound p c q h⟩
  · rintro ⟨hc,hq⟩
    obtain ⟨r,hr⟩ := compact_eval_exists p c hc hq.drainsBoundary
    have he := (compact_eval_sound p c r hr).unique hq
    exact he ▸ hr

end Circuit
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ColumnSweep
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
namespace PartialColumn

open Finset
open scoped Classical
variable {K : Type*} [CommRing K] {n : ℕ}

def program (w : Fin n → Weights K) : (k : ℕ) → k≤n → Program (n+1) K
  | 0,_ => .nil
  | k+1,hk => .snoc (program w k (by omega)) (position ⟨k,hk⟩) (w ⟨k,hk⟩)

def choicesEquiv (w : Fin n → Weights K) : (k : ℕ) → (hk : k≤n) →
    (program w k hk).Choices ≃ (Fin k → Tile)
  | 0,_ => {
      toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun f => funext (fun i => Fin.elim0 i) }
  | k+1,hk => (Equiv.prodCongr (choicesEquiv w k (by omega)) (Equiv.refl Tile)).trans
      ((Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (k+1) => Tile)))

omit [CommRing K] in
lemma choices_circuit (w : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (c : (program w k hk).Choices) (t : Configuration n)
    (ht : ∀ i : Fin k, t ⟨i.val,lt_of_lt_of_le i.isLt hk⟩=choicesEquiv w k hk c i) :
    (program w k hk).circuit c=circuit t k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases c with ⟨c,v⟩
    change Circuit.snoc ((program w k _).circuit c) ((position ⟨k,hk⟩).gate v)=
      Circuit.snoc (circuit t k _) (gate t ⟨k,hk⟩)
    have he : choicesEquiv w (k+1) hk (c,v) =
        Fin.snoc (choicesEquiv w k (by omega) c) v := by
      simp only [choicesEquiv, Equiv.prodCongr]
      rfl
    have ht' (i : Fin k) : t ⟨i.val,by omega⟩=choicesEquiv w k (by omega) c i := by
      simpa only [he, Fin.snoc_castSucc, Fin.val_castSucc] using ht i.castSucc
    rw [ih (by omega) c ht']
    congr 1
    have hv : t ⟨k,hk⟩=v := by simpa only [he, Fin.snoc_last, Fin.val_last] using ht (Fin.last k)
    simp only [position,Position.gate,gate,hv]

lemma choices_weight (w : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (c : (program w k hk).Choices) :
    (program w k hk).weight c = ∏ i : Fin k, (w ⟨i.val,lt_of_lt_of_le i.isLt hk⟩).tile
      (choicesEquiv w k hk c i) := by
  induction k with
  | zero => simp [program,Program.weight]
  | succ k ih =>
    rcases c with ⟨c,v⟩
    rw [Fin.prod_univ_castSucc]
    change (program w k _).weight c * (w ⟨k,hk⟩).tile v = _
    rw [ih (by omega) c]
    have he : choicesEquiv w (k+1) hk (c,v) =
        Fin.snoc (choicesEquiv w k (by omega) c) v := by
      simp only [choicesEquiv, Equiv.prodCongr]
      rfl
    simp only [he, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

lemma program_column (hn : 0<n) (w : Fin n → Weights K) (p q : Pairing n) :
    (program w n le_rfl).matrix q.padTop p.padBottom=column w q p := by
  rw [Program.matrix_apply]
  unfold column
  apply Fintype.sum_equiv (choicesEquiv w n le_rfl)
  intro c
  have hc : (program w n le_rfl).circuit c=circuit (choicesEquiv w n le_rfl c) n le_rfl :=
    choices_circuit w n le_rfl c _ (fun _ => rfl)
  simp only [hc,column_eval_iff hn,choices_weight]

end PartialColumn
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxProfiles
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset



def profile : Config → Option (Fin 51)
  | (.vacant,.vacant,.vacant) => some 0
  | (.vacant,.vacant,.cup) => some 50
  | (.vacant,.vertical₀,.vacant) => some 14
  | (.vacant,.vertical₀,.cup) => some 22
  | (.vacant,.diagonal₀,.vertical₀) => some 23
  | (.vacant,.diagonal₀,.diagonal₀) => some 27
  | (.vacant,.cup,.vertical₀) => some 48
  | (.vacant,.cup,.diagonal₀) => some 49
  | (.vertical₀,.vertical₁,.vertical₀) => some 39
  | (.vertical₀,.vertical₁,.diagonal₀) => some 41
  | (.vertical₀,.diagonal₁,.vacant) => some 35
  | (.vertical₀,.diagonal₁,.cup) => some 38
  | (.vertical₀,.cap,.vacant) => some 1
  | (.vertical₀,.cap,.cup) => some 9
  | (.vertical₀,.verticalPair,.vertical₀) => some 17
  | (.vertical₀,.verticalPair,.diagonal₀) => some 19
  | (.vertical₀,.capCup,.vertical₀) => some 7
  | (.vertical₀,.capCup,.diagonal₀) => some 8
  | (.vertical₁,.vacant,.vertical₁) => some 46
  | (.vertical₁,.vacant,.diagonal₁) => some 45
  | (.vertical₁,.vertical₀,.vertical₁) => some 21
  | (.vertical₁,.vertical₀,.diagonal₁) => some 20
  | (.vertical₁,.diagonal₀,.cap) => some 10
  | (.vertical₁,.diagonal₀,.verticalPair) => some 26
  | (.vertical₁,.diagonal₀,.capCup) => some 13
  | (.vertical₁,.cup,.cap) => some 43
  | (.vertical₁,.cup,.verticalPair) => some 47
  | (.vertical₁,.cup,.capCup) => some 44
  | (.diagonal₀,.vacant,.vertical₁) => some 41
  | (.diagonal₀,.vacant,.diagonal₁) => some 39
  | (.diagonal₀,.vertical₀,.vertical₁) => some 19
  | (.diagonal₀,.vertical₀,.diagonal₁) => some 17
  | (.diagonal₀,.diagonal₀,.cap) => some 1
  | (.diagonal₀,.diagonal₀,.verticalPair) => some 25
  | (.diagonal₀,.diagonal₀,.capCup) => some 9
  | (.diagonal₀,.cup,.cap) => some 35
  | (.diagonal₀,.cup,.verticalPair) => some 42
  | (.diagonal₀,.cup,.capCup) => some 38
  | (.diagonal₁,.vertical₁,.vertical₀) => some 45
  | (.diagonal₁,.vertical₁,.diagonal₀) => some 46
  | (.diagonal₁,.diagonal₁,.vacant) => some 43
  | (.diagonal₁,.diagonal₁,.cup) => some 44
  | (.diagonal₁,.cap,.vacant) => some 10
  | (.diagonal₁,.cap,.cup) => some 13
  | (.diagonal₁,.verticalPair,.vertical₀) => some 20
  | (.diagonal₁,.verticalPair,.diagonal₀) => some 21
  | (.diagonal₁,.capCup,.vertical₀) => some 11
  | (.diagonal₁,.capCup,.diagonal₀) => some 12
  | (.cap,.vacant,.vacant) => some 31
  | (.cap,.vacant,.cup) => some 34
  | (.cap,.vertical₀,.vacant) => some 15
  | (.cap,.vertical₀,.cup) => some 16
  | (.cap,.diagonal₀,.vertical₀) => some 24
  | (.cap,.diagonal₀,.diagonal₀) => some 28
  | (.cap,.cup,.vertical₀) => some 32
  | (.cap,.cup,.diagonal₀) => some 33
  | (.cup,.vertical₁,.verticalPair) => some 50
  | (.cup,.diagonal₁,.vertical₁) => some 49
  | (.cup,.diagonal₁,.diagonal₁) => some 48
  | (.cup,.cap,.vertical₁) => some 27
  | (.cup,.cap,.diagonal₁) => some 23
  | (.cup,.verticalPair,.verticalPair) => some 22
  | (.cup,.capCup,.cap) => some 14
  | (.cup,.capCup,.verticalPair) => some 30
  | (.cup,.capCup,.capCup) => some 22
  | (.verticalPair,.vertical₁,.cap) => some 31
  | (.verticalPair,.vertical₁,.verticalPair) => some 40
  | (.verticalPair,.vertical₁,.capCup) => some 34
  | (.verticalPair,.diagonal₁,.vertical₁) => some 37
  | (.verticalPair,.diagonal₁,.diagonal₁) => some 36
  | (.verticalPair,.cap,.vertical₁) => some 5
  | (.verticalPair,.cap,.diagonal₁) => some 4
  | (.verticalPair,.verticalPair,.cap) => some 15
  | (.verticalPair,.verticalPair,.verticalPair) => some 18
  | (.verticalPair,.verticalPair,.capCup) => some 16
  | (.verticalPair,.capCup,.cap) => some 2
  | (.verticalPair,.capCup,.verticalPair) => some 6
  | (.verticalPair,.capCup,.capCup) => some 3
  | (.capCup,.vertical₁,.verticalPair) => some 34
  | (.capCup,.diagonal₁,.vertical₁) => some 33
  | (.capCup,.diagonal₁,.diagonal₁) => some 32
  | (.capCup,.cap,.vertical₁) => some 28
  | (.capCup,.cap,.diagonal₁) => some 24
  | (.capCup,.verticalPair,.verticalPair) => some 16
  | (.capCup,.capCup,.cap) => some 15
  | (.capCup,.capCup,.verticalPair) => some 29
  | (.capCup,.capCup,.capCup) => some 16
  | _ => none

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxWeights
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset
open scoped Classical

theorem fiber_correct_0 : ∀ t : Config, t ∈ fiber 0 ↔ profile t = some 0 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_1 : ∀ t : Config, t ∈ fiber 1 ↔ profile t = some 1 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_2 : ∀ t : Config, t ∈ fiber 2 ↔ profile t = some 2 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_3 : ∀ t : Config, t ∈ fiber 3 ↔ profile t = some 3 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_10 : ∀ t : Config, t ∈ fiber 10 ↔ profile t = some 10 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_11 : ∀ t : Config, t ∈ fiber 11 ↔ profile t = some 11 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_12 : ∀ t : Config, t ∈ fiber 12 ↔ profile t = some 12 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_13 : ∀ t : Config, t ∈ fiber 13 ↔ profile t = some 13 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_14 : ∀ t : Config, t ∈ fiber 14 ↔ profile t = some 14 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_15 : ∀ t : Config, t ∈ fiber 15 ↔ profile t = some 15 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_16 : ∀ t : Config, t ∈ fiber 16 ↔ profile t = some 16 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_17 : ∀ t : Config, t ∈ fiber 17 ↔ profile t = some 17 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_18 : ∀ t : Config, t ∈ fiber 18 ↔ profile t = some 18 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_19 : ∀ t : Config, t ∈ fiber 19 ↔ profile t = some 19 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_20 : ∀ t : Config, t ∈ fiber 20 ↔ profile t = some 20 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_21 : ∀ t : Config, t ∈ fiber 21 ↔ profile t = some 21 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_22 : ∀ t : Config, t ∈ fiber 22 ↔ profile t = some 22 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_23 : ∀ t : Config, t ∈ fiber 23 ↔ profile t = some 23 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_24 : ∀ t : Config, t ∈ fiber 24 ↔ profile t = some 24 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_25 : ∀ t : Config, t ∈ fiber 25 ↔ profile t = some 25 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_26 : ∀ t : Config, t ∈ fiber 26 ↔ profile t = some 26 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_27 : ∀ t : Config, t ∈ fiber 27 ↔ profile t = some 27 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_28 : ∀ t : Config, t ∈ fiber 28 ↔ profile t = some 28 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_29 : ∀ t : Config, t ∈ fiber 29 ↔ profile t = some 29 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_30 : ∀ t : Config, t ∈ fiber 30 ↔ profile t = some 30 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_31 : ∀ t : Config, t ∈ fiber 31 ↔ profile t = some 31 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_32 : ∀ t : Config, t ∈ fiber 32 ↔ profile t = some 32 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_33 : ∀ t : Config, t ∈ fiber 33 ↔ profile t = some 33 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_34 : ∀ t : Config, t ∈ fiber 34 ↔ profile t = some 34 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_35 : ∀ t : Config, t ∈ fiber 35 ↔ profile t = some 35 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_36 : ∀ t : Config, t ∈ fiber 36 ↔ profile t = some 36 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_37 : ∀ t : Config, t ∈ fiber 37 ↔ profile t = some 37 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_38 : ∀ t : Config, t ∈ fiber 38 ↔ profile t = some 38 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TripleCircuit
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.ThreeBox.boundaryDataDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.cleanDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def rightCircuit (t : ThreeBox.Config) : Circuit n :=
  .snoc (.snoc (.snoc .nil (s.right.gate t.1)) (s.left.gate t.2.1)) (s.right.gate t.2.2)

end TriplePosition

 

 

namespace CompactGate
variable {V : Type*} {n : ℕ} (r : V → V → Prop) (old : Fin n → V)
  (active : Fin n → Prop) (a b : Fin n) (t : Tile)

lemma output_used (k : Fin 4) (hk0 : k≠0) (hk1 : k≠1) :
    Graph.Used (wiring r old active a b t) (.inr k) ↔ t.Occupied k := by
  constructor
  · rintro ⟨(v|l),h⟩
    · exact h.elim (fun h => (hk0 h.2.1).elim) (fun h => (hk1 h.2.1).elim)
    · exact ⟨l,h⟩
  · rintro ⟨l,h⟩; exact ⟨.inr l,h⟩

lemma passed_used (hinj : Function.Injective old) (i : Fin n) (hia : i≠a) (hib : i≠b) :
    Graph.Used (wiring r old active a b t) (.inl (old i)) ↔ Graph.Used r (old i) := by
  constructor
  · rintro ⟨(v|k),h⟩
    · exact ⟨v,h⟩
    · exact h.elim (fun h => (hia (hinj h.1)).elim) (fun h => (hib (hinj h.1)).elim)
  · rintro ⟨v,h⟩; exact ⟨.inl v,h⟩

lemma boundary_used (hinj : Function.Injective old) (_hab : a≠b)
    (ha : ∀ i, Graph.Used r (old i) ↔ active i) (i : Fin n) :
    Graph.Used (wiring r old active a b t) (boundary old a b i) ↔
      if i=a then t.Occupied 2 else if i=b then t.Occupied 3 else active i := by
  by_cases hia : i=a
  · subst i
    simp only [boundary]
    exact output_used r old active a b t 2 (by decide) (by decide)
  · by_cases hib : i=b
    · subst i
      simp only [boundary, ite_eq_right hia]
      exact output_used r old active a b t 3 (by decide) (by decide)
    · simp only [boundary,ite_eq_right hia,ite_eq_right hib]
      exact (passed_used r old active a b t hinj i hia hib).trans (ha i)
end CompactGate

namespace Circuit
variable {n : ℕ}
lemma compact_boundary_used (p : Pairing n) (c : Circuit n) (i : Fin n) :
    Graph.Used (compactWiring p c) (c.compactBoundary i) ↔ support p c i := by
  induction c generalizing i with
  | nil => rfl
  | snoc c g ih =>
    have hne : g.left≠g.right := by intro he; have:=congrArg Fin.val he; have:=g.adjacent; omega
    exact CompactGate.boundary_used (compactWiring p c) c.compactBoundary (support p c)
      g.left g.right g.tile c.compactBoundary_injective hne ih i
end Circuit





namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

lemma circuit_support (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) :
    Circuit.support p (s.rightCircuit t) i ↔ s.support p t i := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : i=s.a <;> by_cases hb : i=s.b <;> by_cases hc : i=s.c <;>
    simp_all [rightCircuit,Circuit.support,Position.gate,left,right,support]

end TriplePosition
end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MirrorExterior
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical





namespace Position
variable {n : ℕ}

def pairCircuit (a b : Position n) (t u : Tile) : Circuit n :=
  .snoc (.snoc .nil (a.gate t)) (b.gate u)

lemma exchange_edge (a b : Position n) (h : a.Disjoint b) (p : Pairing n) (t u : Tile)
    (v w : ((Fin n ⊕ Fin 4) ⊕ Fin 4)) :
    Circuit.compactWiring p (pairCircuit a b t u) v w ↔
      Circuit.compactWiring p (pairCircuit b a u t) (exchangeEquiv v) (exchangeEquiv w) := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  rcases v with (i|k)|k <;> rcases w with (j|l)|l
  all_goals simp [pairCircuit,Circuit.compactWiring,CompactGate.wiring,Circuit.support,
    Circuit.compactBoundary,CompactGate.boundary,gate,exchangeEquiv,
    h₀,h₁,h₂,h₃,h₀.symm,h₁.symm,h₂.symm,h₃.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp only [Sum.inl.injEq]

lemma exchange_boundary (a b : Position n) (h : a.Disjoint b) (t u : Tile) (i : Fin n) :
    exchangeEquiv ((pairCircuit a b t u).compactBoundary i)=
      (pairCircuit b a u t).compactBoundary i := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  by_cases ha : i=a.left <;> by_cases ha' : i=a.right <;>
    by_cases hb : i=b.left <;> by_cases hb' : i=b.right
  all_goals simp_all [pairCircuit,Circuit.compactBoundary,CompactGate.boundary,gate,exchangeEquiv]
  all_goals rfl

lemma exchange_compatible (a b : Position n) (h : a.Disjoint b) (p : Pairing n) (t u : Tile) :
    Circuit.Compatible p (pairCircuit a b t u) ↔ Circuit.Compatible p (pairCircuit b a u t) := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  simp only [pairCircuit,Circuit.Compatible,Circuit.support,gate,
    h₀,h₁,h₂,h₃,h₀.symm,h₁.symm,h₂.symm,h₃.symm,true_and]
  itauto

lemma exchange_eval (a b : Position n) (h : a.Disjoint b) (p q : Pairing n) (t u : Tile) :
    Circuit.eval p (pairCircuit a b t u)=some q ↔ Circuit.eval p (pairCircuit b a u t)=some q := by
  rw [Circuit.compact_eval_iff,Circuit.compact_eval_iff,exchange_compatible a b h]
  exact and_congr_right fun _ =>
    (Graph.BoundaryEquiv.ofEquiv exchangeEquiv (exchange_edge a b h p t u)
      (exchange_boundary a b h t u)).realizes_iff

lemma steps_commute (a b : Position n) (h : a.Disjoint b) (p : Pairing n) (t u : Tile) :
    (p.tileStep a.left a.right a.adjacent t).bind (fun q => q.tileStep b.left b.right b.adjacent u) =
      (p.tileStep b.left b.right b.adjacent u).bind (fun q => q.tileStep a.left a.right a.adjacent t) := by
  apply Option.ext
  intro q
  exact exchange_eval a b h p q t u

end Position

lemma localR_commute {K : Type*} [CommRing K] {n : ℕ} (a b : Position n)
    (h : a.Disjoint b) (w v : Weights K) :
    localR a w * localR b v = localR b v * localR a w := by
  unfold localR
  simp only [Finset.sum_mul,Finset.mul_sum,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  rw [optionMatrix_mul,optionMatrix_mul]
  congr 1
  · ring
  · apply congrArg optionMatrix
    funext p
    exact (a.steps_commute b h p t u).symm


 

 

namespace Pairing
variable {n m : ℕ} (f : Fin n ↪o Fin m)

lemma map_cutLabels (p : Pairing n) (a b : Fin n) (i : Fin 4) :
    (p.map f).cutLabels (f a) (f b) i=f (p.cutLabels a b i) := by
  fin_cases i <;> simp [cutLabels]

lemma map_cutRelation (p : Pairing n) (a b : Fin n) (d : Finset (Fin 4 × Fin 4)) (x y : Fin m) :
    (p.map f).cutRelation (f a) (f b) d x y ↔
      ∃ i j, p.cutRelation a b d i j ∧ f i=x ∧ f j=y := by
  simp only [cutRelation,map_omit_adj,map_cutLabels]
  constructor
  · rintro (⟨i,j,h,hi,hj⟩|⟨r,s,h,hi,hj⟩)
    · exact ⟨i,j,Or.inl h,hi,hj⟩
    · exact ⟨p.cutLabels a b r,p.cutLabels a b s,Or.inr ⟨r,s,h,rfl,rfl⟩,hi,hj⟩
  · rintro ⟨i,j,(h|⟨r,s,h,rfl,rfl⟩),hi,hj⟩
    · exact Or.inl ⟨i,j,h,hi,hj⟩
    · exact Or.inr ⟨r,s,h,hi,hj⟩

lemma map_tileStep (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val)
    (hf : (f a).val+1=(f b).val) (t : Tile) :
    (p.map f).tileStep (f a) (f b) hf t=(p.tileStep a b hab t).map (Pairing.map f) := by
  cases hp : p.tileStep a b hab t with
  | none =>
    simp only [Option.map_none]
    rw [tileStep_none_iff,map_cutShape,←tileStep_none_iff p a b hab t,hp]
  | some q =>
    have hd : CutPatch.profile (p.cutShape a b) t≠none := by
      rw [ne_eq,←tileStep_none_iff p a b hab t,hp]
      exact Option.some_ne_none q
    obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp hd
    have hn : (p.map f).tileStep (f a) (f b) hf t≠none := by
      rw [ne_eq,tileStep_none_iff,map_cutShape,hd]
      exact Option.some_ne_none d
    obtain ⟨r,hr⟩ := Option.ne_none_iff_exists'.mp hn
    simp only [hr,Option.map_some,Option.some.injEq]
    apply ext_adj
    intro x y
    rw [tileStep_sound (p.map f) _ _ hf t r d hr (by simpa only [map_cutShape] using hd),
      map_cutRelation,map_adj]
    simp_rw [tileStep_sound p a b hab t q d hp hd]

end Pairing
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LocalPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
open Finset

lemma localR_padTop {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p q : Pairing n) :
    localR a.padTop w q.padTop p.padTop=localR a w q p := by
  unfold localR
  simp only [Matrix.sum_apply,Matrix.smul_apply]
  apply sum_congr rfl
  intro t _
  congr 1
  exact optionMatrix_map Pairing.padTop (Pairing.map_injective Fin.castSuccOrderEmb)
    _ _ (fun p => p.map_tileStep Fin.castSuccOrderEmb a.left a.right a.adjacent a.adjacent t) p q

lemma localR_padBottom {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p q : Pairing n) :
    localR a.padBottom w q.padBottom p.padBottom=localR a w q p := by
  unfold localR
  simp only [Matrix.sum_apply,Matrix.smul_apply]
  apply sum_congr rfl
  intro t _
  congr 1
  exact optionMatrix_map Pairing.padBottom (Pairing.map_injective (Fin.succOrderEmb n))
    _ _ (fun p => p.map_tileStep (Fin.succOrderEmb n) a.left a.right a.adjacent a.padBottom.adjacent t) p q

lemma localR_zero_of_support {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p q : Pairing n) (i : Fin n) (hia : i≠a.left) (hib : i≠a.right)
    (h : ¬ (q.Occupied i ↔ p.Occupied i)) : localR a w q p=0 := by
  unfold localR
  simp only [Matrix.sum_apply,Matrix.smul_apply,optionMatrix]
  apply sum_eq_zero
  intro t _
  have hn : p.tileStep a.left a.right a.adjacent t≠some q := by
    intro hh
    have hs := p.tileStep_support a.left a.right a.adjacent t q hh i
    exact h (by simpa only [Pairing.stepSupport,ite_eq_right hia,ite_eq_right hib] using hs)
  simp only [hn,ite_false,smul_zero]

lemma localR_padTop_outside {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p : Pairing (n+1)) (q : Pairing n) (hp : ¬ ∃ r : Pairing n, r.padTop=p) :
    localR a.padTop w q.padTop p=0 := by
  apply localR_zero_of_support a.padTop w p q.padTop (Fin.last n)
  · intro he; have hh:=congrArg Fin.val he; simp [Position.padTop] at hh; omega
  · intro he; have hh:=congrArg Fin.val he; simp [Position.padTop] at hh; omega
  · simp only [Pairing.padTop_not_occupied_last,false_iff,not_not]
    by_contra hh
    exact hp ⟨p.restrict Fin.castSuccOrderEmb,Pairing.padTop_restrict p hh⟩

lemma localR_padBottom_outside {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (p : Pairing n) (q : Pairing (n+1)) (hq : ¬ ∃ r : Pairing n, r.padBottom=q) :
    localR a.padBottom w q p.padBottom=0 := by
  apply localR_zero_of_support a.padBottom w p.padBottom q 0
  · intro he; have hh:=congrArg Fin.val he; simp [Position.padBottom] at hh
  · intro he; have hh:=congrArg Fin.val he; simp [Position.padBottom] at hh
  · simp only [Pairing.padBottom_not_occupied_zero,iff_false,not_not]
    by_contra hh
    exact hq ⟨q.restrict (Fin.succOrderEmb n),Pairing.padBottom_restrict q hh⟩

lemma localR_top_matrix {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (M : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (p q : Pairing n) :
    (localR a.padTop w * M) q.padTop p.padBottom =
      (localR a w * M.submatrix Pairing.padTop Pairing.padBottom) q p := by
  simp only [Matrix.mul_apply,Matrix.submatrix_apply]
  symm
  apply Fintype.sum_of_injective Pairing.padTop (Pairing.map_injective Fin.castSuccOrderEmb)
  · intro r hr
    simp only [localR_padTop_outside a w r q hr,zero_mul]
  · intro r
    rw [localR_padTop]

lemma localR_bottom_matrix {K : Type*} [CommRing K] {n : ℕ} (a : Position n) (w : Weights K)
    (M : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (p q : Pairing n) :
    (M * localR a.padBottom w) q.padTop p.padBottom =
      (M.submatrix Pairing.padTop Pairing.padBottom * localR a w) q p := by
  simp only [Matrix.mul_apply,Matrix.submatrix_apply]
  symm
  apply Fintype.sum_of_injective Pairing.padBottom (Pairing.map_injective (Fin.succOrderEmb n))
  · intro r hr
    simp only [localR_padBottom_outside a w p r hr,mul_zero]
  · intro r
    rw [localR_padBottom]

end

 

 

noncomputable section
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

omit [CommRing K] in
lemma program_congr (w v : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (h : ∀ i : Fin n, i.val<k → w i=v i) : program w k hk=program v k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Program.snoc (program w k _) (position ⟨k,hk⟩) (w ⟨k,hk⟩)=
      Program.snoc (program v k _) (position ⟨k,hk⟩) (v ⟨k,hk⟩)
    rw [ih (by omega) (fun i hi => h i (by omega)),h ⟨k,hk⟩ (by simp)]

lemma program_commute (w : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (R : Matrix (Pairing (n+1)) (Pairing (n+1)) K)
    (h : ∀ i : Fin n, i.val<k → localR (position i) (w i)*R=R*localR (position i) (w i)) :
    (program w k hk).matrix*R=R*(program w k hk).matrix := by
  induction k with
  | zero => simp [program,Program.matrix]
  | succ k ih =>
    change (localR (position ⟨k,hk⟩) (w ⟨k,hk⟩)*(program w k _).matrix)*R=
      R*(localR (position ⟨k,hk⟩) (w ⟨k,hk⟩)*(program w k _).matrix)
    rw [Matrix.mul_assoc,ih (by omega) (fun i hi => h i (by omega)),
      ←Matrix.mul_assoc,h ⟨k,hk⟩ (by simp),Matrix.mul_assoc]

end PartialColumn

 

 

open scoped Classical
end

 

 

noncomputable section
open scoped Classical
open Finset
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

lemma program_zero_above (w : Fin n → Weights K) (k : ℕ) (hk : k≤n)
    (p q : Pairing (n+1)) (j : Fin (n+1)) (hj : k<j.val)
    (h : ¬ (q.Occupied j ↔ p.Occupied j)) : (program w k hk).matrix q p=0 := by
  induction k generalizing q with
  | zero =>
    change (1 : Matrix (Pairing (n+1)) (Pairing (n+1)) K) q p=0
    exact Matrix.one_apply_ne (fun he => h (he ▸ Iff.rfl))
  | succ k ih =>
    change (localR (position (n := n) ⟨k,hk⟩) (w ⟨k,hk⟩) * (program w k _).matrix) q p=0
    rw [Matrix.mul_apply]
    apply sum_eq_zero
    intro r _
    by_cases hr : q.Occupied j ↔ r.Occupied j
    · rw [ih (by omega) r (by omega) (fun hh => h (hr.trans hh)),mul_zero]
    · rw [localR_zero_of_support _ _ r q j (by intro he; have hh:=congrArg Fin.val he; change j.val=k at hh; omega)
        (by intro he; have hh:=congrArg Fin.val he; change j.val=k+1 at hh; omega) hr,zero_mul]

 

lemma exchange_program_column (w v : Fin n → Weights K) (r : ℕ) (hr : r+2≤n)
    (L R : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (p : Pairing (n+1))
    (P : Pairing (n+1) → Prop)
    (hzero : ∀ t, ¬P t → (program w r (by omega)).matrix t p=0)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (hlow : ∀ i : Fin n, i.val < r → localR (position i) (w i)*R=R*localR (position i) (w i))
    (hhigh : ∀ i : Fin n, r + 1 < i.val → localR (position i) (w i)*L=L*localR (position i) (w i))
    (hyb : ∀ t, P t → ∀ q,
      (localR (position (n := n) ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
        localR (position (n := n) ⟨r,by omega⟩) (w ⟨r,by omega⟩) * R) q t =
      (L * localR (position (n := n) ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
        localR (position (n := n) ⟨r,by omega⟩) (v ⟨r,by omega⟩)) q t) :
    ∀ q, ((program w n le_rfl).matrix*R) q p = (L*(program v n le_rfl).matrix) q p := by
  have hbase (q : Pairing (n+1)) :
      ((program w (r+2) hr).matrix*R) q p = (L*(program v (r+2) hr).matrix) q p := by
    have hcomm := program_commute w r (by omega) R hlow
    have heq := program_congr w v r (by omega) (fun i hi => he i (by omega) (by omega))
    change ((localR (position (n := n) ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
      (localR (position (n := n) ⟨r,by omega⟩) (w ⟨r,by omega⟩) * (program w r _).matrix))*R) q p =
      (L*(localR (position (n := n) ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
      (localR (position (n := n) ⟨r,by omega⟩) (v ⟨r,by omega⟩) * (program v r _).matrix))) q p
    rw [Matrix.mul_assoc,Matrix.mul_assoc,hcomm,←Matrix.mul_assoc,←Matrix.mul_assoc]
    rw [←Matrix.mul_assoc L,←Matrix.mul_assoc,←heq]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    apply sum_congr rfl
    intro t _
    by_cases ht : P t
    · rw [hyb t ht q]
    · rw [hzero t ht,mul_zero,mul_zero]
  have hstep (k : ℕ) (hkr : r+2≤k) (hkn : k≤n) :
      ∀ q, ((program w k hkn).matrix*R) q p=(L*(program v k hkn).matrix) q p := by
    induction k,hkr using Nat.le_induction with
    | base => exact hbase
    | succ k hk ih =>
      intro q
      have hk' : k<n := by omega
      change ((localR (position (n := n) ⟨k,hk'⟩) (w ⟨k,hk'⟩) * (program w k _).matrix)*R) q p =
        (L*(localR (position (n := n) ⟨k,hk'⟩) (v ⟨k,hk'⟩) * (program v k _).matrix)) q p
      rw [Matrix.mul_assoc]
      have hi : (localR (position (n := n) ⟨k,hk'⟩) (w ⟨k,hk'⟩) *
        ((program w k (by omega)).matrix*R)) q p =
        (localR (position (n := n) ⟨k,hk'⟩) (w ⟨k,hk'⟩) * (L*(program v k (by omega)).matrix)) q p := by
        rw [Matrix.mul_apply, Matrix.mul_apply]
        apply sum_congr rfl
        intro t _
        rw [ih (by omega) t]
      rw [hi,←Matrix.mul_assoc,hhigh ⟨k,hk'⟩ (by change r+1<k; omega),
        he ⟨k,hk'⟩ (by change k≠r; omega) (by change k≠r+1; omega),Matrix.mul_assoc]
  exact hstep n hr le_rfl

end PartialColumn
end

 

 

noncomputable section
open scoped Classical
namespace PartialColumn
variable {n m : ℕ}






lemma column_restricted_train {K : Type*} [CommRing K]
    (w v : Fin n → Weights K) (r : ℕ) (hr : r+2≤n) (a : Weights K)
    (p : Pairing n) (P : Pairing (n+1) → Prop)
    (hzero : ∀ t, ¬P t → (program w r (by omega)).matrix t p.padBottom=0)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (hyb : ∀ t, P t → ∀ q,
      (localR (position (n := n) ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
        localR (position (n := n) ⟨r,by omega⟩) (w ⟨r,by omega⟩) *
        localR (rowPosition r hr).padBottom a) q t =
      (localR (rowPosition r hr).padTop a *
        localR (position (n := n) ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
        localR (position (n := n) ⟨r,by omega⟩) (v ⟨r,by omega⟩)) q t) (q : Pairing n) :
    (column w * localR (rowPosition r hr) a) q p =
      (localR (rowPosition r hr) a * column v) q p := by
  have H := exchange_program_column w v r hr
    (localR (rowPosition r hr).padTop a) (localR (rowPosition r hr).padBottom a)
    p.padBottom P hzero he
    (fun i hi => localR_commute _ _ (row_disjoint_low r hr i hi) _ _)
    (fun i hi => localR_commute _ _ (row_disjoint_high r hr i hi) _ _) hyb q.padTop
  have hcw : (program w n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column w := by
    ext q p; exact program_column (by omega) w p q
  have hcv : (program v n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column v := by
    ext q p; exact program_column (by omega) v p q
  rw [localR_bottom_matrix,localR_top_matrix,hcw,hcv] at H
  exact H


end PartialColumn
end





end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SwapVacancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
open Finset
namespace Pairing

lemma moveIntoVacancy_eq_self {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬p.Occupied a) (hb : ¬p.Occupied b) :
    p.moveIntoVacancy a b hab hb=p := by
  apply ext_adj
  intro i j
  rw [moveIntoVacancy_adj]
  have hn (x y : Fin n) (h : p.Adj x y) : Equiv.swap a b x=x := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; exact ha ⟨y,he ▸ h⟩
    · intro he; exact hb ⟨y,he ▸ h⟩
  constructor
  · intro h
    have hi := hn _ _ h
    have hj := hn _ _ (adj_symm h)
    simp only [Equiv.swap_apply_self] at hi hj
    rwa [←hi,←hj] at h
  · intro h
    rw [hn _ _ h,hn _ _ (adj_symm h)]
    exact h

lemma moveIntoVacancy_map_omit {n : ℕ} (p : Pairing n) (a b : Fin (n+1))
    (hab : a.val+1=b.val) :
    (p.map (Fin.succAboveOrderEmb b)).moveIntoVacancy a b hab (p.map_not_occupied_omit b)=
      p.map (Fin.succAboveOrderEmb a) := by
  apply ext_adj
  intro x y
  rw [moveIntoVacancy_adj,map_adj,map_adj]
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    refine ⟨i,j,h,?_,?_⟩
    · have hh:=congrArg (Equiv.swap a b) hi
      simpa only [Fin.succAboveOrderEmb_apply,Fin.swap_succAbove_adjacent a b hab,
        Equiv.swap_apply_self] using hh
    · have hh:=congrArg (Equiv.swap a b) hj
      simpa only [Fin.succAboveOrderEmb_apply,Fin.swap_succAbove_adjacent a b hab,
        Equiv.swap_apply_self] using hh
  · rintro ⟨i,j,h,hi,hj⟩
    refine ⟨i,j,h,?_,?_⟩
    · have hh:=congrArg (Equiv.swap a b) hi
      simp only [Fin.succAboveOrderEmb_apply] at hh
      rw [←Fin.swap_succAbove_adjacent a b hab i,Equiv.swap_apply_self] at hh
      exact hh
    · have hh:=congrArg (Equiv.swap a b) hj
      simp only [Fin.succAboveOrderEmb_apply] at hh
      rw [←Fin.swap_succAbove_adjacent a b hab j,Equiv.swap_apply_self] at hh
      exact hh
end Pairing

end





noncomputable section
open scoped Classical
open Finset

lemma Pairing.tileStep_empty_iff {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) :
    p.tileStep a b hab t=some (empty n) ↔ p=empty n ∧ t=.vacant := by
  constructor
  · intro h
    have hg:=p.stepWiring_realizes a b hab t (empty n) h
    have hp : p=empty n := by
      apply (Pairing.eq_empty_iff p).mpr
      rintro i ⟨j,hij⟩
      obtain ⟨k,hk,_⟩ := hg.no_loop (.old i) (.old j) hij
      exact empty_not_occupied k hk
    have ht : t=.vacant := by
      apply (Tile.eq_vacant_iff t).mpr
      rintro i ⟨j,hij⟩
      obtain ⟨k,hk,_⟩ := hg.no_loop (.box i) (.box j) hij
      exact empty_not_occupied k hk
    exact ⟨hp,ht⟩
  · rintro ⟨rfl,rfl⟩
    simp [Pairing.tileStep]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical
open Finset

lemma localR_padTop_zero_last {K : Type*} [CommRing K] {n : ℕ} (a : Position n)
    (w : Weights K) (p q : Pairing (n+1))
    (h : ¬ (q.Occupied (Fin.last n) ↔ p.Occupied (Fin.last n))) :
    localR a.padTop w q p=0 := by
  apply localR_zero_of_support a.padTop w p q (Fin.last n) _ _ h
  · exact Ne.symm (Fin.castSucc_ne_last _)
  · exact Ne.symm (Fin.castSucc_ne_last _)

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
open scoped Classical
open Finset

 
def LastMatrix {K:Type*} [Zero K] {n m:ℕ}
    (M:Matrix (Pairing (m+1)) (Pairing (n+1)) K) : Prop :=
  ∀p q, ¬(p.Occupied (Fin.last m) ↔ q.Occupied (Fin.last n)) → M p q=0

def matrixPolynomial {K:Type*} [CommRing K] {n m:ℕ}
    (M:Matrix (Pairing m) (Pairing n) K) (P:Pairing n → Polynomial K) :
    Pairing m → Polynomial K := fun p =>∑q,Polynomial.C (M p q)*P q

lemma matrixPolynomial_coeff {K:Type*} [CommRing K] {n m:ℕ}
    (M:Matrix (Pairing m) (Pairing n) K) (P:Pairing n → Polynomial K) (p:Pairing m) (k:ℕ) :
    (matrixPolynomial M P p).coeff k=M.mulVec (fun q =>(P q).coeff k) p := by
  simp only [matrixPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,Matrix.mulVec,dotProduct]

lemma LastMatrix.degree {K:Type*} [CommRing K] {n m d:ℕ}
    {M:Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM:LastMatrix M)
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree d P) : LastDegree d (matrixPolynomial M P) := by
  intro p k hk
  rw [matrixPolynomial_coeff]
  apply sum_eq_zero
  intro q _
  change M p q*(P q).coeff k=0
  by_cases h:p.Occupied (Fin.last m) ↔ q.Occupied (Fin.last n)
  · rw [hP q k (by rwa [←h]),mul_zero]
  · rw [hM p q h,zero_mul]

lemma LastMatrix.lastValue {K:Type*} [CommRing K] {n m:ℕ}
    {M:Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM:LastMatrix M)
    (b s:K) (P:Pairing (n+1) → Polynomial K) :
    lastValue (RingHom.id K) b s (matrixPolynomial M P)=
      M.mulVec (lastValue (RingHom.id K) b s P) := by
  funext p
  simp only [CriticalStrip.Diagram.lastValue,matrixPolynomial,Polynomial.eval₂_id,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,Matrix.mulVec,dotProduct]
  split_ifs with hp
  · rw [mul_sum]
    apply sum_congr rfl
    intro q _
    by_cases hq:q.Occupied (Fin.last n)
    · simp only [hq,ite_true]; ring
    · rw [hM p q (by simp [hp,hq]),zero_mul,mul_zero]
      simp
  · apply sum_congr rfl
    intro q _
    by_cases hq:q.Occupied (Fin.last n)
    · rw [hM p q (by simp [hp,hq]),zero_mul,zero_mul]
    · simp [hq]

lemma LastMatrix.leading {K:Type*} [CommRing K] {n m d:ℕ}
    {M:Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM:LastMatrix M)
    (M':Matrix (Pairing m) (Pairing n) K)
    (h:∀p q,M p.padTop q.padTop=M' p q)
    (P:Pairing (n+1) → Polynomial K) (p:Pairing m) :
    (matrixPolynomial M P p.padTop).coeff d=M'.mulVec (fun q =>(P q.padTop).coeff d) p := by
  rw [matrixPolynomial_coeff]
  simp only [Matrix.mulVec,dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padTop Pairing.padTop_injective
  · intro q hq
    have ho:q.Occupied (Fin.last n) := by
      by_contra hn
      exact hq ⟨q.restrict Fin.castSuccOrderEmb,Pairing.padTop_restrict q hn⟩
    rw [hM p.padTop q (by simp [ho]),zero_mul]
  · intro q; rw [h]

lemma LastMatrix.local {K:Type*} [CommRing K] {n:ℕ} (a:Position n) (w:Weights K) :
    LastMatrix (localR a.padTop w) := fun p q =>localR_padTop_zero_last a w q p

lemma LastMatrix.omit {K:Type*} [CommRing K] {n:ℕ} (r:Fin (n+1)) :
    LastMatrix (functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc))) := by
  intro p q h
  unfold functionMatrix optionMatrix
  split_ifs with he
  · have hh:q.map (Fin.succAboveOrderEmb r.castSucc)=p := Option.some.inj he
    exfalso; apply h
    rw [←hh,←Pairing.omit_last r]
    exact Pairing.map_occupied _ q _
  · rfl

lemma LastMatrix.mul {K:Type*} [CommRing K] {n m r:ℕ}
    {M:Matrix (Pairing (r+1)) (Pairing (m+1)) K}
    {N:Matrix (Pairing (m+1)) (Pairing (n+1)) K}
    (hM:LastMatrix M) (hN:LastMatrix N) : LastMatrix (M*N) := by
  intro p q h
  apply sum_eq_zero; intro t _
  change M p t*N t q=0
  by_cases ht:p.Occupied (Fin.last r) ↔ t.Occupied (Fin.last m)
  · rw [hN t q (fun hh =>h (ht.trans hh)),mul_zero]
  · rw [hM p t ht,zero_mul]

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


theorem Pairing.padBottom_injective {n : ℕ} : Function.Injective (@Pairing.padBottom n) := by
  intro p q h
  have := congrArg (fun r => r.restrict (Fin.succOrderEmb n)) h
  simpa [Pairing.padBottom, Pairing.restrict_map] using this

 
theorem Pairing.padBottom_padTop {n : ℕ} (p : Pairing n) :
    p.padBottom.padTop = p.padTop.padBottom := by
  apply Subtype.ext
  simp only [Pairing.padTop, Pairing.padBottom, Pairing.map, Finset.map_map]
  congr 1



theorem LastDegree.vacantBottomExtension {K : Type*} [CommRing K] {n m : ℕ}
    {P : Pairing (n+1) → Polynomial K} (hP : LastDegree m P) :
    LastDegree m (vacantBottomExtension P) := by
  intro p k hk
  by_cases hp : p.Occupied 0
  · simp [CriticalStrip.Diagram.vacantBottomExtension, hp]
  · rw [← p.padBottom_restrict hp] at hk ⊢
    rw [vacantBottomExtension_padBottom]
    apply hP
    simpa only [← Fin.succ_last, Pairing.padBottom_occupied_succ] using hk



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairSelfNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical



lemma LastDegree.mul_poly {K:Type*} [CommRing K] {n m d:ℕ}
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree m P)
    (F:Polynomial K) (hF:F.natDegree≤d) : LastDegree (m+d) (fun p =>F*P p) := by
  intro p k hk
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have hk':ab.1+ab.2=k:=by simpa using hab
  by_cases ha:d<ab.1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF ha),zero_mul]
  · rw [hP p ab.2 (by split_ifs at hk ⊢ <;> omega),mul_zero]

lemma LastDegree.mul_poly_top {K:Type*} [CommRing K] {n m d:ℕ}
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree m P)
    (F:Polynomial K) (hF:F.natDegree≤d) (p:Pairing n) :
    (F*P p.padTop).coeff (m+d)=F.coeff d*(P p.padTop).coeff m := by
  rw [add_comm,Polynomial.coeff_mul_add_eq_of_natDegree_le hF]
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk =>hP _ k (by simpa using hk))

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MergePairCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical







def PairExchangeRegular {n m:ℕ} (z:Fin (n+1) → SpectralField m) (i j:Fin n) : Prop :=
  ∀a b:Fin n,a≠b → ¬(a=i ∧ b=j ∨ a=j ∧ b=i) →
    torusL (z b.castSucc/z a.castSucc)≠0

lemma PairExchangeRegular.perm {n m:ℕ} {z:Fin (n+1) → SpectralField m} {i j:Fin n}
    (h:PairExchangeRegular z i j) (σ:Equiv.Perm (Fin n)) :
    PairExchangeRegular (z ∘ topPerm σ) (σ.symm i) (σ.symm j) := by
  intro a b hab hij
  simp only [Function.comp_apply,topPerm_cast]
  apply h (σ a) (σ b) (fun e =>hab (σ.injective e))
  simpa only [←Equiv.eq_symm_apply] using hij



end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

 

def fullPeel {n:ℕ} (i:Fin (n+1)) : Laurent (n+1) →+* LaurentPolynomial (SpectralField (n+1)) :=
  (AddMonoidAlgebra.mapRingHom ℤ (insertSpectral i)).comp (peelLaurent i)

lemma fullPeel_coeff {n:ℕ} (i:Fin (n+1)) (f:Laurent (n+1)) (k:ℤ) :
    (fullPeel i f).coeff k=insertSpectral i ((peelLaurent i f).coeff k) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

lemma LaurentBox.fullPeel {n:ℕ} {f:Laurent (n+1)} {b:Fin (n+1) → ℕ}
    (hb:LaurentBox f b) (i:Fin (n+1)) : LaurentInterval (fullPeel i f) (-(b i:ℤ)) (b i) := by
  intro k hk
  apply hb.peel i k
  intro hz
  rw [fullPeel_coeff,hz,map_zero] at hk
  exact hk rfl

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ResidualParityCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical







lemma PairExchangeRegular.symm {n m:ℕ} {z:Fin (n+1) → SpectralField m} {i j:Fin n}
    (h:PairExchangeRegular z i j) : PairExchangeRegular z j i := by
  intro a b hab hij
  exact h a b hab (by tauto)



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma Pairing.exists_earlier_occupied {n:ℕ} (p:Pairing (n+1)) (hp:p≠empty (n+1)) :
    ∃i:Fin n,p.Occupied i.castSucc := by
  have hn:p.val.Nonempty := by
    by_contra h
    apply hp
    apply Subtype.ext
    exact Finset.not_nonempty_iff_eq_empty.mp h
  obtain ⟨⟨a,b⟩,hab⟩:=hn
  have hlt:a<b := p.property.1 _ hab
  have ha:a.val<n := by have:=b.isLt; exact lt_of_lt_of_le hlt (by omega)
  exact ⟨⟨a.val,ha⟩,b,Or.inl hab⟩








lemma Pairing.one_eq_empty (p:Pairing 1) : p=empty 1 := by
  apply p.eq_empty_iff.mpr
  rintro i ⟨j,hj⟩
  have he:j=i := Subsingleton.elim _ _
  exact p.adj_irrefl i (he ▸ hj)







lemma LastMatrix.lastValue_map {K L:Type*} [CommRing K] [CommRing L] {n m:ℕ}
    {M:Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM:LastMatrix M)
    (f:K →+* L) (b s:L) (P:Pairing (n+1) → Polynomial K) :
    CriticalStrip.Diagram.lastValue f b s (matrixPolynomial M P)=(M.map f).mulVec (CriticalStrip.Diagram.lastValue f b s P) := by
  funext p
  simp only [CriticalStrip.Diagram.lastValue,matrixPolynomial,Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,Matrix.mulVec,dotProduct,Matrix.map_apply]
  split_ifs with hp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq:q.Occupied (Fin.last n)
    · simp only [hq,ite_true]; ring
    · rw [hM p q (by simp [hp,hq]),map_zero,zero_mul,mul_zero]
      simp
  · apply Finset.sum_congr rfl
    intro q _
    by_cases hq:q.Occupied (Fin.last n)
    · rw [hM p q (by simp [hp,hq]),map_zero,zero_mul,zero_mul]
    · simp [hq]

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



def boundaryClosure {V : Type*} {n : ℕ} (r : V → V → Prop) (a : Fin n → V)
    (q : Pairing n) (v w : V) : Prop :=
  r v w ∨ ∃ i j, q.Adj i j ∧ a i = v ∧ a j = w

lemma closure_lift {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {q : Pairing n} {v w : V} (h : Relation.ReflTransGen r v w) :
    Relation.ReflTransGen (boundaryClosure r a q) v w :=
  Relation.ReflTransGen.mono (fun _ _ hh => Or.inl hh) _ _ h

 

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

namespace Pairing

instance join_symm {n : ℕ} (p q : Pairing n) : Std.Symm (join p q) :=
  ⟨fun _ _ h => h.elim (fun h => Or.inl (adj_symm h)) (fun h => Or.inr (adj_symm h))⟩



end Pairing

namespace GraphRealizes
variable {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
  {p q : Pairing n}

lemma closure_reach (hp : GraphRealizes r a p) (i j : Fin n) :
    Relation.ReflTransGen (Graph.boundaryClosure r a q) (a i) (a j) ↔
      Relation.ReflTransGen (p.join q) i j := by
  constructor
  · intro h
    have hs : ∀ {x}, Relation.ReflTransGen (Graph.boundaryClosure r a q) (a i) x →
        ∃ k, Relation.ReflTransGen (p.join q) i k ∧ Relation.ReflTransGen r (a k) x := by
      intro x hx
      induction hx with
      | refl => exact ⟨i,.refl,.refl⟩
      | @tail x y hx hxy ih =>
        obtain ⟨k,hk,hr⟩ := ih
        rcases hxy with hxy | ⟨l,m,hlm,hl,hm⟩
        · exact ⟨k,hk,hr.tail hxy⟩
        · subst x; subst y
          have hkl : Relation.ReflTransGen (p.join q) k l := by
            rcases (hp.reach k l).mp hr with rfl | hkl
            · exact .refl
            · exact .single (Or.inl hkl)
          exact ⟨m,(hk.trans hkl).tail (Or.inr hlm),.refl⟩
    obtain ⟨k,hk,hr⟩ := hs h
    rcases (hp.reach k j).mp hr with rfl | hkj
    · exact hk
    · exact hk.tail (Or.inl hkj)
  · intro h
    apply Graph.map_reach a _ h
    intro k l hkl
    rcases hkl with hkl | hkl
    · exact Graph.closure_lift ((hp.reach k l).mpr (Or.inr hkl))
    · exact .single (Or.inr ⟨k,l,hkl,rfl,rfl⟩)

lemma closure_drains_iff (hp : GraphRealizes r a p) (ha : Function.Injective a)
    (root : Fin n) :
    Graph.DrainsAt (Graph.boundaryClosure r a q) (a root) ↔
      Graph.DrainsAt (p.join q) root := by
  constructor
  · intro h i j hij
    apply (hp.closure_reach i root).mp
    rcases hij with hpij | hqij
    · obtain ⟨w,hw⟩ := (hp.boundary_used_iff ha i).mpr ⟨j,hpij⟩
      exact h _ _ (Or.inl hw)
    · exact h _ _ (Or.inr ⟨i,j,hqij,rfl,rfl⟩)
  · intro h v w hvw
    rcases hvw with hvw | ⟨i,j,hij,rfl,rfl⟩
    · obtain ⟨i,⟨j,hij⟩,hi⟩ := hp.no_loop v w hvw
      exact (Graph.closure_lift hi).trans ((hp.closure_reach i root).mpr
        (h i j (Or.inl hij)))
    · exact (hp.closure_reach i root).mpr (h i j (Or.inr hij))

end GraphRealizes

namespace Pairing

 
def GateCompatible {n : ℕ} (p q : Pairing n) (a b : Fin n) (t : Tile) : Prop :=
  CutPatch.Compatible (p.cutShape a b) t ∧
    ∀ i, p.stepSupport a b t i ↔ q.Occupied i


def closedStep {n : ℕ} (p q : Pairing n) (a b : Fin n) (t : Tile) :=
  Graph.boundaryClosure (p.stepWiring a b t) StepVertex.out q

end Pairing



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchTrig
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators






def twoPair : Pairing 2 := ⟨{(0,1)}, by simp [IsPairing]⟩

@[simp] lemma twoPair_adj (i j : Fin 2) : twoPair.Adj i j ↔ (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by
  simp [twoPair,Pairing.Adj,and_comm]

@[simp] lemma twoPair_occupied (i : Fin 2) : twoPair.Occupied i := by
  fin_cases i <;> simp [Pairing.Occupied]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhysicalStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset _root_.Matrix









namespace Pairing

structure ArcAddition {n : ℕ} (p q : Pairing n) (a b : Fin n) : Prop where
  lt : a < b
  vacant : ∀ i, a ≤ i → i ≤ b → ¬ p.Occupied i
  adj : ∀ i j, q.Adj i j ↔
    (i=a ∧ j=b) ∨ (i=b ∧ j=a) ∨ p.Adj i j

end Pairing



namespace ArcColumn
variable {n : ℕ} {p q : Pairing n} {a b : Fin n} (h : Pairing.ArcAddition p q a b)

include h

def label (a : Fin n) (v : Vertex n) : Fin n := if v.2=0 ∨ v.2=3 then a else v.1

end ArcColumn



def ColumnNonnegative {n : ℕ} (w : Fin n → Weights ℝ) : Prop :=
  ∀ (p q : Pairing n) (t : Configuration n), Realizes p q t →
    0 ≤ ∏ i, (w i).tile (t i)

end
end CriticalStrip.Diagram

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
open scoped BigOperators Classical
namespace ColumnChain
section RingCoefficients
variable {K : Type*} [CommRing K] {n : ℕ}

def mass (w : Fin n → Weights K) (m : ℕ) (q p : Pairing n) : K :=
  ∑ h : Fin m → Configuration n, if Runs p (List.ofFn h) q then weight w (List.ofFn h) else 0

end RingCoefficients

 

 


variable {n : ℕ}

lemma weight_head_ne_zero (w : Fin n → Weights ℝ) (t : Configuration n)
    (ts : List (Configuration n)) (h : weight w (t::ts)≠0) (i : Fin n) :
    (w i).tile (t i)≠0 := by
  have hh := (mul_ne_zero_iff.mp h).1
  exact (Finset.prod_ne_zero_iff.mp hh) i (Finset.mem_univ i)

lemma weight_tail_ne_zero (w : Fin n → Weights ℝ) (t : Configuration n)
    (ts : List (Configuration n)) (h : weight w (t::ts)≠0) : weight w ts≠0 :=
  (mul_ne_zero_iff.mp h).2

 

theorem north_shape (w : Fin n → Weights ℝ) (ts : List (Configuration (n+1)))
    (q : Pairing (n+1)) (hr : Runs (empty (n+1)) ts q)
    (hw : weight (Fin.snoc w northInjectionWeights) ts≠0) :
    (q.Occupied (Fin.last n) → ∃ k l : ℕ,
      ts.map (fun t=>t (Fin.last n))=
        List.replicate k Tile.diagonal₁ ++ Tile.vertical₀ :: List.replicate l Tile.vacant) ∧
    (¬q.Occupied (Fin.last n) →
      ts.map (fun t=>t (Fin.last n))=List.replicate ts.length Tile.vacant) := by
  induction ts generalizing q with
  | nil =>
    have he : empty (n+1)=q := hr
    subst q
    refine ⟨fun h=>(empty_not_occupied _ h).elim,fun _=>rfl⟩
  | cons t ts ih =>
    obtain ⟨p,hp,ht⟩:=hr
    have hf := weight_head_ne_zero (Fin.snoc w northInjectionWeights) t ts hw (Fin.last n)
    rw [Fin.snoc_last] at hf
    obtain ⟨h₁,h₀⟩ := ih p hp (weight_tail_ne_zero _ t ts hw)
    have he:=ht.last_eq
    by_cases hp : p.Occupied (Fin.last n)
    · by_cases hq : q.Occupied (Fin.last n)
      · have he' : t (Fin.last n)=.diagonal₁ := by simpa only [lastTile,hp,hq,ite_true] using he
        obtain ⟨k,l,hshape⟩:=h₁ hp
        refine ⟨fun _=>⟨k+1,l,?_⟩,fun h=>(h hq).elim⟩
        simp only [List.map_cons,he',hshape,List.replicate_succ,List.cons_append]
      · have he' : t (Fin.last n)=.cap := by simpa only [lastTile,hp,hq,ite_true,ite_false] using he
        simp only [he',northInjectionWeights,Weights.tile,ne_eq,not_true_eq_false] at hf
    · by_cases hq : q.Occupied (Fin.last n)
      · have he' : t (Fin.last n)=.vertical₀ := by simpa only [lastTile,hp,hq,ite_true,ite_false] using he
        refine ⟨fun _=>⟨0,ts.length,?_⟩,fun h=>(h hq).elim⟩
        simp only [List.map_cons,he',h₀ hp,List.replicate_zero,List.nil_append]
      · have he' : t (Fin.last n)=.vacant := by simpa only [lastTile,hp,hq,ite_false] using he
        refine ⟨fun h=>(hq h).elim,fun _=>?_⟩
        simp only [List.map_cons,he',h₀ hp,List.length_cons,List.replicate_succ]

end ColumnChain
end

 

 

noncomputable section
open scoped Classical
namespace ColumnChain
variable {n : ℕ}



lemma read_tile_ne_zero {w : Fin n → Weights ℝ} {ts : List (Configuration n)}
    (h : weight w ts ≠ 0) (k : ℕ) (i : Fin n) : (w i).tile (read ts k i)≠0 := by
  induction ts generalizing k with
  | nil => simp [Weights.tile]
  | cons t ts ih =>
    cases k with
    | zero => exact weight_head_ne_zero w t ts h i
    | succ k => exact ih (weight_tail_ne_zero w t ts h) k

end ColumnChain
end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BoundaryTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/







namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped BigOperators Classical
open FiniteBranchTree

def factor (b : Bool) : ℂ := (rho : ℂ) * Diagram.phase ^ sign b

end
end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CollisionLeaf
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


def turnPotential {n : ℕ} (p : Pairing n) (g : Fin n → ℤ) (i : Fin n) : ℤ :=
  g i - if p.Occupied i ∧ p.partnerOrSelf i < i then 3 else 0

end Pairing








end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombDictionary
attribute [-instance] _root_.OAI.CriticalStrip.HoneycombAssignment.portWiring_symm_instance
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

lemma down_support_iff (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) :
    down i j ∈ D.graph.support ↔ (D.tile (i,j)).lowerUsed := by
  change (∃ w, D.graph.Adj (down i j) w) ↔ _
  constructor
  · rintro ⟨w,hw⟩
    apply (Tile.lowerUsed_iff _ (D.physical (i,j))).mpr
    rcases (D.down_neighbors i j w).mp hw with ⟨_,h⟩
    rcases h with ⟨_,hm⟩ | ⟨_,he⟩ | ⟨_,_,hs⟩
    · exact Or.inr (Or.inr hm)
    · exact Or.inl he
    · exact Or.inr (Or.inl hs)
  · intro hu
    have hj : j<N := by
      by_contra hn
      rw [D.outside i j (by omega)] at hu
      exact Bool.false_ne_true hu
    rcases Tile.lowerUsed_internal _ (D.physical (i,j)) hu with hw | hm
    · exact ⟨up (i+1) j,(D.down_neighbors i j _).mpr ⟨hj,Or.inr (Or.inl ⟨rfl,hw⟩)⟩⟩
    · exact ⟨up i j,(D.down_neighbors i j _).mpr ⟨hj,Or.inl ⟨rfl,hm⟩⟩⟩

end HoneycombAssignment

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
open _root_.Matrix Set
open scoped BigOperators Classical

lemma physicalWeights_lambda : physicalWeights lambda=(⟨rho,rho^2,rho^2,rho^2,0⟩ : Weights ℝ) := by
  have hh:=physicalWeights_reflection (2*lambda)
  rw [show 3*lambda-2*lambda=lambda by ring,physicalWeights_two_lambda] at hh
  exact hh

end





end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace HoneycombAssignment
variable {N : ℕ}



lemma port_projects_used (D : HoneycombAssignment N) {v : HoneycombPort}
    (hv : Graph.Used D.portWiring v) : portTriangle v∈D.graph.support := by
  have hp := (D.port_used v).mp hv
  have h := Tile.occupied_triangle (D.tile v.1) (D.physical v.1) v.2 hp
  rcases v with ⟨⟨i,j⟩,a⟩
  dsimp only [portTriangle]
  by_cases ha : a.val<2
  · simpa only [ha,decide_true,ite_true,←D.up_support_iff,up] using h
  · simpa only [ha,decide_false,Bool.false_eq_true,ite_false,←D.down_support_iff,down] using h

lemma port_projects_edge (D : HoneycombAssignment N) {v w : HoneycombPort}
    (h : D.portWiring v w) : Relation.ReflTransGen D.graph.Adj (portTriangle v) (portTriangle w) := by
  rcases v with ⟨⟨i,j⟩,a⟩
  rcases w with ⟨⟨k,l⟩,b⟩
  dsimp only [portWiring,Prod.fst,Prod.snd] at h
  rcases h with ⟨he,h⟩ | ⟨hj,hi,ha,hb,h⟩ | ⟨hj,hi,hb,ha,h⟩ |
    ⟨hi,hj,hn,ha,hb,h⟩ | ⟨hi,hj,hn,hb,ha,h⟩
  · cases he
    rcases Tile.adjacent_projects (D.tile (i,j)) (D.physical (i,j)) a b h with hp | hm
    · have : portTriangle ((i,j),a)=portTriangle ((i,j),b) := by
        simp only [portTriangle,hp]
      exact this ▸ Relation.ReflTransGen.refl
    · have hn := D.port_in_strip (show (D.tile (i,j)).Occupied a from ⟨b,h⟩)
      have he : D.graph.Adj (up i j) (down i j) := (tileGraph_middle N D.tile i j).mpr ⟨hn,hm⟩
      by_cases ha : a.val<2 <;> by_cases hb : b.val<2
      · simp only [portTriangle,ha,hb,decide_true]; exact .refl
      · simpa only [portTriangle,ha,hb,decide_true,decide_false,up,down] using Relation.ReflTransGen.single he
      · simpa only [portTriangle,ha,hb,decide_true,decide_false,up,down] using
          Relation.ReflTransGen.single (D.graph.symm.symm _ _ he)
      · simp only [portTriangle,ha,hb,decide_false]; exact .refl
  · subst k; subst l; subst a; subst b
    have hh : D.graph.Adj (down i j) (up (i+1) j) :=
      (D.down_neighbors i j _).mpr ⟨D.port_in_strip h,Or.inr (Or.inl ⟨rfl,h⟩)⟩
    exact .single hh
  · subst i; subst j; subst a; subst b
    have hh : D.graph.Adj (down k l) (up (k+1) l) :=
      (D.down_neighbors k l _).mpr ⟨D.port_in_strip h,Or.inr (Or.inl ⟨rfl,h⟩)⟩
    exact .single (D.graph.symm.symm _ _ hh)
  · subst k; subst l; subst a; subst b
    exact .single ((D.down_neighbors i j _).mpr ⟨by omega,Or.inr (Or.inr ⟨hn,rfl,h⟩)⟩)
  · subst i; subst j; subst a; subst b
    exact .single (D.graph.symm.symm _ _
      ((D.down_neighbors k l _).mpr ⟨by omega,Or.inr (Or.inr ⟨hn,rfl,h⟩)⟩))

lemma representative_used (D : HoneycombAssignment N) {v : Triangle}
    (hv : v∈D.graph.support) : Graph.Used D.portWiring (D.representative v) := by
  rw [D.port_used]
  rcases v with ⟨i,j,b⟩
  change (D.tile (i,j)).Occupied ((D.tile (i,j)).representative b)
  rw [Tile.representative_occupied _ (D.physical (i,j))]
  cases b
  · exact (D.down_support_iff i j).mp hv
  · exact (D.up_support_iff i j).mp hv



lemma port_reach_iff (D : HoneycombAssignment N) {v w : HoneycombPort}
    (hv : Graph.Used D.portWiring v) (hw : Graph.Used D.portWiring w) :
    Relation.ReflTransGen D.portWiring v w ↔
      Relation.ReflTransGen D.graph.Adj (portTriangle v) (portTriangle w) := by
  constructor
  · exact Graph.map_reach portTriangle (fun _ _=>D.port_projects_edge)
  · intro h
    exact ((D.port_to_representative hv).trans
      (Graph.map_reach D.representative (fun _ _=>D.lifts_edge) h)).trans
      (symm (D.port_to_representative hw))

 

lemma port_drains_iff (D : HoneycombAssignment N) {root : HoneycombPort}
    (hr : Graph.Used D.portWiring root) :
    Graph.DrainsAt D.portWiring root ↔ Graph.DrainsAt D.graph.Adj (portTriangle root) := by
  constructor
  · intro h v w hvw
    obtain ⟨a,ha⟩ := D.representative_used (show v∈D.graph.support from ⟨w,hvw⟩)
    have hh := Graph.map_reach portTriangle (fun _ _=>D.port_projects_edge) (h _ _ ha)
    simpa only [D.representative_projects] using hh
  · intro h v w hvw
    have hv := D.port_projects_used (show Graph.Used D.portWiring v from ⟨w,hvw⟩)
    obtain ⟨a,ha⟩ := hv
    exact (D.port_reach_iff ⟨w,hvw⟩ hr).mpr (h _ _ ha)

end HoneycombAssignment
end
end CriticalStrip

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

namespace SewnRectangle
variable {n : ℕ}



lemma horizontal (l r : List (Configuration n))
    (hl : ColumnChain.LocallyCompatible l) (hr : ColumnChain.LocallyCompatible r)
    (hcut : ∀j, (ColumnChain.read l 0 j).Occupied 2 ↔ (ColumnChain.read r 0 j).Occupied 2)
    (i : ℤ) (j : ℕ) : (tile l r (i,j)).Occupied 2 ↔ (tile l r (i+1,j)).Occupied 1 := by
  by_cases hj : j<n
  · let j' : Fin n := ⟨j,hj⟩
    rcases split_column i with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · cases k with
      | zero =>
        change (tile l r (-1-(0:ℕ),j'.val)).Occupied 2 ↔ (tile l r ((0:ℕ),j'.val)).Occupied 1
        rw [tile_left l r 0 j',tile_right l r 0 j',Tile.horizontal_occupied_one]
        exact hcut j'
      | succ k =>
        have he : -1-((k+1:ℕ):ℤ)+1 = -1-(k:ℤ) := by omega
        rw [tile_left l r (k+1) j',he,tile_left l r k j']
        exact hl.horizontal k j'
    · rw [tile_right l r k j',show (k:ℤ)+1=((k+1:ℕ):ℤ) by omega,tile_right l r (k+1) j',
        Tile.horizontal_occupied_two,Tile.horizontal_occupied_one]
      exact (hr.horizontal k j').symm
  · rw [tile_outside l r i j (by omega),tile_outside l r (i+1) j (by omega)]
    exact ⟨fun h=>(Tile.vacant_not_occupied 2 h).elim,fun h=>(Tile.vacant_not_occupied 1 h).elim⟩

lemma vertical (l r : List (Configuration n))
    (hl : ColumnChain.LocallyCompatible l) (hr : ColumnChain.LocallyCompatible r)
    (i : ℤ) (j : ℕ) (hj : j+1<n) :
    (tile l r (i,j)).Occupied 3 ↔ (tile l r (i,j+1)).Occupied 0 := by
  rcases split_column i with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rw [tile_left l r k ⟨j,by omega⟩,tile_left l r k ⟨j+1,hj⟩]
    exact hl.vertical k _ _ rfl
  · rw [tile_right l r k ⟨j,by omega⟩,tile_right l r k ⟨j+1,hj⟩,
      Tile.horizontal_occupied_three,Tile.horizontal_occupied_zero]
    exact hr.vertical k _ _ rfl

 

def assignment (l r : List (Configuration n))
    (hl : ColumnChain.LocallyCompatible l) (hr : ColumnChain.LocallyCompatible r)
    (hcut : ∀j, (ColumnChain.read l 0 j).Occupied 2 ↔ (ColumnChain.read r 0 j).Occupied 2)
    (hp : ∀k j, ColumnChain.read l k j≠.verticalPair)
    (hq : ∀k j, ColumnChain.read r k j≠.capCup) : HoneycombAssignment n where
  tile := tile l r
  physical := physical l r hp hq
  outside := tile_outside l r
  horizontal := horizontal l r hl hr hcut
  vertical := vertical l r hl hr

lemma south_vacant (l r : List (Configuration n))
    (hl : ColumnChain.LocallyCompatible l) (hr : ColumnChain.LocallyCompatible r) (i : ℤ) :
    ¬(tile l r (i,0)).Occupied 0 := by
  by_cases hn : 0<n
  · rcases split_column i with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · rw [tile_left l r k ⟨0,hn⟩]; exact hl.south k _ rfl
    · rw [tile_right l r k ⟨0,hn⟩,Tile.horizontal_occupied_zero]; exact hr.south k _ rfl
  · rw [tile_outside l r i 0 (by omega)]; exact Tile.vacant_not_occupied 0

lemma physical_from_weights (l r : List (Configuration (n+1)))
    (hl : ColumnChain.weight (Fin.snoc (fun _ : Fin n=>physicalWeights (2*Diagram.lambda)) northInjectionWeights) l≠0)
    (hr : ColumnChain.weight (Fin.snoc (fun _ : Fin n=>physicalWeights Diagram.lambda) northInjectionWeights) r≠0) :
    (∀k j, ColumnChain.read l k j≠.verticalPair) ∧ (∀k j, ColumnChain.read r k j≠.capCup) := by
  constructor
  · intro k j h
    have hh := ColumnChain.read_tile_ne_zero hl k j
    rw [h] at hh
    induction j using Fin.lastCases with
    | last => simp [Fin.snoc_last,northInjectionWeights,Weights.tile] at hh
    | cast i =>
      rw [Fin.snoc_castSucc] at hh
      change (physicalWeights (2*Diagram.lambda)).E≠0 at hh
      rw [physicalWeights_two_lambda] at hh
      exact hh rfl
  · intro k j h
    have hh := ColumnChain.read_tile_ne_zero hr k j
    rw [h] at hh
    induction j using Fin.lastCases with
    | last => simp [Fin.snoc_last,northInjectionWeights,Weights.tile] at hh
    | cast i =>
      rw [Fin.snoc_castSucc] at hh
      change (physicalWeights Diagram.lambda).F≠0 at hh
      rw [physicalWeights_lambda] at hh
      exact hh rfl

end SewnRectangle
end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace GraphRealizes
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    {a : Fin n → V} {b : Fin n → W} {p q : Pairing n}

lemma compressed_closure_edge (hp : GraphRealizes r a p) {x y : W}
    (h : Patch.compressed r s a b p.Occupied x y) :
    x=y ∨ Graph.boundaryClosure s b p x y := by
  rcases h with h | ⟨i,j,hi,hj,hr,rfl,rfl⟩
  · exact Or.inr (Or.inl h)
  · rcases (hp.reach i j).mp hr with rfl | he
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨i,j,he,rfl,rfl⟩)

lemma closure_compressed_edge (hp : GraphRealizes r a p) {x y : W}
    (h : Graph.boundaryClosure s b p x y) :
    Patch.compressed r s a b p.Occupied x y := by
  rcases h with h | ⟨i,j,hij,rfl,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨i,j,⟨j,hij⟩,⟨i,Pairing.adj_symm hij⟩,
      (hp.reach i j).mpr (Or.inr hij),rfl,rfl⟩

lemma compressed_closure_reach (hp : GraphRealizes r a p) (x y : W) :
    Relation.ReflTransGen (Patch.compressed r s a b p.Occupied) x y ↔
      Relation.ReflTransGen (Graph.boundaryClosure s b p) x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail z w h hzw ih =>
      rcases hp.compressed_closure_edge hzw with rfl | he
      · exact ih
      · exact ih.tail he
  · exact Relation.ReflTransGen.mono (fun _ _=>hp.closure_compressed_edge) _ _

lemma compressed_closure_drains (hp : GraphRealizes r a p) (root : W) :
    Graph.DrainsAt (Patch.compressed r s a b p.Occupied) root ↔
      Graph.DrainsAt (Graph.boundaryClosure s b p) root := by
  constructor
  · intro h v w hvw
    exact (hp.compressed_closure_reach v root).mp (h v w (hp.closure_compressed_edge hvw))
  · intro h v w hvw
    apply (hp.compressed_closure_reach v root).mpr
    rcases hvw with he | ⟨i,j,⟨k,hik⟩,hj,hr,rfl,rfl⟩
    · exact h v w (Or.inl he)
    · exact h (b i) (b k) (Or.inr ⟨i,k,hik,rfl,rfl⟩)

 

theorem sewn_drains_iff (hp : GraphRealizes r a p) (hq : GraphRealizes s b q)
    (hb : Function.Injective b) (root : Fin n) :
    Graph.DrainsAt (Patch.glued r s a b p.Occupied) (.inr (b root)) ↔
      Graph.DrainsAt (p.join q) root := by
  rw [Graph.drainsAt_glued_iff,hp.compressed_closure_drains,hq.closure_drains_iff hb]
  have he : Graph.DrainsAt (q.join p) root ↔ Graph.DrainsAt (p.join q) root := by
    have hj : q.join p=p.join q := by funext i j; exact propext or_comm
    rw [hj]
  rw [he]
  exact ⟨fun h=>h.2,fun h=>⟨hp.no_loop,h⟩⟩



end GraphRealizes






end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace SewnRectangle
variable {n : ℕ}

 
def port : Sum (PaddedColumn.V n) (PaddedColumn.V n) → HoneycombPort
  | .inl (k,j,a) => ((-1-(k:ℤ),j.val),a)
  | .inr (k,j,a) => (((k:ℤ),j.val),Tile.horizontalPort a)

lemma port_injective : Function.Injective (port (n:=n)) := by
  rintro (⟨k,j,a⟩|⟨k,j,a⟩) (⟨l,i,b⟩|⟨l,i,b⟩) h
  all_goals simp only [port,Prod.mk.injEq] at h
  · obtain ⟨⟨hk,hj⟩,rfl⟩:=h
    have hk : k=l := by omega
    have hj : j=i := Fin.ext hj
    subst k j; rfl
  · obtain ⟨⟨hk,_⟩,_⟩:=h; omega
  · obtain ⟨⟨hk,_⟩,_⟩:=h; omega
  · obtain ⟨⟨hk,hj⟩,ha⟩:=h
    have hk : k=l := by omega
    have hj : j=i := Fin.ext hj
    have ha : a=b := Tile.horizontalPort.injective ha
    subst k j a; rfl

lemma mem_range_port (v : HoneycombPort) (hv : v.1.2<n) :
    v∈Set.range (port (n:=n)) := by
  rcases v with ⟨⟨i,j⟩,a⟩
  rcases split_column i with ⟨k,rfl⟩|⟨k,rfl⟩
  · exact ⟨.inl (k,⟨j,hv⟩,a),rfl⟩
  · exact ⟨.inr (k,⟨j,hv⟩,Tile.horizontalPort.symm a),by simp [port]⟩

lemma wiring_left (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (k l' : ℕ) (i j : Fin n) (a b : Fin 4) :
    D.portWiring (port (.inl (k,i,a))) (port (.inl (l',j,b))) ↔
      PaddedColumn.wiring l (k,i,a) (l',j,b) := by
  have h₁ : -1-(k:ℤ)= -1-(l':ℤ) ↔ k=l' := by omega
  have h₂ : -1-(k:ℤ)+1= -1-(l':ℤ) ↔ l'+1=k := by omega
  have h₃ : -1-(l':ℤ)+1= -1-(k:ℤ) ↔ k+1=l' := by omega
  simp only [HoneycombAssignment.portWiring,port,ht,
    tile_left l r k i,tile_left l r l' j,Prod.mk.injEq,h₁,h₂,h₃,
    Fin.val_inj,j.isLt,i.isLt,PaddedColumn.wiring,BareColumn]
  constructor
  · rintro (⟨⟨hki,hij⟩,ht⟩|h|h|⟨hki,hij,_,ha,hb,ho⟩|⟨hki,hij,_,hb,ha,ho⟩)
    · exact Or.inl ⟨hki,Or.inl ⟨hij,ht⟩⟩
    · exact Or.inr (Or.inl ⟨h.1,h.2.2.1,h.2.2.2.1,h.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inr ⟨h.1.symm,h.2.2.2.1,h.2.2.1,h.2.1,h.2.2.2.2⟩)
    · exact Or.inl ⟨hki,Or.inr (Or.inl ⟨ha,hb,hij,ho⟩)⟩
    · have he : l'=k := by omega
      subst l'; exact Or.inl ⟨rfl,Or.inr (Or.inr ⟨hb,ha,hij,ho⟩)⟩
  · rintro (⟨rfl,(h|h|h)⟩|h|h)
    · exact Or.inl ⟨⟨rfl,h.1⟩,h.2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,h.2.2.1,True.intro,h.1,h.2.1,h.2.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,h.2.2.1,True.intro,h.1,h.2.1,h.2.2.2⟩)))
    · exact Or.inr (Or.inl ⟨h.1,h.2.2.2.1,h.2.1,h.2.2.1,h.2.2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1.symm,h.2.2.2.1,h.2.2.1,h.2.1,h.2.2.2.2⟩))

lemma wiring_right (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (hr : ColumnChain.LocallyCompatible r)
    (k l' : ℕ) (i j : Fin n) (a b : Fin 4) :
    D.portWiring (port (.inr (k,i,a))) (port (.inr (l',j,b))) ↔
      PaddedColumn.wiring r (k,i,a) (l',j,b) := by
  have h₁ : (k:ℤ)=(l':ℤ) ↔ k=l' := by omega
  have h₂ : (k:ℤ)+1=(l':ℤ) ↔ k+1=l' := by omega
  have h₃ : (l':ℤ)+1=(k:ℤ) ↔ l'+1=k := by omega
  have h₄ : (l':ℤ)=(k:ℤ) ↔ k=l' := by omega
  have hp₀ : Tile.horizontalPort 0=0 := by decide
  have hp₁ : Tile.horizontalPort 1=2 := by decide
  have hp₂ : Tile.horizontalPort 2=1 := by decide
  have hp₃ : Tile.horizontalPort 3=3 := by decide
  simp only [HoneycombAssignment.portWiring,port,ht,
    tile_right l r k i,tile_right l r l' j,Prod.mk.injEq,h₁,h₂,h₃,h₄,
    Fin.val_inj,j.isLt,i.isLt,PaddedColumn.wiring,BareColumn,
    Tile.horizontal_adj,horizontalPort_eq,hp₀,hp₁,hp₂,hp₃,
    Tile.horizontal_occupied_two,Tile.horizontal_occupied_three]
  constructor
  · rintro (⟨⟨hki,hij⟩,ht⟩|⟨hij,hkl,ha,hb,ho⟩|⟨hij,hkl,hb,ha,ho⟩|
      ⟨hki,hij,_,ha,hb,ho⟩|⟨hki,hij,_,hb,ha,ho⟩)
    · exact Or.inl ⟨hki,Or.inl ⟨hij,ht⟩⟩
    · subst l'; subst j
      exact Or.inr (Or.inr ⟨rfl,ha,hb,rfl,(hr.horizontal k i).mpr ho⟩)
    · subst k; subst j
      exact Or.inr (Or.inl ⟨rfl,ha,hb,rfl,(hr.horizontal l' i).mpr ho⟩)
    · exact Or.inl ⟨hki,Or.inr (Or.inl ⟨ha,hb,hij,ho⟩)⟩
    · subst l'; exact Or.inl ⟨rfl,Or.inr (Or.inr ⟨hb,ha,hij,ho⟩)⟩
  · rintro (⟨rfl,(h|h|h)⟩|⟨hij,ha,hb,hkl,ho⟩|⟨hij,ha,hb,hkl,ho⟩)
    · exact Or.inl ⟨⟨rfl,h.1⟩,h.2⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,h.2.2.1,True.intro,h.1,h.2.1,h.2.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,h.2.2.1,True.intro,h.1,h.2.1,h.2.2.2⟩)))
    · subst k; subst j
      exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl,hb,ha,(hr.horizontal l' i).mp ho⟩))
    · subst l'; subst j
      exact Or.inr (Or.inl ⟨rfl,rfl,ha,hb,(hr.horizontal k i).mp ho⟩)

lemma wiring_cross (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (k l' : ℕ) (i j : Fin n) (a b : Fin 4) :
    D.portWiring (port (.inl (k,i,a))) (port (.inr (l',j,b))) ↔
      ∃ h : Fin n, PaddedColumn.active l h ∧
        (k,i,a)=PaddedColumn.boundary h ∧ (l',j,b)=PaddedColumn.boundary h := by
  have h₁ : ¬ -1-(k:ℤ)=(l':ℤ) := by omega
  have h₂ : -1-(k:ℤ)+1=(l':ℤ) ↔ k=0 ∧ l'=0 := by omega
  have h₃ : ¬ (l':ℤ)+1= -1-(k:ℤ) := by omega
  have h₄ : ¬ (l':ℤ)= -1-(k:ℤ) := by omega
  have hp₁ : Tile.horizontalPort 1=2 := by decide
  simp only [HoneycombAssignment.portWiring,port,ht,
    tile_left l r k i,tile_right l r l' j,Prod.mk.injEq,h₁,h₂,h₃,h₄,
    horizontalPort_eq,hp₁,false_and,and_false,false_or,or_false,Fin.val_inj]
  constructor
  · rintro ⟨rfl,⟨rfl,rfl⟩,rfl,rfl,ho⟩
    exact ⟨i,ho,rfl,rfl⟩
  · rintro ⟨h,ho,he,hf⟩
    simp only [PaddedColumn.boundary,Prod.mk.injEq] at he hf
    rcases he with ⟨rfl,rfl,rfl⟩
    rcases hf with ⟨rfl,rfl,rfl⟩
    exact ⟨rfl,⟨rfl,rfl⟩,rfl,rfl,ho⟩

 

theorem sewn_wiring (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (hr : ColumnChain.LocallyCompatible r)
    (v w : Sum (PaddedColumn.V n) (PaddedColumn.V n)) :
    D.portWiring (port v) (port w) ↔
      Patch.glued (PaddedColumn.wiring l) (PaddedColumn.wiring r)
        PaddedColumn.boundary PaddedColumn.boundary (PaddedColumn.active l) v w := by
  cases v with
  | inl v =>
    rcases v with ⟨k,i,a⟩
    cases w with
    | inl w =>
      rcases w with ⟨l',j,b⟩
      exact wiring_left D l r ht k l' i j a b
    | inr w =>
      rcases w with ⟨l',j,b⟩
      exact wiring_cross D l r ht k l' i j a b
  | inr v =>
    rcases v with ⟨k,i,a⟩
    cases w with
    | inl w =>
      rcases w with ⟨l',j,b⟩
      have hs : D.portWiring (port (.inr (k,i,a))) (port (.inl (l',j,b))) ↔
          D.portWiring (port (.inl (l',j,b))) (port (.inr (k,i,a))) :=
        ⟨D.portWiring_symm,D.portWiring_symm⟩
      rw [hs,wiring_cross D l r ht l' k j i b a]
      simp only [Patch.glued,and_comm]
    | inr w =>
      rcases w with ⟨l',j,b⟩
      exact wiring_right D l r ht hr k l' i j a b

lemma sewn_drains_iff (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) (hr : ColumnChain.LocallyCompatible r)
    (root : Sum (PaddedColumn.V n) (PaddedColumn.V n)) :
    Graph.DrainsAt (Patch.glued (PaddedColumn.wiring l) (PaddedColumn.wiring r)
      PaddedColumn.boundary PaddedColumn.boundary (PaddedColumn.active l)) root ↔
      Graph.DrainsAt D.portWiring (port root) := by
  apply Graph.drainsAt_embedding_iff port port_injective (sewn_wiring D l r ht hr)
  intro v w hvw
  exact ⟨mem_range_port v (D.port_in_strip ((D.port_used v).mp ⟨w,hvw⟩)),
    mem_range_port w (D.port_in_strip ((D.port_used w).mp ⟨v,D.portWiring_symm hvw⟩))⟩

 

theorem gluesAt_physical_iff (l r : List (Configuration n)) (p q : Pairing n)
    (hl : ColumnChain.Runs (empty n) l p) (hr : ColumnChain.Runs (empty n) r q)
    (D : HoneycombAssignment n) (ht : D.tile=tile l r) (root : Fin n) :
    p.GluesAt root q ↔ p.Occupied root ∧
      (∀i, p.Occupied i ↔ q.Occupied i) ∧
      Graph.DrainsAt D.portWiring ((0,root.val),1) := by
  have hl' := ColumnChain.runs_sound _ _ _ hl
  have hr' := ColumnChain.runs_sound _ _ _ hr
  have ha : PaddedColumn.active l=p.Occupied := by
    funext i
    exact propext ((ColumnChain.support_empty_read l i).symm.trans
      (by rw [hl'.2.2]))
  have hd := sewn_drains_iff D l r ht (ColumnChain.compatible_empty_iff r |>.mp hr'.1)
    (.inr (PaddedColumn.boundary root))
  have hp := PaddedColumn.runs_realizes l p hl
  have hq := PaddedColumn.runs_realizes r q hr
  have hg := hp.sewn_drains_iff hq PaddedColumn.boundary_injective root
  rw [ha] at hd
  have he : port (.inr (PaddedColumn.boundary root))=((0,root.val),1) := rfl
  rw [he] at hd
  rw [Pairing.GluesAt,hd.symm,hg]

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



lemma up_two (D : HoneycombAssignment N) (i : ℤ) (j : ℕ)
    (hbot : j=0 → ¬(D.tile (i,j)).Occupied 0)
    (hu : Graph.Used D.graph.Adj (up i j)) :
    ∃ x y,D.graph.Adj (up i j) x ∧ D.graph.Adj (up i j) y ∧ x≠y := by
  obtain ⟨w,hw⟩:=hu
  obtain ⟨hn,hw⟩:=(D.up_neighbors i j w).mp hw
  have hp : (D.tile (i,j)).Occupied 0 → 0<j := by
    intro h; by_contra hj; exact hbot (by omega) h
  rcases Tile.physical_up (D.tile (i,j)) (D.physical (i,j)) with h|h|h|h
  · rcases hw with ⟨_,hm⟩|⟨_,he⟩|⟨_,_,hs⟩
    · exact (h.2.2 hm).elim
    · exact (h.2.1 he).elim
    · exact (h.1 hs).elim
  · refine ⟨down i (j-1),down (i-1) j,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inr (Or.inr ⟨hp h.1,rfl,h.1⟩)⟩,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inr (Or.inl ⟨rfl,h.2.1⟩)⟩,?_⟩
    simp only [down,Prod.mk.injEq,ne_eq]; omega
  · refine ⟨down i (j-1),down i j,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inr (Or.inr ⟨hp h.1,rfl,h.1⟩)⟩,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inl ⟨rfl,h.2.2⟩⟩,?_⟩
    have hj := hp h.1
    simp only [down,Prod.mk.injEq,true_and,ne_eq]; omega
  · refine ⟨down (i-1) j,down i j,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inr (Or.inl ⟨rfl,h.2.1⟩)⟩,
      (D.up_neighbors i j _).mpr ⟨hn,Or.inl ⟨rfl,h.2.2⟩⟩,?_⟩
    simp only [down,Prod.mk.injEq,ne_eq]; omega

lemma down_two (D : HoneycombAssignment N) (i : ℤ) (j : ℕ)
    (htop : j+1=N → ¬(D.tile (i,j)).Occupied 3)
    (hu : Graph.Used D.graph.Adj (down i j)) :
    ∃ x y,D.graph.Adj (down i j) x ∧ D.graph.Adj (down i j) y ∧ x≠y := by
  obtain ⟨w,hw⟩:=hu
  obtain ⟨hn,hw⟩:=(D.down_neighbors i j w).mp hw
  have hp : (D.tile (i,j)).Occupied 3 → j+1<N := by
    intro h; by_contra hj; exact htop (by omega) h
  rcases Tile.physical_down (D.tile (i,j)) (D.physical (i,j)) with h|h|h|h
  · rcases hw with ⟨_,hm⟩|⟨_,he⟩|⟨_,_,hs⟩
    · exact (h.2.2 hm).elim
    · exact (h.1 he).elim
    · exact (h.2.1 hs).elim
  · refine ⟨up (i+1) j,up i (j+1),
      (D.down_neighbors i j _).mpr ⟨hn,Or.inr (Or.inl ⟨rfl,h.1⟩)⟩,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inr (Or.inr ⟨hp h.2.1,rfl,h.2.1⟩)⟩,?_⟩
    simp [up]
  · refine ⟨up (i+1) j,up i j,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inr (Or.inl ⟨rfl,h.1⟩)⟩,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inl ⟨rfl,h.2.2⟩⟩,?_⟩
    simp [up]
  · refine ⟨up i (j+1),up i j,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inr (Or.inr ⟨hp h.2.1,rfl,h.2.1⟩)⟩,
      (D.down_neighbors i j _).mpr ⟨hn,Or.inl ⟨rfl,h.2.2⟩⟩,?_⟩
    simp [up]

lemma two_interior_top (D : HoneycombAssignment N) (hN : 1≤N) (a b : ℤ)
    (hs : ∀i,¬(D.tile (i,0)).Occupied 0)
    (ht : ∀i,(D.tile (i,N-1)).Occupied 3 → i=a ∨ i=b)
    (v : Triangle) (ha : v≠down a (N-1)) (hb : v≠down b (N-1))
    (hu : Graph.Used D.graph.Adj v) :
    ∃x y,D.graph.Adj v x ∧ D.graph.Adj v y ∧ x≠y := by
  rcases v with ⟨i,j,c⟩
  cases c
  · apply D.down_two i j _ hu
    intro hj ho
    have hj' : j=N-1 := by omega
    subst j
    exact (ht i ho).elim (fun h=>ha (by subst i; rfl)) (fun h=>hb (by subst i; rfl))
  · exact D.up_two i j (fun hj=>by subst j; exact hs i) hu

 

theorem restrict_drains_of_two_top (D : HoneycombAssignment (N+1)) (hN : 1≤N)
    (a b : ℤ) (root : Triangle) (hr : root.2.1=N)
    (hd : Graph.DrainsAt D.graph.Adj root)
    (hf : (D.restrict N (by omega)).graph.support.Finite)
    (hs : ∀i,¬(D.tile (i,0)).Occupied 0)
    (ht : ∀i,(D.tile (i,N)).Occupied 0 ↔ i=a ∨ i=b) :
    Graph.DrainsAt (D.restrict N (by omega)).graph.Adj (down b (N-1)) := by
  let E := D.restrict N (by omega)
  have ht' (i : ℤ) : (E.tile (i,N-1)).Occupied 3 ↔ i=a ∨ i=b := by
    rw [show E.tile (i,N-1)=D.tile (i,N-1) from D.restrict_tile N (by omega) i (N-1) (by omega)]
    have he := D.vertical i (N-1) (by omega)
    rw [show N-1+1=N by omega] at he
    exact he.trans (ht i)
  have hs' (i : ℤ) : ¬(E.tile (i,0)).Occupied 0 := by
    simpa only [show E.tile (i,0)=D.tile (i,0) from D.restrict_tile N (by omega) i 0 (by omega)] using hs i
  apply PathGraph.drains_of_two_terminals E.graph hf E.two (E.top_one hN ((ht' b).mpr (Or.inr rfl)))
    (E.top_used hN ((ht' b).mpr (Or.inr rfl)))
    (E.two_interior_top hN b a hs' (fun i h=>(ht' i |>.mp h).symm))
  intro v w hvw
  have hm := (D.restrict_adj N (by omega) v w).mp hvw
  have hvr := hd v w hm.2.2
  obtain ⟨x,y,hx,hy,hxy,hvx⟩:=Graph.reach_exit (S:={v : Triangle | v.2.1<N}) hvr hm.1 (by simp [hr])
  have hvx' : Relation.ReflTransGen E.graph.Adj v x :=
    Relation.ReflTransGen.mono (fun s t h=>(D.restrict_adj N (by omega) s t).mpr h) _ _ hvx
  rcases x with ⟨i,j,c⟩
  cases c
  · obtain ⟨hj,hxy⟩:=(D.down_neighbors i j y).mp hxy
    rcases hxy with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨_,rfl,ho⟩
    · exact (hy hx).elim
    · exact (hy hx).elim
    · have hj' : j+1=N := by change ¬j+1<N at hy; have hx' : j<N := hx; omega
      have ho' : (D.tile (i,N)).Occupied 0 := by
        have he := D.vertical i j (by omega)
        simpa only [hj'] using he.mp ho
      have hj'' : j=N-1 := by omega
      rcases (ht i).mp ho' with rfl | rfl
      · exact Or.inr (hj'' ▸ hvx')
      · exact Or.inl (hj'' ▸ hvx')
  · obtain ⟨hj,hxy⟩:=(D.up_neighbors i j y).mp hxy
    rcases hxy with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨_,rfl,_⟩
    · exact (hy hx).elim
    · exact (hy hx).elim
    · have hh : (down i (j-1)).2.1<N := by change j-1<N; have hx' : j<N := hx; omega
      exact (hy hh).elim

end HoneycombAssignment
end

 

 

noncomputable section
open scoped Classical
open Diagram

namespace SewnRectangle
variable {n : ℕ}

lemma tile_nonvacant_bounds (l r : List (Configuration n)) (q : Cell)
    (h : tile l r q≠.vacant) :
    -(l.length:ℤ)≤q.1 ∧ q.1<(r.length:ℤ) ∧ q.2<n := by
  rcases q with ⟨i,j⟩
  have hj : j<n := by
    by_contra hn
    exact h (tile_outside l r i j (by omega))
  refine ⟨?_,?_,hj⟩
  · by_contra hi
    have hn : i<0 := by omega
    have hk : l.length≤(-i-1).toNat := by omega
    simp only [tile,hj,dite_eq_left,hn,ite_true,ColumnChain.read_ge l _ hk] at h
    exact h rfl
  · by_contra hi
    have hn : ¬i<0 := by omega
    have hk : r.length ≤ i.toNat := by omega
    simp only [tile,hj,dite_eq_left,hn,ite_false,ColumnChain.read_ge r _ hk] at h
    exact h rfl

lemma finite_support (D : HoneycombAssignment n) (l r : List (Configuration n))
    (ht : D.tile=tile l r) : D.graph.support.Finite := by
  let F : Set Triangle := Set.Ico (-(l.length:ℤ)) (r.length:ℤ) ×ˢ
    (Set.Iio n ×ˢ (Set.univ : Set Bool))
  have hF : F.Finite := (Set.finite_Ico _ _).prod ((Set.finite_Iio n).prod (Set.toFinite _))
  apply hF.subset
  rintro ⟨i,j,b⟩ hv
  have hv' : D.tile (i,j)≠.vacant := by
    apply (Tile.nonvacant_iff_used _).mpr
    cases b
    · exact Or.inr ((D.down_support_iff i j).mp hv)
    · exact Or.inl ((D.up_support_iff i j).mp hv)
  rw [ht] at hv'
  obtain ⟨hi,hj,hk⟩:=tile_nonvacant_bounds l r (i,j) hv'
  exact ⟨⟨hi,hj⟩,hk,Set.mem_univ _⟩

lemma restrict_finite_support (D : HoneycombAssignment (n+1))
    (l r : List (Configuration (n+1))) (ht : D.tile=tile l r) :
    (D.restrict n (by omega)).graph.support.Finite := by
  apply (finite_support D l r ht).subset
  rintro v ⟨w,hw⟩
  exact ⟨w,((D.restrict_adj n (by omega) v w).mp hw).2.2⟩

end SewnRectangle
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

namespace NorthExtension


lemma north (a b i : ℤ) : ¬(tile a b i).Occupied 3 := by
  unfold tile
  split_ifs <;> decide

lemma middle (a b i : ℤ) (h : a<b) :
    (tile a b i).middle ↔ a≤ i ∧ i<b := by
  unfold tile
  split_ifs with ha hb hi
  · subst i
    simp only [h,le_refl,and_self]; decide
  · subst i
    have hh : ¬b<b := by omega
    simp only [hh,and_false]; decide
  · have ha' : a≤ i := le_of_lt hi.1
    simp only [ha',hi.2,and_self]; decide
  · have hi' : ¬(a≤ i ∧ i<b) := by omega
    simp only [hi']; decide

lemma nonvacant (a b i : ℤ) (h : a<b) : tile a b i≠.vacant ↔ a≤ i ∧ i≤b := by
  unfold tile
  split_ifs <;> simp_all <;> omega

end NorthExtension

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}



lemma extend_base_edge (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {v w : Triangle} (h : D.toHoneycombAssignment.graph.Adj v w) :
    (D.extend hN hab).graph.Adj v w := by
  have hh:=tileGraph_allowed N D.tile h
  have he:= (D.extend hN hab).restrict_adj N (by omega) v w
  rw [D.extend_restrict hN hab] at he
  exact (he.mp h).2.2

lemma extend_up_edge (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {i : ℤ} (ha : a≤ i) (hb : i<b) :
    (D.extend hN hab).graph.Adj (up i N) (down i N) := by
  apply (HoneycombAssignment.up_neighbors _ _ _ _).mpr
  refine ⟨by omega,Or.inl ⟨rfl,?_⟩⟩
  rw [D.extend_last hN hab,NorthExtension.middle _ _ _ hab]
  exact ⟨ha,hb⟩

lemma extend_next_edge (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {i : ℤ} (ha : a≤ i) (hb : i<b) :
    (D.extend hN hab).graph.Adj (down i N) (up (i+1) N) := by
  apply (HoneycombAssignment.down_neighbors _ _ _ _).mpr
  refine ⟨by omega,Or.inr (Or.inl ⟨rfl,?_⟩)⟩
  rw [D.extend_last hN hab,NorthExtension.east _ _ _ hab]
  exact ⟨ha,hb⟩

lemma extend_up_reach (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {i : ℤ} (ha : a≤ i) (hb : i≤b) :
    Relation.ReflTransGen (D.extend hN hab).graph.Adj (up i N) (up b N) := by
  generalize he : (b-i).toNat=k
  induction k using Nat.strong_induction_on generalizing i with
  | h k ih =>
    by_cases hi : i=b
    · subst i; exact .refl
    · have hlt : i<b := by omega
      have he' : (b-(i+1)).toNat<k := by omega
      exact (Relation.ReflTransGen.single (D.extend_up_edge hN hab ha hlt)).trans
        ((Relation.ReflTransGen.single (D.extend_next_edge hN hab ha hlt)).trans
          (ih _ he' (by omega) (by omega) rfl))

lemma extend_enter (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) :
    (D.extend hN hab).graph.Adj (down b (N-1)) (up b N) := by
  apply (HoneycombAssignment.down_neighbors _ _ _ _).mpr
  refine ⟨by omega,Or.inr (Or.inr ⟨by omega,?_,?_⟩)⟩
  · congr 1; omega
  · rw [D.extend_base hN hab b (N-1) (by omega)]
    exact (D.top b).mpr (Or.inr rfl)

lemma extend_drains_right (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) :
    Graph.DrainsAt (D.extend hN hab).graph.Adj (up b N) := by
  intro v w hvw
  have hv:=(tileGraph_allowed (N+1) (D.extend hN hab).tile hvw).2.1
  by_cases hvN : v.2.1<N
  · have hu : Graph.Used D.toHoneycombAssignment.graph.Adj v := by
      rcases v with ⟨i,j,c⟩
      cases c
      · apply (D.toHoneycombAssignment.down_support_iff i j).mpr
        rw [←D.extend_base hN hab i j hvN]
        exact (HoneycombAssignment.down_support_iff _ i j).mp ⟨w,hvw⟩
      · apply (D.toHoneycombAssignment.up_support_iff i j).mpr
        rw [←D.extend_base hN hab i j hvN]
        exact (HoneycombAssignment.up_support_iff _ i j).mp ⟨w,hvw⟩
    obtain ⟨x,hx⟩:=hu
    exact (Relation.ReflTransGen.mono (fun _ _=>D.extend_base_edge hN hab) _ _
      (D.drains _ _ hx)).tail (D.extend_enter hN hab)
  · have hvN' : v.2.1=N := by omega
    rcases v with ⟨i,j,c⟩
    dsimp at hvN'; subst j
    cases c
    · obtain ⟨_,hh⟩:=(HoneycombAssignment.down_neighbors _ _ _ _).mp hvw
      rw [D.extend_last hN hab,NorthExtension.middle _ _ _ hab,
        NorthExtension.east _ _ _ hab] at hh
      have hi : a≤ i ∧ i<b := by
        rcases hh with ⟨_,h⟩|⟨_,h⟩|⟨h,_,_⟩
        · exact h
        · exact h
        · omega
      exact (Relation.ReflTransGen.single (D.extend_next_edge hN hab hi.1 hi.2)).trans
        (D.extend_up_reach hN hab (by omega) (by omega))
    · obtain ⟨_,hh⟩:=(HoneycombAssignment.up_neighbors _ _ _ _).mp hvw
      rw [D.extend_last hN hab,NorthExtension.middle _ _ _ hab,
        NorthExtension.west _ _ _ hab,NorthExtension.south _ _ _ hab] at hh
      have hi : a≤ i ∧ i≤b := by
        rcases hh with ⟨_,h⟩|⟨_,h⟩|⟨_,_,h|h⟩ <;> omega
      exact D.extend_up_reach hN hab hi.1 hi.2

lemma extend_drains (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a≤0) (hb : 0≤b) :
    Graph.DrainsAt (D.extend hN hab).graph.Adj (up 0 N) := by
  apply (D.extend_drains_right hN hab).mono_root
  have := (D.extend hN hab).graph.symm
  exact symm (D.extend_up_reach hN hab ha hb)

end TopArchConfiguration
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombClip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram


namespace HoneycombAssignment
variable {N : ℕ}

def weight (D : HoneycombAssignment N) : ℝ :=
  ∏ᶠ q : Cell,(physicalWeights (2*Diagram.lambda)).tile (D.tile q)

lemma sewn_clips (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m) :
    D.tile=SewnRectangle.tile (List.ofFn (D.leftClip m)) (List.ofFn (D.rightClip m)) := by
  funext ⟨i,j⟩
  by_cases hj : j<N
  · rcases SewnRectangle.split_column i with ⟨k,rfl⟩|⟨k,rfl⟩
    · rw [SewnRectangle.tile_left _ _ k ⟨j,hj⟩,D.read_leftClip m h k ⟨j,hj⟩]
    · rw [SewnRectangle.tile_right _ _ k ⟨j,hj⟩,D.read_rightClip m h k ⟨j,hj⟩,
        Tile.horizontal_involutive]
  · rw [D.outside i j (by omega),SewnRectangle.tile_outside _ _ i j (by omega)]

lemma clips_compatible (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m)
    (hs : ∀i,¬(D.tile (i,0)).Occupied 0)
    (hn : ∀i,¬(D.tile (i,N-1)).Occupied 3) :
    ColumnChain.LocallyCompatible (List.ofFn (D.leftClip m)) ∧
      ColumnChain.LocallyCompatible (List.ofFn (D.rightClip m)) := by
  constructor
  · constructor
    · intro k j
      rw [D.read_leftClip m h (k+1) j,D.read_leftClip m h k j]
      have hh:=D.horizontal (-1-((k+1:ℕ):ℤ)) j.val
      simpa only [show -1-((k+1:ℕ):ℤ)+1= -1-(k:ℤ) by omega] using hh
    · intro k j hj
      rw [D.read_leftClip m h k j,hj]
      exact hs _
    · intro k j hj
      rw [D.read_leftClip m h k j,show j.val=N-1 by omega]
      exact hn _
    · intro k i j hij
      rw [D.read_leftClip m h k i,D.read_leftClip m h k j,←hij]
      exact D.vertical _ i.val (by omega)
  · constructor
    · intro k j
      rw [D.read_rightClip m h (k+1) j,D.read_rightClip m h k j,
        Tile.horizontal_occupied_two,Tile.horizontal_occupied_one]
      have hh:=D.horizontal (k:ℤ) j.val
      simpa only [Nat.cast_add,Nat.cast_one] using hh.symm
    · intro k j hj
      rw [D.read_rightClip m h k j,Tile.horizontal_occupied_zero,hj]
      exact hs _
    · intro k j hj
      rw [D.read_rightClip m h k j,Tile.horizontal_occupied_three,show j.val=N-1 by omega]
      exact hn _
    · intro k i j hij
      rw [D.read_rightClip m h k i,D.read_rightClip m h k j,
        Tile.horizontal_occupied_three,Tile.horizontal_occupied_zero,←hij]
      exact D.vertical _ i.val (by omega)

end HoneycombAssignment

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

lemma extend_fits (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    {m : ℕ} (hf : D.toHoneycombAssignment.Fits m) : (D.extend hN hab).Fits m := by
  intro ⟨i,j⟩ hq
  by_cases hj : j=N
  · subst j
    rw [D.extend_last hN hab,NorthExtension.nonvacant _ _ _ hab] at hq
    have ha : D.tile (a,N-1)≠.vacant := by
      intro he
      have hh:=(D.top a).mpr (Or.inl rfl)
      exact Tile.vacant_not_occupied 3 (he ▸ hh)
    have hb : D.tile (b,N-1)≠.vacant := by
      intro he
      have hh:=(D.top b).mpr (Or.inr rfl)
      exact Tile.vacant_not_occupied 3 (he ▸ hh)
    have ha':=(hf _ ha).1
    have hb':=(hf _ hb).2
    constructor <;> dsimp <;> omega
  · have he : (D.extend hN hab).tile (i,j)=D.tile (i,j) := ite_eq_right hj
    exact hf _ (he ▸ hq)

end TopArchConfiguration
end

 

 

noncomputable section
open scoped Classical
open Diagram

namespace HoneycombAssignment
variable {N : ℕ}

lemma clip_occupancies (D : HoneycombAssignment N) (m : ℕ) (hf : D.Fits m)
    (p q : Pairing N)
    (hl : ColumnChain.Runs (empty N) (List.ofFn (D.leftClip m)) p)
    (hr : ColumnChain.Runs (empty N) (List.ofFn (D.rightClip m)) q) :
    (∀i,p.Occupied i ↔ (D.tile (-1,i.val)).Occupied 2) ∧
      (∀i,q.Occupied i ↔ (D.tile (0,i.val)).Occupied 1) := by
  have hp:=(ColumnChain.runs_sound _ _ _ hl).2.2
  have hq:=(ColumnChain.runs_sound _ _ _ hr).2.2
  constructor
  · intro i
    rw [←hp,ColumnChain.support_empty_read,D.read_leftClip m hf]
    norm_num
  · intro i
    rw [←hq,ColumnChain.support_empty_read,D.read_rightClip m hf,Tile.horizontal_occupied_two]
    norm_num

 

lemma clips_runs_glues (D : HoneycombAssignment N) (hN : 0<N) (m : ℕ) (hf : D.Fits m)
    (hs : ∀i,¬(D.tile (i,0)).Occupied 0)
    (hn : ∀i,¬(D.tile (i,N-1)).Occupied 3)
    (root : Fin N) (ho : (D.tile (0,root.val)).Occupied 1)
    (hd : Graph.DrainsAt D.graph.Adj (up 0 root.val)) :
    ∃p q, ColumnChain.Runs (empty N) (List.ofFn (D.leftClip m)) p ∧
      ColumnChain.Runs (empty N) (List.ofFn (D.rightClip m)) q ∧ p.GluesAt root q := by
  let l:=List.ofFn (D.leftClip m)
  let r:=List.ofFn (D.rightClip m)
  have ht:=D.sewn_clips m hf
  obtain ⟨hcl,hcr⟩:=D.clips_compatible m hf hs hn
  have hu : Graph.Used D.portWiring ((0,root.val),1) := (D.port_used _).mpr ho
  have hd':= (D.port_drains_iff hu).mpr hd
  have hdg := (SewnRectangle.sewn_drains_iff D l r ht hcr
    (.inr (PaddedColumn.boundary root))).mpr hd'
  obtain ⟨hdl,hdr⟩:=Graph.glued_drainsAt_halves (PaddedColumn.wiring l) (PaddedColumn.wiring r)
    PaddedColumn.boundary PaddedColumn.boundary (PaddedColumn.active l) root hdg
  obtain ⟨p,hp⟩:=PaddedColumn.runs_exists hN l ((ColumnChain.compatible_empty_iff _).mpr hcl) hdl
  obtain ⟨q,hq⟩:=PaddedColumn.runs_exists hN r ((ColumnChain.compatible_empty_iff _).mpr hcr) hdr
  have hx:=D.clip_occupancies m hf p q hp hq
  refine ⟨p,q,hp,hq,(SewnRectangle.gluesAt_physical_iff l r p q hp hq D ht root).mpr ⟨?_,?_,hd'⟩⟩
  · exact (hx.1 root).mpr ((D.horizontal (-1) root.val).mpr (by simpa using ho))
  · intro i
    exact (hx.1 i).trans ((D.horizontal (-1) i.val).trans (by simpa using (hx.2 i).symm))

end HoneycombAssignment

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

 

lemma extend_clips_runs (D : TopArchConfiguration N a b) (hN : 1≤N) (ha : a<0) (hb : 0≤b)
    (m : ℕ) (hf : D.toHoneycombAssignment.Fits m) :
    let E:=D.extend hN (by omega)
    ∃p q, ColumnChain.Runs (empty (N+1)) (List.ofFn (E.leftClip m)) p ∧
      ColumnChain.Runs (empty (N+1)) (List.ofFn (E.rightClip m)) q ∧
      p.GluesAt (Fin.last N) q := by
  dsimp only
  apply HoneycombAssignment.clips_runs_glues _ (by omega) m (D.extend_fits hN (by omega) hf)
  · intro i
    rw [D.extend_base hN (by omega) i 0 (by omega)]
    exact D.bottom i
  · intro i
    rw [show N+1-1=N by omega,D.extend_last hN (by omega)]
    exact NorthExtension.north _ _ _
  · rw [Fin.val_last,D.extend_last hN (by omega),NorthExtension.west _ _ _ (by omega)]
    exact ⟨ha,hb⟩
  · exact D.extend_drains hN (by omega) (le_of_lt ha) hb

end TopArchConfiguration
end

 

 

noncomputable section
open scoped Classical BigOperators
open Diagram

namespace SewnRectangle
variable {N : ℕ}

lemma north_row_tile (l r : List (Configuration (N+1))) (kl ll kr lr : ℕ)
    (hl : l.map (fun t=>t (Fin.last N))=
      List.replicate kl Tile.diagonal₁ ++ Tile.vertical₀::List.replicate ll Tile.vacant)
    (hr : r.map (fun t=>t (Fin.last N))=
      List.replicate kr Tile.diagonal₁ ++ Tile.vertical₀::List.replicate lr Tile.vacant)
    (i : ℤ) : tile l r (i,N)=NorthExtension.tile (-1-(kl:ℤ)) kr i := by
  rcases split_column i with ⟨k,rfl⟩|⟨k,rfl⟩
  · rw [show tile l r (-1-(k:ℤ),N)=ColumnChain.read l k (Fin.last N) from tile_left l r k (Fin.last N),ColumnChain.north_shape_read l kl ll hl k]
    unfold NorthExtension.tile
    split_ifs <;> first | rfl | omega
  · rw [show tile l r ((k:ℤ),N)=(ColumnChain.read r k (Fin.last N)).horizontal from tile_right l r k (Fin.last N),ColumnChain.north_shape_read r kr lr hr k]
    unfold NorthExtension.tile
    split_ifs <;> first | rfl | omega

lemma runs_cut {l r : List (Configuration (N+1))} {p q : Pairing (N+1)}
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q) :
    ∀i,(ColumnChain.read l 0 i).Occupied 2 ↔ (ColumnChain.read r 0 i).Occupied 2 := by
  intro i
  rw [←ColumnChain.support_empty_read,←ColumnChain.support_empty_read,
    (ColumnChain.runs_sound _ _ _ hl).2.2,(ColumnChain.runs_sound _ _ _ hr).2.2]
  exact hg.2.1 i

 

def northAssignment (l r : List (Configuration (N+1))) (p q : Pairing (N+1))
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q)
    (hwl : ColumnChain.weight (leftWeights N) l≠0)
    (hwr : ColumnChain.weight (rightWeights N) r≠0) : HoneycombAssignment (N+1) :=
  assignment l r ((ColumnChain.compatible_empty_iff l).mp (ColumnChain.runs_sound _ _ _ hl).1)
    ((ColumnChain.compatible_empty_iff r).mp (ColumnChain.runs_sound _ _ _ hr).1)
    (runs_cut hl hr hg) (physical_from_weights l r hwl hwr).1 (physical_from_weights l r hwl hwr).2

lemma northAssignment_drains (l r : List (Configuration (N+1))) (p q : Pairing (N+1))
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q)
    (hwl : ColumnChain.weight (leftWeights N) l≠0)
    (hwr : ColumnChain.weight (rightWeights N) r≠0) :
    Graph.DrainsAt (northAssignment l r p q hl hr hg hwl hwr).graph.Adj (up 0 N) := by
  let D:=northAssignment l r p q hl hr hg hwl hwr
  have hh:=(gluesAt_physical_iff l r p q hl hr D rfl (Fin.last N)).mp hg
  have ho : (D.tile (0,N)).Occupied 1 := by
    change (tile l r ((0:ℕ), (Fin.last N).val)).Occupied 1
    rw [tile_right,Tile.horizontal_occupied_one,←ColumnChain.support_empty_read,
      (ColumnChain.runs_sound _ _ _ hr).2.2]
    exact (hg.2.1 _).mp hg.1
  exact (D.port_drains_iff ((D.port_used _).mpr ho)).mp hh.2.2

 
def northArch (l r : List (Configuration (N+1))) (p q : Pairing (N+1)) (hN : 1≤N)
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q)
    (hwl : ColumnChain.weight (leftWeights N) l≠0)
    (hwr : ColumnChain.weight (rightWeights N) r≠0)
    (kl ll kr lr : ℕ)
    (hsl : l.map (fun t=>t (Fin.last N))=
      List.replicate kl Tile.diagonal₁ ++ Tile.vertical₀::List.replicate ll Tile.vacant)
    (hsr : r.map (fun t=>t (Fin.last N))=
      List.replicate kr Tile.diagonal₁ ++ Tile.vertical₀::List.replicate lr Tile.vacant) :
    TopArchConfiguration N (-1-(kl:ℤ)) kr where
  toHoneycombAssignment := (northAssignment l r p q hl hr hg hwl hwr).restrict N (by omega)
  bottom i := by
    rw [HoneycombAssignment.restrict_tile _ _ _ i 0 (by omega)]
    exact south_vacant l r ((ColumnChain.compatible_empty_iff l).mp (ColumnChain.runs_sound _ _ _ hl).1)
      ((ColumnChain.compatible_empty_iff r).mp (ColumnChain.runs_sound _ _ _ hr).1) i
  top i := by
    rw [HoneycombAssignment.restrict_tile _ _ _ i (N-1) (by omega)]
    have hh:=(northAssignment l r p q hl hr hg hwl hwr).vertical i (N-1) (by omega)
    rw [show N-1+1=N by omega] at hh
    exact hh.trans (north_south_occupied l r kl ll kr lr hsl hsr i)
  drains := by
    apply HoneycombAssignment.restrict_drains_of_two_top _ hN _ _ (up 0 N) rfl
      (northAssignment_drains l r p q hl hr hg hwl hwr)
      (restrict_finite_support _ l r rfl)
    · exact south_vacant l r ((ColumnChain.compatible_empty_iff l).mp (ColumnChain.runs_sound _ _ _ hl).1)
        ((ColumnChain.compatible_empty_iff r).mp (ColumnChain.runs_sound _ _ _ hr).1)
    · exact north_south_occupied l r kl ll kr lr hsl hsr

lemma northArch_extend (l r : List (Configuration (N+1))) (p q : Pairing (N+1)) (hN : 1≤N)
    (hl : ColumnChain.Runs (empty (N+1)) l p)
    (hr : ColumnChain.Runs (empty (N+1)) r q)
    (hg : p.GluesAt (Fin.last N) q)
    (hwl : ColumnChain.weight (leftWeights N) l≠0)
    (hwr : ColumnChain.weight (rightWeights N) r≠0)
    (kl ll kr lr : ℕ)
    (hsl : l.map (fun t=>t (Fin.last N))=
      List.replicate kl Tile.diagonal₁ ++ Tile.vertical₀::List.replicate ll Tile.vacant)
    (hsr : r.map (fun t=>t (Fin.last N))=
      List.replicate kr Tile.diagonal₁ ++ Tile.vertical₀::List.replicate lr Tile.vacant) :
    (northArch l r p q hN hl hr hg hwl hwr kl ll kr lr hsl hsr).extend hN (by omega)=
      northAssignment l r p q hl hr hg hwl hwr := by
  apply HoneycombAssignment.ext
  funext ⟨i,j⟩
  by_cases hj : j=N
  · subst j
    rw [TopArchConfiguration.extend_last]
    exact (north_row_tile l r kl ll kr lr hsl hsr i).symm
  · by_cases hn : j<N
    · rw [TopArchConfiguration.extend_base _ _ _ _ _ hn]
      exact HoneycombAssignment.restrict_tile _ _ (by omega) _ _ hn
    · rw [HoneycombAssignment.outside _ i j (by omega),HoneycombAssignment.outside _ i j (by omega)]

end SewnRectangle






end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthBijection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

namespace Diagram.ColumnChain
lemma read_ofFn {n m : ℕ} (h : Fin m → Configuration n) (k : Fin m) (j : Fin n) :
    read (List.ofFn h) k.val j=h k j := by
  simp only [read,List.getElem?_ofFn,k.isLt,dite_eq_left,Option.getD_some]
end Diagram.ColumnChain

namespace SewnRectangle
variable {n m : ℕ}

lemma clips_left (l r : Fin m → Configuration n) (D : HoneycombAssignment n)
    (ht : D.tile=tile (List.ofFn l) (List.ofFn r)) : D.leftClip m=l := by
  funext k j
  change D.tile (-1-(k.val:ℤ),j.val)=l k j
  rw [ht,tile_left,ColumnChain.read_ofFn]

lemma clips_right (l r : Fin m → Configuration n) (D : HoneycombAssignment n)
    (ht : D.tile=tile (List.ofFn l) (List.ofFn r)) : D.rightClip m=r := by
  funext k j
  change (D.tile ((k.val:ℤ),j.val)).horizontal=r k j
  rw [ht,tile_right,ColumnChain.read_ofFn,Tile.horizontal_involutive]

lemma fits_ofFn (l r : Fin m → Configuration n) (D : HoneycombAssignment n)
    (ht : D.tile=tile (List.ofFn l) (List.ofFn r)) : D.Fits m := by
  intro q hq
  rw [ht] at hq
  have hh:=tile_nonvacant_bounds _ _ q hq
  simp only [List.length_ofFn] at hh
  exact ⟨hh.1,hh.2.1⟩
end SewnRectangle



namespace CrossTopArch
variable {N : ℕ}

def weight (D : CrossTopArch N) : ℝ := D.arch.toHoneycombAssignment.weight

end CrossTopArch



namespace NorthHistory
variable {N m : ℕ}

instance instFintype : Fintype (NorthHistory N m) := Fintype.ofInjective
  (fun D=>(D.left,D.right)) (fun _ _ h=>ext (congrArg Prod.fst h) (congrArg Prod.snd h))

def leftState (h : NorthHistory N m) : Pairing (N+1) := Classical.choose h.realizes

def rightState (h : NorthHistory N m) : Pairing (N+1) :=
  Classical.choose (Classical.choose_spec h.realizes)

lemma runs_left (h : NorthHistory N m) :
    ColumnChain.Runs (empty (N+1)) (List.ofFn h.left) h.leftState :=
  (Classical.choose_spec (Classical.choose_spec h.realizes)).1

lemma runs_right (h : NorthHistory N m) :
    ColumnChain.Runs (empty (N+1)) (List.ofFn h.right) h.rightState :=
  (Classical.choose_spec (Classical.choose_spec h.realizes)).2.1

lemma glues (h : NorthHistory N m) : h.leftState.GluesAt (Fin.last N) h.rightState :=
  (Classical.choose_spec (Classical.choose_spec h.realizes)).2.2

lemma shape_left_exists (h : NorthHistory N m) : ∃kl : ℕ×ℕ,
    (List.ofFn h.left).map (fun t=>t (Fin.last N))=
      List.replicate kl.1 Tile.diagonal₁ ++ Tile.vertical₀::List.replicate kl.2 Tile.vacant := by
  obtain ⟨k,l,hh⟩ := (ColumnChain.north_shape (fun _ : Fin N=>physicalWeights (2*Diagram.lambda))
    (List.ofFn h.left) h.leftState h.runs_left h.nzleft).1 h.glues.1
  exact ⟨(k,l),hh⟩

lemma shape_right_exists (h : NorthHistory N m) : ∃kl : ℕ×ℕ,
    (List.ofFn h.right).map (fun t=>t (Fin.last N))=
      List.replicate kl.1 Tile.diagonal₁ ++ Tile.vertical₀::List.replicate kl.2 Tile.vacant := by
  obtain ⟨k,l,hh⟩ := (ColumnChain.north_shape (fun _ : Fin N=>physicalWeights Diagram.lambda)
    (List.ofFn h.right) h.rightState h.runs_right h.nzright).1 ((h.glues.2.1 _).mp h.glues.1)
  exact ⟨(k,l),hh⟩

def ls (h : NorthHistory N m) : ℕ×ℕ := Classical.choose h.shape_left_exists

def rs (h : NorthHistory N m) : ℕ×ℕ := Classical.choose h.shape_right_exists

lemma ls_spec (h : NorthHistory N m) :
    (List.ofFn h.left).map (fun t=>t (Fin.last N))=
      List.replicate h.ls.1 Tile.diagonal₁ ++ Tile.vertical₀::List.replicate h.ls.2 Tile.vacant :=
  Classical.choose_spec h.shape_left_exists

lemma rs_spec (h : NorthHistory N m) :
    (List.ofFn h.right).map (fun t=>t (Fin.last N))=
      List.replicate h.rs.1 Tile.diagonal₁ ++ Tile.vertical₀::List.replicate h.rs.2 Tile.vacant :=
  Classical.choose_spec h.shape_right_exists

 

def toCross (h : NorthHistory N m) (hN : 1≤N) : CrossTopArch N where
  left := h.ls.1
  right := h.rs.1
  arch := SewnRectangle.northArch (List.ofFn h.left) (List.ofFn h.right)
    h.leftState h.rightState hN h.runs_left h.runs_right h.glues h.nzleft h.nzright
    h.ls.1 h.ls.2 h.rs.1 h.rs.2 h.ls_spec h.rs_spec

lemma toCross_extend (h : NorthHistory N m) (hN : 1≤N) :
    ((h.toCross hN).arch.extend hN (by dsimp [toCross]; omega)).tile=
      SewnRectangle.tile (List.ofFn h.left) (List.ofFn h.right) := by
  exact congrArg HoneycombAssignment.tile
    (SewnRectangle.northArch_extend (List.ofFn h.left) (List.ofFn h.right)
      h.leftState h.rightState hN h.runs_left h.runs_right h.glues h.nzleft h.nzright
      h.ls.1 h.ls.2 h.rs.1 h.rs.2 h.ls_spec h.rs_spec)

lemma toCross_fits (h : NorthHistory N m) (hN : 1≤N) : (h.toCross hN).Fits m := by
  have hf := SewnRectangle.fits_ofFn h.left h.right _ (h.toCross_extend hN)
  intro q hq
  have hj : q.2<N := by
    by_contra hp
    exact hq ((h.toCross hN).arch.outside _ _ (by omega))
  apply hf q
  rw [(h.toCross hN).arch.extend_base hN _ _ _ hj]
  exact hq

 
def ofCross (D : CrossTopArch.Bounded N m) (hN : 1≤N) : NorthHistory N m where
  left := (D.val.arch.extend hN (by omega)).leftClip m
  right := (D.val.arch.extend hN (by omega)).rightClip m
  nzleft := (D.val.arch.clips_weight_ne_zero hN (by omega) (by omega) (by omega) m).1
  nzright := (D.val.arch.clips_weight_ne_zero hN (by omega) (by omega) (by omega) m).2
  realizes := D.val.arch.extend_clips_runs hN (by omega) (by omega) m D.property

lemma ofCross_toCross (h : NorthHistory N m) (hN : 1≤N) :
    ofCross ⟨h.toCross hN,h.toCross_fits hN⟩ hN=h := by
  apply ext
  · exact SewnRectangle.clips_left h.left h.right _ (h.toCross_extend hN)
  · exact SewnRectangle.clips_right h.left h.right _ (h.toCross_extend hN)

lemma toCross_ofCross (D : CrossTopArch.Bounded N m) (hN : 1≤N) :
    (ofCross D hN).toCross hN=D.val := by
  apply CrossTopArch.ext
  have he := (ofCross D hN).toCross_extend hN
  have hs := (D.val.arch.extend hN (by omega)).sewn_clips m
    (D.val.arch.extend_fits hN (by omega) D.property)
  have hh : (((ofCross D hN).toCross hN).arch.extend hN (by omega)).tile=
      (D.val.arch.extend hN (by omega)).tile := he.trans hs.symm
  funext ⟨i,j⟩
  by_cases hj : j<N
  · have hx:=congrFun hh (i,j)
    simpa only [TopArchConfiguration.extend_base _ _ _ _ _ hj] using hx
  · rw [((ofCross D hN).toCross hN).arch.outside _ _ (by omega),D.val.arch.outside _ _ (by omega)]

 

def equivCross (hN : 1≤N) : NorthHistory N m ≃ CrossTopArch.Bounded N m where
  toFun h := ⟨h.toCross hN,h.toCross_fits hN⟩
  invFun D := ofCross D hN
  left_inv h := ofCross_toCross h hN
  right_inv D := Subtype.ext (toCross_ofCross D hN)

end NorthHistory
end
end CriticalStrip





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

namespace NorthHistory
variable {N m : ℕ}

instance boundedFintype (N m : ℕ) [hN : Fact (1≤N)] : Fintype (CrossTopArch.Bounded N m) :=
  Fintype.ofEquiv (NorthHistory N m) (equivCross hN.out)

end NorthHistory
end
end CriticalStrip





namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical
open Diagram Filter Topology

namespace CrossTopArch
variable {N : ℕ}

def window (N m : ℕ) [Fact (1≤N)] : Finset (CrossTopArch N) :=
  (Finset.univ : Finset (Bounded N m)).map ⟨Subtype.val,Subtype.val_injective⟩

@[simp] lemma mem_window [Fact (1≤N)] (D : CrossTopArch N) (m : ℕ) :
    D∈window N m ↔ D.Fits m := by
  simp only [window,Finset.mem_map,Finset.mem_univ,true_and,Function.Embedding.coeFn_mk]
  exact ⟨fun ⟨D',he⟩=>he ▸ D'.property,fun h=>⟨⟨D,h⟩,rfl⟩⟩

end CrossTopArch
end

 

 

noncomputable section
open scoped Classical BigOperators
open Diagram

namespace CrossTopArch

def sigmaEquiv (N : ℕ) : CrossTopArch N ≃
    Sigma (fun x : ℕ×ℕ=>TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ)) where
  toFun D := ⟨(D.left,D.right),D.arch⟩
  invFun D := ⟨D.1.1,D.1.2,D.2⟩
  left_inv D := by cases D; rfl
  right_inv D := by rcases D with ⟨⟨l,r⟩,D⟩; rfl

end CrossTopArch



end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnGate
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



structure GatePotentials {n : ℕ} (p q : Pairing n) (a b : Fin n) (t : Tile)
    (g h : Fin n → ℤ) (B : Fin n → ℤ) (T : Fin 4 → ℤ) : Prop where
  old_arc : ∀ i j,p.Adj i j → B j-B i=arcTurn g i j
  tile_arc : ∀ i j,t.Adj i j →
    T j-T i=gateTurn (g a) (g b) (h a) (h b) i j
  input_left : B a=T 0
  input_right : B b=T 1
  output_left : T 2=q.turnPotential h a
  output_right : T 3=q.turnPotential h b
  outside : ∀ i,i≠a → i≠b → B i=q.turnPotential h i


end Pairing






namespace BoundaryInsert
variable {n m : ℕ}


def pairing (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m) : Pairing (n+m) where
  val := (p.map (old k hk)).val ∪ (t.map (fresh k hk)).val
  property := by
    have hp := (p.map (old (m:=m) k hk)).property
    have ht := (t.map (fresh (n:=n) k hk)).property
    refine ⟨?_,?_,?_⟩
    · intro a h
      rcases Finset.mem_union.mp h with h|h
      · exact hp.1 a h
      · exact ht.1 a h
    · intro a ha b hb
      rcases Finset.mem_union.mp ha with ha|ha <;>
        rcases Finset.mem_union.mp hb with hb|hb
      · exact hp.2.1 a ha b hb
      · obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_map.mp ha
        obtain ⟨⟨x,y⟩,hxy,hf⟩ := Finset.mem_map.mp hb
        subst a; subst b
        exact Or.inr ⟨disjoint k hk i x,disjoint k hk i y,
          disjoint k hk j x,disjoint k hk j y⟩
      · obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_map.mp ha
        obtain ⟨⟨x,y⟩,hxy,hf⟩ := Finset.mem_map.mp hb
        subst a; subst b
        exact Or.inr ⟨(disjoint k hk x i).symm,(disjoint k hk y i).symm,
          (disjoint k hk x j).symm,(disjoint k hk y j).symm⟩
      · exact ht.2.1 a ha b hb
    · intro a ha b hb
      rcases Finset.mem_union.mp ha with ha|ha <;>
        rcases Finset.mem_union.mp hb with hb|hb
      · exact hp.2.2 a ha b hb
      · obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_map.mp ha
        obtain ⟨⟨x,y⟩,hxy,hf⟩ := Finset.mem_map.mp hb
        subst a; subst b
        intro hh
        exact not_cross k hk i j x y (Or.inl hh)
      · obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_map.mp ha
        obtain ⟨⟨x,y⟩,hxy,hf⟩ := Finset.mem_map.mp hb
        subst a; subst b
        intro hh
        exact not_cross k hk x y i j (Or.inr (Or.inl hh))
      · exact ht.2.2 a ha b hb

end BoundaryInsert
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace BoundarySew






variable {V : Type*} {n : ℕ}


variable {r : V → V → Prop} [Std.Symm r] {old : Fin (n+2) → V} {p : Pairing (n+2)}

omit [Std.Symm r] in
lemma project_edge (a b : Fin (n+2)) (_hc : p.Occupied a ↔ p.Occupied b)
    {v w : V ⊕ Fin 4}
    (h : CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a)) v w) :
    Relation.ReflTransGen (graph r (old a) (old b) (p.Occupied a))
      (project (old a) (old b) v) (project (old a) (old b) w) := by
  cases v with
  | inl v =>
    cases w with
    | inl w => exact .single (Or.inl h)
    | inr j =>
      rcases h with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩ <;> simp only [project] <;> exact .refl
  | inr i =>
    cases w with
    | inl w =>
      rcases h with ⟨rfl,rfl,_⟩|⟨rfl,rfl,_⟩ <;> simp only [project] <;> exact .refl
    | inr j =>
      change (tile (p.Occupied a)).Adj i j at h
      by_cases ha : p.Occupied a
      · have hh : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by
          simpa only [tile,ite_eq_left ha,Tile.Adj,Tile.edges,Finset.mem_singleton,Prod.mk.injEq,and_comm] using h
        rcases hh with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact .single (Or.inr ⟨ha,Or.inl ⟨rfl,rfl⟩⟩)
        · exact .single (Or.inr ⟨ha,Or.inr ⟨rfl,rfl⟩⟩)
      · simp only [tile,ite_eq_right ha,Tile.vacant_not_adj] at h

lemma include_edge (a b : Fin (n+2)) (hc : p.Occupied a ↔ p.Occupied b)
    {v w : V} (h : graph r (old a) (old b) (p.Occupied a) v w) :
    Relation.ReflTransGen (CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a)))
      (.inl v) (.inl w) := by
  have forward (ha : p.Occupied a) :
      Relation.ReflTransGen (CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a)))
        (.inl (old a)) (.inl (old b)) := by
    have h₁ : CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a))
        (.inl (old a)) (.inr 0) := Or.inl ⟨rfl,rfl,ha⟩
    have h₂ : CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a))
        (.inr 0) (.inr 1) := by simp [CompactGate.wiring,tile,ha,Tile.Adj,Tile.edges]
    have h₃ : CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a))
        (.inr 1) (.inl (old b)) := Or.inr ⟨rfl,rfl,hc.mp ha⟩
    exact ((Relation.ReflTransGen.single h₁).tail h₂).tail h₃
  rcases h with h|⟨ha,h⟩
  · exact .single h
  · rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact forward ha
    · exact symm (forward ha)

omit [Std.Symm r] in
lemma used_port (a b : Fin (n+2)) (hc : p.Occupied a ↔ p.Occupied b) {i : Fin 4}
    (hi : Graph.Used (CompactGate.wiring r old p.Occupied a b (tile (p.Occupied a))) (.inr i)) :
    p.Occupied a ∧ (i=0 ∨ i=1) := by
  obtain ⟨w,hw⟩:=hi
  cases w with
  | inl w =>
    rcases hw with ⟨rfl,rfl,ha⟩|⟨rfl,rfl,hb⟩
    · exact ⟨ha,Or.inl rfl⟩
    · exact ⟨hc.mpr hb,Or.inr rfl⟩
  | inr j =>
    by_cases ha : p.Occupied a
    · have hh : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by
        simpa only [CompactGate.wiring,tile,ite_eq_left ha,Tile.Adj,Tile.edges,
          Finset.mem_singleton,Prod.mk.injEq,and_comm] using hw
      exact ⟨ha,hh.elim (fun h=>Or.inl h.1) (fun h=>Or.inr h.1)⟩
    · simp only [CompactGate.wiring,tile,ite_eq_right ha,Tile.vacant_not_adj] at hw

def equivalence (k : ℕ) (hk : k≤n) (hp : GraphRealizes r old p)
    (hinj : Function.Injective old)
    (hc : p.Occupied (BoundaryErase.left k hk) ↔ p.Occupied (BoundaryErase.right k hk)) :
    Graph.BoundaryEquiv
      (CompactGate.wiring r old p.Occupied (BoundaryErase.left k hk) (BoundaryErase.right k hk)
        (tile (p.Occupied (BoundaryErase.left k hk))))
      (graph r (old (BoundaryErase.left k hk)) (old (BoundaryErase.right k hk))
        (p.Occupied (BoundaryErase.left k hk)))
      (CompactGate.boundary old (BoundaryErase.left k hk) (BoundaryErase.right k hk) ∘
        BoundaryErase.keep k hk) (old ∘ BoundaryErase.keep k hk) := by
  let a:=BoundaryErase.left k hk
  let b:=BoundaryErase.right k hk
  have hup (i : Fin (n+2)) (hi : p.Occupied i) : Graph.Used r (old i) :=
    (hp.boundary_used_iff hinj i).mpr hi
  refine ⟨project (old a) (old b),Sum.inl,
    fun _ _=>project_edge a b hc,fun _ _=>include_edge a b hc,?_,?_,?_,?_,?_,?_⟩
  · intro i
    simp only [Function.comp_apply,CompactGate.boundary,
      ite_eq_right (BoundaryErase.keep_ne_left k hk i),ite_eq_right (BoundaryErase.keep_ne_right k hk i),project]
  · intro i
    simp only [Function.comp_apply,CompactGate.boundary,
      ite_eq_right (BoundaryErase.keep_ne_left k hk i),ite_eq_right (BoundaryErase.keep_ne_right k hk i)]
  · rintro (v|i) hv
    · obtain ⟨w,hw⟩:=hv
      cases w with
      | inl w => exact ⟨w,Or.inl hw⟩
      | inr j =>
        rcases hw with ⟨rfl,rfl,ha⟩|⟨rfl,rfl,hb⟩
        · obtain ⟨w,hw⟩:=hup a ha; exact ⟨w,Or.inl hw⟩
        · obtain ⟨w,hw⟩:=hup b hb; exact ⟨w,Or.inl hw⟩
    · obtain ⟨ha,hi⟩:=used_port a b hc hv
      rcases hi with rfl|rfl
      · obtain ⟨w,hw⟩:=hup a ha; exact ⟨w,Or.inl hw⟩
      · obtain ⟨w,hw⟩:=hup b (hc.mp ha); exact ⟨w,Or.inl hw⟩
  · rintro v ⟨w,hw⟩
    rcases hw with hw|⟨ha,hw⟩
    · exact ⟨.inl w,hw⟩
    · rcases hw with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨.inr 0,Or.inl ⟨rfl,rfl,ha⟩⟩
      · exact ⟨.inr 1,Or.inr ⟨rfl,rfl,hc.mp ha⟩⟩
  · rintro (v|i) hv
    · exact .refl
    · obtain ⟨ha,hi⟩:=used_port a b hc hv
      rcases hi with rfl|rfl
      · exact .single (Or.inl ⟨rfl,rfl,ha⟩)
      · exact .single (Or.inr ⟨rfl,rfl,hc.mp ha⟩)
  · exact fun _ _=>.refl


end BoundarySew
end
end CriticalStrip.Diagram

end OAI
end


