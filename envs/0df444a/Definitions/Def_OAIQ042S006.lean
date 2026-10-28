-- Prove2me | Definitions.Def_OAIQ042S006
-- name    : OAIQ042S006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:40:32.56876+00:00
-- url     : https://prove2.me/theorems/565fb85e-3675-4d1c-84bc-7c2623230e74
-- title:
--   Definitions bundle OAIQ042S006 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 98 declarations of OpenAI's Lean: 15 definitions, 2 instances and 81 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.PolynomialBox`, `OAI.CriticalStrip.Diagram.ThreeBox.ForestConditions`, `OAI.CriticalStrip.Diagram.ThreeBox.certificate`, `OAI.CriticalStrip.Diagram.ThreeBox.parentTable`, `OAI.CriticalStrip.Diagram.ThreeBox.rankTable`, `OAI.CriticalStrip.Diagram.TriplePosition.exteriorPredicate`, `OAI.CriticalStrip.Diagram.TriplePosition.mirrorAttached`, `OAI.CriticalStrip.Diagram.TriplePosition.mirrorExteriorPredicate`, `OAI.CriticalStrip.Diagram.TriplePosition.mirrorPatch`, `OAI.CriticalStrip.Diagram.TriplePosition.mirrorPatchEquiv`, `OAI.CriticalStrip.Diagram.TriplePosition.mirrorSupport`, `OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring`, `OAI.CriticalStrip.Diagram.TriplePosition.patchEquiv`, `OAI.CriticalStrip.Diagram.tripleProgram`, `OAI.CriticalStrip.HoneycombConfiguration.weight`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_CollisionSubstitutions`, `StripMass_HoneycombDictionary`, `StripMass_MirrorExterior`, `StripMass_PairingDiagrams`, `StripMass_PhaseAlgebra`, `StripMass_SwapVacancy`, `StripMass_ThreeBoxBraidPolynomial`, `StripMass_ThreeBoxCertificates`, `StripMass_ThreeBoxProfiles`, `StripMass_ThreeBoxSplitPolynomial`, `StripMass_ThreeBoxWeights`, `StripMass_TopPadding`, `StripMass_TripleCircuit`, `StripMass_TriplePatch`.
--
--   **Imports.** It imports the bundles `OAIQ042S002`, `OAIQ042S003` and `OAIQ042S004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S010` and `OAIQ042S011`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S002
import Definitions.Def_OAIQ042S003
import Definitions.Def_OAIQ042S004

section
-- module Solutions.OAIQ042_SS.StripMass_PairingDiagrams
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


theorem realizes_empty_iff {n : ℕ} (p : Pairing n) (t : Configuration n) :
    Realizes p (empty n) t ↔ p = empty n ∧ t = fun _ => Tile.vacant := by
  constructor
  · intro h
    have ht : ∀ i, t i = .vacant := by
      intro i
      apply (Tile.eq_vacant_iff _).2
      intro a ⟨b, hab⟩
      obtain ⟨j, hj, _⟩ := h.no_loop (i,a) (i,b) (Or.inl ⟨rfl, hab⟩)
      exact empty_not_occupied j hj
    refine ⟨(Pairing.eq_empty_iff _).2 ?_, funext ht⟩
    intro i hi
    have := (h.west i).2 hi
    simp [ht i] at this
  · rintro ⟨rfl, rfl⟩
    have hw : ∀ v w : Vertex n, ¬ Wiring (empty n) (fun _ => Tile.vacant) v w := by
      intro v w
      simp [Wiring]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; simp
    · intro i; simp
    · intro i _; simp
    · intro i _; simp
    · intro i j _; simp
    · intro v w h; exact (hw v w h).elim
    · intro i j hij
      have hr : Reach (empty n) (fun _ : Fin n => Tile.vacant) (i,2) (j,2) ↔
          (j, (2 : Fin 4)) = (i,2) := Relation.reflTransGen_iff_eq (hw (i,2))
      simp [hr, Ne.symm hij]

theorem column_empty_row {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (p : Pairing n) :
    column w (empty n) p = if p = empty n then 1 else 0 := by
  classical
  by_cases hp : p = empty n
  · subst p
    simp [column, realizes_empty_iff, Weights.tile]
  · simp [column, realizes_empty_iff, hp]



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TopPadding
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

theorem Realizes.top_vacant {n : ℕ} {p q : Pairing n} {t : Configuration (n+1)}
    (h : Realizes p.padTop q.padTop t) : t (Fin.last n) = .vacant :=
  Tile.vacant_of_three_top _ (h.north (Fin.last n) rfl)
    (fun hc => p.padTop_not_occupied_last ((h.west (Fin.last n)).mp hc))
    (fun hc => q.padTop_not_occupied_last ((h.east (Fin.last n)).mp hc))

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxCertificates
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.ThreeBox.boundaryDataDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.cleanDecidable _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section



def parentTable : Config → Fin 12 → Fin 12
  | (.vacant,.vacant,.vacant) => ![0,1,2,3,4,5,6,7,8,9,10,11]
  | (.vacant,.vacant,.cup) => ![0,1,2,3,4,5,6,7,8,9,10,10]
  | (.vacant,.vertical₀,.vacant) => ![0,1,2,3,4,5,4,7,8,9,10,11]
  | (.vacant,.vertical₀,.cup) => ![0,1,2,3,4,5,4,7,8,9,10,10]
  | (.vacant,.diagonal₀,.vertical₀) => ![0,1,2,3,4,5,6,4,7,9,8,11]
  | (.vacant,.diagonal₀,.diagonal₀) => ![0,1,2,3,4,5,6,4,7,9,10,8]
  | (.vacant,.cup,.vertical₀) => ![0,1,2,3,4,5,6,6,7,9,8,11]
  | (.vacant,.cup,.diagonal₀) => ![0,1,2,3,4,5,6,6,7,9,10,8]
  | (.vertical₀,.vertical₁,.vertical₀) => ![0,1,0,3,4,2,6,5,7,9,8,11]
  | (.vertical₀,.vertical₁,.diagonal₀) => ![0,1,0,3,4,2,6,5,7,9,10,8]
  | (.vertical₀,.diagonal₁,.vacant) => ![0,1,0,3,4,2,5,7,8,9,10,11]
  | (.vertical₀,.diagonal₁,.cup) => ![0,1,0,3,4,2,5,7,8,9,10,10]
  | (.vertical₀,.cap,.vacant) => ![0,1,0,3,5,2,6,7,8,9,10,11]
  | (.vertical₀,.cap,.cup) => ![0,1,0,3,5,2,6,7,8,9,10,10]
  | (.vertical₀,.verticalPair,.vertical₀) => ![0,1,0,3,4,2,4,5,7,9,8,11]
  | (.vertical₀,.verticalPair,.diagonal₀) => ![0,1,0,3,4,2,4,5,7,9,10,8]
  | (.vertical₀,.capCup,.vertical₀) => ![0,1,0,3,5,2,6,6,7,9,8,11]
  | (.vertical₀,.capCup,.diagonal₀) => ![0,1,0,3,5,2,6,6,7,9,10,8]
  | (.vertical₁,.vacant,.vertical₁) => ![0,1,2,1,4,5,6,7,8,3,10,9]
  | (.vertical₁,.vacant,.diagonal₁) => ![0,1,2,1,4,5,6,7,8,3,9,11]
  | (.vertical₁,.vertical₀,.vertical₁) => ![0,1,2,1,4,5,4,7,8,3,10,9]
  | (.vertical₁,.vertical₀,.diagonal₁) => ![0,1,2,1,4,5,4,7,8,3,9,11]
  | (.vertical₁,.diagonal₀,.cap) => ![0,1,2,1,7,5,6,8,9,3,10,11]
  | (.vertical₁,.diagonal₀,.verticalPair) => ![0,1,2,1,4,5,6,4,7,3,8,9]
  | (.vertical₁,.diagonal₀,.capCup) => ![0,1,2,1,7,5,6,8,9,3,10,10]
  | (.vertical₁,.cup,.cap) => ![0,1,2,1,4,5,7,8,9,3,10,11]
  | (.vertical₁,.cup,.verticalPair) => ![0,1,2,1,4,5,6,6,7,3,8,9]
  | (.vertical₁,.cup,.capCup) => ![0,1,2,1,4,5,7,8,9,3,10,10]
  | (.diagonal₀,.vacant,.vertical₁) => ![0,1,2,0,4,5,6,7,8,3,10,9]
  | (.diagonal₀,.vacant,.diagonal₁) => ![0,1,2,0,4,5,6,7,8,3,9,11]
  | (.diagonal₀,.vertical₀,.vertical₁) => ![0,1,2,0,4,5,4,7,8,3,10,9]
  | (.diagonal₀,.vertical₀,.diagonal₁) => ![0,1,2,0,4,5,4,7,8,3,9,11]
  | (.diagonal₀,.diagonal₀,.cap) => ![0,1,2,0,7,5,6,8,9,3,10,11]
  | (.diagonal₀,.diagonal₀,.verticalPair) => ![0,1,2,0,4,5,6,4,7,3,8,9]
  | (.diagonal₀,.diagonal₀,.capCup) => ![0,1,2,0,7,5,6,8,9,3,10,10]
  | (.diagonal₀,.cup,.cap) => ![0,1,2,0,4,5,7,8,9,3,10,11]
  | (.diagonal₀,.cup,.verticalPair) => ![0,1,2,0,4,5,6,6,7,3,8,9]
  | (.diagonal₀,.cup,.capCup) => ![0,1,2,0,4,5,7,8,9,3,10,10]
  | (.diagonal₁,.vertical₁,.vertical₀) => ![0,1,1,3,4,2,6,5,7,9,8,11]
  | (.diagonal₁,.vertical₁,.diagonal₀) => ![0,1,1,3,4,2,6,5,7,9,10,8]
  | (.diagonal₁,.diagonal₁,.vacant) => ![0,1,1,3,4,2,5,7,8,9,10,11]
  | (.diagonal₁,.diagonal₁,.cup) => ![0,1,1,3,4,2,5,7,8,9,10,10]
  | (.diagonal₁,.cap,.vacant) => ![0,1,1,3,5,2,6,7,8,9,10,11]
  | (.diagonal₁,.cap,.cup) => ![0,1,1,3,5,2,6,7,8,9,10,10]
  | (.diagonal₁,.verticalPair,.vertical₀) => ![0,1,1,3,4,2,4,5,7,9,8,11]
  | (.diagonal₁,.verticalPair,.diagonal₀) => ![0,1,1,3,4,2,4,5,7,9,10,8]
  | (.diagonal₁,.capCup,.vertical₀) => ![0,1,1,3,5,2,6,6,7,9,8,11]
  | (.diagonal₁,.capCup,.diagonal₀) => ![0,1,1,3,5,2,6,6,7,9,10,8]
  | (.cap,.vacant,.vacant) => ![0,0,2,3,4,5,6,7,8,9,10,11]
  | (.cap,.vacant,.cup) => ![0,0,2,3,4,5,6,7,8,9,10,10]
  | (.cap,.vertical₀,.vacant) => ![0,0,2,3,4,5,4,7,8,9,10,11]
  | (.cap,.vertical₀,.cup) => ![0,0,2,3,4,5,4,7,8,9,10,10]
  | (.cap,.diagonal₀,.vertical₀) => ![0,0,2,3,4,5,6,4,7,9,8,11]
  | (.cap,.diagonal₀,.diagonal₀) => ![0,0,2,3,4,5,6,4,7,9,10,8]
  | (.cap,.cup,.vertical₀) => ![0,0,2,3,4,5,6,6,7,9,8,11]
  | (.cap,.cup,.diagonal₀) => ![0,0,2,3,4,5,6,6,7,9,10,8]
  | (.cup,.vertical₁,.cap) => ![0,1,2,2,4,2,6,5,9,3,10,11]
  | (.cup,.vertical₁,.verticalPair) => ![0,1,2,2,4,2,6,5,7,3,8,9]
  | (.cup,.vertical₁,.capCup) => ![0,1,2,2,4,2,6,5,9,3,10,10]
  | (.cup,.diagonal₁,.vertical₁) => ![0,1,2,2,4,2,5,7,8,3,10,9]
  | (.cup,.diagonal₁,.diagonal₁) => ![0,1,2,2,4,2,5,7,8,3,9,11]
  | (.cup,.cap,.vertical₁) => ![0,1,2,2,5,2,6,7,8,3,10,9]
  | (.cup,.cap,.diagonal₁) => ![0,1,2,2,5,2,6,7,8,3,9,11]
  | (.cup,.verticalPair,.cap) => ![0,1,2,2,4,2,4,5,9,3,10,11]
  | (.cup,.verticalPair,.verticalPair) => ![0,1,2,2,4,2,4,5,7,3,8,9]
  | (.cup,.verticalPair,.capCup) => ![0,1,2,2,4,2,4,5,9,3,10,10]
  | (.cup,.capCup,.cap) => ![0,1,2,2,5,2,7,8,9,3,10,11]
  | (.cup,.capCup,.verticalPair) => ![0,1,2,2,5,2,6,6,7,3,8,9]
  | (.cup,.capCup,.capCup) => ![0,1,2,2,5,2,7,8,9,3,10,10]
  | (.verticalPair,.vertical₁,.cap) => ![0,3,0,9,4,2,6,5,7,8,10,11]
  | (.verticalPair,.vertical₁,.verticalPair) => ![0,1,0,1,4,2,6,5,7,3,8,9]
  | (.verticalPair,.vertical₁,.capCup) => ![0,3,0,9,4,2,6,5,7,8,10,10]
  | (.verticalPair,.diagonal₁,.vertical₁) => ![0,1,0,1,4,2,5,7,8,3,10,9]
  | (.verticalPair,.diagonal₁,.diagonal₁) => ![0,1,0,1,4,2,5,7,8,3,9,11]
  | (.verticalPair,.cap,.vertical₁) => ![0,1,0,1,5,2,6,7,8,3,10,9]
  | (.verticalPair,.cap,.diagonal₁) => ![0,1,0,1,5,2,6,7,8,3,9,11]
  | (.verticalPair,.verticalPair,.cap) => ![0,3,0,9,4,2,4,5,7,8,10,11]
  | (.verticalPair,.verticalPair,.verticalPair) => ![0,1,0,1,4,2,4,5,7,3,8,9]
  | (.verticalPair,.verticalPair,.capCup) => ![0,3,0,9,4,2,4,5,7,8,10,10]
  | (.verticalPair,.capCup,.cap) => ![0,1,0,1,5,2,7,8,9,3,10,11]
  | (.verticalPair,.capCup,.verticalPair) => ![0,1,0,1,5,2,6,6,7,3,8,9]
  | (.verticalPair,.capCup,.capCup) => ![0,1,0,1,5,2,7,8,9,3,10,10]
  | (.capCup,.vertical₁,.cap) => ![0,0,2,2,4,2,6,5,9,3,10,11]
  | (.capCup,.vertical₁,.verticalPair) => ![0,0,2,2,4,2,6,5,7,3,8,9]
  | (.capCup,.vertical₁,.capCup) => ![0,0,2,2,4,2,6,5,9,3,10,10]
  | (.capCup,.diagonal₁,.vertical₁) => ![0,0,2,2,4,2,5,7,8,3,10,9]
  | (.capCup,.diagonal₁,.diagonal₁) => ![0,0,2,2,4,2,5,7,8,3,9,11]
  | (.capCup,.cap,.vertical₁) => ![0,0,2,2,5,2,6,7,8,3,10,9]
  | (.capCup,.cap,.diagonal₁) => ![0,0,2,2,5,2,6,7,8,3,9,11]
  | (.capCup,.verticalPair,.cap) => ![0,0,2,2,4,2,4,5,9,3,10,11]
  | (.capCup,.verticalPair,.verticalPair) => ![0,0,2,2,4,2,4,5,7,3,8,9]
  | (.capCup,.verticalPair,.capCup) => ![0,0,2,2,4,2,4,5,9,3,10,10]
  | (.capCup,.capCup,.cap) => ![0,0,2,2,5,2,7,8,9,3,10,11]
  | (.capCup,.capCup,.verticalPair) => ![0,0,2,2,5,2,6,6,7,3,8,9]
  | (.capCup,.capCup,.capCup) => ![0,0,2,2,5,2,7,8,9,3,10,10]
  | _ => fun i => i

def rankTable : Config → Fin 12 → ℕ
  | (.vacant,.vacant,.vacant) => ![0,0,0,0,0,0,0,0,0,0,0,0]
  | (.vacant,.vacant,.cup) => ![0,0,0,0,0,0,0,0,0,0,0,1]
  | (.vacant,.vertical₀,.vacant) => ![0,0,0,0,0,0,1,0,0,0,0,0]
  | (.vacant,.vertical₀,.cup) => ![0,0,0,0,0,0,1,0,0,0,0,1]
  | (.vacant,.diagonal₀,.vertical₀) => ![0,0,0,0,0,0,0,1,2,0,3,0]
  | (.vacant,.diagonal₀,.diagonal₀) => ![0,0,0,0,0,0,0,1,2,0,0,3]
  | (.vacant,.cup,.vertical₀) => ![0,0,0,0,0,0,0,1,2,0,3,0]
  | (.vacant,.cup,.diagonal₀) => ![0,0,0,0,0,0,0,1,2,0,0,3]
  | (.vertical₀,.vertical₁,.vertical₀) => ![0,0,1,0,0,2,0,3,4,0,5,0]
  | (.vertical₀,.vertical₁,.diagonal₀) => ![0,0,1,0,0,2,0,3,4,0,0,5]
  | (.vertical₀,.diagonal₁,.vacant) => ![0,0,1,0,0,2,3,0,0,0,0,0]
  | (.vertical₀,.diagonal₁,.cup) => ![0,0,1,0,0,2,3,0,0,0,0,1]
  | (.vertical₀,.cap,.vacant) => ![0,0,1,0,3,2,0,0,0,0,0,0]
  | (.vertical₀,.cap,.cup) => ![0,0,1,0,3,2,0,0,0,0,0,1]
  | (.vertical₀,.verticalPair,.vertical₀) => ![0,0,1,0,0,2,1,3,4,0,5,0]
  | (.vertical₀,.verticalPair,.diagonal₀) => ![0,0,1,0,0,2,1,3,4,0,0,5]
  | (.vertical₀,.capCup,.vertical₀) => ![0,0,1,0,3,2,0,1,2,0,3,0]
  | (.vertical₀,.capCup,.diagonal₀) => ![0,0,1,0,3,2,0,1,2,0,0,3]
  | (.vertical₁,.vacant,.vertical₁) => ![0,0,0,1,0,0,0,0,0,2,0,3]
  | (.vertical₁,.vacant,.diagonal₁) => ![0,0,0,1,0,0,0,0,0,2,3,0]
  | (.vertical₁,.vertical₀,.vertical₁) => ![0,0,0,1,0,0,1,0,0,2,0,3]
  | (.vertical₁,.vertical₀,.diagonal₁) => ![0,0,0,1,0,0,1,0,0,2,3,0]
  | (.vertical₁,.diagonal₀,.cap) => ![0,0,0,1,5,0,0,4,3,2,0,0]
  | (.vertical₁,.diagonal₀,.verticalPair) => ![0,0,0,1,0,0,0,1,2,2,3,3]
  | (.vertical₁,.diagonal₀,.capCup) => ![0,0,0,1,5,0,0,4,3,2,0,1]
  | (.vertical₁,.cup,.cap) => ![0,0,0,1,0,0,5,4,3,2,0,0]
  | (.vertical₁,.cup,.verticalPair) => ![0,0,0,1,0,0,0,1,2,2,3,3]
  | (.vertical₁,.cup,.capCup) => ![0,0,0,1,0,0,5,4,3,2,0,1]
  | (.diagonal₀,.vacant,.vertical₁) => ![0,0,0,1,0,0,0,0,0,2,0,3]
  | (.diagonal₀,.vacant,.diagonal₁) => ![0,0,0,1,0,0,0,0,0,2,3,0]
  | (.diagonal₀,.vertical₀,.vertical₁) => ![0,0,0,1,0,0,1,0,0,2,0,3]
  | (.diagonal₀,.vertical₀,.diagonal₁) => ![0,0,0,1,0,0,1,0,0,2,3,0]
  | (.diagonal₀,.diagonal₀,.cap) => ![0,0,0,1,5,0,0,4,3,2,0,0]
  | (.diagonal₀,.diagonal₀,.verticalPair) => ![0,0,0,1,0,0,0,1,2,2,3,3]
  | (.diagonal₀,.diagonal₀,.capCup) => ![0,0,0,1,5,0,0,4,3,2,0,1]
  | (.diagonal₀,.cup,.cap) => ![0,0,0,1,0,0,5,4,3,2,0,0]
  | (.diagonal₀,.cup,.verticalPair) => ![0,0,0,1,0,0,0,1,2,2,3,3]
  | (.diagonal₀,.cup,.capCup) => ![0,0,0,1,0,0,5,4,3,2,0,1]
  | (.diagonal₁,.vertical₁,.vertical₀) => ![0,0,1,0,0,2,0,3,4,0,5,0]
  | (.diagonal₁,.vertical₁,.diagonal₀) => ![0,0,1,0,0,2,0,3,4,0,0,5]
  | (.diagonal₁,.diagonal₁,.vacant) => ![0,0,1,0,0,2,3,0,0,0,0,0]
  | (.diagonal₁,.diagonal₁,.cup) => ![0,0,1,0,0,2,3,0,0,0,0,1]
  | (.diagonal₁,.cap,.vacant) => ![0,0,1,0,3,2,0,0,0,0,0,0]
  | (.diagonal₁,.cap,.cup) => ![0,0,1,0,3,2,0,0,0,0,0,1]
  | (.diagonal₁,.verticalPair,.vertical₀) => ![0,0,1,0,0,2,1,3,4,0,5,0]
  | (.diagonal₁,.verticalPair,.diagonal₀) => ![0,0,1,0,0,2,1,3,4,0,0,5]
  | (.diagonal₁,.capCup,.vertical₀) => ![0,0,1,0,3,2,0,1,2,0,3,0]
  | (.diagonal₁,.capCup,.diagonal₀) => ![0,0,1,0,3,2,0,1,2,0,0,3]
  | (.cap,.vacant,.vacant) => ![0,1,0,0,0,0,0,0,0,0,0,0]
  | (.cap,.vacant,.cup) => ![0,1,0,0,0,0,0,0,0,0,0,1]
  | (.cap,.vertical₀,.vacant) => ![0,1,0,0,0,0,1,0,0,0,0,0]
  | (.cap,.vertical₀,.cup) => ![0,1,0,0,0,0,1,0,0,0,0,1]
  | (.cap,.diagonal₀,.vertical₀) => ![0,1,0,0,0,0,0,1,2,0,3,0]
  | (.cap,.diagonal₀,.diagonal₀) => ![0,1,0,0,0,0,0,1,2,0,0,3]
  | (.cap,.cup,.vertical₀) => ![0,1,0,0,0,0,0,1,2,0,3,0]
  | (.cap,.cup,.diagonal₀) => ![0,1,0,0,0,0,0,1,2,0,0,3]
  | (.cup,.vertical₁,.cap) => ![0,0,0,1,0,1,0,2,3,2,0,0]
  | (.cup,.vertical₁,.verticalPair) => ![0,0,0,1,0,1,0,2,3,2,4,3]
  | (.cup,.vertical₁,.capCup) => ![0,0,0,1,0,1,0,2,3,2,0,1]
  | (.cup,.diagonal₁,.vertical₁) => ![0,0,0,1,0,1,2,0,0,2,0,3]
  | (.cup,.diagonal₁,.diagonal₁) => ![0,0,0,1,0,1,2,0,0,2,3,0]
  | (.cup,.cap,.vertical₁) => ![0,0,0,1,2,1,0,0,0,2,0,3]
  | (.cup,.cap,.diagonal₁) => ![0,0,0,1,2,1,0,0,0,2,3,0]
  | (.cup,.verticalPair,.cap) => ![0,0,0,1,0,1,1,2,3,2,0,0]
  | (.cup,.verticalPair,.verticalPair) => ![0,0,0,1,0,1,1,2,3,2,4,3]
  | (.cup,.verticalPair,.capCup) => ![0,0,0,1,0,1,1,2,3,2,0,1]
  | (.cup,.capCup,.cap) => ![0,0,0,1,2,1,5,4,3,2,0,0]
  | (.cup,.capCup,.verticalPair) => ![0,0,0,1,2,1,0,1,2,2,3,3]
  | (.cup,.capCup,.capCup) => ![0,0,0,1,2,1,5,4,3,2,0,1]
  | (.verticalPair,.vertical₁,.cap) => ![0,7,1,6,0,2,0,3,4,5,0,0]
  | (.verticalPair,.vertical₁,.verticalPair) => ![0,0,1,1,0,2,0,3,4,2,5,3]
  | (.verticalPair,.vertical₁,.capCup) => ![0,7,1,6,0,2,0,3,4,5,0,1]
  | (.verticalPair,.diagonal₁,.vertical₁) => ![0,0,1,1,0,2,3,0,0,2,0,3]
  | (.verticalPair,.diagonal₁,.diagonal₁) => ![0,0,1,1,0,2,3,0,0,2,3,0]
  | (.verticalPair,.cap,.vertical₁) => ![0,0,1,1,3,2,0,0,0,2,0,3]
  | (.verticalPair,.cap,.diagonal₁) => ![0,0,1,1,3,2,0,0,0,2,3,0]
  | (.verticalPair,.verticalPair,.cap) => ![0,7,1,6,0,2,1,3,4,5,0,0]
  | (.verticalPair,.verticalPair,.verticalPair) => ![0,0,1,1,0,2,1,3,4,2,5,3]
  | (.verticalPair,.verticalPair,.capCup) => ![0,7,1,6,0,2,1,3,4,5,0,1]
  | (.verticalPair,.capCup,.cap) => ![0,0,1,1,3,2,5,4,3,2,0,0]
  | (.verticalPair,.capCup,.verticalPair) => ![0,0,1,1,3,2,0,1,2,2,3,3]
  | (.verticalPair,.capCup,.capCup) => ![0,0,1,1,3,2,5,4,3,2,0,1]
  | (.capCup,.vertical₁,.cap) => ![0,1,0,1,0,1,0,2,3,2,0,0]
  | (.capCup,.vertical₁,.verticalPair) => ![0,1,0,1,0,1,0,2,3,2,4,3]
  | (.capCup,.vertical₁,.capCup) => ![0,1,0,1,0,1,0,2,3,2,0,1]
  | (.capCup,.diagonal₁,.vertical₁) => ![0,1,0,1,0,1,2,0,0,2,0,3]
  | (.capCup,.diagonal₁,.diagonal₁) => ![0,1,0,1,0,1,2,0,0,2,3,0]
  | (.capCup,.cap,.vertical₁) => ![0,1,0,1,2,1,0,0,0,2,0,3]
  | (.capCup,.cap,.diagonal₁) => ![0,1,0,1,2,1,0,0,0,2,3,0]
  | (.capCup,.verticalPair,.cap) => ![0,1,0,1,0,1,1,2,3,2,0,0]
  | (.capCup,.verticalPair,.verticalPair) => ![0,1,0,1,0,1,1,2,3,2,4,3]
  | (.capCup,.verticalPair,.capCup) => ![0,1,0,1,0,1,1,2,3,2,0,1]
  | (.capCup,.capCup,.cap) => ![0,1,0,1,2,1,5,4,3,2,0,0]
  | (.capCup,.capCup,.verticalPair) => ![0,1,0,1,2,1,0,1,2,2,3,3]
  | (.capCup,.capCup,.capCup) => ![0,1,0,1,2,1,5,4,3,2,0,1]
  | _ => fun _ => 0

def ForestConditions (t : Config) : Prop :=
  (∀ v w, Adj t v w → rootTable t v = rootTable t w) ∧
  (∀ v, v ≠ rootTable t v → Adj t v (parentTable t v)) ∧
  (∀ v, v ≠ rootTable t v → rankTable t (parentTable t v) < rankTable t v)

instance forestConditionsDecidable (t : Config) : Decidable (ForestConditions t) := by
  unfold ForestConditions; infer_instance

theorem forestConditions_0 (x y : Tile) (h : Compatible (.vacant,x,y)) :
    ForestConditions (.vacant,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_1 (x y : Tile) (h : Compatible (.vertical₀,x,y)) :
    ForestConditions (.vertical₀,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_2 (x y : Tile) (h : Compatible (.vertical₁,x,y)) :
    ForestConditions (.vertical₁,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_3 (x y : Tile) (h : Compatible (.diagonal₀,x,y)) :
    ForestConditions (.diagonal₀,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_4 (x y : Tile) (h : Compatible (.diagonal₁,x,y)) :
    ForestConditions (.diagonal₁,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_5 (x y : Tile) (h : Compatible (.cap,x,y)) :
    ForestConditions (.cap,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_6 (x y : Tile) (h : Compatible (.cup,x,y)) :
    ForestConditions (.cup,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_7 (x y : Tile) (h : Compatible (.verticalPair,x,y)) :
    ForestConditions (.verticalPair,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_8 (x y : Tile) (h : Compatible (.capCup,x,y)) :
    ForestConditions (.capCup,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions (t : Config) (h : Compatible t) : ForestConditions t := by
  rcases t with ⟨t,x,y⟩
  cases t
  · exact forestConditions_0 x y h
  · exact forestConditions_1 x y h
  · exact forestConditions_2 x y h
  · exact forestConditions_3 x y h
  · exact forestConditions_4 x y h
  · exact forestConditions_5 x y h
  · exact forestConditions_6 x y h
  · exact forestConditions_7 x y h
  · exact forestConditions_8 x y h

def certificate (t : Config) (h : Compatible t) : ConnectivityCertificate (Adj t) where
  root := rootTable t
  parent := parentTable t
  rank := rankTable t
  edge_root := (forestConditions t h).1
  parent_edge := (forestConditions t h).2.1
  parent_rank := (forestConditions t h).2.2

theorem reach_iff_root_eq (t : Config) (h : Compatible t) (v w : Fin 12) :
    Relation.ReflTransGen (Adj t) v w ↔ rootTable t v = rootTable t w :=
  (certificate t h).reach_iff (adj_symm t) v w

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxProfiles
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset



theorem realizes_iff_conditions {t : Config} {d : Finset (Fin 6 × Fin 6)} :
    Realizes t d ↔ Compatible t ∧ Clean t ∧ BoundaryData t d := by
  constructor
  · intro h
    refine ⟨h.compatible, ?_, h.occupied, ?_⟩
    · intro v w he
      obtain ⟨i,hi,hr⟩ := h.no_loop v w he
      exact ⟨i,hi,(reach_iff_root_eq t h.compatible v (boundary i)).mp hr⟩
    · intro i j hij
      exact (h.output i j hij).trans (reach_iff_root_eq t h.compatible _ _)
  · rintro ⟨hc,hl,ho,he⟩
    refine ⟨hc,ho,?_,?_⟩
    · intro v w hvw
      obtain ⟨i,hi,hr⟩ := hl v w hvw
      exact ⟨i,hi,(reach_iff_root_eq t hc v (boundary i)).mpr hr⟩
    · intro i j hij
      exact (he i j hij).trans (reach_iff_root_eq t hc _ _).symm

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

theorem coefficient_1 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 1 = a .vertical₀ * b .cap * c .vacant + a .diagonal₀ * b .diagonal₀ * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_7 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 7 = a .vertical₀ * b .capCup * c .vertical₀ := by
  simp [coefficient, fiber]

theorem coefficient_8 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 8 = a .vertical₀ * b .capCup * c .diagonal₀ := by
  simp [coefficient, fiber]

theorem coefficient_9 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 9 = a .vertical₀ * b .cap * c .cup + a .diagonal₀ * b .diagonal₀ * c .capCup := by
  simp [coefficient, fiber]

theorem coefficient_17 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 17 = a .vertical₀ * b .verticalPair * c .vertical₀ + a .diagonal₀ * b .vertical₀ * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_19 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 19 = a .vertical₀ * b .verticalPair * c .diagonal₀ + a .diagonal₀ * b .vertical₀ * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_25 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 25 = a .diagonal₀ * b .diagonal₀ * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_31 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 31 = a .cap * b .vacant * c .vacant + a .verticalPair * b .vertical₁ * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_32 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 32 = a .cap * b .cup * c .vertical₀ + a .capCup * b .diagonal₁ * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_33 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 33 = a .cap * b .cup * c .diagonal₀ + a .capCup * b .diagonal₁ * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_34 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 34 = a .cap * b .vacant * c .cup + a .verticalPair * b .vertical₁ * c .capCup + a .capCup * b .vertical₁ * c .verticalPair := by
  simp [coefficient, fiber, add_assoc]

theorem coefficient_35 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 35 = a .vertical₀ * b .diagonal₁ * c .vacant + a .diagonal₀ * b .cup * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_36 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 36 = a .verticalPair * b .diagonal₁ * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_37 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 37 = a .verticalPair * b .diagonal₁ * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_38 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 38 = a .vertical₀ * b .diagonal₁ * c .cup + a .diagonal₀ * b .cup * c .capCup := by
  simp [coefficient, fiber]

theorem coefficient_39 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 39 = a .vertical₀ * b .vertical₁ * c .vertical₀ + a .diagonal₀ * b .vacant * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_40 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 40 = a .verticalPair * b .vertical₁ * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_41 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 41 = a .vertical₀ * b .vertical₁ * c .diagonal₀ + a .diagonal₀ * b .vacant * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_42 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 42 = a .diagonal₀ * b .cup * c .verticalPair := by
  simp [coefficient, fiber]

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxBraidPolynomial
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

theorem braid_numerator_0 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 0 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 0 := by
  rw [coefficient_0, coefficient_0]
  simp only [tileNumerator]
  ring_nf

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxSplitPolynomial
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

theorem split2_numerator_0 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 0 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 0 := by
  rw [coefficient_0, coefficient_0]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf

theorem split2_numerator_1 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 1 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 31 := by
  rw [coefficient_1, coefficient_31]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_44 hq]
  all_goals ring

theorem split2_numerator_7 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 7 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 34 := by
  rw [coefficient_7, coefficient_34]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_8 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 8 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 33 := by
  rw [coefficient_8, coefficient_33]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq]
  all_goals ring

theorem split2_numerator_9 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 9 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 32 := by
  rw [coefficient_9, coefficient_32]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_14 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 14 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 46 := by
  rw [coefficient_14, coefficient_46]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_44 hq]
  all_goals ring

theorem split2_numerator_17 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 17 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 40 := by
  rw [coefficient_17, coefficient_40]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf

theorem split2_numerator_19 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 19 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 37 := by
  rw [coefficient_19, coefficient_37]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq]
  all_goals ring

theorem split2_numerator_22 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 22 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 47 := by
  rw [coefficient_22, coefficient_47]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_23 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 23 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 45 := by
  rw [coefficient_23, coefficient_45]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_44 hq]
  all_goals ring

theorem split2_numerator_25 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 25 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 36 := by
  rw [coefficient_25, coefficient_36]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq]
  all_goals ring

theorem split2_numerator_27 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 27 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 43 := by
  rw [coefficient_27, coefficient_43]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_46 hq]
  all_goals ring

theorem split2_numerator_30 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 30 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 44 := by
  rw [coefficient_30, coefficient_44]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq]
  all_goals ring

theorem split2_numerator_35 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 35 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 41 := by
  rw [coefficient_35, coefficient_41]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_38 {K : Type*} [CommRing K] (q z : K) (_hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 38 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 42 := by
  rw [coefficient_38, coefficient_42]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf

theorem split2_numerator_39 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 39 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 39 := by
  rw [coefficient_39, coefficient_39]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq]
  all_goals ring

theorem split2_numerator_41 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 41 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 35 := by
  rw [coefficient_41, coefficient_35]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq, eighthRoot_power_47 hq]
  all_goals ring

theorem split2_numerator_42 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 42 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 38 := by
  rw [coefficient_42, coefficient_38]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_36 hq, eighthRoot_power_38 hq, eighthRoot_power_40 hq, eighthRoot_power_42 hq, eighthRoot_power_44 hq]
  all_goals ring

theorem split2_numerator_48 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 48 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 50 := by
  rw [coefficient_48, coefficient_50]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq, eighthRoot_power_47 hq]
  all_goals ring

theorem split2_numerator_49 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 49 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 49 := by
  rw [coefficient_49, coefficient_49]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq]
  all_goals ring

theorem split2_numerator_50 {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) 50 * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) 48 := by
  rw [coefficient_50, coefficient_48]
  simp only [tileNumerator, swapTile, mergeNumerator, commonNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_33 hq, eighthRoot_power_35 hq, eighthRoot_power_37 hq, eighthRoot_power_39 hq, eighthRoot_power_41 hq, eighthRoot_power_43 hq, eighthRoot_power_45 hq]
  all_goals ring


 

 

open Finset



end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhaseAlgebra
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram.ThreeBox





noncomputable section
open scoped Classical

theorem split2_numerator {K : Type*} [CommRing K] (q z : K) (hq : q^8 = -1)
    (k : Fin 51) (h₂ : ¬ boundarySupport (diagram k) 2) :
    coefficient (mergeNumerator q) (tileNumerator q (q^4) (q^2*z)) (tileNumerator q (q^4) z) k * commonNumerator q (q*z) =
      commonNumerator q (q^2*z) * commonNumerator q z * coefficient (tileNumerator q (q^4) (q*z)) swapTile (mergeNumerator q) (mirrorIndex k) := by
  fin_cases k
  · exact split2_numerator_0 q z hq
  · exact split2_numerator_1 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_7 q z hq
  · exact split2_numerator_8 q z hq
  · exact split2_numerator_9 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_14 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_17 q z hq
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_19 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_22 q z hq
  · exact split2_numerator_23 q z hq
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_25 q z hq
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_27 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_30 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_35 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_38 q z hq
  · exact split2_numerator_39 q z hq
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_41 q z hq
  · exact split2_numerator_42 q z hq
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact False.elim (h₂ (by decide))
  · exact split2_numerator_48 q z hq
  · exact split2_numerator_49 q z hq
  · exact split2_numerator_50 q z hq

end
end CriticalStrip.Diagram.ThreeBox

 

 

namespace CriticalStrip.Diagram
noncomputable section


namespace ThreeBox

lemma coefficient_scale₁₃ {K : Type*} [CommSemiring K] (a b c : Tile → K)
    (r s : K) (k : Fin 51) :
    coefficient (fun t => r*a t) b (fun t => s*c t) k =
      (r*s) * coefficient a b c k := by
  simpa using coefficient_scale a b c r 1 s k

end ThreeBox






end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TripleCircuit
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.ThreeBox.boundaryDataDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.cleanDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.forestConditionsDecidable
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

lemma interface_old (p q : Pairing n) (v : Fin 12) (i : Fin n) :
    (∃ k, s.active p q k ∧ v=ThreeBox.boundary k ∧ (.inl i : Fin n ⊕ Fin n)=s.interface k) ↔
      (i=s.a ∧ v=4 ∧ p.Occupied s.a) ∨
      (i=s.b ∧ v=0 ∧ p.Occupied s.b) ∨ (i=s.c ∧ v=1 ∧ p.Occupied s.c) := by
  simp only [Fin.exists_fin_succ,interface,active,ThreeBox.boundary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Sum.inl.injEq,Sum.inl_ne_inr,and_false,or_false,Fin.exists_fin_zero]
  itauto

lemma interface_new (p q : Pairing n) (v : Fin 12) (i : Fin n) :
    (∃ k, s.active p q k ∧ v=ThreeBox.boundary k ∧ (.inr i : Fin n ⊕ Fin n)=s.interface k) ↔
      ((i=s.a ∧ v=6) ∨ (i=s.b ∧ v=10) ∨ (i=s.c ∧ v=11)) ∧ q.Occupied i := by
  simp only [Fin.exists_fin_succ,interface,active,ThreeBox.boundary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    Sum.inr.injEq,Sum.inr_ne_inl,and_false,false_or,or_false,Fin.exists_fin_zero]
  constructor
  · rintro (⟨h,hv,hi⟩ | ⟨h,hv,hi⟩ | ⟨h,hv,hi⟩) <;> subst i
    · exact ⟨Or.inl ⟨rfl,hv⟩,h⟩
    · exact ⟨Or.inr (Or.inl ⟨rfl,hv⟩),h⟩
    · exact ⟨Or.inr (Or.inr ⟨rfl,hv⟩),h⟩
  · rintro ⟨(⟨rfl,hv⟩|⟨rfl,hv⟩|⟨rfl,hv⟩),h⟩
    · exact Or.inl ⟨h,hv,rfl⟩
    · exact Or.inr (Or.inl ⟨h,hv,rfl⟩)
    · exact Or.inr (Or.inr ⟨h,hv,rfl⟩)

lemma exterior_edge (p q : Pairing n) (t : ThreeBox.Config)
    (v w : (Fin n ⊕ Fin 12) ⊕ Fin n) :
    s.attached p q t v w ↔ s.patch p q t (exteriorEquiv v) (exteriorEquiv w) := by
  rcases v with (i|v)|i <;> rcases w with (j|w)|j
  all_goals dsimp only [attached,Graph.Attached.wiring,patch,Patch.glued,exteriorEquiv,Equiv.coe_fn_mk]
  · rfl
  · simpa only [wiring,and_comm,and_left_comm,and_assoc] using (s.interface_old p q w i).symm
  · rw [s.boundary_old]
    change ((i=j ∧ i≠s.a ∧ i≠s.b ∧ i≠s.c) ∧ q.Occupied j) ↔
      i=j ∧ i≠s.a ∧ i≠s.b ∧ i≠s.c ∧ q.Occupied i
    constructor
    · rintro ⟨⟨rfl,ha,hb,hc⟩,hq⟩; exact ⟨rfl,ha,hb,hc,hq⟩
    · rintro ⟨rfl,ha,hb,hc,hq⟩; exact ⟨⟨rfl,ha,hb,hc⟩,hq⟩
  · exact (s.interface_old p q v j).symm
  · rfl
  · rw [s.boundary_new]
    exact (s.interface_new p q v j).symm
  · rw [s.boundary_old]
    change ((j=i ∧ j≠s.a ∧ j≠s.b ∧ j≠s.c) ∧ q.Occupied i) ↔
      j=i ∧ j≠s.a ∧ j≠s.b ∧ j≠s.c ∧ q.Occupied j
    constructor
    · rintro ⟨⟨rfl,ha,hb,hc⟩,hq⟩; exact ⟨rfl,ha,hb,hc,hq⟩
    · rintro ⟨rfl,ha,hb,hc,hq⟩; exact ⟨⟨rfl,ha,hb,hc⟩,hq⟩
  · rw [s.boundary_new]
    simpa only [and_comm,and_left_comm,and_assoc] using (s.interface_new p q w i).symm
  · rfl

end TriplePosition
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TriplePatch
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
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def exteriorPredicate (p q : Pairing n) (k : Fin 51) : Prop :=
  s.Outside p q ∧ ThreeBox.exteriorTest (s.exterior p q) s.interface (s.active p q)
    (output q) (reachTest q) k

def patchEquiv (p q : Pairing n) (t : ThreeBox.Config) :
    Graph.BoundaryEquiv (s.attached p q t) (s.patch p q t) Sum.inr
      (fun i => .inr (.inr i)) :=
  Graph.BoundaryEquiv.ofEquiv exteriorEquiv (s.exterior_edge p q t) (fun _ => rfl)

lemma patchTest_realizes (p q : Pairing n) (t : ThreeBox.Config) :
    ThreeBox.patchTest (s.exterior p q) s.interface (s.active p q) (output q) (reachTest q) t ↔
      ThreeBox.Compatible t ∧ (∀ i, s.active p q i ↔ ThreeBox.boundaryOccupied t i) ∧
        GraphRealizes (s.patch p q t) (fun i => .inr (.inr i)) q := by
  unfold ThreeBox.patchTest
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  constructor
  · rintro ⟨hd,hr⟩
    refine ⟨?_,hr⟩
    intro v w he
    obtain ⟨(x|(i|i)),hi,h⟩ := hd v w he
    · exact hi.elim
    · exact hi.elim
    · exact ⟨i,hi,h⟩
  · intro h
    refine ⟨?_,h.reach⟩
    intro v w he
    obtain ⟨i,hi,hr⟩ := h.no_loop v w he
    exact ⟨.inr (.inr i),hi,hr⟩

end TriplePosition

 

 

namespace Tile

lemma mirror_adj (t : Tile) (i j : Fin 4) :
    t.mirror.Adj i j ↔ t.Adj (mirrorPort i) (mirrorPort j) := by
  revert t i j
  decide

lemma mirror_occupied (t : Tile) (i : Fin 4) :
    t.mirror.Occupied i ↔ t.Occupied (mirrorPort i) := by
  unfold Occupied
  simp only [mirror_adj]
  exact mirrorPortEquiv.surjective.exists.symm

lemma weight_mirror {K : Type*} [One K] (w : Weights K) (t : Tile) :
    w.tile t.mirror=w.tile t := by cases t <;> rfl

end Tile

 

 

namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def mirrorWiring (p : Pairing n) (t : ThreeBox.Config) : (Fin n ⊕ Fin 12) → (Fin n ⊕ Fin 12) → Prop
  | .inl i,.inl j => p.Adj i j
  | .inr v,.inr w => ThreeBox.Adj t v w
  | .inl i,.inr v | .inr v,.inl i =>
      (i=s.c ∧ v=4 ∧ p.Occupied s.c) ∨
      (i=s.b ∧ v=0 ∧ p.Occupied s.b) ∨
      (i=s.a ∧ v=1 ∧ p.Occupied s.a)






instance mirrorWiring_symm (p : Pairing n) (t : ThreeBox.Config) : Std.Symm (s.mirrorWiring p t) := by
  constructor
  rintro (i|v) (j|w) h
  · exact Pairing.adj_symm h
  · exact h
  · exact h
  · exact (ThreeBox.adj_symm t).symm _ _ h

def mirrorSupport (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) : Prop :=
  if i=s.c then t.2.1.Occupied 2 else if i=s.b then t.2.2.Occupied 2
    else if i=s.a then t.2.2.Occupied 3 else p.Occupied i

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
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def mirrorAttached (p q : Pairing n) (t : ThreeBox.Config) :=
  Graph.Attached.wiring (s.mirrorWiring p t) s.mirrorBoundary q.Occupied

def mirrorPatch (p q : Pairing n) (t : ThreeBox.Config) :=
  Patch.glued (ThreeBox.Adj t) (s.mirrorExterior p q) ThreeBox.boundary s.mirrorInterface (s.mirrorActive p q)

lemma mirror_exterior_edge (p q : Pairing n) (t : ThreeBox.Config)
    (v w : (Fin n ⊕ Fin 12) ⊕ Fin n) :
    s.mirrorAttached p q t v w ↔ s.mirrorPatch p q t (mirrorExteriorEquiv v) (mirrorExteriorEquiv w) := by
  rcases v with (i|v)|i <;> rcases w with (j|w)|j
  all_goals dsimp only [mirrorAttached,Graph.Attached.wiring,mirrorPatch,Patch.glued,mirrorExteriorEquiv,Equiv.coe_fn_mk]
  · rfl
  · simpa only [mirrorWiring,and_comm,and_left_comm,and_assoc] using (s.mirror_interface_old p q w i).symm
  · rw [s.mirror_boundary_old]
    change ((i=j ∧ i≠s.c ∧ i≠s.b ∧ i≠s.a) ∧ q.Occupied j) ↔
      i=j ∧ i≠s.c ∧ i≠s.b ∧ i≠s.a ∧ q.Occupied i
    constructor
    · rintro ⟨⟨rfl,ha,hb,hc⟩,hq⟩; exact ⟨rfl,ha,hb,hc,hq⟩
    · rintro ⟨rfl,ha,hb,hc,hq⟩; exact ⟨⟨rfl,ha,hb,hc⟩,hq⟩
  · exact (s.mirror_interface_old p q v j).symm
  · rfl
  · rw [s.mirror_boundary_new]
    exact (s.mirror_interface_new p q v j).symm
  · rw [s.mirror_boundary_old]
    change ((j=i ∧ j≠s.c ∧ j≠s.b ∧ j≠s.a) ∧ q.Occupied i) ↔
      j=i ∧ j≠s.c ∧ j≠s.b ∧ j≠s.a ∧ q.Occupied j
    constructor
    · rintro ⟨⟨rfl,ha,hb,hc⟩,hq⟩; exact ⟨rfl,ha,hb,hc,hq⟩
    · rintro ⟨rfl,ha,hb,hc,hq⟩; exact ⟨⟨rfl,ha,hb,hc⟩,hq⟩
  · rw [s.mirror_boundary_new]
    simpa only [and_comm,and_left_comm,and_assoc] using (s.mirror_interface_new p q w i).symm
  · rfl

end TriplePosition
end
end CriticalStrip.Diagram





namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def mirrorExteriorPredicate (p q : Pairing n) (k : Fin 51) : Prop :=
  s.MirrorOutside p q ∧ ThreeBox.exteriorTest (s.mirrorExterior p q) s.mirrorInterface (s.mirrorActive p q)
    (output q) (reachTest q) k

def mirrorPatchEquiv (p q : Pairing n) (t : ThreeBox.Config) :
    Graph.BoundaryEquiv (s.mirrorAttached p q t) (s.mirrorPatch p q t) Sum.inr
      (fun i => .inr (.inr i)) :=
  Graph.BoundaryEquiv.ofEquiv mirrorExteriorEquiv (s.mirror_exterior_edge p q t) (fun _ => rfl)

lemma mirror_active_iff (p q : Pairing n) (t : ThreeBox.Config) :
    (∀ i, s.mirrorActive p q i ↔ ThreeBox.boundaryOccupied t i) ↔
      (p.Occupied s.c ↔ t.2.1.Occupied 0) ∧
      (p.Occupied s.b ↔ t.1.Occupied 0) ∧ (p.Occupied s.a ↔ t.1.Occupied 1) ∧
      (q.Occupied s.c ↔ t.2.1.Occupied 2) ∧
      (q.Occupied s.b ↔ t.2.2.Occupied 2) ∧ (q.Occupied s.a ↔ t.2.2.Occupied 3) := by
  simp [Fin.forall_fin_succ,mirrorActive,ThreeBox.boundaryOccupied,ThreeBox.boundary,
    ThreeBox.atRow,ThreeBox.row,ThreeBox.port]

lemma mirror_patchTest_realizes (p q : Pairing n) (t : ThreeBox.Config) :
    ThreeBox.patchTest (s.mirrorExterior p q) s.mirrorInterface (s.mirrorActive p q) (output q) (reachTest q) t ↔
      ThreeBox.Compatible t ∧ (∀ i, s.mirrorActive p q i ↔ ThreeBox.boundaryOccupied t i) ∧
        GraphRealizes (s.mirrorPatch p q t) (fun i => .inr (.inr i)) q := by
  unfold ThreeBox.patchTest
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  constructor
  · rintro ⟨hd,hr⟩
    refine ⟨?_,hr⟩
    intro v w he
    obtain ⟨(x|(i|i)),hi,h⟩ := hd v w he
    · exact hi.elim
    · exact hi.elim
    · exact ⟨i,hi,h⟩
  · intro h
    refine ⟨?_,h.reach⟩
    intro v w he
    obtain ⟨i,hi,hr⟩ := h.no_loop v w he
    exact ⟨.inr (.inr i),hi,hr⟩

end TriplePosition
end

 

 

noncomputable section
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

lemma mirror_active (p q : Pairing n) :
    s.mirrorActive p q=s.active p q ∘ ThreeBox.reverseSlots := by
  funext i; fin_cases i <;> rfl

lemma mirror_exterior (p q : Pairing n) : s.mirrorExterior p q=s.exterior p q := by
  funext x y
  rcases x with x|x <;> rcases y with y|y
  all_goals simp only [mirrorExterior,exterior]
  all_goals apply propext
  all_goals itauto

lemma mirror_outside (p q : Pairing n) : s.MirrorOutside p q ↔ s.Outside p q := by
  unfold MirrorOutside Outside
  constructor <;> intro h i ha hb hc
  · exact h i hc hb ha
  · exact h i hc hb ha

lemma mirror_predicate (p q : Pairing n) (k : Fin 51) :
    s.mirrorExteriorPredicate p q k ↔ s.exteriorPredicate p q (ThreeBox.mirrorIndex k) := by
  unfold mirrorExteriorPredicate exteriorPredicate
  rw [s.mirror_outside,s.mirror_interface,s.mirror_active,s.mirror_exterior]
  exact and_congr_right fun _ => ThreeBox.exteriorTest_mirror _ _ _ _ _ k

end TriplePosition

 

 

open scoped Classical
open Finset

variable {K : Type*} [CommRing K] {n : ℕ}

def tripleProgram (a b : Position n) (w₀ w₁ w₂ : Weights K) : Program n K :=
  .snoc (.snoc (.snoc .nil a w₀) b w₁) a w₂

namespace ThreeBox

lemma config_sum_mirror (f : Config → K) : ∑ t, f t = ∑ t, f (mirrorConfig t) :=
  (Equiv.sum_comp mirrorConfig f).symm

end ThreeBox

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
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

lemma omit_top_matrix (r : Fin (n+1))
    (M : Matrix (Pairing (n+1)) (Pairing (n+1)) K) (p : Pairing n) (q : Pairing (n+1)) :
    (functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) * M) q.padTop p.padBottom =
      (functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r)) *
        M.submatrix Pairing.padTop Pairing.padBottom) q p := by
  rw [Matrix.mul_apply,Matrix.mul_apply]
  symm
  apply Fintype.sum_of_injective Pairing.padTop (Pairing.map_injective Fin.castSuccOrderEmb)
  · intro t ht
    have hn : t.map (Fin.succAboveOrderEmb r.castSucc)≠q.padTop := by
      intro he
      exact ht (Pairing.omit_eq_padTop_exists r t q he)
    simp only [functionMatrix,optionMatrix,Function.comp_apply,Option.some.injEq,
      ite_eq_right hn,zero_mul]
  · intro t
    simp only [Matrix.submatrix_apply,functionMatrix,optionMatrix,Function.comp_apply,
      Option.some.injEq,←Pairing.omit_padTop]
    simp only [Pairing.padTop,(Pairing.map_injective Fin.castSuccOrderEmb).eq_iff]



end PartialColumn
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







def PolynomialBox {n:ℕ} (P:Polynomial (Laurent n)) (b:Fin n → ℕ) : Prop :=
  ∀ k,LaurentBox (P.coeff k) b

lemma PolynomialBox.mono {n:ℕ} {P:Polynomial (Laurent n)} {a b:Fin n → ℕ}
    (hP:PolynomialBox P a) (hab:∀ i,a i≤b i) : PolynomialBox P b := fun k => (hP k).mono hab
lemma PolynomialBox.C {n:ℕ} {f:Laurent n} {b:Fin n → ℕ} (hf:LaurentBox f b) :
    PolynomialBox (Polynomial.C f) b := by
  intro k
  by_cases hk:k=0
  · subst k; simpa only [Polynomial.coeff_C_zero] using hf
  · rw [Polynomial.coeff_C,ite_eq_right hk]
    exact LaurentBox.zero _
lemma PolynomialBox.X {n:ℕ} : PolynomialBox (Polynomial.X:Polynomial (Laurent n)) 0 := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs
  · exact LaurentBox.one
  · exact LaurentBox.zero _
lemma PolynomialBox.add {n:ℕ} {P Q:Polynomial (Laurent n)} {b:Fin n → ℕ}
    (hP:PolynomialBox P b) (hQ:PolynomialBox Q b) : PolynomialBox (P+Q) b := by
  intro k; rw [Polynomial.coeff_add]; exact (hP k).add (hQ k)
lemma PolynomialBox.sub {n:ℕ} {P Q:Polynomial (Laurent n)} {b:Fin n → ℕ}
    (hP:PolynomialBox P b) (hQ:PolynomialBox Q b) : PolynomialBox (P-Q) b := by
  intro k; rw [Polynomial.coeff_sub]; exact (hP k).sub (hQ k)
lemma PolynomialBox.mul {n:ℕ} {P Q:Polynomial (Laurent n)} {a b:Fin n → ℕ}
    (hP:PolynomialBox P a) (hQ:PolynomialBox Q b) : PolynomialBox (P*Q) (a+b) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact LaurentBox.sum _ _ _ (fun ij _ => (hP ij.1).mul (hQ ij.2))
lemma PolynomialBox.one {n:ℕ} : PolynomialBox (1:Polynomial (Laurent n)) 0 := by
  simpa only [Polynomial.C_1] using (PolynomialBox.C (n:=n) LaurentBox.one)

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

namespace HoneycombConfiguration
variable {N : ℕ} {b : BoundaryPort}



def weight (D : HoneycombConfiguration N b) : ℝ :=
  ∏ᶠ q : Cell, (physicalWeights (2*Diagram.lambda)).tile (D.tile q)

end HoneycombConfiguration
end
end CriticalStrip

end OAI
end


