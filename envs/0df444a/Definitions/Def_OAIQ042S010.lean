-- Prove2me | Definitions.Def_OAIQ042S010
-- name    : OAIQ042S010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:49:37.573998+00:00
-- url     : https://prove2.me/theorems/df76db6d-1a0c-4085-8d88-8d2d999a8ab2
-- title:
--   Definitions bundle OAIQ042S010 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 120 declarations of OpenAI's Lean: 5 definitions, 1 instance and 114 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.ThreeBox.ProfileCorrect`, `OAI.CriticalStrip.Diagram.TriplePosition.equiv`, `OAI.CriticalStrip.Diagram.TriplePosition.leftCircuit`, `OAI.CriticalStrip.Diagram.TriplePosition.mirrorEquiv`, `OAI.CriticalStrip.Diagram.tripleCircuit`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: [`StripMass_CollisionSubstitutions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/CollisionSubstitutions.lean), [`StripMass_LocalPadding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/LocalPadding.lean), [`StripMass_MirrorExterior`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/MirrorExterior.lean), [`StripMass_PhaseAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/PhaseAlgebra.lean), [`StripMass_SwapVacancy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/SwapVacancy.lean), [`StripMass_ThreeBoxBraidPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/ThreeBoxBraidPolynomial.lean), [`StripMass_ThreeBoxProfiles`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/ThreeBoxProfiles.lean), [`StripMass_ThreeBoxSplitPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/ThreeBoxSplitPolynomial.lean), [`StripMass_ThreeBoxWeights`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/ThreeBoxWeights.lean), [`StripMass_TopPadding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/TopPadding.lean), [`StripMass_TripleCircuit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/TripleCircuit.lean), [`StripMass_TriplePatch`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/StripMass/StripMass/TriplePatch.lean).
--
--   **Imports.** It imports the bundles `OAIQ042S005`, `OAIQ042S006` and `OAIQ042S008` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ042S013`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S005
import Definitions.Def_OAIQ042S006
import Definitions.Def_OAIQ042S008

section
-- module Solutions.OAIQ042_SS.StripMass_TopPadding
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Circuit.compactWiring_symm _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset

theorem realizes_snoc_top_iff {n : ℕ} (p q : Pairing n)
    (a : Tile) (t : Configuration n) :
    Realizes p.padTop q.padTop (Fin.snoc t a) ↔
      a = .vacant ∧ Realizes p q t := by
  constructor
  · intro h
    have ha : a = .vacant := by simpa using h.top_vacant
    subst a
    exact ⟨rfl, (realizes_padTop_iff p q t).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (realizes_padTop_iff p q t).mpr h

theorem column_mulVec_empty {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (v : Pairing n → 𝕜) :
    (column w).mulVec v (empty n) = v (empty n) := by
  classical
  simp [Matrix.mulVec, dotProduct, column_empty_row]

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxProfiles
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset



def ProfileCorrect (t : Config) : Prop :=
  match profile t with
  | none => ¬ Compatible t ∨ ¬ Clean t
  | some k => Compatible t ∧ Clean t ∧ BoundaryData t (diagram k)
instance profileCorrectDecidable (t : Config) : Decidable (ProfileCorrect t) := by
  unfold ProfileCorrect; split <;> infer_instance

theorem profileCorrect_0 (x y : Tile) : ProfileCorrect (.vacant,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_1 (x y : Tile) : ProfileCorrect (.vertical₀,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_2 (x y : Tile) : ProfileCorrect (.vertical₁,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_3 (x y : Tile) : ProfileCorrect (.diagonal₀,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_4 (x y : Tile) : ProfileCorrect (.diagonal₁,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_5 (x y : Tile) : ProfileCorrect (.cap,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_6 (x y : Tile) : ProfileCorrect (.cup,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_7 (x y : Tile) : ProfileCorrect (.verticalPair,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect_8 (x y : Tile) : ProfileCorrect (.capCup,x,y) := by
  cases x <;> cases y <;> decide

theorem profileCorrect (t : Config) : ProfileCorrect t := by
  rcases t with ⟨t,x,y⟩
  cases t
  · exact profileCorrect_0 x y
  · exact profileCorrect_1 x y
  · exact profileCorrect_2 x y
  · exact profileCorrect_3 x y
  · exact profileCorrect_4 x y
  · exact profileCorrect_5 x y
  · exact profileCorrect_6 x y
  · exact profileCorrect_7 x y
  · exact profileCorrect_8 x y



theorem profile_some_iff {t : Config} {k : Fin 51} :
    profile t = some k ↔ Realizes t (diagram k) := by
  have ht := profileCorrect t
  unfold ProfileCorrect at ht
  constructor
  · intro h
    rw [h] at ht
    exact realizes_iff_conditions.mpr ht
  · intro h
    cases he : profile t with
    | none =>
      rw [he] at ht
      obtain ⟨hc,hl,_⟩ := realizes_iff_conditions.mp h
      exact (ht.elim (fun hh => hh hc) (fun hh => hh hl)).elim
    | some j =>
      rw [he] at ht
      have hj := realizes_iff_conditions.mpr ht
      rw [realizes_unique hj h]

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxWeights
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
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

theorem fiber_correct_4 : ∀ t : Config, t ∈ fiber 4 ↔ profile t = some 4 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_5 : ∀ t : Config, t ∈ fiber 5 ↔ profile t = some 5 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_6 : ∀ t : Config, t ∈ fiber 6 ↔ profile t = some 6 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_7 : ∀ t : Config, t ∈ fiber 7 ↔ profile t = some 7 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_8 : ∀ t : Config, t ∈ fiber 8 ↔ profile t = some 8 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_9 : ∀ t : Config, t ∈ fiber 9 ↔ profile t = some 9 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_39 : ∀ t : Config, t ∈ fiber 39 ↔ profile t = some 39 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_40 : ∀ t : Config, t ∈ fiber 40 ↔ profile t = some 40 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_41 : ∀ t : Config, t ∈ fiber 41 ↔ profile t = some 41 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_42 : ∀ t : Config, t ∈ fiber 42 ↔ profile t = some 42 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_43 : ∀ t : Config, t ∈ fiber 43 ↔ profile t = some 43 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_44 : ∀ t : Config, t ∈ fiber 44 ↔ profile t = some 44 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_45 : ∀ t : Config, t ∈ fiber 45 ↔ profile t = some 45 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_46 : ∀ t : Config, t ∈ fiber 46 ↔ profile t = some 46 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_47 : ∀ t : Config, t ∈ fiber 47 ↔ profile t = some 47 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_48 : ∀ t : Config, t ∈ fiber 48 ↔ profile t = some 48 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_49 : ∀ t : Config, t ∈ fiber 49 ↔ profile t = some 49 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem fiber_correct_50 : ∀ t : Config, t ∈ fiber 50 ↔ profile t = some 50 := by
  rintro ⟨a,b,c⟩
  cases a <;> revert b c <;> decide

theorem mem_fiber_iff (k : Fin 51) (t : Config) : t ∈ fiber k ↔ profile t = some k := by
  fin_cases k
  · exact fiber_correct_0 t
  · exact fiber_correct_1 t
  · exact fiber_correct_2 t
  · exact fiber_correct_3 t
  · exact fiber_correct_4 t
  · exact fiber_correct_5 t
  · exact fiber_correct_6 t
  · exact fiber_correct_7 t
  · exact fiber_correct_8 t
  · exact fiber_correct_9 t
  · exact fiber_correct_10 t
  · exact fiber_correct_11 t
  · exact fiber_correct_12 t
  · exact fiber_correct_13 t
  · exact fiber_correct_14 t
  · exact fiber_correct_15 t
  · exact fiber_correct_16 t
  · exact fiber_correct_17 t
  · exact fiber_correct_18 t
  · exact fiber_correct_19 t
  · exact fiber_correct_20 t
  · exact fiber_correct_21 t
  · exact fiber_correct_22 t
  · exact fiber_correct_23 t
  · exact fiber_correct_24 t
  · exact fiber_correct_25 t
  · exact fiber_correct_26 t
  · exact fiber_correct_27 t
  · exact fiber_correct_28 t
  · exact fiber_correct_29 t
  · exact fiber_correct_30 t
  · exact fiber_correct_31 t
  · exact fiber_correct_32 t
  · exact fiber_correct_33 t
  · exact fiber_correct_34 t
  · exact fiber_correct_35 t
  · exact fiber_correct_36 t
  · exact fiber_correct_37 t
  · exact fiber_correct_38 t
  · exact fiber_correct_39 t
  · exact fiber_correct_40 t
  · exact fiber_correct_41 t
  · exact fiber_correct_42 t
  · exact fiber_correct_43 t
  · exact fiber_correct_44 t
  · exact fiber_correct_45 t
  · exact fiber_correct_46 t
  · exact fiber_correct_47 t
  · exact fiber_correct_48 t
  · exact fiber_correct_49 t
  · exact fiber_correct_50 t

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

theorem braid_numerator_1 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 1 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 31 := by
  rw [coefficient_1, coefficient_31]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_17 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 17 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 40 := by
  rw [coefficient_17, coefficient_40]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_38 hq]
  all_goals ring

theorem braid_numerator_19 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 19 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 37 := by
  rw [coefficient_19, coefficient_37]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_25 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 25 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 36 := by
  rw [coefficient_25, coefficient_36]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_31 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 31 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 1 := by
  rw [coefficient_31, coefficient_1]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_32 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 32 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 9 := by
  rw [coefficient_32, coefficient_9]
  simp only [tileNumerator]
  ring_nf

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxSplitPolynomial
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Patch.glued_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section






open Finset



theorem profile_exists_of_drains {B : Type*} {t : Config} (hc : Compatible t)
    (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop)
    (ha : ∀ i, active i ↔ boundaryOccupied t i) (out : B → Prop)
    (hd : Patch.drains (Patch.glued (Adj t) s boundary b active) (Patch.exteriorOutput out)) :
    ∃ k, profile t = some k := by
  have hl := ((Patch.drains_glued_iff (Adj t) s boundary b active out).mp hd).1
  have hclean : Clean t := by
    intro x y hxy
    obtain ⟨i,hi,hr⟩ := hl x y hxy
    exact ⟨i,(ha i).mp hi,(reach_iff_root_eq t hc x (boundary i)).mp hr⟩
  have hp := profileCorrect t
  unfold ProfileCorrect at hp
  cases he : profile t with
  | none =>
    rw [he] at hp
    exact (hp.elim (fun hh => hh hc) (fun hh => hh hclean)).elim
  | some k => exact ⟨k,rfl⟩



theorem patchTest_iff {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (out : B → Prop) (test : (B → B → Prop) → Prop)
    (t : Config) :
    patchTest s b active out test t ↔
      ∃ k, profile t = some k ∧ exteriorTest s b active out test k := by
  constructor
  · rintro ⟨hc,ha,hd,ht⟩
    obtain ⟨k,hk⟩ := profile_exists_of_drains hc s b active ha out hd
    have hr := profile_some_iff.mp hk
    refine ⟨k,hk,?_,(substitute_drains hr s b active ha out).mp hd,?_⟩
    · exact fun i => (ha i).trans (hr.occupied i)
    · have he : (fun x y => Relation.ReflTransGen
          (Patch.glued (Adj t) s boundary b active) (.inr x) (.inr y)) =
          Relation.ReflTransGen (diagramExterior (diagram k) s b active) := by
        funext x y
        exact propext (substitute_reach hr s b active x y)
      rwa [← he]
  · rintro ⟨k,hk,ha,hd,ht⟩
    have hr := profile_some_iff.mp hk
    have ha' : ∀ i, active i ↔ boundaryOccupied t i :=
      fun i => (ha i).trans (hr.occupied i).symm
    refine ⟨hr.compatible,ha',(substitute_drains hr s b active ha' out).mpr hd,?_⟩
    have he : (fun x y => Relation.ReflTransGen
        (Patch.glued (Adj t) s boundary b active) (.inr x) (.inr y)) =
        Relation.ReflTransGen (diagramExterior (diagram k) s b active) := by
      funext x y
      exact propext (substitute_reach hr s b active x y)
    simpa only [he] using ht

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhaseAlgebra
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.CompactGate.wiring_symm _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableActive _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableBadChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableCompatible _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableForestConditions _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableGoodChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableProfileChecks _root_.OAI.CriticalStrip.Diagram.CutPatch.instDecidableRelFinOfNatNatAdj _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.gateWiring_symm
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

theorem coefficient_eq_sumif {K : Type*} [CommSemiring K] (a b c : Tile → K) (k : Fin 51) :
    coefficient a b c k =
      ∑ t : Config, if profile t = some k then a t.1*b t.2.1*c t.2.2 else 0 := by
  unfold coefficient
  rw [← sum_filter]
  congr 1
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_fiber_iff]

 

theorem profile_partition {K : Type*} [CommSemiring K] (a b c : Tile → K)
    (P : Fin 51 → Prop) :
    (∑ t : Config, if ∃ k, profile t = some k ∧ P k
      then a t.1*b t.2.1*c t.2.2 else 0) =
    ∑ k : Fin 51, if P k then coefficient a b c k else 0 := by
  have hk (k : Fin 51) : (if P k then coefficient a b c k else 0) =
      ∑ t : Config, if profile t = some k ∧ P k then a t.1*b t.2.1*c t.2.2 else 0 := by
    rw [coefficient_eq_sumif]
    by_cases h : P k <;> simp [h]
  simp_rw [hk]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  cases he : profile t with
  | none => simp
  | some j =>
    simp only [Option.some.injEq]
    have hs (x : Fin 51) :
        (if j = x ∧ P x then a t.1*b t.2.1*c t.2.2 else 0) =
        if x = j then (if P j then a t.1*b t.2.1*c t.2.2 else 0) else 0 := by
      by_cases h : x = j
      · subst x; simp
      · simp [h, Ne.symm h]
    simp_rw [hs]
    simp



end





end CriticalStrip.Diagram.ThreeBox

 

 

namespace CriticalStrip.Diagram
noncomputable section


namespace ThreeBox

lemma coefficient_merge {n : ℕ} (z : SpectralField n)
    (hz : z≠0) (hL : torusL z≠0) (hL1 : torusL (constF n phase*z)≠0)
    (hL2 : torusL (constF n phase^2*z)≠0)
    (k : Fin 51) (h₂ : ¬ boundarySupport (diagram k) 2) :
    coefficient (mergeWeights (constF n phase)).tile
        (torusWeights (constF n phase^2*z)).tile (torusWeights z).tile k =
      coefficient (torusWeights (constF n phase*z)).tile swapWeights.tile
        (mergeWeights (constF n phase)).tile (mirrorIndex k) := by
  let q := constF n phase
  have hq := eighthRoot_two_add_one_ne_zero (constF_phase_eight n)
  have hN (v : SpectralField n) (hv : v≠0) (hLv : torusL v≠0) :
      (fun t => torusCommon v*(torusWeights v).tile t) =
        tileNumerator q (q^4) v := funext (torusWeights_cleared v hv hLv)
  have hz1 := mul_ne_zero (constF_phase_ne_zero n) hz
  have hz2 := mul_ne_zero (pow_ne_zero 2 (constF_phase_ne_zero n)) hz
  have h := split2_numerator q z (constF_phase_eight n) k h₂
  change coefficient (mergeNumerator q) _ _ k * torusCommon (q*z) =
    torusCommon (q^2*z)*torusCommon z *
      coefficient _ swapTile (mergeNumerator q) (mirrorIndex k) at h
  rw [←hN _ hz2 hL2,←hN _ hz hL,←hN _ hz1 hL1,
    ←mergeWeights_cleared q hq,coefficient_scale,coefficient_scale₁₃] at h
  have hc : (q^2+1)*torusCommon (q^2*z)*torusCommon z*torusCommon (q*z)≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hq (torusCommon_ne_zero _ hz2 hL2))
      (torusCommon_ne_zero _ hz hL)) (torusCommon_ne_zero _ hz1 hL1)
  apply mul_left_cancel₀ hc
  simp only [swapWeights_tile]
  calc
    _ = ((q^2+1)*torusCommon (q^2*z)*torusCommon z) *
        coefficient (mergeWeights q).tile (torusWeights (q^2*z)).tile (torusWeights z).tile k *
        torusCommon (q*z) := by ring
    _ = _ := h
    _ = _ := by ring

end ThreeBox






end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TripleCircuit
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.ThreeBox.boundaryDataDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.cleanDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.forestConditionsDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.profileCorrectDecidable _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm
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

lemma boundary_eq (t : ThreeBox.Config) (i : Fin n) :
    vertexEquiv ((s.rightCircuit t).compactBoundary i) = s.boundary i := by
  have hab := s.ab; have hbc := s.bc; have hac := s.ac
  by_cases ha : i=s.a <;> by_cases hb : i=s.b <;> by_cases hc : i=s.c <;>
    simp_all [rightCircuit, Circuit.compactBoundary, CompactGate.boundary, Position.gate, left,
      right, boundary] <;> rfl

lemma edge_0_0 (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) (j : Fin n) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inl i))) (.inl (.inl (.inl j))) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inl i)))) (vertexEquiv (.inl (.inl (.inl j)))) := by
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, wiring, vertex_old]

lemma edge_0_1 (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inl i))) (.inl (.inl (.inr w))) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inl i)))) (vertexEquiv (.inl (.inl (.inr w)))) := by
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, Position.gate, left, right, wiring, vertex_old, vertex_zero]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_0_2 (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inl i))) (.inl (.inr w)) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inl i)))) (vertexEquiv (.inl (.inr w))) := by
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_old,
    vertex_one, s.ab, s.ac]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_0_3 (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inl i))) (.inr w) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inl i)))) (vertexEquiv (.inr w)) := by
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_old,
    vertex_two, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_1_0 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (j : Fin n) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inr v))) (.inl (.inl (.inl j))) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inr v)))) (vertexEquiv (.inl (.inl (.inl j)))) := by
  fin_cases v
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, Position.gate, left, right, wiring, vertex_old, vertex_zero]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_1_1 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inr v))) (.inl (.inl (.inr w))) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inr v)))) (vertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, wiring, vertex_zero, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port,
    ThreeBox.atRow, ThreeBox.wireEdge]

lemma edge_1_2 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inr v))) (.inl (.inr w)) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inr v)))) (vertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_zero,
    vertex_one, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab, s.ac]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_1_3 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inl (.inr v))) (.inr w) ↔
      s.wiring p t (vertexEquiv (.inl (.inl (.inr v)))) (vertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_zero,
    vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_2_0 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (j : Fin n) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inr v)) (.inl (.inl (.inl j))) ↔
      s.wiring p t (vertexEquiv (.inl (.inr v))) (vertexEquiv (.inl (.inl (.inl j)))) := by
  fin_cases v
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_old,
    vertex_one, s.ab, s.ac]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_2_1 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inr v)) (.inl (.inl (.inr w))) ↔
      s.wiring p t (vertexEquiv (.inl (.inr v))) (vertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_zero,
    vertex_one, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab, s.ac]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_2_2 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inr v)) (.inl (.inr w)) ↔
      s.wiring p t (vertexEquiv (.inl (.inr v))) (vertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, wiring, vertex_one, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port,
    ThreeBox.atRow, ThreeBox.wireEdge]

lemma edge_2_3 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inl (.inr v)) (.inr w) ↔
      s.wiring p t (vertexEquiv (.inl (.inr v))) (vertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_one,
    vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_3_0 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (j : Fin n) :
    Circuit.compactWiring p (s.rightCircuit t) (.inr v) (.inl (.inl (.inl j))) ↔
      s.wiring p t (vertexEquiv (.inr v)) (vertexEquiv (.inl (.inl (.inl j)))) := by
  fin_cases v
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_old,
    vertex_two, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_3_1 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inr v) (.inl (.inl (.inr w))) ↔
      s.wiring p t (vertexEquiv (.inr v)) (vertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_zero,
    vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_3_2 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inr v) (.inl (.inr w)) ↔
      s.wiring p t (vertexEquiv (.inr v)) (vertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, wiring, vertex_one,
    vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow,
    ThreeBox.wireEdge, s.ab.symm, s.bc.symm, s.ac.symm]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma edge_3_3 (p : Pairing n) (t : ThreeBox.Config) (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.rightCircuit t) (.inr v) (.inr w) ↔
      s.wiring p t (vertexEquiv (.inr v)) (vertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [rightCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, wiring, vertex_two, ThreeBox.Adj, ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port,
    ThreeBox.atRow, ThreeBox.wireEdge]

lemma edge_iff (p : Pairing n) (t : ThreeBox.Config)
    (v w : (s.rightCircuit t).CompactVertex) :
    Circuit.compactWiring p (s.rightCircuit t) v w ↔ s.wiring p t (vertexEquiv v) (vertexEquiv w) := by
  rcases v with ((i|v)|v)|v <;> rcases w with ((j|w)|w)|w
  · exact s.edge_0_0 p t _ _
  · exact s.edge_0_1 p t _ _
  · exact s.edge_0_2 p t _ _
  · exact s.edge_0_3 p t _ _
  · exact s.edge_1_0 p t _ _
  · exact s.edge_1_1 p t _ _
  · exact s.edge_1_2 p t _ _
  · exact s.edge_1_3 p t _ _
  · exact s.edge_2_0 p t _ _
  · exact s.edge_2_1 p t _ _
  · exact s.edge_2_2 p t _ _
  · exact s.edge_2_3 p t _ _
  · exact s.edge_3_0 p t _ _
  · exact s.edge_3_1 p t _ _
  · exact s.edge_3_2 p t _ _
  · exact s.edge_3_3 p t _ _

end TriplePosition





namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def equiv (p : Pairing n) (t : ThreeBox.Config) :
    Graph.BoundaryEquiv (Circuit.compactWiring p (s.rightCircuit t)) (s.wiring p t)
      (s.rightCircuit t).compactBoundary s.boundary :=
  Graph.BoundaryEquiv.ofEquiv vertexEquiv (s.edge_iff p t) (s.boundary_eq t)

lemma boundary_injective : Function.Injective s.boundary := by
  let t : ThreeBox.Config := (.vacant,.vacant,.vacant)
  intro i j hij
  apply (s.rightCircuit t).compactBoundary_injective
  apply vertexEquiv.injective
  simpa only [s.boundary_eq] using hij

lemma boundary_used (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) :
    Graph.Used (s.wiring p t) (s.boundary i) ↔ s.support p t i := by
  rw [←s.circuit_support p t i,←Circuit.compact_boundary_used]
  constructor
  · intro h
    have hh := (s.equiv p t).inv_used _ h
    rwa [(s.equiv p t).inv_boundary] at hh
  · intro h
    have hh := (s.equiv p t).map_used _ h
    rwa [(s.equiv p t).map_boundary] at hh

lemma compatible_iff (p : Pairing n) (t : ThreeBox.Config) :
    Circuit.Compatible p (s.rightCircuit t) ↔
      ThreeBox.Compatible t ∧ (p.Occupied s.a ↔ t.2.1.Occupied 0) ∧
        (p.Occupied s.b ↔ t.1.Occupied 0) ∧ (p.Occupied s.c ↔ t.1.Occupied 1) := by
  simp only [rightCircuit, Circuit.Compatible, Circuit.support, Position.gate, left, right, s.ab,
    s.bc, s.ac, s.ab.symm, s.bc.symm, s.ac.symm, ThreeBox.Compatible, true_and]
  itauto

lemma eval_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.rightCircuit t)=some q ↔
      Circuit.Compatible p (s.rightCircuit t) ∧ GraphRealizes (s.wiring p t) s.boundary q := by
  rw [Circuit.compact_eval_iff,(s.equiv p t).realizes_iff]

end TriplePosition
end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TriplePatch
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm
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

lemma compatible_support_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.Compatible p (s.rightCircuit t) ∧ (∀ i, q.Occupied i ↔ s.support p t i) ↔
      s.Outside p q ∧ ThreeBox.Compatible t ∧
        (∀ i, s.active p q i ↔ ThreeBox.boundaryOccupied t i) := by
  rw [s.compatible_iff,s.active_iff]
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  constructor
  · rintro ⟨⟨hc,ha,hb,hc'⟩,hs⟩
    refine ⟨?_,hc,ha,hb,hc',?_,?_,?_⟩
    · intro i hia hib hic
      simpa only [support,ite_eq_right hia,ite_eq_right hib,ite_eq_right hic] using (hs i).symm
    · simpa [support] using hs s.a
    · simpa [support,hab.symm] using hs s.b
    · simpa [support,hac.symm,hbc.symm] using hs s.c
  · rintro ⟨ho,hc,ha,hb,hc',hqa,hqb,hqc⟩
    refine ⟨⟨hc,ha,hb,hc'⟩,?_⟩
    intro i
    by_cases hia : i=s.a
    · subst i; simpa [support] using hqa
    · by_cases hib : i=s.b
      · subst i; simpa [support,hia] using hqb
      · by_cases hic : i=s.c
        · subst i; simpa [support,hia,hib] using hqc
        · simpa only [support,ite_eq_right hia,ite_eq_right hib,ite_eq_right hic] using (ho i hia hib hic).symm

lemma eval_patch_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.rightCircuit t)=some q ↔
      s.Outside p q ∧ ThreeBox.patchTest (s.exterior p q) s.interface (s.active p q)
        (output q) (reachTest q) t := by
  rw [s.eval_iff,s.patchTest_realizes]
  constructor
  · rintro ⟨hc,hr⟩
    have hs : ∀ i, q.Occupied i ↔ s.support p t i := fun i =>
      (hr.boundary_used_iff s.boundary_injective i).symm.trans (s.boundary_used p t i)
    obtain ⟨ho,hc',ha⟩ := (s.compatible_support_iff p q t).mp ⟨hc,hs⟩
    refine ⟨ho,hc',ha,?_⟩
    apply (s.patchEquiv p q t).realizes_iff.mp
    exact (Graph.Attached.contraction (s.wiring p t) s.boundary q.Occupied
      (fun i => (hs i).trans (s.boundary_used p t i).symm) s.boundary_injective).realizes_inv hr
  · rintro ⟨ho,hc,ha,hr⟩
    obtain ⟨hc',hs⟩ := (s.compatible_support_iff p q t).mpr ⟨ho,hc,ha⟩
    refine ⟨hc',?_⟩
    apply (Graph.Attached.contraction (s.wiring p t) s.boundary q.Occupied
      (fun i => (hs i).trans (s.boundary_used p t i).symm) s.boundary_injective).realizes
    exact (s.patchEquiv p q t).realizes_iff.mpr hr

lemma eval_profile_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.rightCircuit t)=some q ↔
      ∃ k, ThreeBox.profile t=some k ∧ s.exteriorPredicate p q k := by
  rw [s.eval_patch_iff,ThreeBox.patchTest_iff]
  unfold exteriorPredicate
  constructor
  · rintro ⟨ho,k,hk,hp⟩; exact ⟨k,hk,ho,hp⟩
  · rintro ⟨k,hk,ho,hp⟩; exact ⟨ho,k,hk,hp⟩

end TriplePosition





namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def leftCircuit (t : ThreeBox.Config) : Circuit n :=
  .snoc (.snoc (.snoc .nil (s.left.gate t.1.mirror)) (s.right.gate t.2.1.mirror))
    (s.left.gate t.2.2.mirror)

lemma mirror_boundary_eq (t : ThreeBox.Config) (i : Fin n) :
    mirrorVertexEquiv ((s.leftCircuit t).compactBoundary i)=s.mirrorBoundary i := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : i=s.a <;> by_cases hb : i=s.b <;> by_cases hc : i=s.c <;>
    simp_all [leftCircuit, Circuit.compactBoundary, CompactGate.boundary, Position.gate, left,
      right, mirrorBoundary] <;> rfl

lemma mirror_edge_0_0 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin n) (w : Fin n) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inl v))) (.inl (.inl (.inl w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inl v)))) (mirrorVertexEquiv (.inl (.inl (.inl w)))) := by
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, mirrorWiring, mirror_vertex_old]

lemma mirror_edge_0_1 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inl v))) (.inl (.inl (.inr w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inl v)))) (mirrorVertexEquiv (.inl (.inl (.inr w)))) := by
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, Position.gate, left, right, mirrorWiring, mirror_vertex_old,
    mirror_vertex_zero, Tile.mirrorPort]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_0_2 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inl v))) (.inl (.inr w)) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inl v)))) (mirrorVertexEquiv (.inl (.inr w))) := by
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_old, mirror_vertex_one, Tile.mirror_occupied, Tile.mirrorPort, s.ab.symm,
    s.bc.symm, s.ac.symm]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_0_3 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin n) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inl v))) (.inr w) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inl v)))) (mirrorVertexEquiv (.inr w)) := by
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_old, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_1_0 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin n) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inr v))) (.inl (.inl (.inl w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inr v)))) (mirrorVertexEquiv (.inl (.inl (.inl w)))) := by
  fin_cases v
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, Position.gate, left, right, mirrorWiring, mirror_vertex_old,
    mirror_vertex_zero, Tile.mirrorPort]
  all_goals dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_1_1 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inr v))) (.inl (.inl (.inr w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inr v)))) (mirrorVertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, mirrorWiring, mirror_vertex_zero, Tile.mirror_adj, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge]
  all_goals simp [Tile.Adj]
  all_goals itauto

lemma mirror_edge_1_2 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inr v))) (.inl (.inr w)) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inr v)))) (mirrorVertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_zero, mirror_vertex_one, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab.symm,
    s.bc.symm, s.ac.symm]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_1_3 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inl (.inr v))) (.inr w) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inl (.inr v)))) (mirrorVertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_zero, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_2_0 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin n) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inr v)) (.inl (.inl (.inl w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inr v))) (mirrorVertexEquiv (.inl (.inl (.inl w)))) := by
  fin_cases v
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_old, mirror_vertex_one, Tile.mirror_occupied, Tile.mirrorPort, s.ab.symm,
    s.bc.symm, s.ac.symm]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_2_1 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inr v)) (.inl (.inl (.inr w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inr v))) (mirrorVertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_zero, mirror_vertex_one, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab.symm,
    s.bc.symm, s.ac.symm]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_2_2 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inr v)) (.inl (.inr w)) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inr v))) (mirrorVertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, mirrorWiring, mirror_vertex_one, Tile.mirror_adj, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge]
  all_goals simp [Tile.Adj]
  all_goals itauto

lemma mirror_edge_2_3 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inl (.inr v)) (.inr w) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inl (.inr v))) (mirrorVertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_one, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_3_0 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin n) :
    Circuit.compactWiring p (s.leftCircuit t) (.inr v) (.inl (.inl (.inl w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inr v)) (mirrorVertexEquiv (.inl (.inl (.inl w)))) := by
  fin_cases v
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_old, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_3_1 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inr v) (.inl (.inl (.inr w))) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inr v)) (mirrorVertexEquiv (.inl (.inl (.inr w)))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_zero, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_3_2 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inr v) (.inl (.inr w)) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inr v)) (mirrorVertexEquiv (.inl (.inr w))) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Circuit.support,
    Circuit.compactBoundary, CompactGate.boundary, Position.gate, left, right, mirrorWiring,
    mirror_vertex_one, mirror_vertex_two, Tile.mirror_occupied, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge, s.ab, s.ac]
  all_goals try dsimp only [Circuit.CompactVertex] at *
  all_goals simp

lemma mirror_edge_3_3 (p : Pairing n) (t : ThreeBox.Config)
    (v : Fin 4) (w : Fin 4) :
    Circuit.compactWiring p (s.leftCircuit t) (.inr v) (.inr w) ↔
      s.mirrorWiring p t (mirrorVertexEquiv (.inr v)) (mirrorVertexEquiv (.inr w)) := by
  fin_cases v
  all_goals fin_cases w
  all_goals simp [leftCircuit, Circuit.compactWiring, CompactGate.wiring, Position.gate, left,
    right, mirrorWiring, mirror_vertex_two, Tile.mirror_adj, Tile.mirrorPort, ThreeBox.Adj,
    ThreeBox.tileEdge, ThreeBox.row, ThreeBox.port, ThreeBox.atRow, ThreeBox.wireEdge]
  all_goals simp [Tile.Adj]
  all_goals itauto

lemma mirror_edge_iff (p : Pairing n) (t : ThreeBox.Config)
    (v w : (s.leftCircuit t).CompactVertex) :
    Circuit.compactWiring p (s.leftCircuit t) v w ↔
      s.mirrorWiring p t (mirrorVertexEquiv v) (mirrorVertexEquiv w) := by
  rcases v with ((v|v)|v)|v <;> rcases w with ((w|w)|w)|w
  · exact s.mirror_edge_0_0 p t v w
  · exact s.mirror_edge_0_1 p t v w
  · exact s.mirror_edge_0_2 p t v w
  · exact s.mirror_edge_0_3 p t v w
  · exact s.mirror_edge_1_0 p t v w
  · exact s.mirror_edge_1_1 p t v w
  · exact s.mirror_edge_1_2 p t v w
  · exact s.mirror_edge_1_3 p t v w
  · exact s.mirror_edge_2_0 p t v w
  · exact s.mirror_edge_2_1 p t v w
  · exact s.mirror_edge_2_2 p t v w
  · exact s.mirror_edge_2_3 p t v w
  · exact s.mirror_edge_3_0 p t v w
  · exact s.mirror_edge_3_1 p t v w
  · exact s.mirror_edge_3_2 p t v w
  · exact s.mirror_edge_3_3 p t v w

def mirrorEquiv (p : Pairing n) (t : ThreeBox.Config) :
    Graph.BoundaryEquiv (Circuit.compactWiring p (s.leftCircuit t)) (s.mirrorWiring p t)
      (s.leftCircuit t).compactBoundary s.mirrorBoundary :=
  Graph.BoundaryEquiv.ofEquiv mirrorVertexEquiv (s.mirror_edge_iff p t) (s.mirror_boundary_eq t)






lemma mirror_boundary_injective : Function.Injective s.mirrorBoundary := by
  let t : ThreeBox.Config := (.vacant,.vacant,.vacant)
  intro i j hij
  apply (s.leftCircuit t).compactBoundary_injective
  apply mirrorVertexEquiv.injective
  simpa only [s.mirror_boundary_eq] using hij

lemma mirror_circuit_support (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) :
    Circuit.support p (s.leftCircuit t) i ↔ s.mirrorSupport p t i := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : i=s.c <;> by_cases hb : i=s.b <;> by_cases hc : i=s.a <;>
    simp_all [leftCircuit,Circuit.support,Position.gate,left,right,mirrorSupport,Tile.mirror_occupied,Tile.mirrorPort]

lemma mirror_boundary_used (p : Pairing n) (t : ThreeBox.Config) (i : Fin n) :
    Graph.Used (s.mirrorWiring p t) (s.mirrorBoundary i) ↔ s.mirrorSupport p t i := by
  rw [←s.mirror_circuit_support p t i,←Circuit.compact_boundary_used]
  constructor
  · intro h
    have hh := (s.mirrorEquiv p t).inv_used _ h
    rwa [(s.mirrorEquiv p t).inv_boundary] at hh
  · intro h
    have hh := (s.mirrorEquiv p t).map_used _ h
    rwa [(s.mirrorEquiv p t).map_boundary] at hh

lemma mirror_compatible_iff (p : Pairing n) (t : ThreeBox.Config) :
    Circuit.Compatible p (s.leftCircuit t) ↔
      ThreeBox.Compatible t ∧ (p.Occupied s.c ↔ t.2.1.Occupied 0) ∧
        (p.Occupied s.b ↔ t.1.Occupied 0) ∧ (p.Occupied s.a ↔ t.1.Occupied 1) := by
  simp only [leftCircuit, Circuit.Compatible, Circuit.support, Position.gate, left, right, s.ab,
    s.bc, s.ac, s.ab.symm, s.bc.symm, s.ac.symm, ThreeBox.Compatible, true_and,
    Tile.mirror_occupied, Tile.mirrorPort, Matrix.cons_val_zero]
  itauto

lemma mirror_eval_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.leftCircuit t)=some q ↔
      Circuit.Compatible p (s.leftCircuit t) ∧ GraphRealizes (s.mirrorWiring p t) s.mirrorBoundary q := by
  rw [Circuit.compact_eval_iff,(s.mirrorEquiv p t).realizes_iff]

end TriplePosition
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MirrorExterior
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.FreshGate.Ports.wiring_symm _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm
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

lemma mirror_compatible_support_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.Compatible p (s.leftCircuit t) ∧ (∀ i, q.Occupied i ↔ s.mirrorSupport p t i) ↔
      s.MirrorOutside p q ∧ ThreeBox.Compatible t ∧
        (∀ i, s.mirrorActive p q i ↔ ThreeBox.boundaryOccupied t i) := by
  rw [s.mirror_compatible_iff,s.mirror_active_iff]
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  constructor
  · rintro ⟨⟨hc,ha,hb,hc'⟩,hs⟩
    refine ⟨?_,hc,ha,hb,hc',?_,?_,?_⟩
    · intro i hia hib hic
      simpa only [mirrorSupport,ite_eq_right hia,ite_eq_right hib,ite_eq_right hic] using (hs i).symm
    · simpa [mirrorSupport] using hs s.c
    · simpa [mirrorSupport,s.ab,s.bc,s.ac,s.ab.symm,s.bc.symm,s.ac.symm] using hs s.b
    · simpa [mirrorSupport,s.ab,s.bc,s.ac,s.ab.symm,s.bc.symm,s.ac.symm] using hs s.a
  · rintro ⟨ho,hc,ha,hb,hc',hqa,hqb,hqc⟩
    refine ⟨⟨hc,ha,hb,hc'⟩,?_⟩
    intro i
    by_cases hia : i=s.c
    · subst i; simpa [mirrorSupport] using hqa
    · by_cases hib : i=s.b
      · subst i; simpa [mirrorSupport,hia] using hqb
      · by_cases hic : i=s.a
        · subst i; simpa [mirrorSupport,hia,hib] using hqc
        · simpa only [mirrorSupport,ite_eq_right hia,ite_eq_right hib,ite_eq_right hic] using (ho i hia hib hic).symm

lemma mirror_eval_patch_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.leftCircuit t)=some q ↔
      s.MirrorOutside p q ∧ ThreeBox.patchTest (s.mirrorExterior p q) s.mirrorInterface (s.mirrorActive p q)
        (output q) (reachTest q) t := by
  rw [s.mirror_eval_iff,s.mirror_patchTest_realizes]
  constructor
  · rintro ⟨hc,hr⟩
    have hs : ∀ i, q.Occupied i ↔ s.mirrorSupport p t i := fun i =>
      (hr.boundary_used_iff s.mirror_boundary_injective i).symm.trans (s.mirror_boundary_used p t i)
    obtain ⟨ho,hc',ha⟩ := (s.mirror_compatible_support_iff p q t).mp ⟨hc,hs⟩
    refine ⟨ho,hc',ha,?_⟩
    apply (s.mirrorPatchEquiv p q t).realizes_iff.mp
    exact (Graph.Attached.contraction (s.mirrorWiring p t) s.mirrorBoundary q.Occupied
      (fun i => (hs i).trans (s.mirror_boundary_used p t i).symm) s.mirror_boundary_injective).realizes_inv hr
  · rintro ⟨ho,hc,ha,hr⟩
    obtain ⟨hc',hs⟩ := (s.mirror_compatible_support_iff p q t).mpr ⟨ho,hc,ha⟩
    refine ⟨hc',?_⟩
    apply (Graph.Attached.contraction (s.mirrorWiring p t) s.mirrorBoundary q.Occupied
      (fun i => (hs i).trans (s.mirror_boundary_used p t i).symm) s.mirror_boundary_injective).realizes
    exact (s.mirrorPatchEquiv p q t).realizes_iff.mpr hr

lemma mirror_eval_profile_iff (p q : Pairing n) (t : ThreeBox.Config) :
    Circuit.eval p (s.leftCircuit t)=some q ↔
      ∃ k, ThreeBox.profile t=some k ∧ s.mirrorExteriorPredicate p q k := by
  rw [s.mirror_eval_patch_iff,ThreeBox.patchTest_iff]
  unfold mirrorExteriorPredicate
  constructor
  · rintro ⟨ho,k,hk,hp⟩; exact ⟨k,hk,ho,hp⟩
  · rintro ⟨k,hk,ho,hp⟩; exact ⟨ho,k,hk,hp⟩

end TriplePosition
end

 

 

noncomputable section





open scoped Classical
open Finset

variable {K : Type*} [CommRing K] {n : ℕ}

def tripleCircuit (a b : Position n) (t : ThreeBox.Config) : Circuit n :=
  .snoc (.snoc (.snoc .nil (a.gate t.1)) (b.gate t.2.1)) (a.gate t.2.2)

lemma triple_expansion (a b : Position n) (w₀ w₁ w₂ : Weights K) (p q : Pairing n) :
    (localR a w₂ * localR b w₁ * localR a w₀) q p =
      ∑ t : ThreeBox.Config, if Circuit.eval p (tripleCircuit a b t)=some q
        then w₀.tile t.1*w₁.tile t.2.1*w₂.tile t.2.2 else 0 := by
  have h := (tripleProgram a b w₀ w₁ w₂).matrix_apply q p
  simp only [tripleProgram,Program.matrix,mul_one] at h
  rw [Matrix.mul_assoc]
  rw [h]
  change (∑ x : ((PUnit × Tile) × Tile) × Tile, _) = ∑ t : Tile × (Tile × Tile), _
  simp only [Fintype.sum_prod_type,Fintype.sum_unique,Program.weight,Program.circuit,
    one_mul,tripleCircuit]
  rfl

lemma triple_expansion_mirror (a b : Position n) (w₀ w₁ w₂ : Weights K) (p q : Pairing n) :
    (localR a w₂ * localR b w₁ * localR a w₀) q p =
      ∑ t : ThreeBox.Config, if Circuit.eval p (tripleCircuit a b (ThreeBox.mirrorConfig t))=some q
        then w₀.tile t.1*w₁.tile t.2.1*w₂.tile t.2.2 else 0 := by
  rw [triple_expansion,ThreeBox.config_sum_mirror]
  apply sum_congr rfl
  intro t _
  simp only [ThreeBox.mirrorConfig, Equiv.prodCongr, Tile.mirrorEquiv]
  change (if Circuit.eval p (tripleCircuit a b (ThreeBox.mirrorConfig t))=some q then
      w₀.tile t.1.mirror*w₁.tile t.2.1.mirror*w₂.tile t.2.2.mirror else 0) = _
  simp only [Tile.weight_mirror]
  rfl

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LocalPadding
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

lemma exchange_program (w v : Fin n → Weights K) (r : ℕ) (hr : r+2≤n)
    (L R : Matrix (Pairing (n+1)) (Pairing (n+1)) K)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (hlow : ∀ i : Fin n, i.val < r → localR (position i) (w i)*R=R*localR (position i) (w i))
    (hhigh : ∀ i : Fin n, r + 1 < i.val → localR (position i) (w i)*L=L*localR (position i) (w i))
    (hyb : localR (position ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
        localR (position ⟨r,by omega⟩) (w ⟨r,by omega⟩) * R =
      L * localR (position ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
        localR (position ⟨r,by omega⟩) (v ⟨r,by omega⟩)) :
    (program w n le_rfl).matrix *R=L*(program v n le_rfl).matrix := by
  have hbase : (program w (r+2) hr).matrix*R=L*(program v (r+2) hr).matrix := by
    have hcomm := program_commute w r (by omega) R hlow
    have heq := program_congr w v r (by omega) (fun i hi => he i (by omega) (by omega))
    change (localR (position ⟨r+1,by omega⟩) (w ⟨r+1,by omega⟩) *
      (localR (position ⟨r,by omega⟩) (w ⟨r,by omega⟩) * (program w r _).matrix))*R =
      L*(localR (position ⟨r+1,by omega⟩) (v ⟨r+1,by omega⟩) *
      (localR (position ⟨r,by omega⟩) (v ⟨r,by omega⟩) * (program v r _).matrix))
    rw [Matrix.mul_assoc,Matrix.mul_assoc,hcomm,←Matrix.mul_assoc,
      ←Matrix.mul_assoc,hyb,heq]
    simp only [Matrix.mul_assoc]
  have hstep (k : ℕ) (hkr : r+2≤k) (hkn : k≤n) :
      (program w k hkn).matrix*R=L*(program v k hkn).matrix := by
    induction k,hkr using Nat.le_induction with
    | base => exact hbase
    | succ k hk ih =>
      have hk' : k<n := by omega
      change (localR (position ⟨k,hk'⟩) (w ⟨k,hk'⟩) * (program w k _).matrix)*R =
        L*(localR (position ⟨k,hk'⟩) (v ⟨k,hk'⟩)*(program v k _).matrix)
      rw [Matrix.mul_assoc,ih (by omega),←Matrix.mul_assoc,hhigh ⟨k,hk'⟩ (by dsimp; omega),
        he ⟨k,hk'⟩ (by dsimp; omega) (by dsimp; omega),Matrix.mul_assoc]
  exact hstep n hr le_rfl

end PartialColumn

 

 

open scoped Classical
namespace TriplePosition
variable {n m : ℕ} (s : TriplePosition n)

 

lemma coefficient_replacement {K : Type*} [CommRing K]
    (a b c d e f : Weights K) (p q : Pairing n)
    (h : ∀ k, s.exteriorPredicate p q k →
      ThreeBox.coefficient a.tile b.tile c.tile k =
        ThreeBox.coefficient d.tile e.tile f.tile (ThreeBox.mirrorIndex k)) :
    (localR s.right c * localR s.left b * localR s.right a) q p =
      (localR s.left f * localR s.right e * localR s.left d) q p := by
  rw [triple_expansion,triple_expansion_mirror]
  change (∑ t : ThreeBox.Config, if Circuit.eval p (s.rightCircuit t)=some q
    then a.tile t.1*b.tile t.2.1*c.tile t.2.2 else 0) =
    (∑ t : ThreeBox.Config, if Circuit.eval p (s.leftCircuit t)=some q
    then d.tile t.1*e.tile t.2.1*f.tile t.2.2 else 0)
  simp_rw [s.eval_profile_iff,s.mirror_eval_profile_iff,s.mirror_predicate]
  rw [ThreeBox.profile_partition,ThreeBox.profile_partition]
  let e' : Fin 51 ≃ Fin 51 := ⟨ThreeBox.mirrorIndex,ThreeBox.mirrorIndex,
    ThreeBox.mirrorIndex_involutive,ThreeBox.mirrorIndex_involutive⟩
  have he (k : Fin 51) : e' k = ThreeBox.mirrorIndex k := rfl
  refine Fintype.sum_equiv e' _ _ ?_
  intro k
  change (if s.exteriorPredicate p q k then _ else 0) =
    (if s.exteriorPredicate p q (ThreeBox.mirrorIndex (ThreeBox.mirrorIndex k)) then _ else 0)
  rw [ThreeBox.mirrorIndex_involutive]
  by_cases hk : s.exteriorPredicate p q k
  · simpa only [ite_eq_left hk, he] using h k hk
  · simp only [ite_eq_right hk]

 

theorem deletion (z : SpectralField m) (hz : z≠0) (hL : torusL z≠0)
    (hL3 : torusL (constF m phase^3*z)≠0) (p q : Pairing n)
    (hb : ¬p.Occupied s.b) (hc : ¬p.Occupied s.c) :
    (localR s.right (torusWeights z) * localR s.left (torusWeights (constF m phase^3*z)) *
        localR s.right deletionWeights : Matrix (Pairing n) (Pairing n) (SpectralField m)) q p =
      (localR s.left deletionWeights * localR s.right swapWeights *
        localR s.left swapWeights : Matrix (Pairing n) (Pairing n) (SpectralField m)) q p := by
  apply s.coefficient_replacement
  intro k hk
  apply ThreeBox.coefficient_deletion z hz hL hL3 k
  · intro hi; exact hb ((hk.2.1 1).mpr hi)
  · intro hi; exact hc ((hk.2.1 2).mpr hi)

 

theorem merge (z : SpectralField m) (hz : z≠0) (hL : torusL z≠0)
    (hL1 : torusL (constF m phase*z)≠0) (hL2 : torusL (constF m phase^2*z)≠0)
    (p q : Pairing n) (hc : ¬p.Occupied s.c) :
    (localR s.right (torusWeights z) * localR s.left (torusWeights (constF m phase^2*z)) *
        localR s.right (mergeWeights (constF m phase)) : Matrix (Pairing n) (Pairing n) (SpectralField m)) q p =
      (localR s.left (mergeWeights (constF m phase)) * localR s.right swapWeights *
        localR s.left (torusWeights (constF m phase*z)) : Matrix (Pairing n) (Pairing n) (SpectralField m)) q p := by
  apply s.coefficient_replacement
  intro k hk
  apply ThreeBox.coefficient_merge z hz hL hL1 hL2 k
  intro hi; exact hc ((hk.2.1 2).mpr hi)

end TriplePosition
end





noncomputable section
open scoped Classical
namespace PartialColumn
variable {n m : ℕ}


theorem column_deletion (r : ℕ) (hr : r+2≤n)
    (w v : Fin n → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL3 : torusL (constF m phase^3*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^3*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z)
    (hv₀ : v ⟨r,by omega⟩=swapWeights) (hv₁ : v ⟨r+1,by omega⟩=swapWeights)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (p q : Pairing n) (hb : ¬p.Occupied ⟨r,by omega⟩)
    (hc : ¬p.Occupied ⟨r+1,by omega⟩) :
    ((column w * localR (rowPosition r hr) deletionWeights :
      Matrix (Pairing n) (Pairing n) (SpectralField m))) q p =
    ((localR (rowPosition r hr) deletionWeights * column v :
      Matrix (Pairing n) (Pairing n) (SpectralField m))) q p := by
  apply column_restricted_train w v r hr deletionWeights p
    (fun t => ¬t.Occupied ⟨r+1,by omega⟩ ∧ ¬t.Occupied ⟨r+2,by omega⟩) _ he _ q
  · intro t ht
    by_cases h₁ : t.Occupied ⟨r+1,by omega⟩
    · apply program_zero_above w r (by omega) p.padBottom t ⟨r+1,by omega⟩ (by simp)
      intro hh
      exact hb ((Pairing.padBottom_occupied_succ p ⟨r,by omega⟩).mp (hh.mp h₁))
    · have h₂ : t.Occupied ⟨r+2,by omega⟩ := Classical.not_not.mp (fun h₂ => ht ⟨h₁,h₂⟩)
      apply program_zero_above w r (by omega) p.padBottom t ⟨r+2,by omega⟩ (by simp)
      intro hh
      exact hc ((Pairing.padBottom_occupied_succ p ⟨r+1,by omega⟩).mp (hh.mp h₂))
  · intro t ht s
    rw [hw₀,hw₁,hv₀,hv₁]
    simpa only [rowTriple,TriplePosition.left,TriplePosition.right,position,rowPosition,
      Position.padTop,Position.padBottom,Fin.castSucc_mk,Fin.succ_mk,Nat.add_assoc]
      using (rowTriple r hr).deletion z hz hL hL3 t s ht.1 ht.2

 
theorem column_merge (r : ℕ) (hr : r+2≤n)
    (w v : Fin n → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL1 : torusL (constF m phase*z)≠0)
    (hL2 : torusL (constF m phase^2*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^2*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z)
    (hv₀ : v ⟨r,by omega⟩=torusWeights (constF m phase*z))
    (hv₁ : v ⟨r+1,by omega⟩=swapWeights)
    (he : ∀ i : Fin n, i.val≠r → i.val≠r+1 → w i=v i)
    (p q : Pairing n) (hc : ¬p.Occupied ⟨r+1,by omega⟩) :
    ((column w * localR (rowPosition r hr) (mergeWeights (constF m phase)) :
      Matrix (Pairing n) (Pairing n) (SpectralField m))) q p =
    ((localR (rowPosition r hr) (mergeWeights (constF m phase)) * column v :
      Matrix (Pairing n) (Pairing n) (SpectralField m))) q p := by
  apply column_restricted_train w v r hr (mergeWeights (constF m phase)) p
    (fun t => ¬t.Occupied ⟨r+2,by omega⟩) _ he _ q
  · intro t ht
    apply program_zero_above w r (by omega) p.padBottom t ⟨r+2,by omega⟩ (by simp)
    intro hh
    exact hc ((Pairing.padBottom_occupied_succ p ⟨r+1,by omega⟩).mp (hh.mp (Classical.not_not.mp ht)))
  · intro t ht s
    rw [hw₀,hw₁,hv₀,hv₁]
    simpa only [rowTriple,TriplePosition.left,TriplePosition.right,position,rowPosition,
      Position.padTop,Position.padBottom,Fin.castSucc_mk,Fin.succ_mk,Nat.add_assoc]
      using (rowTriple r hr).merge z hz hL hL1 hL2 t s ht

end PartialColumn
end

 

 

noncomputable section
open scoped Classical
open Finset

variable {K : Type*} [CommRing K]

lemma localR_natural {n m : ℕ} (f : Fin n ↪o Fin m)
    (a : Position n) (b : Position m) (ha : f a.left=b.left) (hb : f a.right=b.right)
    (w : Weights K) :
    localR b w * functionMatrix (K := K) (Pairing.map f) = functionMatrix (K := K) (Pairing.map f) * localR a w := by
  simp only [localR,Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul]
  apply sum_congr rfl
  intro t _
  congr 1
  apply optionMatrix_natural
  intro p
  simpa only [ha,hb] using p.map_tileStep f a.left a.right a.adjacent (by rw [ha,hb]; exact b.adjacent) t

end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SwapVacancy
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm
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

variable {K : Type*} [CommRing K]
lemma localR_swap_vacant {n : ℕ} (a : Position n) (p q : Pairing n)
    (hb : ¬p.Occupied a.right) :
    (localR a (swapWeights : Weights K)) q p =
      if p.moveIntoVacancy a.left a.right a.adjacent hb=q then 1 else 0 := by
  simp only [localR,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  by_cases ha : p.Occupied a.left
  · rw [sum_eq_single .diagonal₀]
    · simp [swapWeights,Weights.tile,optionMatrix,Pairing.tileStep,ha,hb]
    · intro t _ ht
      cases t <;> simp_all [swapWeights,Weights.tile,optionMatrix,Pairing.tileStep]
    · simp
  · rw [Pairing.moveIntoVacancy_eq_self p _ _ a.adjacent ha hb]
    rw [sum_eq_single .vacant]
    · simp [Weights.tile,optionMatrix,Pairing.tileStep,ha,hb]
    · intro t _ ht
      cases t <;> simp_all [swapWeights,Weights.tile,optionMatrix,Pairing.tileStep]
    · simp

lemma localR_swap_omit {n : ℕ} (a : Position (n+1)) :
    localR a (swapWeights : Weights K) *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.right)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.left)) := by
  ext q p
  rw [mul_functionMatrix,localR_swap_vacant _ _ _ (p.map_not_occupied_omit a.right),
    Pairing.moveIntoVacancy_map_omit]
  simp [functionMatrix,optionMatrix]

end

 

 

noncomputable section
open scoped Classical
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

lemma insert_before_gate (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i) (i : Fin n) (hi : i.val < r.val) :
    localR (position i.castSucc) (w i.castSucc) *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) *
        localR (position i) (v i) := by
  have hiw := hw i
  rw [Fin.succAbove_of_castSucc_lt r i hi] at hiw
  rw [hiw]
  apply localR_natural
  · change r.succ.succAbove i.castSucc=i.castSucc.castSucc
    apply Fin.succAbove_of_castSucc_lt
    change i.val < r.val+1
    omega
  · change r.succ.succAbove i.succ=i.castSucc.succ
    rw [Fin.succAbove_of_castSucc_lt _ _ (by change i.val+1 < r.val+1; omega)]
    exact Fin.ext rfl

lemma insert_after_gate (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i) (i : Fin n) (hi : r.val ≤ i.val) :
    localR (position i.succ) (w i.succ) *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) *
        localR (position i) (v i) := by
  have hiw := hw i
  rw [Fin.succAbove_of_le_castSucc r i hi] at hiw
  rw [hiw]
  apply localR_natural
  · change r.castSucc.succAbove i.castSucc=i.succ.castSucc
    rw [Fin.succAbove_of_le_castSucc _ _ (by change r.val ≤ i.val; exact hi)]
    exact Fin.ext rfl
  · change r.castSucc.succAbove i.succ=i.succ.succ
    apply Fin.succAbove_of_le_castSucc
    change r.val ≤ i.val+1
    omega

lemma insert_before_program (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i)
    (k : ℕ) (hk : k ≤ r.val) :
    (program w k (by omega)).matrix *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) *
        (program v k (by omega)).matrix := by
  induction k with
  | zero => change 1*_=_*1; simp
  | succ k ih =>
    have hkn : k<n := by have:=r.isLt; omega
    change (localR (position (n:=n+1) ⟨k,by omega⟩) (w ⟨k,by omega⟩) *
      (program w k _).matrix)*_ = _ *
      (localR (position (n:=n) ⟨k,hkn⟩) (v ⟨k,hkn⟩) * (program v k _).matrix)
    have hgate := insert_before_gate r w v hw ⟨k,hkn⟩ (by change k < r.val; omega)
    simp only [Fin.castSucc_mk] at hgate
    rw [Matrix.mul_assoc,ih (by omega),←Matrix.mul_assoc,hgate,Matrix.mul_assoc]

lemma insert_after_program (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i) (hr : w r=swapWeights)
    (k : ℕ) (hk : r.val ≤ k) (hkn : k≤n) :
    (program w (k+1) (by omega)).matrix *
        functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) *
        (program v k hkn).matrix := by
  induction k,hk using Nat.le_induction with
  | base =>
    rw [program,Program.matrix]
    have hrr : (⟨r.val,by omega⟩ : Fin (n+1))=r := Fin.ext rfl
    rw [hrr]
    rw [Matrix.mul_assoc,insert_before_program r w v hw r.val le_rfl,←Matrix.mul_assoc,hr]
    have hs := localR_swap_omit (K:=K) (position r)
    change localR (position r) swapWeights *
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.succ)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) at hs
    rw [hs]
  | succ k hk ih =>
    have hi : k<n := by omega
    change (localR (position (n:=n+1) ⟨k+1,by omega⟩) (w ⟨k+1,by omega⟩) *
      (program w (k+1) _).matrix)*_ = _ *
      (localR (position (n:=n) ⟨k,hi⟩) (v ⟨k,hi⟩) * (program v k _).matrix)
    have hgate := insert_after_gate r w v hw ⟨k,hi⟩ hk
    simp only [Fin.succ_mk] at hgate
    rw [Matrix.mul_assoc,ih (by omega),←Matrix.mul_assoc,hgate,Matrix.mul_assoc]

end PartialColumn





end

 

 

noncomputable section
open scoped Classical
open Finset
namespace PartialColumn
variable {K : Type*} [CommRing K] {n : ℕ}

lemma program_column_all (w : Fin n → Weights K) (p q : Pairing n) :
    (program w n le_rfl).matrix q.padTop p.padBottom=column w q p := by
  by_cases hn : 0<n
  · exact program_column hn w p q
  · have h : n=0 := by omega
    subst n
    rw [p.eq_empty_of_le_one (by omega),q.eq_empty_of_le_one (by omega),column_empty_row]
    simp only [ite_true]
    change (1 : Matrix (Pairing 1) (Pairing 1) K) (empty 0).padTop (empty 0).padBottom=1
    rw [show (empty 0).padTop=(empty 0).padBottom by rw [Pairing.padTop,Pairing.padBottom,
      Pairing.map_empty,Pairing.map_empty]]
    exact Matrix.one_apply_eq _



theorem column_insert_swap (r : Fin (n+1)) (w : Fin (n+1) → Weights K)
    (v : Fin n → Weights K) (hw : ∀ i, w (r.succAbove i)=v i) (hr : w r=swapWeights) :
    column w * functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r)) =
      functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r)) * column v := by
  have H := insert_after_program r w v hw hr n (by omega) le_rfl
  have he : (program v n le_rfl).matrix.submatrix Pairing.padTop Pairing.padBottom=column v := by
    ext q p; exact program_column_all v p q
  ext q p
  have hh:=congrArg (fun M => M q.padTop p.padBottom) H
  rw [mul_functionMatrix,←Pairing.omit_padBottom,program_column_all,omit_top_matrix,he] at hh
  rw [mul_functionMatrix]
  exact hh

end PartialColumn
end

 

 

noncomputable section
open scoped Classical
namespace PartialColumn
variable {n m : ℕ}



theorem column_merge_intertwiner (r : ℕ) (hr : r+2≤n+1)
    (w : Fin (n+1) → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL1 : torusL (constF m phase*z)≠0)
    (hL2 : torusL (constF m phase^2*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^2*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z) :
    let j : Fin (n+1) := ⟨r+1,by omega⟩
    let v := twoRows w r (torusWeights (constF m phase*z)) swapWeights
    let E := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j))
    let S := localR (rowPosition r hr) (mergeWeights (constF m phase))
    column w * (S*E) = (S*E) * column (fun i => v (j.succAbove i)) := by
  dsimp only
  let j : Fin (n+1) := ⟨r+1,by omega⟩
  let v := twoRows w r (torusWeights (constF m phase*z)) swapWeights
  let E := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j))
  let S := localR (rowPosition r hr) (mergeWeights (constF m phase))
  change column w*(S*E)=(S*E)*column (fun i => v (j.succAbove i))
  have hpass := column_insert_swap j v (fun i => v (j.succAbove i)) (fun _ => rfl)
    (twoRows₁ w r hr _ _)
  have htrain : (column w*S)*E=(S*column v)*E := by
    ext q p
    rw [mul_functionMatrix,mul_functionMatrix]
    apply column_merge r hr w v z hz hL hL1 hL2 hw₀ hw₁
      (twoRows₀ w r hr _ _) (twoRows₁ w r hr _ _) (twoRows_other w r _ _)
    exact p.map_not_occupied_omit j
  rw [←Matrix.mul_assoc,htrain,Matrix.mul_assoc,hpass,←Matrix.mul_assoc]

 
theorem column_deletion_intertwiner (r : ℕ) (hr : r+2≤n+2)
    (w : Fin (n+2) → Weights (SpectralField m)) (z : SpectralField m)
    (hz : z≠0) (hL : torusL z≠0) (hL3 : torusL (constF m phase^3*z)≠0)
    (hw₀ : w ⟨r,by omega⟩=torusWeights (constF m phase^3*z))
    (hw₁ : w ⟨r+1,by omega⟩=torusWeights z) :
    let j : Fin (n+2) := ⟨r+1,by omega⟩
    let k : Fin (n+1) := ⟨r,by omega⟩
    let v := twoRows w r swapWeights swapWeights
    let ER := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j))
    let EL := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb k))
    let S : Matrix (Pairing (n+2)) (Pairing (n+2)) (SpectralField m) := localR (rowPosition r hr) deletionWeights
    (column w * (S*(ER*EL)) : Matrix (Pairing (n+2)) (Pairing n) (SpectralField m)) = (S*(ER*EL)) * column (fun i => v (j.succAbove (k.succAbove i))) := by
  dsimp only
  let j : Fin (n+2) := ⟨r+1,by omega⟩
  let k : Fin (n+1) := ⟨r,by omega⟩
  let v := twoRows w r swapWeights swapWeights
  let ER := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j))
  let EL := functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb k))
  let S : Matrix (Pairing (n+2)) (Pairing (n+2)) (SpectralField m) := localR (rowPosition r hr) deletionWeights
  change column w*(S*(ER*EL))=(S*(ER*EL))*column (fun i => v (j.succAbove (k.succAbove i)))
  have hjk : j.succAbove k=⟨r,by omega⟩ := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · change r < r+1; omega
  have hpassR := column_insert_swap j v (fun i => v (j.succAbove i)) (fun _ => rfl)
    (twoRows₁ w r hr _ _)
  have hpassL := column_insert_swap k (fun i => v (j.succAbove i))
    (fun i => v (j.succAbove (k.succAbove i))) (fun _ => rfl)
    (by rw [hjk]; exact twoRows₀ w r hr _ _)
  have htrain : (column w*S)*(ER*EL)=(S*column v)*(ER*EL) := by
    ext q p
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,mul_functionMatrix,mul_functionMatrix,
      mul_functionMatrix,mul_functionMatrix]
    apply column_deletion r hr w v z hz hL hL3 hw₀ hw₁
      (twoRows₀ w r hr _ _) (twoRows₁ w r hr _ _) (twoRows_other w r _ _)
    · rw [←hjk]
      exact fun h => p.map_not_occupied_omit k ((Pairing.map_occupied _ _ _).mp h)
    · exact (p.map (Fin.succAboveOrderEmb k)).map_not_occupied_omit j
  rw [←Matrix.mul_assoc,htrain]
  simp only [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (column v) ER EL,hpassR,Matrix.mul_assoc,hpassL]

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

lemma PolynomialBox.prod {n:ℕ} {ι:Type*} (s:Finset ι) (P:ι → Polynomial (Laurent n))
    (b:ι → Fin n → ℕ) (h:∀ i∈s,PolynomialBox (P i) (b i)) :
    PolynomialBox (∏ i∈s,P i) (∑ i∈s,b i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty] using PolynomialBox.one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end





end CriticalStrip.Diagram

end OAI
end


