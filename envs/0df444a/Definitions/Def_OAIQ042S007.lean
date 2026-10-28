-- Prove2me | Definitions.Def_OAIQ042S007
-- name    : OAIQ042S007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:40:07.390874+00:00
-- url     : https://prove2.me/theorems/852ea423-81a2-4330-a9a6-fcb783bda5d6
-- title:
--   Definitions bundle OAIQ042S007 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 141 declarations of OpenAI's Lean: 39 definitions, 1 inductive type or structure, 3 instances and 98 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.SourcePairing.padBottom`, `OAI.CriticalStrip.Diagram.TurnDisk`, `OAI.CriticalStrip.Diagram.TurnDisk.Compatible`, `OAI.CriticalStrip.Diagram.TurnDisk.Gate4.stage0`, `OAI.CriticalStrip.Diagram.TurnDisk.Gate4.stage1`, `OAI.CriticalStrip.Diagram.TurnDisk.Gate4.stage2`, `OAI.CriticalStrip.Diagram.TurnDisk.Gate4.stage3`, `OAI.CriticalStrip.Diagram.TurnDisk.Gate4.wire`, `OAI.CriticalStrip.Diagram.TurnDisk.Rhombus.disk`, `OAI.CriticalStrip.Diagram.TurnDisk.Rhombus.joined`, `OAI.CriticalStrip.Diagram.TurnDisk.Rhombus.stage`, `OAI.CriticalStrip.Diagram.TurnDisk.Vertex`, `OAI.CriticalStrip.Diagram.TurnDisk.boundary`, `OAI.CriticalStrip.Diagram.TurnDisk.edgeTurn`, `OAI.CriticalStrip.Diagram.TurnDisk.gate4`, `OAI.CriticalStrip.Diagram.TurnDisk.gauge`, `OAI.CriticalStrip.Diagram.TurnDisk.vertexGauge`, `OAI.CriticalStrip.Diagram.TurnDisk.wiring`, `OAI.CriticalStrip.Diagram.TurnNetwork.Matches`, `OAI.CriticalStrip.Diagram.TurnNetwork.Occupied`, `OAI.CriticalStrip.Diagram.TurnNetwork.boundary`, `OAI.CriticalStrip.Diagram.TurnNetwork.disk`, `OAI.CriticalStrip.Diagram.TurnNetwork.edgeTurn`, `OAI.CriticalStrip.Diagram.TurnNetwork.graph`, `OAI.CriticalStrip.Diagram.TurnNetwork.names`, `OAI.CriticalStrip.Diagram.TurnRectangle.InteriorMatches`, `OAI.CriticalStrip.Diagram.TurnRectangle.PhysicalMatches`, `OAI.CriticalStrip.Diagram.TurnRectangle.bdry`, `OAI.CriticalStrip.Diagram.TurnRectangle.box`, `OAI.CriticalStrip.Diagram.TurnRectangle.edges`, `OAI.CriticalStrip.Diagram.TurnRectangle.startPairing`, `OAI.CriticalStrip.Diagram.TurnRectangle.starterActive`, `OAI.CriticalStrip.Diagram.TurnRectangle.turns`, `OAI.CriticalStrip.Diagram.TurnStarter.pairing`, `OAI.CriticalStrip.Diagram.VacuumRegular`, `OAI.CriticalStrip.Diagram.allOneEvaluation`, `OAI.CriticalStrip.Diagram.angleEvaluation`, `OAI.CriticalStrip.Diagram.rationalInterpolationResidual`, `OAI.CriticalStrip.Diagram.rawColumn`, `OAI.CriticalStrip.Diagram.scalarValue`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_AugmentedTail`, `StripMass_BottomPadding`, `StripMass_DiagonalFactors`, `StripMass_FirstFlatSpecialization`, `StripMass_FirstThree`, `StripMass_LastRow`, `StripMass_NodalEmpty`, `StripMass_NodalScalarDeletion`, `StripMass_PairingDiagrams`, `StripMass_PfaffianSupport`, `StripMass_RealEvaluation`, `StripMass_ScalarDegree`, `StripMass_ScalarDeleteContinuation`, `StripMass_SpecializationPolynomial`, `StripMass_SplitGluing`, `StripMass_ThreeBoxBraidPolynomial`, `StripMass_ThreeBoxWeights`, `StripMass_TopPadding`, `StripMass_TripleCircuit`, `StripMass_TurnEvolution`, `StripMass_TurnRectangleMatching`, `StripMass_TurnRhombus`, `StripMass_TurnShelling`, `StripMass_TurnWideGate`.
--
--   **Imports.** It imports the bundles `OAIQ042S002`, `OAIQ042S003` and `OAIQ042S004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S011` and `OAIQ042S012`; the statements `OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne` and `OAI.CriticalStrip.Diagram.scalarValue_homogeneous_ne_zero`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S002
import Definitions.Def_OAIQ042S003
import Definitions.Def_OAIQ042S004

section
-- module Solutions.OAIQ042_SS.StripMass_PairingDiagrams
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


def VacuumRegular {𝕜 : Type*} [Field 𝕜] {n : ℕ} (w : Fin n → Weights 𝕜) : Prop :=
  (1 - restrictedColumn w).det ≠ 0



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BottomPadding
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
theorem realizes_padBottom_iff {n : ℕ} (p q : Pairing n) (t : Configuration n) :
    Realizes p.padBottom q.padBottom t.padBottom ↔ Realizes p q t := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; simpa using h.west i.succ
    · intro i; simpa using h.east i.succ
    · intro i hi hocc
      have hg := h.glued 0 i.succ (by simpa using hi)
      exact Tile.vacant_not_occupied 3 (hg.mpr hocc)
    · intro i hi
      exact h.north i.succ (by change i.val+1+1 = n+1; omega)
    · intro i j hij
      exact h.glued i.succ j.succ (by simpa using hij)
    · intro v w hvw
      obtain ⟨j,hj,hr⟩ := h.no_loop _ _ ((wiring_padBottom_iff p t v w).2 hvw)
      induction j using Fin.cases with
      | zero => exact (q.padBottom_not_occupied_zero hj).elim
      | succ j =>
          exact ⟨j,(q.padBottom_occupied_succ j).1 hj, (reach_padBottom_iff p t v (j,2)).1 hr⟩
    · intro i j hij
      exact (q.padBottom_adj_succ i j).symm.trans <|
        (h.output i.succ j.succ (fun h' => hij (Fin.succ_injective n h'))).trans
          (reach_padBottom_iff p t (i,2) (j,2))
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simp
      | succ i => simpa using h.west i
    · intro i
      induction i using Fin.cases with
      | zero => simp
      | succ i => simpa using h.east i
    · intro i hi
      have : i = 0 := Fin.ext hi
      subst i; simp
    · intro i hi
      induction i using Fin.cases with
      | zero => simp
      | succ i => exact h.north i (by change i.val+1+1 = n+1 at hi; omega)
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
          induction j using Fin.cases with
          | zero => simp only [Fin.val_zero] at hij; omega
          | succ j =>
              have hj : j.val = 0 := by simpa using hij.symm
              simp [h.south j hj]
      | succ i =>
          induction j using Fin.cases with
          | zero => simp only [Fin.val_zero, Fin.val_succ] at hij; omega
          | succ j => exact h.glued i j (by simpa using hij)
    · rintro ⟨i,a⟩ ⟨j,b⟩ hij
      induction i using Fin.cases with
      | zero => exact (wiring_padBottom_zero p t a _ hij).elim
      | succ i =>
          induction j using Fin.cases with
          | zero => exact (wiring_padBottom_zero_right p t _ b hij).elim
          | succ j =>
              obtain ⟨k,hk,hr⟩ := h.no_loop _ _ ((wiring_padBottom_iff p t (i,a) (j,b)).1 hij)
              exact ⟨k.succ,(q.padBottom_occupied_succ k).2 hk,
                (reach_padBottom_iff p t (i,a) (k,2)).2 hr⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero => simp [hij.symm]
      | succ i =>
          induction j using Fin.cases with
          | zero => simp
          | succ j =>
              exact (Pairing.padBottom_adj_succ q i j).trans <|
                (h.output i j (fun h' => hij (congrArg Fin.succ h'))).trans
                  (reach_padBottom_iff p t (i,2) (j,2)).symm

theorem Realizes.bottom_vacant {n : ℕ} {p q : Pairing n} {t : Configuration (n+1)}
    (h : Realizes p.padBottom q.padBottom t) : t 0 = .vacant :=
  Tile.vacant_of_three _ (h.south 0 rfl)
    (fun hc => p.padBottom_not_occupied_zero ((h.west 0).mp hc))
    (fun hc => q.padBottom_not_occupied_zero ((h.east 0).mp hc))

theorem realizes_cons_bottom_iff {n : ℕ} (p q : Pairing n)
    (a : Tile) (t : Configuration n) :
    Realizes p.padBottom q.padBottom (Fin.cons a t) ↔
      a = .vacant ∧ Realizes p q t := by
  constructor
  · intro h
    have ha : a = .vacant := h.bottom_vacant
    subst a
    exact ⟨rfl, (realizes_padBottom_iff p q t).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (realizes_padBottom_iff p q t).mpr h

 
theorem column_padBottom {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (p q : Pairing n) :
    column w q.padBottom p.padBottom = column (fun i => w i.succ) q p := by
  classical
  unfold column
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Tile))
    (fun tt : Tile × Configuration n =>
      if Realizes p.padBottom q.padBottom (Fin.cons tt.1 tt.2)
      then ∏ i : Fin (n+1), (w i).tile ((Fin.cons tt.1 tt.2 : Configuration (n+1)) i) else 0)
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [realizes_cons_bottom_iff]
  rw [Finset.sum_eq_single Tile.vacant]
  · apply Finset.sum_congr rfl
    intro t _
    simp [Fin.prod_univ_succ, Weights.tile]
  · intro a ha hav
    simp [hav]
  · simp


theorem column_identity_bottom_row {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (hw : w 0 = identityWeights)
    (p q : Pairing (n+1)) (hq : q.Occupied 0) : column w q p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with h
  · apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n+1)))
    rw [hw]
    exact Tile.identity_zero_of_south_vacant_east_occupied _
      (h.south 0 rfl) ((h.east 0).mpr hq)
  · rfl

 
theorem column_deletion_bottom_col {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (hw : w 0 = deletionWeights)
    (p q : Pairing (n+1)) (hp : p.Occupied 0) : column w q p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with h
  · apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n+1)))
    rw [hw]
    exact Tile.deletion_zero_of_south_vacant_west_occupied _
      (h.south 0 rfl) ((h.west 0).mpr hp)
  · rfl


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

theorem column_deletion_top_row {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (hw : w (Fin.last n) = deletionWeights)
    (p q : Pairing (n+1)) (hq : q.Occupied (Fin.last n)) : column w q p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with h
  · apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last n))
    rw [hw]
    exact Tile.deletion_zero_of_north_vacant_east_occupied _
      (h.north (Fin.last n) rfl) ((h.east (Fin.last n)).mpr hq)
  · rfl

theorem column_identity_top_col {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin (n+1) → Weights 𝕜) (hw : w (Fin.last n) = identityWeights)
    (p q : Pairing (n+1)) (hp : p.Occupied (Fin.last n)) : column w q p = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with h
  · apply Finset.prod_eq_zero (Finset.mem_univ (Fin.last n))
    rw [hw]
    exact Tile.identity_zero_of_north_vacant_west_occupied _
      (h.north (Fin.last n) rfl) ((h.west (Fin.last n)).mpr hp)
  · rfl

theorem det_column_le_one {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} (hn : n ≤ 1)
    (w : Fin n → Weights 𝕜) : (1-restrictedColumn w).det = 1 := by
  let : IsEmpty (NonemptyPairing n) := ⟨fun p => p.property (p.val.eq_empty_of_le_one hn)⟩
  exact Matrix.det_isEmpty

theorem column_mulVec_nonempty {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (v : Pairing n → 𝕜) (p : NonemptyPairing n) :
    (column w).mulVec v p.val = injectionColumn w p * v (empty n) +
      (restrictedColumn w).mulVec (fun q => v q.val) p := by
  classical
  exact Fintype.sum_eq_add_sum_subtype_ne _ (empty n)

end

noncomputable section
 

def rawColumn {R : Type*} [CommRing R] {n : ℕ} (w : Fin n → Tile → R) :
    Matrix (Pairing n) (Pairing n) R := by
  classical
  exact fun q p => ∑ t : Configuration n,
    if Realizes p q t then ∏ i, w i (t i) else 0

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






open scoped Classical

lemma column_map {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Weights K) :
    (column w).map f=column (fun i => (w i).map f) := by
  ext p q
  simp only [Matrix.map_apply,column,map_sum,Weights.map_tile]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp only [map_prod,map_zero]

lemma restrictedColumn_map {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Weights K) :
    (restrictedColumn w).map f=restrictedColumn (fun i => (w i).map f) := by
  ext p q
  exact congrFun (congrFun (column_map f w) p.val) q.val

lemma VacuumRegular.map {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Weights K) (h : VacuumRegular w) :
    VacuumRegular (fun i => (w i).map f) := by
  unfold VacuumRegular at h ⊢
  have hm : (1-restrictedColumn w).map f=1-restrictedColumn (fun i => (w i).map f) := by
    rw [←restrictedColumn_map]
    ext i j
    simp only [Matrix.map_apply,Matrix.sub_apply,Matrix.one_apply,map_sub]
    split_ifs <;> simp only [map_one,map_zero]
  have hh : f (1-restrictedColumn w).det≠0 := (map_ne_zero f).mpr h
  rw [f.map_det] at hh
  change ((1-restrictedColumn w).map f).det≠0 at hh
  rwa [hm] at hh

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



theorem scalarNumerator_eval_vandermonde {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (a : Fin n → K) (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0) :
    MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) =
      (∏ i, ∏ j ∈ Finset.Ioi i, (a i-a j)) * scalarNormalization (f dd) (f rr) a := by
  rw [scalarNumerator_eval f n dd rr a hD, product_augmentedDenominator]
  unfold scalarNormalization
  rw [← prod_upperPair, ← prod_upperPair, ← prod_upperPair,
    Finset.prod_div_distrib]
  have hv : (∏ e : UpperPair n, (a e.val.1-a e.val.2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro e _
    exact sub_ne_zero.mpr (ha.ne (ne_of_lt e.property))
  field_simp







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



theorem scalarNumerator_eq_vandermonde (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) :
    scalarNumerator n dd rr = sourceVandermonde MvPolynomial.X * scalarPolynomial n dd rr hdd :=
  Classical.choose_spec (scalarNumerator_vandermonde_dvd n dd rr hdd)

 

theorem scalarPolynomial_eval {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) (a : Fin n → K)
    (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0) :
    MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) =
      scalarNormalization (f dd) (f rr) a := by
  have h := scalarNumerator_eval_vandermonde f n dd rr a ha hD
  rw [scalarNumerator_eq_vandermonde n dd rr hdd, map_mul,
    map_sourceVandermonde] at h
  simp only [MvPolynomial.eval₂Hom_X'] at h
  rw [← prod_upperPair] at h
  exact mul_left_cancel₀ (sourceVandermonde_ne_zero a ha) h

 
theorem scalarPolynomial_rename {n : ℕ} (dd rr : ℂ) (hdd : dd ≠ 0)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.rename σ (scalarPolynomial n dd rr hdd) = scalarPolynomial n dd rr hdd := by
  have h := congrArg (MvPolynomial.rename σ) (scalarNumerator_eq_vandermonde n dd rr hdd)
  have hv : MvPolynomial.rename σ
      (sourceVandermonde (MvPolynomial.X : Fin n → CosineRing n)) =
      sourceVandermonde (MvPolynomial.X ∘ σ) := by
    simp [sourceVandermonde, map_prod]
  rw [scalarNumerator_rename dd rr hdd σ, map_mul, hv] at h
  rw [sourceVandermonde_reindex MvPolynomial.X σ,
    scalarNumerator_eq_vandermonde n dd rr hdd] at h
  have hs : (((Equiv.Perm.sign σ : ℤ) : CosineRing n)) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  apply mul_left_cancel₀ (mul_ne_zero hs
    (sourceVandermonde_ne_zero (MvPolynomial.X : Fin n → CosineRing n) MvPolynomial.X_injective))
  simpa only [mul_assoc] using h.symm

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedTail
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.wiring_symm _root_.OAI.CriticalStrip.Diagram.spectralFieldCharZero
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



def rationalInterpolationResidual (n : ℕ) (p : Pairing (n+1)) : SpectralField (n+1) :=
  (∏ i : Fin (n+1), evalLaurent (rowDenominator i)) *
    (((column (spectralWeights (n+1))).mulVec (rationalInterpolant n)) p -
      rationalInterpolant n p)

end
end CriticalStrip.Diagram

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

theorem coefficient_2 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 2 = a .verticalPair * b .capCup * c .cap := by
  simp [coefficient, fiber]

theorem coefficient_3 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 3 = a .verticalPair * b .capCup * c .capCup := by
  simp [coefficient, fiber]

theorem coefficient_4 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 4 = a .verticalPair * b .cap * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_5 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 5 = a .verticalPair * b .cap * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_6 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 6 = a .verticalPair * b .capCup * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_10 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 10 = a .vertical₁ * b .diagonal₀ * c .cap + a .diagonal₁ * b .cap * c .vacant := by
  simp [coefficient, fiber]

theorem coefficient_11 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 11 = a .diagonal₁ * b .capCup * c .vertical₀ := by
  simp [coefficient, fiber]

theorem coefficient_12 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 12 = a .diagonal₁ * b .capCup * c .diagonal₀ := by
  simp [coefficient, fiber]

theorem coefficient_13 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 13 = a .vertical₁ * b .diagonal₀ * c .capCup + a .diagonal₁ * b .cap * c .cup := by
  simp [coefficient, fiber]

theorem coefficient_15 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 15 = a .cap * b .vertical₀ * c .vacant + a .verticalPair * b .verticalPair * c .cap + a .capCup * b .capCup * c .cap := by
  simp [coefficient, fiber, add_assoc]

theorem coefficient_16 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 16 = a .cap * b .vertical₀ * c .cup + a .verticalPair * b .verticalPair * c .capCup + a .capCup * b .verticalPair * c .verticalPair + a .capCup * b .capCup * c .capCup := by
  simp [coefficient, fiber, add_assoc]

theorem coefficient_18 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 18 = a .verticalPair * b .verticalPair * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_20 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 20 = a .vertical₁ * b .vertical₀ * c .diagonal₁ + a .diagonal₁ * b .verticalPair * c .vertical₀ := by
  simp [coefficient, fiber]

theorem coefficient_21 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 21 = a .vertical₁ * b .vertical₀ * c .vertical₁ + a .diagonal₁ * b .verticalPair * c .diagonal₀ := by
  simp [coefficient, fiber]

theorem coefficient_24 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 24 = a .cap * b .diagonal₀ * c .vertical₀ + a .capCup * b .cap * c .diagonal₁ := by
  simp [coefficient, fiber]

theorem coefficient_26 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 26 = a .vertical₁ * b .diagonal₀ * c .verticalPair := by
  simp [coefficient, fiber]

theorem coefficient_28 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 28 = a .cap * b .diagonal₀ * c .diagonal₀ + a .capCup * b .cap * c .vertical₁ := by
  simp [coefficient, fiber]

theorem coefficient_29 {K : Type*} [CommSemiring K] (a b c : Tile → K) :
    coefficient a b c 29 = a .capCup * b .capCup * c .verticalPair := by
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

theorem braid_numerator_2 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 2 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 28 := by
  rw [coefficient_2, coefficient_28]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq]
  all_goals ring

theorem braid_numerator_3 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 3 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 29 := by
  rw [coefficient_3, coefficient_29]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_4 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 4 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 24 := by
  rw [coefficient_4, coefficient_24]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_5 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 5 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 15 := by
  rw [coefficient_5, coefficient_15]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_6 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 6 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 16 := by
  rw [coefficient_6, coefficient_16]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_10 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 10 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 10 := by
  rw [coefficient_10, coefficient_10]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_11 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 11 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 13 := by
  rw [coefficient_11, coefficient_13]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq]
  all_goals ring

theorem braid_numerator_12 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 12 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 12 := by
  rw [coefficient_12, coefficient_12]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_13 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 13 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 11 := by
  rw [coefficient_13, coefficient_11]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq]
  all_goals ring

theorem braid_numerator_14 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 14 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 46 := by
  rw [coefficient_14, coefficient_46]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_38 hq]
  all_goals ring

theorem braid_numerator_15 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 15 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 5 := by
  rw [coefficient_15, coefficient_5]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_16 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 16 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 6 := by
  rw [coefficient_16, coefficient_6]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_18 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 18 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 18 := by
  rw [coefficient_18, coefficient_18]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_20 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 20 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 26 := by
  rw [coefficient_20, coefficient_26]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_21 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 21 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 21 := by
  rw [coefficient_21, coefficient_21]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_22 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 22 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 47 := by
  rw [coefficient_22, coefficient_47]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_23 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 23 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 45 := by
  rw [coefficient_23, coefficient_45]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_24 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 24 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 4 := by
  rw [coefficient_24, coefficient_4]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_26 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 26 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 20 := by
  rw [coefficient_26, coefficient_20]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_27 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 27 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 43 := by
  rw [coefficient_27, coefficient_43]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_28 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 28 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 2 := by
  rw [coefficient_28, coefficient_2]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq]
  all_goals ring

theorem braid_numerator_29 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 29 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 3 := by
  rw [coefficient_29, coefficient_3]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_30 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 30 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 44 := by
  rw [coefficient_30, coefficient_44]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq]
  all_goals ring

theorem braid_numerator_43 {K : Type*} [CommRing K] (q z w : K) (_hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 43 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 27 := by
  rw [coefficient_43, coefficient_27]
  simp only [tileNumerator]
  ring_nf

theorem braid_numerator_44 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 44 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 30 := by
  rw [coefficient_44, coefficient_30]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq]
  all_goals ring

theorem braid_numerator_45 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 45 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 23 := by
  rw [coefficient_45, coefficient_23]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_36 hq]
  all_goals ring

theorem braid_numerator_46 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 46 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 14 := by
  rw [coefficient_46, coefficient_14]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_8 hq, eighthRoot_power_10 hq, eighthRoot_power_12 hq, eighthRoot_power_14 hq, eighthRoot_power_16 hq, eighthRoot_power_18 hq, eighthRoot_power_20 hq, eighthRoot_power_22 hq, eighthRoot_power_24 hq, eighthRoot_power_26 hq, eighthRoot_power_28 hq, eighthRoot_power_30 hq, eighthRoot_power_32 hq, eighthRoot_power_34 hq, eighthRoot_power_38 hq]
  all_goals ring

theorem braid_numerator_47 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 47 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 22 := by
  rw [coefficient_47, coefficient_22]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_48 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 48 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 50 := by
  rw [coefficient_48, coefficient_50]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

theorem braid_numerator_49 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 49 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 49 := by
  rw [coefficient_49, coefficient_49]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_9 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_33 hq]
  all_goals ring

theorem braid_numerator_50 {K : Type*} [CommRing K] (q z w : K) (hq : q^8 = -1) :
    coefficient (tileNumerator q (q^4) z) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) w) 50 =
    coefficient (tileNumerator q (q^4) w) (tileNumerator q (q^4) (z*w))
      (tileNumerator q (q^4) z) 48 := by
  rw [coefficient_50, coefficient_48]
  simp only [tileNumerator]
  ring_nf
  all_goals simp only [eighthRoot_power_11 hq, eighthRoot_power_13 hq, eighthRoot_power_15 hq, eighthRoot_power_17 hq, eighthRoot_power_19 hq, eighthRoot_power_21 hq, eighthRoot_power_23 hq, eighthRoot_power_25 hq, eighthRoot_power_27 hq, eighthRoot_power_29 hq, eighthRoot_power_31 hq, eighthRoot_power_35 hq]
  all_goals ring

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TripleCircuit
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.ThreeBox.boundaryDataDecidable _root_.OAI.CriticalStrip.Diagram.ThreeBox.cleanDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical





namespace ThreeBox
instance adjStdSymm (t : Config) : Std.Symm (Adj t) := adj_symm t
end ThreeBox
end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalScalarDeletion
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

 
theorem rationalNodalPolynomial_at_node {n : ℕ} (p : Pairing (n+1)) (i : Fin n) :
    (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) *
      (rationalNodalPolynomial n p).eval (deletionBeta i) = nodalVacuum i p := by
  have hinj := (deletionBeta_injective n).injOn (s := (univ : Finset (Fin n)))
  by_cases hp : p.Occupied (Fin.last n)
  · simp only [rationalNodalPolynomial, hp, ite_true]
    rw [Lagrange.eval_interpolate_at_node _ hinj (mem_univ _)]
    field_simp [deletionNode_sine_ne_zero i]
  · simp only [rationalNodalPolynomial, hp, ite_false, one_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Lagrange.eval_nodal_at_node (mem_univ _),
      mul_zero, zero_add]
    exact Lagrange.eval_interpolate_at_node _ hinj (mem_univ _)

theorem rationalNodalPolynomial_degree (n : ℕ) : LastDegree n (rationalNodalPolynomial n) := by
  intro p k hk
  have hinj := (deletionBeta_injective n).injOn (s := (univ : Finset (Fin n)))
  by_cases hp : p.Occupied (Fin.last n)
  · simp only [rationalNodalPolynomial, hp, ite_true] at hk ⊢
    apply Polynomial.coeff_eq_zero_of_degree_lt
    have hdeg := Lagrange.degree_interpolate_lt
      (fun i => nodalVacuum i p / torusSin (deletionNode i)) hinj
    simp only [card_univ, Fintype.card_fin] at hdeg
    exact hdeg.trans_le (by exact_mod_cast hk)
  · simp only [rationalNodalPolynomial, hp, ite_false] at hk ⊢
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul]
    have hi := Lagrange.degree_interpolate_lt (fun i => nodalVacuum i p) hinj
    have hn := Lagrange.degree_nodal (s := (univ : Finset (Fin n))) (v := @deletionBeta n)
    simp only [card_univ, Fintype.card_fin] at hi hn
    rw [Polynomial.coeff_eq_zero_of_degree_lt (hi.trans_le (by exact_mod_cast Nat.le_of_lt hk)),
      Polynomial.coeff_eq_zero_of_degree_lt (hn.trans_lt (by exact_mod_cast hk)), mul_zero, add_zero]

theorem rationalNodalPolynomial_leading {n : ℕ} (p : Pairing n) :
    (rationalNodalPolynomial n p.padTop).coeff n = rationalVacuum n p := by
  simp only [rationalNodalPolynomial, Pairing.padTop_not_occupied_last, ite_false,
    Polynomial.coeff_add, Polynomial.coeff_C_mul]
  rw [Pairing.padTop, Pairing.restrict_map]
  have hnod : (Lagrange.nodal univ (@deletionBeta n)).coeff n = 1 := by
    simpa only [Lagrange.natDegree_nodal, card_univ, Fintype.card_fin] using
      (Lagrange.nodal_monic (s := (univ : Finset (Fin n))) (v := @deletionBeta n)).coeff_natDegree
  rw [hnod, mul_one, Polynomial.coeff_eq_zero_of_degree_lt, add_zero]
  simpa only [card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := univ) (fun i => nodalVacuum i (p.map Fin.castSuccOrderEmb))
      (deletionBeta_injective n).injOn

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

lemma lastCosine_box (n:ℕ) : LaurentBox (lastCosine n) (selfBound (Fin.last n) 2) := by
  rw [lastCosine_eq]
  apply LaurentBox.cosine
  intro i
  by_cases hi:i=Fin.last n <;> simp [selfBound,variableExponent,hi]

lemma lastSine_box (n:ℕ) : LaurentBox (lastSine n) (selfBound (Fin.last n) 1) := by
  unfold lastSine
  apply LaurentBox.sub
  all_goals apply LaurentBox.single
  all_goals intro i; induction i using Fin.lastCases <;> simp [lastExponent,selfBound]


lemma lastLaurent_map {n:ℕ} (p:Pairing (n+1)) (P:Polynomial (Laurent n))
    (hP:P.map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p) :
    evalLaurent (lastLaurent p P)=rationalInterpolant n p := by
  have he:evalLaurent (P.eval₂ (liftLaurentHom n) (lastCosine n))=
      (rationalNodalPolynomial n p).eval₂ (liftSpectral n) (spectralA (Fin.last n)) := by
    rw [←hP,Polynomial.eval₂_map,←lastCosine_map]
    change (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) _ = _
    rw [Polynomial.hom_eval₂]
    have hh:(algebraMap (SpectralRing (n+1)) (SpectralField (n+1))).comp (liftLaurentHom n)=
        (liftSpectral n).comp (algebraMap (SpectralRing n) (SpectralField n)) := by
      apply RingHom.ext
      intro a
      exact (liftSpectral_evalLaurent a).symm
    rw [hh]
    rfl
  unfold lastLaurent rationalInterpolant
  rw [evalLaurent,map_mul]
  change evalLaurent (if p.Occupied (Fin.last n) then lastSine n else 1) *
    evalLaurent (P.eval₂ (liftLaurentHom n) (lastCosine n)) = _
  rw [he]
  congr 1
  split_ifs
  · exact evalLaurent_lastSine n
  · exact map_one _

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FirstFlatSpecialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma scalarPolynomial_eval_spectral (n : ℕ) :
    MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n)) spectralA
      (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero))=spectralNormalization n := by
  exact scalarPolynomial_eval _ _ _ _ _ _ (spectralA_injective n)
    (fun i j hij => spectralA_discriminant_ne i j hij)


end

 

 

noncomputable section
open Finset

theorem sum_selectedPairs {R : Type*} [AddCommMonoid R] {n : ℕ}
    (D : Fin n → Fin n → R) (hD : ∀ i j, D i j = D j i)
    (σ : Equiv.Perm (Fin n)) :
    (∑ e ∈ selectedPairs σ, D e.val.1 e.val.2) =
      ∑ i : Fin (n/2), D (σ (pairFirst n i)) (σ (pairSecond n i)) := by
  rw [selectedPairs, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    exact upperPair_value D hD _ _ _
  · exact fun i _ j _ h => permutationPair_injective σ h

 

theorem clearedPfaffianTerm_degree {n m : ℕ} (k : Fin m)
    (N D : Matrix (Fin n) (Fin n) (CosineRing m))
    (w : Fin n → Fin n → ℕ) (hw : ∀ i j, w i j = w j i)
    (hN : ∀ i j, MvPolynomial.degreeOf k (N i j) ≤ w i j)
    (hD : ∀ i j, MvPolynomial.degreeOf k (D i j) ≤ w i j)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.degreeOf k (clearedPfaffianTerm N D σ) ≤
      ∑ e : UpperPair n, w e.val.1 e.val.2 := by
  unfold clearedPfaffianTerm
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add ((MvPolynomial.degreeOf_prod_le _ _ _).trans
    (Finset.sum_le_sum (fun i _ => hN _ _)))
    ((MvPolynomial.degreeOf_prod_le _ _ _).trans
    (Finset.sum_le_sum (fun e _ => hD _ _)))).trans ?_
  rw [← sum_selectedPairs w hw σ, Finset.sum_add_sum_compl]

 
theorem clearedPfaffian_degree {n m : ℕ} (k : Fin m) (t : ℂ)
    (N D : Matrix (Fin n) (Fin n) (CosineRing m))
    (w : Fin n → Fin n → ℕ) (hw : ∀ i j, w i j = w j i)
    (hN : ∀ i j, MvPolynomial.degreeOf k (N i j) ≤ w i j)
    (hD : ∀ i j, MvPolynomial.degreeOf k (D i j) ≤ w i j) :
    MvPolynomial.degreeOf k (clearedPfaffian (MvPolynomial.C t) N D) ≤
      ∑ e : UpperPair n, w e.val.1 e.val.2 := by
  unfold clearedPfaffian
  apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  have hs : ((Equiv.Perm.sign σ : ℤ) : CosineRing m) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) := by simp
  rw [hs]
  exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
    (clearedPfaffianTerm_degree k N D w hw hN hD σ)

theorem incidentPair_injective {n : ℕ} (k : Fin n) : Function.Injective (incidentPair k) := by
  intro j l h
  rcases (upperPair_eq_iff _ _).mp h with h | h
  · exact Subtype.ext h.2
  · exact False.elim (j.property h.2)

theorem sum_incident_degree {n : ℕ} (k : Fin n) (r : ℕ) :
    (∑ e : UpperPair n, if e.val.1 = k ∨ e.val.2 = k then r else 0) = r*(n-1) := by
  have hc : Fintype.card {j : Fin n // j ≠ k} = n-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hs : (∑ j : {j : Fin n // j ≠ k}, r) =
      ∑ e : UpperPair n, if e.val.1 = k ∨ e.val.2 = k then r else 0 := by
    apply Fintype.sum_of_injective (incidentPair k) (incidentPair_injective k)
    · intro e he
      simp only [incidentPair_range] at he
      simp [he]
    · intro j
      simp [incidentPair_has_k]
  simpa [hc, mul_comm] using hs.symm

theorem sum_scalarEdgeDegree {n : ℕ} (k : Fin n) :
    (∑ e : UpperPair (n+n%2), scalarEdgeDegree k e.val.1 e.val.2) = 2*(n-1) := by
  let hn : n ≤ n+n%2 := Nat.le_add_right _ _
  have hs : (∑ e : UpperPair n, if e.val.1 = k ∨ e.val.2 = k then 2 else 0) =
      ∑ e : UpperPair (n+n%2), scalarEdgeDegree k e.val.1 e.val.2 := by
    apply Fintype.sum_of_injective (upperPairEmbed hn) (upperPairEmbed_injective hn)
    · intro e he
      unfold scalarEdgeDegree
      split_ifs with h
      · exfalso
        apply he
        refine ⟨⟨(⟨e.val.1.val,h.1⟩,⟨e.val.2.val,h.2.1⟩),e.property⟩,?_⟩
        apply Subtype.ext
        exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
      · rfl
    · intro e
      simp [scalarEdgeDegree, upperPairEmbed, e.val.1.isLt, e.val.2.isLt, Fin.ext_iff]
  rw [← hs]
  exact sum_incident_degree k 2

theorem scalarNumerator_degree (n : ℕ) (dd rr : ℂ) (k : Fin n) :
    MvPolynomial.degreeOf k (scalarNumerator n dd rr) ≤ 2*(n-1) := by
  rw [← sum_scalarEdgeDegree k]
  exact clearedPfaffian_degree k _ _ _ (scalarEdgeDegree k) (scalarEdgeDegree_symm k)
    (augmentedNumerator_degree k rr) (augmentedDenominator_degree k dd)









theorem clearedPfaffianTerm_top {R : Type*} [CommRing R] {n : ℕ}
    (N D : Matrix (Fin n) (Fin n) (Polynomial R))
    (w : Fin n → Fin n → ℕ) (hw : ∀ i j, w i j = w j i)
    (hN : ∀ i j, (N i j).natDegree ≤ w i j)
    (hD : ∀ i j, (D i j).natDegree ≤ w i j)
    (σ : Equiv.Perm (Fin n)) :
    (clearedPfaffianTerm N D σ).coeff (∑ e : UpperPair n, w e.val.1 e.val.2) =
      clearedPfaffianTerm (fun i j => (N i j).coeff (w i j))
        (fun i j => (D i j).coeff (w i j)) σ := by
  have hs : (∑ e : UpperPair n, w e.val.1 e.val.2) =
      (∑ i : Fin (n/2), w (σ (pairFirst n i)) (σ (pairSecond n i))) +
        ∑ e ∈ (selectedPairs σ)ᶜ, w e.val.1 e.val.2 := by
    rw [← sum_selectedPairs w hw σ,Finset.sum_add_sum_compl]
  rw [clearedPfaffianTerm,hs,Polynomial.coeff_mul_add_eq_of_natDegree_le]
  · rw [coeff_prod_budget _ _ _ (fun i _ => hN _ _),
      coeff_prod_budget _ _ _ (fun i _ => hD _ _)]
    rfl
  · exact (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun i _ => hN _ _))
  · exact (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun i _ => hD _ _))

theorem clearedPfaffian_top {R : Type*} [CommRing R] {n : ℕ} (t : R)
    (N D : Matrix (Fin n) (Fin n) (Polynomial R))
    (w : Fin n → Fin n → ℕ) (hw : ∀ i j, w i j = w j i)
    (hN : ∀ i j, (N i j).natDegree ≤ w i j)
    (hD : ∀ i j, (D i j).natDegree ≤ w i j) :
    (clearedPfaffian (Polynomial.C t) N D).coeff (∑ e : UpperPair n, w e.val.1 e.val.2) =
      clearedPfaffian t (fun i j => (N i j).coeff (w i j))
        (fun i j => (D i j).coeff (w i j)) := by
  unfold clearedPfaffian
  rw [Polynomial.coeff_C_mul,Polynomial.finsetSum_coeff,mul_sum]
  symm
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have he : ((Equiv.Perm.sign σ : ℤ) : Polynomial R) =
      Polynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  rw [he,Polynomial.coeff_C_mul,clearedPfaffianTerm_top N D w hw hN hD σ]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FirstThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

def allOneEvaluation (n:ℕ) : Laurent n →ₐ[ℂ] SpectralField 0 :=
  torusEvaluation (fun _ =>1) (fun _ =>one_ne_zero)

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

theorem sourceVandermonde_degree {n : ℕ} (k : Fin n) :
    MvPolynomial.degreeOf k (sourceVandermonde (MvPolynomial.X : Fin n → CosineRing n)) = n-1 := by
  unfold sourceVandermonde
  rw [MvPolynomial.degreeOf_prod_eq _ _ (fun e _ =>
    (prime_cosine_difference e.val.1 e.val.2 (ne_of_lt e.property)).ne_zero)]
  calc
    _ = ∑ e : UpperPair n, if e.val.1 = k ∨ e.val.2 = k then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      exact cosine_difference_degree k e.val.1 e.val.2 (ne_of_lt e.property)
    _ = n-1 := by simpa using sum_incident_degree k 1

 

theorem scalarPolynomial_degree (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) (k : Fin n) :
    MvPolynomial.degreeOf k (scalarPolynomial n dd rr hdd) ≤ n-1 := by
  by_cases hp : scalarPolynomial n dd rr hdd = 0
  · simp [hp]
  have hv := sourceVandermonde_ne_zero (MvPolynomial.X : Fin n → CosineRing n)
    MvPolynomial.X_injective
  have hd := scalarNumerator_degree n dd rr k
  rw [scalarNumerator_eq_vandermonde n dd rr hdd, MvPolynomial.degreeOf_mul_eq hv hp,
    sourceVandermonde_degree] at hd
  omega

end

 

 

noncomputable section
open scoped Classical



lemma scalarPolynomial_first_degree {K:Type*} [CommRing K] (f:ℂ →+* K)
    (n:ℕ) (dd rr:ℂ) (hdd:dd≠0) (a:Fin n → K) :
    (firstScalarHom f a (scalarPolynomial (n+1) dd rr hdd)).natDegree ≤ n := by
  exact (firstScalarHom_degree f a _).trans (by simpa using scalarPolynomial_degree (n+1) dd rr hdd 0)

lemma scalarNumerator_first_top {K:Type*} [CommRing K] (f:ℂ →+* K)
    (n:ℕ) (dd rr:ℂ) (a:Fin n → K) :
    (firstScalarHom f a (scalarNumerator (n+1) dd rr)).coeff (2*n)=
      clearedPfaffian (f ((2^(((n+1)+(n+1)%2)/2)*
        (Nat.factorial (((n+1)+(n+1)%2)/2):ℂ))⁻¹))
          (infinityNumerator (f rr) a) (infinityDenominator (f dd) a) := by
  have he:2*n=∑e:UpperPair ((n+1)+(n+1)%2), scalarEdgeDegree (0:Fin (n+1)) e.val.1 e.val.2 := by
    rw [sum_scalarEdgeDegree]; simp
  rw [scalarNumerator_first_map]
  rw [he,clearedPfaffian_top _ _ _ _ (scalarEdgeDegree_symm 0)
      (augmentedNumerator_first_degree f rr a) (augmentedDenominator_first_degree f dd a)]
  rfl








lemma scalarNumerator_first_top_eval {K:Type*} [Field K] [CharZero K]
    (f:ℂ →+* K) (n:ℕ) (dd rr:ℂ) (a:Fin n → K)
    (hD:∀i j,i≠j → discriminant (f dd) (a i) (a j)≠0) :
    (firstScalarHom f a (scalarNumerator (n+1) dd rr)).coeff (2*n)=
      MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) := by
  rw [scalarNumerator_first_top]
  simp only [map_inv₀,map_mul,map_pow,map_ofNat,map_natCast]
  refine (clear_pfaffian (infinityNumerator (f rr) a) (infinityDenominator (f dd) a)
    (infinityDenominator_symm _ _) (infinityDenominator_ne _ _ hD)).symm.trans ?_
  rw [infinityKernel_eq,pfaffian_infinityKernel,infinityDenominator_product,
    scalarNumerator_eval f n dd rr a hD,product_augmentedDenominator,←prod_upperPair]



theorem scalarPolynomial_first_top {K:Type*} [Field K] [CharZero K]
    (f:ℂ →+* K) (n:ℕ) (dd rr:ℂ) (hdd:dd≠0) (a:Fin n → K)
    (ha:Function.Injective a) (hD:∀i j,i≠j → discriminant (f dd) (a i) (a j)≠0) :
    (firstScalarHom f a (scalarPolynomial (n+1) dd rr hdd)).coeff n=
      MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have hh:=scalarNumerator_first_top_eval f n dd rr a hD
  rw [scalarNumerator_eq_vandermonde (n+1) dd rr hdd,map_mul (firstScalarHom f a),
    show 2*n=n+n by omega,
    Polynomial.coeff_mul_add_eq_of_natDegree_le (firstScalarHom_vandermonde_degree f a)
      (scalarPolynomial_first_degree f n dd rr hdd a),firstScalarHom_vandermonde_top,
    scalarNumerator_eq_vandermonde n dd rr hdd,map_mul (MvPolynomial.eval₂Hom f a),
    map_sourceVandermonde] at hh
  simp only [MvPolynomial.eval₂Hom_X'] at hh
  exact mul_left_cancel₀ (sourceVandermonde_ne_zero a ha) hh

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarDeleteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical



theorem scalarPolynomial_first_top_continuation {K:Type*} [CommRing K]
    (f:ℂ →+* K) (n:ℕ) (dd rr:ℂ) (hdd:dd≠0) (a:Fin n → K) :
    (firstScalarHom f a (scalarPolynomial (n+1) dd rr hdd)).coeff n=
      MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have hi:
      (firstScalarHom MvPolynomial.C (MvPolynomial.X:Fin n → CosineRing n)
        (scalarPolynomial (n+1) dd rr hdd)).coeff n=scalarPolynomial n dd rr hdd := by
    apply IsFractionRing.injective (CosineRing n) (CosineField n)
    rw [←Polynomial.coeff_map,map_firstScalarHom]
    have hh:=scalarPolynomial_first_top (genericConst n) n dd rr hdd genericVar
      (genericVar_inj n) (fun i j _ => discriminant_genericVar_ne dd hdd i j)
    have hv: MvPolynomial.eval₂Hom (genericConst n) genericVar=
        algebraMap (CosineRing n) (CosineField n) := by
      apply MvPolynomial.ringHom_ext
      · intro z; simp [genericConst, RingHom.comp_apply]
      · intro z; simp [genericVar]
    rw [hv] at hh
    exact hh
  have he:=congrArg (MvPolynomial.eval₂Hom f a) hi
  rw [←Polynomial.coeff_map,map_firstScalarHom] at he
  have hc:(MvPolynomial.eval₂Hom f a).comp MvPolynomial.C=f := by ext z; simp
  simp only [hc,MvPolynomial.eval₂Hom_X'] at he
  exact he


 

 


 
def scalarValue {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ} (a:Fin n → K) : K :=
  MvPolynomial.eval₂Hom f a (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero))

lemma scalarValue_permute {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (a:Fin n → K) (σ:Equiv.Perm (Fin n)) : scalarValue f (a ∘ σ)=scalarValue f a := by
  unfold scalarValue
  have h:=congrArg (MvPolynomial.eval₂Hom f a) (scalarPolynomial_rename (d:ℂ) rho
    (by exact_mod_cast d_ne_zero) σ)
  simpa [MvPolynomial.eval₂Hom_rename] using h

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

lemma scalarValue_snoc {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (a:Fin n → K) (z:K) : scalarValue f (Fin.snoc a z)=scalarValue f (Fin.cons z a) := by
  rw [Fin.snoc_eq_cons_rotate]
  exact scalarValue_permute f _ (finRotate (n+1))

lemma rationalVacuum_empty (n:ℕ) : rationalVacuum n (empty n)=spectralNormalization n := by
  simp [rationalVacuum,normalizedVacuum,attachEmpty]

lemma rationalNodalPolynomial_empty (n:ℕ) :
    rationalNodalPolynomial n (empty (n+1))=
      firstScalarHom (algebraMap ℂ (SpectralField n)) spectralA
        (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero)) := by
  let Q:=firstScalarHom (algebraMap ℂ (SpectralField n)) spectralA
    (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))
  have htop:Q.coeff n=spectralNormalization n := by
    rw [show Q.coeff n=_ from scalarPolynomial_first_top_continuation _ _ _ _ _ _,scalarPolynomial_eval_spectral]
  have hp:(rationalNodalPolynomial n (empty (n+1))).coeff n=spectralNormalization n := by
    rw [←Pairing.padTop_empty,rationalNodalPolynomial_leading,rationalVacuum_empty]
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq Finset.univ (deletionBeta_injective n).injOn
  · simp only [Finset.card_univ,Fintype.card_fin]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [Polynomial.coeff_sub]
    by_cases he:k=n
    · subst k; exact sub_eq_zero.mpr (hp.trans htop.symm)
    · have hkn:n<k := by omega
      rw [rationalNodalPolynomial_degree n _ k (by simp [hkn]),
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (scalarPolynomial_first_degree _ _ _ _ _ _) hkn),sub_self]
  · intro i _
    have hn:=rationalNodalPolynomial_at_node (empty (n+1)) i
    simp only [empty_not_occupied,ite_false,one_mul,nodalVacuum,normalizedVacuum,attachEmpty] at hn
    rw [hn,eval_firstScalarHom]
    change nodalScalar i*1=scalarValue _ (Fin.cons (deletionBeta i) spectralA)
    rw [mul_one,←scalarValue_snoc]
    rfl

lemma rationalInterpolant_empty (n:ℕ) : rationalInterpolant n (empty (n+1))=spectralNormalization (n+1) := by
  simp only [rationalInterpolant,empty_not_occupied,ite_false,one_mul,rationalNodalPolynomial_empty]
  rw [←Polynomial.eval_map,map_firstScalarHom,eval_firstScalarHom]
  change scalarValue ((liftSpectral n).comp (algebraMap ℂ (SpectralField n)))
    (Fin.cons (spectralA (Fin.last n)) (fun i =>liftSpectral n (spectralA i)))=_
  have hc:(liftSpectral n).comp (algebraMap ℂ (SpectralField n))=algebraMap ℂ (SpectralField (n+1)) := by
    ext z; exact liftSpectral_const n z
  rw [hc]
  simp only [liftSpectral_spectralA]
  rw [←scalarValue_snoc]
  have hs:Fin.snoc (fun i:Fin n =>spectralA i.castSucc) (spectralA (Fin.last n))=spectralA := by
    funext i; induction i using Fin.lastCases <;> simp
  rw [hs]
  exact scalarPolynomial_eval_spectral (n+1)







end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators


def SourcePairing.padBottom {n : ℕ} (p : SourcePairing n) : SourcePairing (n+1) :=
  ⟨p.val.padBottom,(p.val.padBottom_occupied_succ (Fin.last n)).mpr p.property⟩

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RealEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset

def angleEvaluation {n : ℕ} (u : Fin n → ℝ) : Laurent n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (angleCharacter u)

@[simp] lemma angleEvaluation_monomial {n : ℕ} (u : Fin n → ℝ) (e : Fin n → ℤ) (z : ℂ) :
    angleEvaluation u (monomialL e z)=z*∏i,anglePhase (u i)^e i := by
  simp [angleEvaluation,monomialL,AddMonoidAlgebra.lift_single,angleCharacter]
@[simp] lemma angleEvaluation_constant {n : ℕ} (u : Fin n → ℝ) (z : ℂ) :
    angleEvaluation u (constantL n z)=z := by
  change angleEvaluation u (monomialL 0 z)=_
  simp
@[simp] lemma angleEvaluation_variable {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    angleEvaluation u (monomialL (variableExponent i) 1)=anglePhase (u i) := by
  simp [variableExponent,Pi.single_apply]

end
end CriticalStrip.Diagram







end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnShelling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical



inductive TurnDisk : ℕ → Type
  | atom {n : ℕ} (p : Pairing n) (g : Fin n → ℤ) : TurnDisk n
  | insert {n m : ℕ} (D : TurnDisk n) (k : ℕ) (hk : k≤n)
      (p : Pairing m) (g : Fin m → ℤ) : TurnDisk (n+m)
  | attach {n m : ℕ} (D : TurnDisk n) (E : TurnDisk m) (k : ℕ) (hk : k≤n) : TurnDisk (n+m)
  | sew {n : ℕ} (D : TurnDisk (n+2)) (k : ℕ) (hk : k≤n) : TurnDisk n

namespace TurnDisk

variable {boundarySize : ℕ}

def Vertex : {n : ℕ} → TurnDisk n → Type
  | n,.atom _ _ => Fin n
  | _,@TurnDisk.insert n m D _ _ _ _ => D.Vertex ⊕ Fin m
  | _,.attach D E _ _ => D.Vertex ⊕ E.Vertex
  | _,.sew D _ _ => D.Vertex

def boundary : {n : ℕ} → (D : TurnDisk n) → Fin n → D.Vertex
  | _,.atom _ _ => id
  | _,.insert D k hk _ _ => BoundaryInsert.boundary k hk D.boundary id
  | _,.attach D E k hk => BoundaryInsert.boundary k hk D.boundary E.boundary
  | _,.sew D k hk => D.boundary ∘ BoundaryErase.keep k hk

def gauge : {n : ℕ} → TurnDisk n → Fin n → ℤ
  | _,.atom _ g => g
  | _,.insert D k hk _ g => BoundaryInsert.gauge k hk D.gauge g
  | _,.attach D E k hk => BoundaryInsert.gauge k hk D.gauge E.gauge
  | _,.sew D k hk => D.gauge ∘ BoundaryErase.keep k hk

def wiring : {n : ℕ} → (D : TurnDisk n) → D.Vertex → D.Vertex → Prop
  | _,.atom p _ => p.Adj
  | _,.insert D _ _ p _ => BoundaryInsert.unionGraph D.wiring p.Adj
  | _,.attach D E _ _ => BoundaryInsert.unionGraph D.wiring E.wiring
  | _,.sew D k hk => BoundarySew.graph D.wiring
      (D.boundary (BoundaryErase.left k hk)) (D.boundary (BoundaryErase.right k hk))
      (Graph.Used D.wiring (D.boundary (BoundaryErase.left k hk)))

instance instSymmVertexWiring (D : TurnDisk boundarySize) : Std.Symm D.wiring := by
  induction D with
  | atom p g => exact ⟨fun _ _ h=> Pairing.adj_symm h⟩
  | insert D k hk p g ih =>
    let := ih
    let : Std.Symm p.Adj := ⟨fun _ _ h=>Pairing.adj_symm h⟩
    exact inferInstanceAs (Std.Symm (BoundaryInsert.unionGraph D.wiring p.Adj))
  | attach D E k hk ih ihE =>
    let := ih
    let := ihE
    exact inferInstanceAs (Std.Symm (BoundaryInsert.unionGraph D.wiring E.wiring))
  | sew D k hk ih =>
    let := ih
    exact inferInstanceAs (Std.Symm (BoundarySew.graph D.wiring _ _ _))

def Compatible : {n : ℕ} → TurnDisk n → Prop
  | _,.atom _ _ => True
  | _,.insert D _ _ _ _ => D.Compatible
  | _,.attach D E _ _ => D.Compatible ∧ E.Compatible
  | _,.sew D k hk => D.Compatible ∧
      (Graph.Used D.wiring (D.boundary (BoundaryErase.left k hk)) ↔
        Graph.Used D.wiring (D.boundary (BoundaryErase.right k hk))) ∧
      D.gauge (BoundaryErase.right k hk)=D.gauge (BoundaryErase.left k hk)-3

 
def edgeTurn : {n : ℕ} → (D : TurnDisk n) → D.Vertex → D.Vertex → ℤ
  | _,.atom _ g => Pairing.arcTurn g
  | _,.insert D _ _ _ g => fun v w=> match v,w with
      | Sum.inl v,Sum.inl w => D.edgeTurn v w
      | Sum.inr i,Sum.inr j => Pairing.arcTurn g i j
      | _,_ => 0
  | _,.attach D E _ _ => fun v w=> match v,w with
      | Sum.inl v,Sum.inl w => D.edgeTurn v w
      | Sum.inr i,Sum.inr j => E.edgeTurn i j
      | _,_ => 0
  | _,.sew D _ _ => fun v w=> if D.wiring v w then D.edgeTurn v w else 0

end TurnDisk
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnWideGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnDisk



def vertexGauge : {n : ℕ} → (D : TurnDisk n) → D.Vertex → ℤ
  | _,.atom _ g => g
  | _,.insert D _ _ _ g => Sum.elim D.vertexGauge g
  | _,.attach D E _ _ => Sum.elim D.vertexGauge E.vertexGauge
  | _,.sew D _ _ => D.vertexGauge

@[simp] lemma vertexGauge_boundary {boundarySize : ℕ} (D : TurnDisk boundarySize)
    (i : Fin boundarySize) :
    D.vertexGauge (D.boundary i)=D.gauge i := by
  induction D with
  | atom p g => rfl
  | @insert n m D k hk p g ih =>
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=BoundaryInsert.cover (m:=m) k hk i
    · simp only [boundary,gauge,vertexGauge,BoundaryInsert.boundary_old,
        BoundaryInsert.gauge_old,Sum.elim_inl,ih]
    · simp only [boundary,gauge,vertexGauge,BoundaryInsert.boundary_fresh,
        BoundaryInsert.gauge_fresh,Sum.elim_inr]
      rfl
  | @attach n m D E k hk ih ihE =>
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=BoundaryInsert.cover (m:=m) k hk i
    · simp only [boundary,gauge,vertexGauge,BoundaryInsert.boundary_old,
        BoundaryInsert.gauge_old,Sum.elim_inl,ih]
    · simp only [boundary,gauge,vertexGauge,BoundaryInsert.boundary_fresh,
        BoundaryInsert.gauge_fresh,Sum.elim_inr,ihE]
  | sew D k hk ih => exact ih _

 

def gate4 {n : ℕ} (D : TurnDisk n) (k : ℕ) (hk : k+4≤n)
    (E : TurnDisk 8) : TurnDisk n :=
  (((D.attach E (k+4) hk).sew (k+3) (by omega)).sew (k+2) (by omega)).sew
    (k+1) (by omega) |>.sew k (by omega)

namespace Gate4

variable {n : ℕ} (D : TurnDisk n) (k : ℕ) (hk : k+4≤n) (E : TurnDisk 8)

abbrev stage0 := D.attach E (k+4) hk
abbrev stage1 := (stage0 D k hk E).sew (k+3) (by omega)
abbrev stage2 := (stage1 D k hk E).sew (k+2) (by omega)
abbrev stage3 := (stage2 D k hk E).sew (k+1) (by omega)

variable (hm : ∀ i : Fin 4, Graph.Used D.wiring (D.boundary (slot k hk i)) ↔ Graph.Used E.wiring (E.boundary (input i)))

include hm


def wire (v w : D.Vertex ⊕ E.Vertex) : Prop := ∃ i : Fin 4,
  Graph.Used E.wiring (E.boundary (input i)) ∧ ((v=.inl (D.boundary (slot k hk i)) ∧ w=.inr (E.boundary (input i))) ∨
    (v=.inr (E.boundary (input i)) ∧ w=.inl (D.boundary (slot k hk i))))

end Gate4
end TurnDisk
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnRhombus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnDisk



namespace Rhombus

def disk (p q : Pairing 6) : TurnDisk 8 :=
  (((TurnDisk.atom p upGauge).insert 6 (by omega) q downGauge).sew 5 (by omega)).sew 4 (by omega)

variable (p q : Pairing 6)

abbrev stage : TurnDisk 12 := (TurnDisk.atom p upGauge).insert 6 (by omega) q downGauge
abbrev joined : TurnDisk 10 := (stage p q).sew 5 (by omega)
end Rhombus
end TurnDisk

 

 


namespace TurnNetwork
open TurnDisk

variable {n : ℕ} (p₀ : Pairing n) (g₀ : Fin n → ℤ)
  (p q : ℕ → Pairing 6) (k : ℕ → ℕ) (hk : ∀ t,k t+4≤n)

def disk : ℕ → TurnDisk n
  | 0 => .atom p₀ g₀
  | t+1 => (disk t).gate4 (k t) (hk t) (Rhombus.disk (p t) (q t))

 

def names : (t : ℕ) → (disk p₀ g₀ p q k hk t).Vertex ≃ Node n t
  | 0 =>
    { toFun := Sum.inl
      invFun := fun v=> match v with
        | .inl i=>i
        | .inr x=>Fin.elim0 x.1
      left_inv := fun _=>rfl
      right_inv := by rintro (i|⟨i,v⟩); rfl; exact Fin.elim0 i }
  | t+1 =>
    Equiv.ofBijective (fun v=> match v with
      | .inl w=>old (names t w)
      | .inr w=>fresh w) ⟨by
        rintro (v|v) (w|w) h
        · exact congrArg Sum.inl ((names t).injective (old_injective h))
        · exact (old_ne_fresh (names t v) w h).elim
        · exact (old_ne_fresh (names t w) v h.symm).elim
        · exact congrArg Sum.inr (fresh_injective h),by
        intro v
        obtain ⟨w,rfl⟩|⟨w,rfl⟩:=cover v
        · exact ⟨.inl ((names t).symm w),by simp only [Equiv.apply_symm_apply]⟩
        · exact ⟨.inr w,rfl⟩⟩

def graph (t : ℕ) (v w : Node n t) : Prop :=
  (disk p₀ g₀ p q k hk t).wiring ((names p₀ g₀ p q k hk t).symm v)
    ((names p₀ g₀ p q k hk t).symm w)
def edgeTurn (t : ℕ) (v w : Node n t) : ℤ :=
  (disk p₀ g₀ p q k hk t).edgeTurn ((names p₀ g₀ p q k hk t).symm v)
    ((names p₀ g₀ p q k hk t).symm w)
def boundary (t : ℕ) (i : Fin n) : Node n t :=
  names p₀ g₀ p q k hk t ((disk p₀ g₀ p q k hk t).boundary i)

instance instSymmNodeGraph (t : ℕ) : Std.Symm (graph p₀ g₀ p q k hk t) :=
  ⟨by intro v w h; exact (symm h : (disk p₀ g₀ p q k hk t).wiring _ _)⟩



def Occupied (t : ℕ) : Node n t → Prop
  | .inl i=>p₀.Occupied i
  | .inr (i,.inl v)=>(p i.val).Occupied v
  | .inr (i,.inr v)=>(q i.val).Occupied v

end TurnNetwork
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnNetwork
open TurnDisk


variable {n : ℕ} (p₀ : Pairing n) (g₀ : Fin n → ℤ)
  (p q : ℕ → Pairing 6) (k : ℕ → ℕ) (hk : ∀ t,k t+4 ≤ n)


def Matches (t : ℕ) : Prop :=
  (∀ u,u<t → ∀ i : Fin 2,(p u).Occupied ⟨4+i.val,by omega⟩ ↔
    (q u).Occupied ⟨1-i.val,by omega⟩) ∧
  (∀ u,u<t → ∀ i : Fin 4,Occupied p₀ p q u (boundary p₀ g₀ p q k hk u
    (Gate4.slot (k u) (hk u) i)) ↔ (p u).Occupied ⟨3-i.val,by omega⟩)

end TurnNetwork

 

 

namespace TurnRectangle
open TurnDisk TurnNetwork
section BoundaryEvolution

variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (g₀ : Fin (ports M N) → ℤ) (p q : ℕ → Pairing 6)

abbrev box (t : ℕ) := disk p₀ g₀ p q (position M N) (position_bound hM hN) t
abbrev bdry (t : ℕ) := boundary p₀ g₀ p q (position M N) (position_bound hM hN) t

end BoundaryEvolution






end TurnRectangle
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnRectangleMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TurnRectangle
open TurnDisk TurnNetwork

variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (p q : ℕ → Pairing 6)

 
def PhysicalMatches : Prop :=
  (∀ c r, c<M → r<N → ∀ l : Fin 2,
    (p (c*N+r)).Occupied ⟨4+l.val,by omega⟩ ↔ (q (c*N+r)).Occupied ⟨1-l.val,by omega⟩) ∧
  (∀ c, (hc : c<M) → ∀ l : Fin 2,
    p₀.Occupied (southSlot hM hN hc (by omega : 0<N) l) ↔
      (p (c*N)).Occupied ⟨3-l.val,by omega⟩) ∧
  (∀ r, (hr : r<N) → ∀ l : Fin 2,
    p₀.Occupied (westSlot hM hN (by omega : 0<M) hr l) ↔
      (p r).Occupied ⟨1-l.val,by omega⟩) ∧
  (∀ c r, c<M → r<N → 0 < r → ∀ l : Fin 2,
    (q (c*N+(r-1))).Occupied ⟨4+l.val,by omega⟩ ↔
      (p (c*N+r)).Occupied ⟨3-l.val,by omega⟩) ∧
  (∀ c r, c<M → 0 < c → r<N → ∀ l : Fin 2,
    (q ((c-1)*N+r)).Occupied ⟨2+l.val,by omega⟩ ↔
      (p (c*N+r)).Occupied ⟨1-l.val,by omega⟩)

end TurnRectangle

 

 

namespace TurnStarter

variable (w : ℕ)

def pairing (active : Fin w → Prop) : Pairing (2*w) :=
  ⟨((Finset.univ.filter active).image (fun i=>(left w i,right w i))),by
    constructor
    · intro e he
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
      exact left_lt_right w i i
    constructor
    · intro e he f hf
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hf
      by_cases hij : i=j
      · subst j
        exact Or.inl rfl
      · right
        exact ⟨fun h=>hij (left_injective w h),(left_lt_right w i j).ne,
          (left_lt_right w j i).ne.symm,fun h=>hij (right_injective w h)⟩
    · intro e he f hf
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hf
      change ¬(left w i<left w j ∧ left w j < right w i ∧ right w i < right w j)
      simp only [Fin.lt_def,left,right]
      omega⟩

end TurnStarter

 

 

namespace TurnRectangle
open TurnDisk TurnNetwork
section PhysicalMatching

variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (p q : ℕ → Pairing 6)

abbrev edges := graph p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) (M*N)
abbrev turns := edgeTurn p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) (M*N)

end PhysicalMatching

 

 


variable {M N : ℕ}

variable (hM : 1 ≤ M) (hN : 1 ≤ N) (p q : ℕ → Pairing 6)

def starterActive (i : Fin (width M N)) : Prop :=
  if i.val<2*M then (p ((M-1-i.val/2)*N)).Occupied ⟨3-i.val%2,by omega⟩
  else (p (i.val/2-M)).Occupied ⟨1-i.val%2,by omega⟩

def startPairing : Pairing (ports M N) := TurnStarter.pairing (width M N) (starterActive (M:=M) (N:=N) p)



def InteriorMatches : Prop :=
  (∀ c r, c<M → r<N → ∀ l : Fin 2,
    (p (c*N+r)).Occupied ⟨4+l.val,by omega⟩ ↔ (q (c*N+r)).Occupied ⟨1-l.val,by omega⟩) ∧
  (∀ c r, c<M → r<N → 0 < r → ∀ l : Fin 2,
    (q (c*N+(r-1))).Occupied ⟨4+l.val,by omega⟩ ↔ (p (c*N+r)).Occupied ⟨3-l.val,by omega⟩) ∧
  (∀ c r, c<M → 0 < c → r<N → ∀ l : Fin 2,
    (q ((c-1)*N+r)).Occupied ⟨2+l.val,by omega⟩ ↔ (p (c*N+r)).Occupied ⟨1-l.val,by omega⟩)

end TurnRectangle






end
end CriticalStrip.Diagram

end OAI
end


