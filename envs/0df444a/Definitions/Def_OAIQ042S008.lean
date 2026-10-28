-- Prove2me | Definitions.Def_OAIQ042S008
-- name    : OAIQ042S008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:42:37.414983+00:00
-- url     : https://prove2.me/theorems/9d5b26d8-a0fc-4d26-9432-5e3d1619c1cb
-- title:
--   Definitions bundle OAIQ042S008 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 251 declarations of OpenAI's Lean: 47 definitions and 204 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.arcColumn`, `OAI.CriticalStrip.Diagram.archRootCoefficient`, `OAI.CriticalStrip.Diagram.copiedNodeScalar`, `OAI.CriticalStrip.Diagram.deleteEvaluation`, `OAI.CriticalStrip.Diagram.deletePairPolynomial`, `OAI.CriticalStrip.Diagram.deletePairScalar`, `OAI.CriticalStrip.Diagram.deletePoint`, `OAI.CriticalStrip.Diagram.deleteWeights`, `OAI.CriticalStrip.Diagram.deletionMapL`, `OAI.CriticalStrip.Diagram.fcos`, `OAI.CriticalStrip.Diagram.firstFlatEvaluation`, `OAI.CriticalStrip.Diagram.firstFlatPoint`, `OAI.CriticalStrip.Diagram.firstFlatSmallerScalar`, `OAI.CriticalStrip.Diagram.firstFlatSmallerWeights`, `OAI.CriticalStrip.Diagram.firstThreeEvaluation`, `OAI.CriticalStrip.Diagram.firstThreePoint`, `OAI.CriticalStrip.Diagram.firstThreePolynomial`, `OAI.CriticalStrip.Diagram.firstZeroPolynomial`, `OAI.CriticalStrip.Diagram.freePoint`, `OAI.CriticalStrip.Diagram.lastCoefficient`, `OAI.CriticalStrip.Diagram.lastEvaluation`, `OAI.CriticalStrip.Diagram.lastTransform`, `OAI.CriticalStrip.Diagram.mergeEvaluation`, `OAI.CriticalStrip.Diagram.mergeNewWeights`, `OAI.CriticalStrip.Diagram.mergeNodeWeights`, `OAI.CriticalStrip.Diagram.mergePairPolynomial`, `OAI.CriticalStrip.Diagram.mergePairScalar`, `OAI.CriticalStrip.Diagram.mergePoint`, `OAI.CriticalStrip.Diagram.mergeZ`, `OAI.CriticalStrip.Diagram.nextScalar`, `OAI.CriticalStrip.Diagram.nodalDatumL`, `OAI.CriticalStrip.Diagram.pairBeta`, `OAI.CriticalStrip.Diagram.pairCosines`, `OAI.CriticalStrip.Diagram.pairEarlierWeights`, `OAI.CriticalStrip.Diagram.pairEvaluation`, `OAI.CriticalStrip.Diagram.pairNodeWeights`, `OAI.CriticalStrip.Diagram.pairPoint`, `OAI.CriticalStrip.Diagram.positiveResidualRoot`, `OAI.CriticalStrip.Diagram.rationalResidualPolynomial`, `OAI.CriticalStrip.Diagram.rawLocal` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_ArchRoots`, `StripMass_AugmentedTail`, `StripMass_BlockPfaffian`, `StripMass_CollisionSubstitutions`, `StripMass_CramerBounds`, `StripMass_DiagonalFactors`, `StripMass_FirstFlatSpecialization`, `StripMass_FirstThree`, `StripMass_InterpolantCovariance`, `StripMass_LastRow`, `StripMass_LaurentBox`, `StripMass_LaurentNumerator`, `StripMass_MergePairCandidate`, `StripMass_NodalEmpty`, `StripMass_NodalExchange`, `StripMass_NodalNodes`, `StripMass_NodalScalarDeletion`, `StripMass_NodalTorusValue`, `StripMass_NorthBijection`, `StripMass_PairSelfNode`, `StripMass_PhysicalStationarity`, `StripMass_ResidualEvaluation`, `StripMass_ResidualParityCoefficients`, `StripMass_ScalarDeleteContinuation`, `StripMass_ScalarFlat`, `StripMass_ScalarMergeTrig`, `StripMass_Specialization`, `StripMass_SpecializationPolynomial`, `StripMass_SplitGluing`, `StripMass_SwapVacancy`, `StripMass_TopPadding`.
--
--   **Imports.** It imports the bundles `OAIQ042S002`, `OAIQ042S003` and `OAIQ042S004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S010`, `OAIQ042S011` and `OAIQ042S012`; the statement `OAI.CriticalStrip.Diagram.nextScalar_homogeneous_of_ne`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ042S002
import Definitions.Def_OAIQ042S003
import Definitions.Def_OAIQ042S004

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
theorem realizes_padTop_iff {n : ℕ} (p q : Pairing n) (t : Configuration n) :
    Realizes p.padTop q.padTop t.padTop ↔ Realizes p q t := by
  constructor
  · intro h
    have ht : ∀ i, i.val+1=n → ¬(t i).Occupied 3 := by
      intro i hi ho
      have hg := h.glued i.castSucc (Fin.last n) hi
      exact Tile.vacant_not_occupied 0 (by simpa using hg.mp (by simpa using ho))
    refine ⟨?_, ?_, ?_, ht, ?_, ?_, ?_⟩
    · intro i; simpa using h.west i.castSucc
    · intro i; simpa using h.east i.castSucc
    · intro i hi
      simpa using h.south i.castSucc hi
    · intro i j hij
      simpa using h.glued i.castSucc j.castSucc hij
    · intro v w hvw
      obtain ⟨j,hj,hr⟩ := h.no_loop _ _ ((wiring_padTop_iff p t v w).2 hvw)
      induction j using Fin.lastCases with
      | last => exact (q.padTop_not_occupied_last hj).elim
      | cast j =>
          exact ⟨j,(q.padTop_occupied_castSucc j).1 hj,
            (reach_padTop_iff p t ht v (j,2)).1 hr⟩
    · intro i j hij
      exact (q.padTop_adj_castSucc i j).symm.trans <|
        (h.output i.castSucc j.castSucc (fun h' => hij (Fin.castSucc_injective n h'))).trans
          (reach_padTop_iff p t ht (i,2) (j,2))
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using h.west i
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using h.east i
    · intro i hi
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using h.south i hi
    · intro i hi
      have he : i = Fin.last n := Fin.ext (by change i.val = n; change i.val+1=n+1 at hi; omega)
      subst i; simp
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
          have hj := j.isLt
          change n+1=j.val at hij
          omega
      | cast i =>
          induction j using Fin.lastCases with
          | last => simp [h.north i hij]
          | cast j => simpa using h.glued i j hij
    · rintro ⟨i,a⟩ ⟨j,b⟩ hij
      induction i using Fin.lastCases with
      | last => exact (wiring_padTop_last p t h.north a _ hij).elim
      | cast i =>
          induction j using Fin.lastCases with
          | last => exact (wiring_padTop_last_right p t h.north _ b hij).elim
          | cast j =>
              obtain ⟨k,hk,hr⟩ := h.no_loop _ _ ((wiring_padTop_iff p t (i,a) (j,b)).1 hij)
              exact ⟨k.castSucc,(q.padTop_occupied_castSucc k).2 hk,
                (reach_padTop_iff p t h.north (i,a) (k,2)).2 hr⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last => simp [reach_padTop_last_iff p t h.north, hij.symm]
      | cast i =>
          induction j using Fin.lastCases with
          | last => simp [reach_padTop_last_right_iff p t h.north]
          | cast j =>
              exact (Pairing.padTop_adj_castSucc q i j).trans <|
                (h.output i j (fun h' => hij (congrArg Fin.castSucc h'))).trans
                  (reach_padTop_iff p t h.north (i,2) (j,2)).symm

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



def lastCoefficient {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (q p : Pairing (n+1)) : K := by
  classical
  exact ∑ t : Configuration n,
    if Realizes p q (Fin.snoc t (lastTile p q)) then ∏ i, w i (t i) else 0

theorem lastCoefficient_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) {n : ℕ} (w : Fin n → Tile → K) (q p : Pairing (n+1)) :
    lastCoefficient (fun i a => f (w i a)) q p = f (lastCoefficient w q p) := by
  classical
  simp only [lastCoefficient, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp



def lastTransform {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (q : Pairing (n+1)) : Polynomial K :=
  ∑ p, Polynomial.C (lastCoefficient w q p) * lastFactor d c C p q * P p


end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DiagonalFactors
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.spectralFieldCharZero
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

lemma scalarNormalization_quotient {K : Type*} [Field K] {n : ℕ}
    (dd rr : K) (a : Fin n → K) :
    scalarNormalization dd rr a =
      (∏ e : UpperPair n,discriminant dd (a e.val.1) (a e.val.2)) /
        sourceVandermonde a * pfaffian (augmentedKernel dd rr a) := by
  rw [scalarNormalization,←prod_upperPair,Finset.prod_div_distrib]
  rfl

lemma scalarNormalization_reindex {K : Type*} [Field K] {n : ℕ}
    (dd rr : K) (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    scalarNormalization dd rr (a ∘ σ)=scalarNormalization dd rr a := by
  rw [scalarNormalization_quotient,scalarNormalization_quotient,
    sourceVandermonde_reindex,augmentedKernel_reindex,pfaffian_reindex,augmentedPerm_sign]
  have hp : (∏ e : UpperPair n, discriminant dd ((a ∘ σ) e.val.1) ((a ∘ σ) e.val.2))=
      ∏ e : UpperPair n, discriminant dd (a e.val.1) (a e.val.2) :=
    prod_upperPair_reindex (fun i j => discriminant dd (a i) (a j))
      (fun i j => discriminant_symm dd (a i) (a j)) σ
  rw [hp]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs,div_neg]

lemma permSpectral_normalization {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permSpectral σ (spectralNormalization n)=spectralNormalization n := by
  simp only [spectralNormalization,map_scalarNormalization,permSpectral_const,permSpectral_spectralA]
  exact scalarNormalization_reindex (constF n d) (constF n rho) spectralA σ

end

 

 

noncomputable section
open scoped Classical



lemma insertSpectral_normalization {n : ℕ} (i : Fin (n+1)) :
    insertSpectral i (spectralNormalization n)=
      scalarNormalization (constF (n+1) d) (constF (n+1) rho) (fun j => spectralA (i.succAbove j)) := by
  simp only [spectralNormalization,map_scalarNormalization,insertSpectral_const,insertSpectral_spectralA]

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
open Finset

theorem isolateFirstNumerator_selected {R : Type*} [Zero R] {m : ℕ}
    (N : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R)
    (σ : Equiv.Perm (Fin (2*(m+1)))) (hσ : firstPair m ∈ selectedPairs σ)
    (i : Fin (2*(m+1)/2)) :
    isolateFirstNumerator N (σ (pairFirst _ i)) (σ (pairSecond _ i)) =
      N (σ (pairFirst _ i)) (σ (pairSecond _ i)) := by
  classical
  unfold isolateFirstNumerator
  rw [ite_eq_right]
  rintro (h | h)
  all_goals
    have he : permutationPair σ i = firstPair m := selectedPairs_incident_unique σ _ _
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hσ 0
      ((upperPair_incident_iff _ _ _ _).mpr (by aesop)) (Or.inl rfl)
    rw [firstPair_eq_upperPair] at he
    rcases (upperPair_eq_iff _ _).mp he with hc | hc
    · simp_all
    · simp_all



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BlockPfaffian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset



theorem clearedPfaffian_collision {R : Type*} [CommRing R] {m : ℕ}
    (t : R) (N D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) (hD : D 0 1 = 0) :
    clearedPfaffian t N D =
      clearedPfaffian t (isolateFirstNumerator N) (repairFirstDenominator D) := by
  classical
  unfold clearedPfaffian
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  by_cases hσ : firstPair m ∈ selectedPairs σ
  · unfold clearedPfaffianTerm
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      exact (isolateFirstNumerator_selected N σ hσ i).symm
    · apply Finset.prod_congr rfl
      intro e he
      exact (repairFirstDenominator_compl D σ hσ e he).symm
  · rw [clearedPfaffianTerm_of_missing_pair N D hD σ hσ]
    simp only [clearedPfaffianTerm,
      isolateFirstNumerator_prod_of_missing_pair N σ hσ, zero_mul]



theorem clearedPfaffian_collision_formula {K : Type*} [Field K] [CharZero K] {m : ℕ}
    (N D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hN : ∀ i j, N j i = -N i j) (hD : ∀ i j, D i j = D j i)
    (hzero : D 0 1 = 0)
    (hne : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) → D i j ≠ 0) :
    clearedPfaffian (2^((2*(m+1))/2) * (Nat.factorial ((2*(m+1))/2) : K))⁻¹ N D =
      (∏ e : UpperPair (2*(m+1)), repairFirstDenominator D e.val.1 e.val.2) *
        (N 0 1 * pfaffian (fun i j : Fin (2*m) =>
          N i.succ.succ j.succ.succ / D i.succ.succ j.succ.succ)) := by
  classical
  rw [clearedPfaffian_collision _ N D hzero]
  rw [← clear_pfaffian (isolateFirstNumerator N) (repairFirstDenominator D)
    (repairFirstDenominator_symm D hD) (by
      intro i j hij
      unfold repairFirstDenominator
      split_ifs with h
      · exact one_ne_zero
      · exact hne i j hij h)]
  congr 1
  let M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K := fun i j =>
    isolateFirstNumerator N i j / repairFirstDenominator D i j
  have hM : ∀ i j, M j i = -M i j := by
    intro i j
    dsimp [M]
    rw [isolateFirstNumerator_skew N hN i j,
      repairFirstDenominator_symm D hD j i, neg_div]
  change pfaffian M = _
  rw [pfaffian_isolated M hM (by intro j hj; simp [M,isolateFirstNumerator,hj])]
  have h01 : M 0 1 = N 0 1 := by
    simp [M,isolateFirstNumerator,repairFirstDenominator]
  rw [h01]
  congr 2








theorem clearedPfaffian_delete_even {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : n % 2 = 0) (N D : Matrix (Fin (n+2)) (Fin (n+2)) K)
    (hN : ∀ i j, N j i = -N i j) (hD : ∀ i j, D i j = D j i)
    (hzero : D 0 1 = 0)
    (hne : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) → D i j ≠ 0) :
    clearedPfaffian (2^((n+2)/2) * (Nat.factorial ((n+2)/2) : K))⁻¹ N D =
      N 0 1 * (∏ j : Fin n, D 0 j.succ.succ * D 1 j.succ.succ) *
        ((∏ e : UpperPair n, D e.val.1.succ.succ e.val.2.succ.succ) *
          pfaffian (fun i j : Fin n => N i.succ.succ j.succ.succ / D i.succ.succ j.succ.succ)) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = 2*m := ⟨n/2,by omega⟩
  apply Eq.trans (clearedPfaffian_collision_formula N D hN hD hzero hne)
  apply Eq.trans (congrArg (fun z => z *
    (N 0 1 * pfaffian (fun i j : Fin (2*m) =>
      N i.succ.succ j.succ.succ / D i.succ.succ j.succ.succ)))
        (prod_upperPair_two (n := 2*m) (repairFirstDenominator D)))
  have hs : ∀ i : Fin (2*m), i.succ.succ ≠ (1 : Fin (2*m+2)) := by
    intro i h
    have := congrArg Fin.val h
    simp at this
  simp only [repairFirstDenominator, Fin.succ_ne_zero, hs,
    and_false, or_false, ite_false,
    and_self, true_or, ite_true, one_mul]
  ac_rfl

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedTail
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

theorem scalarNumerator_delete {K : Type*} [Field K] [CharZero K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (x y : K) (a : Fin n → K)
    (hzero : discriminant (f dd) x y = 0)
    (hD : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) →
      discriminant (f dd) (twoCons x y a i) (twoCons x y a j) ≠ 0) :
    MvPolynomial.eval₂Hom f (twoCons x y a) (scalarNumerator (n+2) dd rr) =
      (x-y)*(x+y+f rr) * (∏ i : Fin n, discriminant (f dd) x (a i) * discriminant (f dd) y (a i)) *
        MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) := by
  let N : Matrix (Fin ((n+n%2)+2)) (Fin ((n+n%2)+2)) K := fun i j =>
    augmentedNumerator (f rr) (twoCons x y a) (augmentTwoIndex n i) (augmentTwoIndex n j)
  let D : Matrix (Fin ((n+n%2)+2)) (Fin ((n+n%2)+2)) K := fun i j =>
    augmentedDenominator (f dd) (twoCons x y a) (augmentTwoIndex n i) (augmentTwoIndex n j)
  have hN : ∀ i j, N j i = -N i j := fun i j =>
    augmentedNumerator_skew _ _ _ _
  have hDs : ∀ i j, D i j = D j i := fun i j =>
    augmentedDenominator_symm _ _ _ _
  have hD0 : D 0 1 = 0 := by simpa [D] using hzero
  have hDn : ∀ i j, i ≠ j → ¬ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) → D i j ≠ 0 := by
    intro i j hij hp
    change (if hi : i.val < n + 2 then
      if hj : j.val < n + 2 then
        discriminant (f dd) (twoCons x y a ⟨i.val, hi⟩) (twoCons x y a ⟨j.val, hj⟩)
      else 1 else 1) ≠ 0
    by_cases hi : i.val < n + 2
    · by_cases hj : j.val < n + 2
      · rw [dite_eq_left hi, dite_eq_left hj]
        apply hD
        · intro he
          exact hij (Fin.ext (congrArg (fun z : Fin (n+2) => z.val) he))
        · intro he
          apply hp
          simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one] at he ⊢
          omega
      · simpa only [dite_eq_left hi, dite_eq_right hj] using (one_ne_zero : (1 : K) ≠ 0)
    · simpa only [dite_eq_right hi] using (one_ne_zero : (1 : K) ≠ 0)
  have hs : (n+2)+(n+2)%2 = (n+n%2)+2 := by omega
  have ht : (2^(((n+2)+(n+2)%2)/2) * (Nat.factorial (((n+2)+(n+2)%2)/2) : K))⁻¹ =
      (2^(((n+n%2)+2)/2) * (Nat.factorial (((n+n%2)+2)/2) : K))⁻¹ := by rw [hs]
  have hc := clearedPfaffian_cast hs
    (2^(((n+2)+(n+2)%2)/2) * (Nat.factorial (((n+2)+(n+2)%2)/2) : K))⁻¹
      (augmentedNumerator (f rr) (twoCons x y a))
      (augmentedDenominator (f dd) (twoCons x y a))
  change clearedPfaffian _ N D = _ at hc
  rw [scalarNumerator_eval_cleared, ← hc, ht,
    clearedPfaffian_delete_even (by omega : (n+n%2)%2 = 0) N D hN hDs hD0 hDn]
  have hN01 : N 0 1 = (x-y)*(x+y+f rr) := by simp [N]
  have hcross : (∏ i : Fin (n+n%2), D 0 i.succ.succ * D 1 i.succ.succ) =
      ∏ i : Fin n, discriminant (f dd) x (a i) * discriminant (f dd) y (a i) := by
    simpa only [D, augmentTwoIndex_zero, augmentTwoIndex_one] using
      augmentedDenominator_two_cross (f dd) x y a
  rw [hN01, hcross]
  congr 1
  have htail : ∀ i j : Fin n, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0 := by
    intro i j hij
    have h := hD i.succ.succ j.succ.succ
      (by simpa only [ne_eq, Fin.succ_inj] using hij) (by simp)
    simpa only [twoCons_succ_succ] using h
  rw [scalarNumerator_eval f n dd rr a htail]
  congr 1
  · apply Finset.prod_congr rfl
    intro e _
    exact augmentedDenominator_two_tail _ _ _ _ _ _
  · congr 1
    funext i j
    dsimp [N,D]
    rw [augmentedNumerator_two_tail, augmentedDenominator_two_tail, ← augmentedKernel_eq]







end

 

 

noncomputable section






open Finset
open scoped Classical



theorem lastTransform_coeff_succ {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (q : Pairing (n+1)) (k : ℕ) :
    (lastTransform w d c C P q).coeff (k+1) = ∑ p, lastCoefficient w q p *
      (if q.Occupied (Fin.last n) then
        if p.Occupied (Fin.last n) then (P p).coeff k - c * (P p).coeff (k+1)
        else (2*d) * (P p).coeff (k+1)
      else if p.Occupied (Fin.last n) then d * ((P p).coeff k - c * (P p).coeff (k+1))
        else (P p).coeff k + C * (P p).coeff (k+1)) := by
  classical
  simp only [lastTransform, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Occupied (Fin.last n) <;> by_cases hq : q.Occupied (Fin.last n)
  all_goals simp [lastFactor, hp, hq, mul_add, mul_sub, add_mul, sub_mul,
    mul_assoc, Polynomial.coeff_C_mul]

theorem lastTransform_degree {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) {m : ℕ} (hP : LastDegree m P) :
    LastDegree (m+1) (lastTransform w d c C P) := by
  classical
  intro q k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := by
    by_cases hq : q.Occupied (Fin.last n) <;> simp only [hq, ite_true, ite_false] at hk <;>
      exact ⟨k-1, by omega⟩
  rw [lastTransform_coeff_succ]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hq : q.Occupied (Fin.last n) <;> by_cases hp : p.Occupied (Fin.last n)
  all_goals simp only [hq, hp, ite_true, ite_false] at hk ⊢
  all_goals have h₁ : (P p).coeff (j+1) = 0 := hP p (j+1) (by simp [hp]; omega)
  · have h₀ : (P p).coeff j = 0 := hP p j (by simp [hp]; omega)
    simp [h₀, h₁]
  · simp [h₁]
  · have h₀ : (P p).coeff j = 0 := hP p j (by simp [hp]; omega)
    simp [h₀, h₁]
  · have h₀ : (P p).coeff j = 0 := hP p j (by simp [hp]; omega)
    simp [h₀, h₁]

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
open scoped Classical LaurentPolynomial

lemma peel_beta_coeff_self {n:ℕ} (i:Fin (n+1)) (e:ℤ) :
    (peelLaurent i (betaL i)).coeff e=
      (if e=2 then constF n (phase^3/2) else 0)+(if e=(-2) then constF n ((phase^3)⁻¹/2) else 0) := by
  rw [peelLaurent_coeff,peel_betaL_self]
  simp only [←LaurentPolynomial.single_eq_C_mul_T,AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single,Finsupp.add_apply]
  change (algebraMap (SpectralRing n) (SpectralField n))
    ((Finsupp.single 2 (constantL n (phase^3/2))) e +
      (Finsupp.single (-2) (constantL n ((phase^3)⁻¹/2))) e)=_
  simp only [Finsupp.single_apply]
  rw [map_add]
  congr 1
  · by_cases h:e=2
    · subst e
      rw [ite_eq_left rfl,ite_eq_left rfl]
      exact map_constantL n _
    · rw [ite_eq_right (Ne.symm h),ite_eq_right h,map_zero]
  · by_cases h:e=(-2)
    · subst e
      rw [ite_eq_left rfl,ite_eq_left rfl]
      exact map_constantL n _
    · rw [ite_eq_right (Ne.symm h),ite_eq_right h,map_zero]

lemma peel_beta_coeff_other {n:ℕ} (i:Fin (n+1)) (j:Fin n) (e:ℤ) :
    (peelLaurent i (betaL (i.succAbove j))).coeff e=if e=0 then deletionBeta j else 0 := by
  rw [peelLaurent_coeff,peel_betaL_other]
  change evalLaurent ((AddMonoidAlgebra.single 0 (betaL j)).coeff e)=_
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  by_cases h:e=0
  · subst e
    rw [ite_eq_left rfl,ite_eq_left rfl]
    exact betaL_map j
  · rw [ite_eq_right (Ne.symm h),ite_eq_right h]
    exact map_zero _

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

lemma functionMatrix_map_mulVec_empty {K : Type*} [CommRing K] {n m : ℕ}
    (e : Fin n ↪o Fin m) (v : Pairing n → K) :
    (functionMatrix (K:=K) (Pairing.map e)).mulVec v (empty m)=v (empty n) := by
  simp [Matrix.mulVec,dotProduct,functionMatrix,optionMatrix,Pairing.map_eq_empty_iff]


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
open scoped Classical

 
def rawLocal {K : Type*} [CommRing K] {n : ℕ} (r : Position n) (w : Tile → K) :
    Matrix (Pairing n) (Pairing n) K :=
  ∑ t : Tile, w t • optionMatrix (fun p => p.tileStep r.left r.right r.adjacent t)

lemma rawLocal_smul {K : Type*} [CommRing K] {n : ℕ} (r : Position n)
    (a : K) (w : Tile → K) : rawLocal r (fun t => a*w t)=a • rawLocal r w := by
  simp only [rawLocal,Finset.smul_sum,smul_smul]


end





noncomputable section


theorem deletion_occupied_sine_cancellation {n : ℕ} (i : Fin n) :
    spectralA i+deletionBeta i+constF n rho=
      4*constF n c*torusSin (deletionNode i)*
        torusSin (constF n phase^3/variableF i) := by
  have hq:=constF_phase_ne_zero n
  have hi:=variableF_ne_zero i
  have hβ : deletionBeta i=torusCos (variableF i^2*constF n phase^3) := by
    unfold deletionBeta deletionNode
    congr 1
    field_simp
  have hs:=torusCos_sum (variableF i^2) (constF n phase^3)
    (pow_ne_zero _ hi) (pow_ne_zero _ hq)
  rw [torusCos_phase_pow] at hs
  change spectralA i+torusCos (variableF i^2*constF n phase^3)=
    2*torusCos (variableF i^2)*constF n c at hs
  have hp:=torusSin_product (deletionNode i) (constF n phase^3/variableF i)
    (mul_ne_zero hi (pow_ne_zero _ hq)) (div_ne_zero (pow_ne_zero _ hq) hi)
  have he₁ : deletionNode i/(constF n phase^3/variableF i)=variableF i^2 := by
    unfold deletionNode
    field_simp
  have he₂ : deletionNode i*(constF n phase^3/variableF i)=constF n phase^6 := by
    unfold deletionNode
    field_simp
  rw [he₁,he₂,torusCos_phase_pow] at hp
  simp only [Nat.cast_ofNat,cos_six_lambda,Complex.ofReal_neg,constF,map_neg] at hp
  have hr:=congrArg (fun x : ℝ => constF n (x:ℂ)) rho_eq_two_c_d
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,constF,map_mul,map_ofNat] at hr
  rw [hβ]
  unfold constF at *
  linear_combination hs+hr-2*(algebraMap ℂ (SpectralField n)) (c:ℂ)*hp


 

 

open scoped Classical



def reducedMovingStep {n : ℕ} (i j : Fin n) :
    Matrix (Pairing (n+1)) (Pairing (n+1)) (SpectralField n) :=
  if j=i then 1 else
    (-4*torusSin (variableF i*variableF j/constF n phase^6)) •
      if i<j then rawLocal (PartialColumn.rowPosition j.val (by omega))
        (torusNumerator (constF n phase^3*(variableF i/variableF j)))
      else torusL (constF n phase^3*(variableF i/variableF j)) • 1

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaurentNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma sineL_product_box {n : ℕ} (e f : Fin n → ℤ) (z w : ℂ) (b : Fin n → ℕ)
    (he : ∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) (hf : ∀ i,-(b i:ℤ)≤f i ∧ f i≤b i) :
    LaurentBox (sineL e z*sineL f w) (b+b) :=
  LaurentBox.mul (LaurentBox.sine e z b he) (LaurentBox.sine f w b hf)

lemma constant_sineL_box {n : ℕ} (e : Fin n → ℤ) (z w : ℂ) (b : Fin n → ℕ)
    (he : ∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) :
    LaurentBox (constantL n z*sineL e w) (b+b) :=
  LaurentBox.mul ((LaurentBox.constant z).mono (fun i => Nat.zero_le (b i)))
    (LaurentBox.sine e w b he)

lemma torusNumeratorL_box {n : ℕ} (e : Fin n → ℤ) (z : ℂ)
    (b : Fin n → ℕ) (h:∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) (t : Tile) :
    LaurentBox (torusNumeratorL e z t) (b+b) := by
  have hn : ∀ i,-(b i:ℤ)≤(-e) i ∧ (-e) i≤b i := by
    intro i; have := h i; simp only [Pi.neg_apply]; omega
  cases t with
  | vacant => exact sineL_product_box e e _ _ b h h
  | cap => exact constant_sineL_box e _ _ b h
  | cup => exact constant_sineL_box e _ _ b h
  | vertical₀ => exact constant_sineL_box (-e) _ _ b hn
  | vertical₁ => exact constant_sineL_box (-e) _ _ b hn
  | diagonal₀ => exact sineL_product_box e (-e) _ _ b h hn
  | diagonal₁ => exact sineL_product_box e (-e) _ _ b h hn
  | verticalPair => exact sineL_product_box (-e) (-e) _ _ b hn hn
  | capCup => exact sineL_product_box e e _ _ b h h


 

 


lemma rawLocal_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    {n : ℕ} (r : Position n) (w : Tile → K) :
    (rawLocal r w).map f=rawLocal r (fun t => f (w t)) := by
  ext p q
  simp only [rawLocal,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro t _
  unfold optionMatrix
  split_ifs <;> simp

lemma rawLocal_box {n m : ℕ} (r : Position m) (w : Tile → Laurent n)
    (b : Fin n → ℕ) (hw : ∀ t,LaurentBox (w t) b) :
    LaurentMatrixBox (rawLocal r w) b := by
  intro p q
  simp only [rawLocal,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply LaurentBox.sum
  intro t _
  unfold optionMatrix
  split_ifs
  · simpa using hw t
  · simp only [mul_zero]; exact LaurentBox.zero _

lemma matrixPrefix_box_partial {n m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (A : Fin m → Matrix α α (Laurent n)) (b : Fin m → Fin n → ℕ)
    (hA : ∀ i,LaurentMatrixBox (A i) (b i)) (k : ℕ) :
    LaurentMatrixBox (matrixPrefix A k)
      (∑ j ∈ Finset.range k, (if h : j < m then b ⟨j, h⟩ else 0)) := by
  induction k with
  | zero => simp only [matrixPrefix,Finset.range_zero,Finset.sum_empty]; exact LaurentMatrixBox.one
  | succ k ih =>
    rw [matrixPrefix,Finset.sum_range_succ]
    by_cases hk : k < m
    · rw [dite_eq_left hk,dite_eq_left hk,add_comm]
      exact (hA ⟨k,hk⟩).mul ih
    · rw [dite_eq_right hk,dite_eq_right hk,add_zero]
      exact ih

lemma matrixPrefix_box {n m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (A : Fin m → Matrix α α (Laurent n)) (b : Fin m → Fin n → ℕ)
    (hA : ∀ i,LaurentMatrixBox (A i) (b i)) :
    LaurentMatrixBox (matrixPrefix A m) (∑ j,b j) := by
  rw [Finset.sum_fin_eq_sum_range]
  exact matrixPrefix_box_partial A b hA m







def reducedMovingStepL {n : ℕ} (i j : Fin n) :
    Matrix (Pairing (n+1)) (Pairing (n+1)) (Laurent n) :=
  if j=i then 1 else
    (constantL n (-4)*sineL (variableExponent i+variableExponent j) (phase^(-6:ℤ))) •
      if i<j then rawLocal (PartialColumn.rowPosition j.val (by omega))
        (torusNumeratorL (variableExponent i-variableExponent j) (phase^3))
      else torusNumeratorL (variableExponent i-variableExponent j) (phase^3) .vacant • 1

lemma reducedMovingStepL_map {n : ℕ} (i j : Fin n) :
    (reducedMovingStepL i j).map (algebraMap (SpectralRing n) (SpectralField n))=
      reducedMovingStep i j := by
  by_cases h:j=i
  · simp [reducedMovingStepL,reducedMovingStep,h]
  · simp only [reducedMovingStepL,reducedMovingStep,ite_eq_right h]
    rw [matrix_map_ring_smul]
    change evalLaurent _ • _ = _
    rw [reducedMovingStepL_scalar]
    congr 1
    by_cases hij:i<j
    · rw [ite_eq_left hij,ite_eq_left hij,rawLocal_map]
      congr 1
      funext t
      exact torusNumeratorL_pair_map i j t
    · rw [ite_eq_right hij,ite_eq_right hij,matrix_map_ring_smul]
      rw [show (1 : Matrix (Pairing (n+1)) (Pairing (n+1)) (Laurent n)).map
        (algebraMap (SpectralRing n) (SpectralField n))=1 by simp]
      congr 1
      exact torusNumeratorL_pair_map i j .vacant

lemma reducedMovingTrainL_map {n : ℕ} (i : Fin n) :
    (matrixPrefix (reducedMovingStepL i) n).map (algebraMap (SpectralRing n) (SpectralField n))=
      matrixPrefix (reducedMovingStep i) n := by
  rw [matrixPrefix_map]
  congr 1
  funext j
  exact reducedMovingStepL_map i j









def deletionMapL {n m : ℕ} (r : ℕ) (hr:r+2≤n+2) :
    Matrix (Pairing (n+2)) (Pairing n) (Laurent m) :=
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (rawLocal (PartialColumn.rowPosition r hr) (deletionWeights : Weights (Laurent m)).tile)
    (@HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (functionMatrix (K:=Laurent m) (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+2)))))
      (functionMatrix (K:=Laurent m) (Pairing.map (Fin.succAboveOrderEmb (⟨r,by omega⟩ : Fin (n+1))))))



def nodalDatumL {n : ℕ} (W : Pairing n → Laurent n) (i : Fin (n+1)) (p : Pairing (n+2)) : Laurent (n+1) :=
  (∏ j,reflectionFactorL i j)*nodalHeadL i (p.Occupied (Fin.last (n+1)))*
    (matrixPrefix (reducedMovingStepL i) (n+1)).mulVec
      ((deletionMapL i.val (show i.val+2≤n+2 by omega)).mulVec
        (fun q => insertLaurent i (W q))) p

lemma functionMatrix_box {n:ℕ} {α β:Type*} (f:α → β) :
    LaurentMatrixBox (functionMatrix (K:=Laurent n) f) 0 := by
  intro p q
  unfold functionMatrix optionMatrix
  split_ifs
  · exact LaurentBox.one
  · exact LaurentBox.zero _

lemma reflectionFactorL_box {n:ℕ} (i j:Fin n) :
    LaurentBox (reflectionFactorL i j) (pairBound i j) := by
  by_cases h:j=i
  · subst j
    rw [reflectionFactorL,ite_eq_left rfl]
    convert LaurentBox.one (n:=n) using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    simp [pairBound]
  · rw [reflectionFactorL,ite_eq_right h]
    exact LaurentBox.sine _ _ _ (pairBound_add i j h)

lemma reducedMovingStepL_box {n:ℕ} (i j:Fin n) :
    LaurentMatrixBox (reducedMovingStepL i j) (fun k => 3*pairBound i j k) := by
  by_cases h:j=i
  · subst j
    rw [reducedMovingStepL,ite_eq_left rfl]
    convert LaurentMatrixBox.one (n:=n) (α:=Pairing (n+1)) using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    simp [pairBound]
  · rw [reducedMovingStepL,ite_eq_right h]
    have hs:LaurentBox (constantL n (-4)*sineL (variableExponent i+variableExponent j) (phase^(-6:ℤ))) (pairBound i j) := by
      simpa using (LaurentBox.constant (-4)).mul (LaurentBox.sine _ _ _ (pairBound_add i j h))
    have hn:=torusNumeratorL_box (variableExponent i-variableExponent j) (phase^3) (pairBound i j) (pairBound_sub i j)
    have ht:LaurentMatrixBox
        (if i<j then rawLocal (PartialColumn.rowPosition (n:=n+1) j.val (by omega))
          (torusNumeratorL (variableExponent i-variableExponent j) (phase^3))
         else torusNumeratorL (variableExponent i-variableExponent j) (phase^3) .vacant • 1)
        (pairBound i j+pairBound i j) := by
      split_ifs
      · exact rawLocal_box _ _ _ hn
      · simpa using LaurentMatrixBox.smul (hn .vacant) LaurentMatrixBox.one
    convert LaurentMatrixBox.smul hs ht using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    simp only [Pi.add_apply]
    omega

lemma nodalHeadL_box {n:ℕ} (i:Fin n) (occupied:Prop) [Decidable occupied] :
    LaurentBox (nodalHeadL i occupied) (selfBound i 2) := by
  have he:∀ k,-(selfBound i 2 k:ℤ)≤((2:ℤ) • variableExponent i) k ∧
      ((2:ℤ) • variableExponent i) k ≤ selfBound i 2 k := by
    intro k
    by_cases h:k=i <;> simp_all [selfBound,variableExponent]
  have hn:∀ k,-(selfBound i 2 k:ℤ)≤(-variableExponent i) k ∧
      (-variableExponent i) k ≤ selfBound i 2 k := by
    intro k
    by_cases h:k=i <;> simp_all [selfBound,variableExponent,Pi.single_apply]
  unfold nodalHeadL
  split_ifs
  · simpa using (LaurentBox.constant (4*c)).mul (LaurentBox.sine _ _ _ hn)
  · exact ((LaurentBox.cosine _ _ _ he).add (LaurentBox.cosine _ _ _ he)).add
      ((LaurentBox.constant rho).mono (fun k => Nat.zero_le _))

lemma deletionMapL_box {n m:ℕ} (r:ℕ) (hr:r+2≤n+2) :
    LaurentMatrixBox (deletionMapL (m:=m) r hr) 0 := by
  have hw:∀ t:Tile,LaurentBox ((deletionWeights : Weights (Laurent m)).tile t) 0 := by
    intro t
    cases t <;> simp only [Weights.tile,deletionWeights]
    all_goals first | exact LaurentBox.one | exact LaurentBox.zero _
  simpa only [deletionMapL,zero_add,Matrix.mul_assoc] using
    (rawLocal_box (PartialColumn.rowPosition r hr) _ _ hw).mul
      ((functionMatrix_box (n:=m) (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+2))))).mul
        (functionMatrix_box (n:=m) (Pairing.map (Fin.succAboveOrderEmb (⟨r,by omega⟩ : Fin (n+1))))))

 
lemma nodalDatumL_box {n:ℕ} (W:Pairing n → Laurent n)
    (hW:∀ p,LaurentBox (W p) (fun _ => 2*n-2)) (i:Fin (n+1)) (p:Pairing (n+2)) :
    LaurentBox (nodalDatumL W i p) (fun k => if k=i then 4*n+2 else 2*n+2) := by
  have hr:=LaurentBox.prod Finset.univ (reflectionFactorL i) (pairBound i)
    (fun j _ => reflectionFactorL_box i j)
  have ht:=matrixPrefix_box (reducedMovingStepL i) (fun j k => 3*pairBound i j k)
    (reducedMovingStepL_box i)
  have hw:= (deletionMapL_box (m:=n+1) i.val (show i.val+2≤n+2 by omega)).mulVec
    (fun q => (hW q).insert i)
  have hres:= (hr.mul (nodalHeadL_box i (p.Occupied (Fin.last (n+1))))).mul
    (ht.mulVec hw p)
  apply hres.mono
  intro k
  simp only [Pi.add_apply,Finset.sum_apply,zero_add,←Finset.mul_sum,sum_pairBound]
  by_cases hk:k=i
  · subst k
    simp only [selfBound,ite_true,Fin.insertNth_apply_same]
    omega
  · obtain ⟨j,hj⟩:=Fin.exists_succAbove_eq hk
    rw [←hj,Fin.insertNth_apply_succAbove]
    simp only [Fin.succAbove_ne,ite_false,selfBound]
    have hn:1≤n := by have :=j.isLt; omega
    omega

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

lemma betaL_box {n:ℕ} (i:Fin n) : LaurentBox (betaL i) (selfBound i 2) := by
  apply LaurentBox.cosine
  intro k
  by_cases h:k=i <;> simp_all [selfBound,variableExponent]



lemma interpolationNumerator_box {n:ℕ} (W:Pairing n → Laurent n)
    (hW:∀ p,LaurentBox (W p) (fun _ => 2*n-2)) (p:Pairing (n+2)) (a:Fin (n+1)) :
    LaurentBox (interpolationNumerator betaL (fun i => nodalDatumL W i p) a)
      (fun _ => 4*n+2) := by
  let dataBound:=fun (i k:Fin (n+1)) => if k=i then 4*n+2 else 2*n+2
  let b:=fun (i j k:Fin (n+1)) => if j=a then dataBound i k else if k=i then 2*j.val else 0
  apply LaurentMatrixBox.det_terms _ b
  · intro i j
    by_cases hj:j=a
    · subst j
      simpa only [Matrix.updateCol_apply,ite_true,b] using nodalDatumL_box W hW i p
    · rw [Matrix.updateCol_apply,ite_eq_right hj,Matrix.vandermonde_apply]
      have hh:LaurentBox (betaL i ^ j.val) (fun k => j.val*selfBound i 2 k) := (betaL_box i).pow j.val
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext k
      dsimp [b]
      rw [ite_eq_right hj]
      by_cases hk:k=i <;> simp [selfBound,hk,Nat.mul_comm]
  · intro σ k
    by_cases hk:k=σ a
    · have hb (j:Fin (n+1)) : b (σ j) j k=if j=a then 4*n+2 else 0 := by
        by_cases hj:j=a
        · subst j; simp [b,dataBound,hk]
        · have hkj:k≠σ j := by intro h; exact hj (σ.injective (h.symm.trans hk))
          simp [b,hj,hkj]
      simp only [hb,Finset.sum_ite_eq',Finset.mem_univ,ite_true,le_refl]
    · have hb (j:Fin (n+1)) : b (σ j) j k ≤
          (if j=a then 2*n+2 else 0)+(if j=σ.symm k then 2*j.val else 0) := by
        have hkj:k=σ j ↔ j=σ.symm k := by
          constructor
          · intro h; simpa only [Equiv.symm_apply_apply] using (congrArg σ.symm h).symm
          · intro h; simp only [h,Equiv.apply_symm_apply]
        by_cases hj:j=a
        · subst j; simp [b,dataBound,hk]
        · simp only [b,ite_eq_right hj,zero_add,hkj]
          exact le_refl _
      have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hb j)
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
      have hj: (σ.symm k).val<n+1 := (σ.symm k).isLt
      omega

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

lemma beta_difference_box {n:ℕ} (i j:Fin n) :
    LaurentBox (betaL j-betaL i) (fun k => 2*((if i=k then 1 else 0)+(if j=k then 1 else 0))) := by
  apply LaurentBox.sub
  · apply (betaL_box j).mono
    intro k
    by_cases hi:i=k <;> by_cases hj:j=k <;> simp_all [selfBound,eq_comm]
  · apply (betaL_box i).mono
    intro k
    by_cases hi:i=k <;> by_cases hj:j=k <;> simp_all [selfBound,eq_comm]

lemma beta_difference_exact {n:ℕ} (k i j:Fin (n+1)) (hij:i<j) :
    let b:ℤ := 2*((if i=k then 1 else 0)+(if j=k then 1 else 0))
    LaurentInterval (peelLaurent k (betaL j-betaL i)) (-b) b ∧
      (peelLaurent k (betaL j-betaL i)).coeff (-b)≠0 ∧
      (peelLaurent k (betaL j-betaL i)).coeff b≠0 := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · convert (beta_difference_box i j).peel k using 1 <;> push_cast <;> rfl
  all_goals
    have hn:=constants_extreme_nonzero n
    by_cases hi:i=k
    · subst i
      obtain ⟨t,rfl⟩:=Fin.exists_succAbove_eq (ne_of_gt hij)
      simp only [Fin.succAbove_ne,ite_false,add_zero,map_sub,
        AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,peel_beta_coeff_self,peel_beta_coeff_other]
      norm_num only [show (-2:ℤ)≠2 by omega,show (2:ℤ)≠ -2 by omega,show (2:ℤ)≠0 by omega,
        show (-2:ℤ)≠0 by omega,ite_true,ite_false,zero_add,add_zero,zero_sub,neg_ne_zero]
      first | exact hn.1 | exact hn.2
    · by_cases hj:j=k
      · subst j
        obtain ⟨t,rfl⟩:=Fin.exists_succAbove_eq hi
        simp only [Fin.succAbove_ne,ite_false,zero_add,map_sub,
          AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,peel_beta_coeff_self,peel_beta_coeff_other]
        norm_num only [show (-2:ℤ)≠2 by omega,show (2:ℤ)≠ -2 by omega,show (2:ℤ)≠0 by omega,
          show (-2:ℤ)≠0 by omega,ite_true,ite_false,zero_add,add_zero,sub_zero]
        first | exact hn.1 | exact hn.2
      · obtain ⟨s,rfl⟩:=Fin.exists_succAbove_eq hi
        obtain ⟨t,rfl⟩:=Fin.exists_succAbove_eq hj
        simp only [Fin.succAbove_ne,ite_false,zero_add,mul_zero,neg_zero,map_sub,
          AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,peel_beta_coeff_other,ite_true]
        apply sub_ne_zero.mpr
        exact (deletionBeta_injective n).ne (by intro h; subst t; exact lt_irrefl _ hij)

 

lemma vandermonde_beta_exact {n:ℕ} (k:Fin (n+1)) :
    let f:=peelLaurent k (Matrix.vandermonde (@betaL (n+1))).det
    LaurentInterval f (-(2*n:ℤ)) (2*n) ∧ f.coeff (-(2*n:ℤ))≠0 ∧ f.coeff (2*n)≠0 := by
  rw [Matrix.det_vandermonde,←prod_upperPair,map_prod]
  have hs:(∑ e:UpperPair (n+1),(2*((if e.val.1=k then 1 else 0)+(if e.val.2=k then 1 else 0)):ℤ))=2*n := by
    rw [←Finset.mul_sum]
    congr 1
    exact_mod_cast upperPair_incidence_sum k
  have hh:=LaurentInterval.prod_exact Finset.univ
    (fun e:UpperPair (n+1) => peelLaurent k (betaL e.val.2-betaL e.val.1))
    (fun e => -(2*((if e.val.1=k then 1 else 0)+(if e.val.2=k then 1 else 0)):ℤ))
    (fun e => (2*((if e.val.1=k then 1 else 0)+(if e.val.2=k then 1 else 0)):ℤ))
    (fun e _ => beta_difference_exact k e.val.1 e.val.2 e.property)
  simpa only [Finset.sum_neg_distrib,hs] using hh

end





noncomputable section
open scoped Classical
open Finset


lemma column_signTwist {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) (i : Fin n) (p q : Pairing n) :
    column (Function.update w i (w i).signTwist) q p=
      occupancySign q i * occupancySign p i * column w q p := by
  simp only [column,mul_sum]
  apply sum_congr rfl
  intro t _
  split_ifs with ht
  · have h (j : Fin n) : ((Function.update w i (w i).signTwist) j).tile (t j)=
        (if j=i then occupancySign q i * occupancySign p i else 1)*(w j).tile (t j) := by
      by_cases hj:j=i
      · subst j
        rw [Function.update_self,Weights.signTwist_tile]
        simp only [ht.west,ht.east,occupancySign,ite_true]
        ring
      · rw [Function.update_of_ne hj,ite_eq_right hj,one_mul]
    simp_rw [h]
    rw [prod_mul_distrib]
    simp
  · simp

end

 

 

noncomputable section
open scoped Classical

lemma signSpectral_normalization {n : ℕ} (i : Fin n) :
    signSpectral i (spectralNormalization n)=spectralNormalization n := by
  simp only [spectralNormalization,map_scalarNormalization,signSpectral_const,
    signSpectral_spectralA]


lemma column_doubleSignTwist {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) (i j : Fin n) (hij : j≠i) (p q : Pairing n) :
    column (doubleSignTwist w i j) q p=
      (occupancySign q i*occupancySign q j)*(occupancySign p i*occupancySign p j)*column w q p := by
  unfold doubleSignTwist
  conv_lhs => arg 1; arg 3; rw [←Function.update_of_ne hij (w i).signTwist w]
  rw [column_signTwist,column_signTwist]
  ring

lemma signSpectral_nodalScalar {n : ℕ} (k i : Fin n) :
    signSpectral k (nodalScalar i)=nodalScalar i := by
  have hc:(signSpectral k).comp (algebraMap ℂ (SpectralField n))=
      algebraMap ℂ (SpectralField n) := by
    ext z
    exact signSpectral_const k z
  have hv:(fun j : Fin (n+1) => signSpectral k
      ((Fin.snoc spectralA (deletionBeta i) : Fin (n+1) → SpectralField n) j))=
      (Fin.snoc spectralA (deletionBeta i) : Fin (n+1) → SpectralField n) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  rw [nodalScalar,MvPolynomial.map_eval₂Hom,hc,hv]

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

lemma lastPolynomial_unique {K : Type*} [Field K] {n : ℕ}
    (P Q : Pairing (n+1) → Polynomial K)
    (hP : LastDegree n P) (hQ : LastDegree n Q)
    (v : Fin n → K) (hv : Function.Injective v)
    (hlead : ∀ p : Pairing n, (P p.padTop).coeff n=(Q p.padTop).coeff n)
    (hnode : ∀ p i, (P p).eval (v i)=(Q p).eval (v i)) : P=Q := by
  funext p
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq univ hv.injOn
  · simp only [card_univ,Fintype.card_fin]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [Polynomial.coeff_sub]
    by_cases hp : p.Occupied (Fin.last n)
    · rw [hP p k (by simpa only [hp,ite_true] using hk),
        hQ p k (by simpa only [hp,ite_true] using hk), sub_self]
    · by_cases he : k=n
      · subst k
        have h:=hlead (p.restrict Fin.castSuccOrderEmb)
        rw [Pairing.padTop_restrict p hp] at h
        exact sub_eq_zero.mpr h
      · rw [hP p k (by simp only [hp,ite_false]; omega),
          hQ p k (by simp only [hp,ite_false]; omega),sub_self]
  · intro i _
    exact hnode p i



end





noncomputable section






open Finset
open scoped Classical

 

def rationalResidualPolynomial (n : ℕ) (p : Pairing (n+1)) : Polynomial (SpectralField n) :=
  lastTransform (fun i => (spectralWeights n i).tile)
      (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) p -
    (Polynomial.X + Polynomial.C (constF n C)) * rationalNodalPolynomial n p

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
variable {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
  [Algebra R F] [IsFractionRing R F] {φ : R →+* K}



omit [IsDomain R] [IsFractionRing R F] in
theorem rationalAt_column {n : ℕ} (w : Fin n → Weights F) (v : Fin n → Weights K)
    (h : ∀ i t, RationalAt φ ((w i).tile t) ((v i).tile t)) (p q : Pairing n) :
    RationalAt φ (column w p q) (column v p q) := by
  classical
  unfold column
  apply RationalAt.sum
  intro t _
  split_ifs
  · exact RationalAt.prod _ _ _ (fun i _ => h i (t i))
  · exact RationalAt.zero



end





noncomputable section
open scoped Classical

def copiedNodeScalar {m n : ℕ} (v : Fin m → Fin n) (i : Fin n) : SpectralField n :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
    (Fin.snoc (fun j => spectralA (v j)) (deletionBeta i))
    (scalarPolynomial (m+1) d rho (by exact_mod_cast d_ne_zero))

lemma rationalAt_copy_scalar {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (nodalScalar i) (copiedNodeScalar v (v i)) := by
  apply RationalAt.mv_eval
  · exact rationalAt_const (copyEvaluation v)
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using rationalAt_copy_deletionBeta v i
    | cast j => simpa using rationalAt_copy_spectralA v j

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

lemma nodalDatumL_reflection {n : ℕ} (W : Pairing n → Laurent n)
    (i : Fin (n+1)) (j : Fin n) (p : Pairing (n+2)) :
    substituteLaurent i (reflectionUnit j) (nodalDatumL W i p)=0 ∧
      substituteLaurent i (reflectionUnit j) (nodalDatumL W (i.succAbove j) p)=0 := by
  have h1 : (∏ l:Fin (n+1),substituteLaurent i (reflectionUnit j) (reflectionFactorL i l))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ (i.succAbove j)) (reflectionFactorL_collision_left i j)
  have h2 : (∏ l:Fin (n+1),substituteLaurent i (reflectionUnit j) (reflectionFactorL (i.succAbove j) l))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (reflectionFactorL_collision_right i j)
  simp only [nodalDatumL,map_mul,map_prod,h1,h2,zero_mul,and_self]







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

lemma rowDenominator_box {n:ℕ} (i:Fin n) : LaurentBox (rowDenominator i) (selfBound i 2) := by
  have h:∀j,-(selfBound i 1 j:ℤ)≤(-variableExponent i) j ∧ (-variableExponent i) j≤ selfBound i 1 j := by
    intro j
    by_cases h:j=i <;> simp [selfBound,variableExponent,h]
  convert sineL_product_box (-variableExponent i) (-variableExponent i) (phase^(5:ℤ)) (phase^(6:ℤ)) (selfBound i 1) h h using 1
  · rfl
  · funext j
    by_cases h:j=i <;> simp [selfBound,h]

lemma rowNumerator_box {n:ℕ} (i:Fin n) (t:Tile) : LaurentBox (rowNumerator i t) (selfBound i 2) := by
  rw [←selfBound_one_add]
  cases t with
  | vacant => rw [selfBound_one_add]; exact rowDenominator_box i
  | vertical₀ => exact constant_sineL_box _ _ _ _ (variableExponent_selfBound i)
  | vertical₁ => exact constant_sineL_box _ _ _ _ (variableExponent_selfBound i)
  | cap => exact constant_sineL_box _ _ _ _ (negVariableExponent_selfBound i)
  | cup => exact constant_sineL_box _ _ _ _ (negVariableExponent_selfBound i)
  | diagonal₀ => exact sineL_product_box _ _ _ _ _ (negVariableExponent_selfBound i) (variableExponent_selfBound i)
  | diagonal₁ => exact sineL_product_box _ _ _ _ _ (negVariableExponent_selfBound i) (variableExponent_selfBound i)
  | verticalPair => exact sineL_product_box _ _ _ _ _ (variableExponent_selfBound i) (variableExponent_selfBound i)
  | capCup => exact sineL_product_box _ _ _ _ _ (negVariableExponent_selfBound i) (negVariableExponent_selfBound i)

lemma signSpectral_lift {n:ℕ} (i:Fin n) (f:SpectralField n) :
    signSpectral i.castSucc (liftSpectral n f)=liftSpectral n (signSpectral i f) := by
  have he:(signSpectral i.castSucc).comp (liftSpectral n)=
      (liftSpectral n).comp (signSpectral i) := by
    apply IsFractionRing.ringHom_ext (A:=SpectralRing n)
    intro P
    change signSpectral i.castSucc (liftSpectral n (evalLaurent P))=liftSpectral n (signSpectral i (evalLaurent P))
    rw [liftSpectral_evalLaurent,signSpectral_evalLaurent,signSpectral_evalLaurent,liftSpectral_evalLaurent,signLaurent_lift]
  exact DFunLike.congr_fun he f

lemma signSpectral_rowDenominator {n:ℕ} (i j:Fin n) :
    signSpectral i (evalLaurent (rowDenominator j))=evalLaurent (rowDenominator j) := by
  unfold evalLaurent
  rw [rowDenominator_map,signSpectral_torusL,map_div₀,map_pow,signSpectral_const,signSpectral_variable]
  split_ifs
  · have he : constF n phase ^ 3 / -variableF j = -(constF n phase ^ 3 / variableF j) := div_neg_eq_neg_div _ _
    rw [he,torusL_neg]
  · rfl

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InterpolantCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma permSpectral_lift {n:ℕ} (σ:Equiv.Perm (Fin n)) (f:SpectralField n) :
    permSpectral (topPerm σ) (liftSpectral n f)=liftSpectral n (permSpectral σ f) := by
  have he:(permSpectral (topPerm σ)).comp (liftSpectral n)=
      (liftSpectral n).comp (permSpectral σ) := by
    apply IsFractionRing.ringHom_ext (A:=SpectralRing n)
    intro P
    change permSpectral (topPerm σ) (liftSpectral n (evalLaurent P))=liftSpectral n (permSpectral σ (evalLaurent P))
    rw [liftSpectral_evalLaurent,permSpectral_evalLaurent,permSpectral_evalLaurent,liftSpectral_evalLaurent,permLaurent_lift]
  exact DFunLike.congr_fun he f

lemma permSpectral_interpolant {n:ℕ} (σ:Equiv.Perm (Fin n)) (p:Pairing (n+1)) :
    permSpectral (topPerm σ) (rationalInterpolant n p)=
      (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1)*
        ((rationalNodalPolynomial n p).map (permSpectral σ)).eval₂ (liftSpectral n) (spectralA (Fin.last n)) := by
  have hm:(permSpectral (topPerm σ)).comp (liftSpectral n)=(liftSpectral n).comp (permSpectral σ) :=
    RingHom.ext (permSpectral_lift σ)
  simp only [rationalInterpolant,map_mul,Polynomial.hom_eval₂,hm,Polynomial.eval₂_map,
    permSpectral_spectralA,topPerm_last]
  split_ifs <;> simp



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



theorem scalarNormalization_cons_flat {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (dd rr cc CC : K) (a : Fin n → K) (hshift : cc+rr = CC)
    (hroot : ∀ z, discriminant dd cc z = (z-cc)*(z+CC))
    (hfirst : ∀ i, a i ≠ cc) (hsecond : ∀ i, a i+CC ≠ 0) :
    scalarNormalization dd rr (Fin.cons cc a) =
      (∏ i : Fin n, (a i+CC)) * scalarNormalization dd rr a := by
  have hf : ∀ i, discriminant dd cc (a i)/(cc-a i) = -(a i+CC) := by
    intro i
    rw [hroot]
    field_simp [sub_ne_zero.mpr (hfirst i).symm]
    ring
  unfold scalarNormalization
  rw [← prod_upperPair, ← prod_upperPair]
  have hp := prod_upperPair_succ (fun (i j : Fin (n+1)) =>
    discriminant dd ((Fin.cons cc a : Fin (n+1) → K) i) ((Fin.cons cc a : Fin (n+1) → K) j) /
      ((Fin.cons cc a : Fin (n+1) → K) i-(Fin.cons cc a : Fin (n+1) → K) j))
  apply Eq.trans (congrArg (fun z => z * pfaffian (augmentedKernel dd rr (Fin.cons cc a))) hp)
  simp only [Fin.cons_zero,Fin.cons_succ,hf]
  rw [Finset.prod_neg, Finset.card_univ,Fintype.card_fin,
    pfaffian_augmented_cons_flat dd rr cc CC a hshift hroot hfirst hsecond]
  have hs : (-1:K)^n * (-1)^n = 1 := by rw [← mul_pow]; simp
  calc
    _ = ((-1:K)^n * (-1)^n) * ((∏ i : Fin n, (a i+CC)) *
      ((∏ e : UpperPair n, discriminant dd (a e.val.1) (a e.val.2)/(a e.val.1-a e.val.2)) *
        pfaffian (augmentedKernel dd rr a))) := by ring
    _ = _ := by rw [hs,one_mul]

end





noncomputable section

lemma c_add_rho_eq_C : c+rho=C := by
  have h₁ := Real.cos_add (3*lambda) (2*lambda)
  have h₂ := Real.cos_sub (3*lambda) (2*lambda)
  rw [show 3*lambda+2*lambda=5*lambda by ring,cos_five_lambda_eq] at h₁
  rw [show 3*lambda-2*lambda=lambda by ring] at h₂
  change -c=c*d-Real.sin (3*lambda)*Real.sin (2*lambda) at h₁
  change C=c*d+Real.sin (3*lambda)*Real.sin (2*lambda) at h₂
  rw [rho_eq_two_c_d]
  linarith

lemma flat_scalar_linear : 2*(d:ℂ)*(c:ℂ)=(C:ℂ)-(c:ℂ) := by
  have h:=congrArg (fun x : ℝ => (x:ℂ)) c_add_rho_eq_C
  rw [rho_eq_two_c_d] at h
  push_cast at h
  linear_combination h

lemma torusSin_phase_pow (n : ℕ) (k : ℕ) :
    torusSin (constF n phase^k)=constF n (Real.sin ((k:ℝ)*lambda)) := by
  have h := congrArg (constF n) (phase_sine (k:ℤ))
  simpa [torusSin,constF,map_ofNat] using h

lemma torusL_one (n : ℕ) :
    torusL (1:SpectralField n)=constF n d*constF n (Real.sin (3*lambda)) := by
  rw [torusL,mul_one,mul_one,torusSin_phase_pow,torusSin_phase_pow]
  simp only [Nat.cast_ofNat,sin_two_lambda_eq_d]

lemma torusL_phase_three (n : ℕ) :
    torusL (constF n phase^3)=constF n d*constF n (Real.sin (3*lambda)) := by
  rw [torusL,←pow_add,←pow_add]
  norm_num only [Nat.reduceAdd]
  rw [torusSin_phase_pow,torusSin_phase_pow]
  simp only [Nat.cast_ofNat]
  rw [sin_five_lambda_eq,sin_six_lambda,mul_comm]

lemma torusL_one_ne_zero (n : ℕ) : torusL (1:SpectralField n)≠0 := by
  rw [torusL_one]
  apply mul_ne_zero
  · exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (by exact_mod_cast d_ne_zero)
  · exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr
      (by exact_mod_cast ne_of_gt sin_three_lambda_pos)

lemma torusWeights_one (n : ℕ) : torusWeights (1:SpectralField n)=identityWeights := by
  have hd := torusL_one_ne_zero n
  have hq:=constF_phase_ne_zero n
  unfold torusWeights
  simp only [div_one,torusSin_one,zero_mul,mul_zero,zero_div,torusSin_phase_pow,Nat.cast_ofNat,
    sin_two_lambda_eq_d,torusL_one]
  have hn:=torusL_one n
  rw [hn] at hd
  simp only [mul_comm (constF n (Real.sin (3*lambda))),div_self hd]
  rfl

lemma torusWeights_phase_three (n : ℕ) :
    torusWeights (constF n phase^3)=deletionWeights := by
  have hd : constF n d*constF n (Real.sin (3*lambda))≠0 := by
    simpa only [torusL_one] using torusL_one_ne_zero n
  have hq:=constF_phase_ne_zero n
  have he : constF n phase^3/constF n phase=constF n phase^2 := by field_simp
  unfold torusWeights
  simp only [div_self (pow_ne_zero 3 hq),torusSin_one,mul_zero,zero_mul,zero_div,he,
    torusSin_phase_pow,Nat.cast_ofNat,sin_two_lambda_eq_d,torusL_phase_three,div_self hd]
  rfl


 

 

 

open Finset
open scoped Classical


theorem lastValue_vacantBottomExtension {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) {n : ℕ} (b s : L) (P : Pairing (n+1) → Polynomial K) :
    lastValue f b s (vacantBottomExtension P) =
      vacantBottomExtension (lastValue f b s P) := by
  funext p
  by_cases hp : p.Occupied 0
  · simp [lastValue, vacantBottomExtension, hp]
  · rw [← p.padBottom_restrict hp]
    simp only [vacantBottomExtension_padBottom, lastValue,
      ← Fin.succ_last, Pairing.padBottom_occupied_succ]



def firstZeroPolynomial {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) : Pairing (n+2) → Polynomial K :=
  lastTransform (Fin.cons (deletionWeights : Weights K).tile w) d c C
    (vacantBottomExtension P)

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

def firstFlatPoint (n : ℕ) : Fin (n+1) → SpectralField n := Fin.cons 1 variableF

lemma firstFlatPoint_ne_zero (n : ℕ) (i : Fin (n+1)) : firstFlatPoint n i ≠ 0 := by
  induction i using Fin.cases with
  | zero => exact one_ne_zero
  | succ i => exact variableF_ne_zero i

def firstFlatEvaluation (n : ℕ) : Laurent (n+1) →ₐ[ℂ] SpectralField n :=
  torusEvaluation (firstFlatPoint n) (firstFlatPoint_ne_zero n)

lemma rationalAt_firstFlat_variable {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (variableF i) (firstFlatPoint n i) :=
  rationalAt_variable _ _ i

lemma rationalAt_firstFlat_spectralA {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (spectralA i)
      ((Fin.cons (constF n c) spectralA : Fin (n+1) → SpectralField n) i) := by
  have h := rationalAt_torusCos (firstFlatEvaluation n)
    (((rationalAt_firstFlat_variable i).pow 2).div
      ((rationalAt_const (firstFlatEvaluation n) phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ (firstFlatPoint_ne_zero n i))
      (pow_ne_zero _ (constF_phase_ne_zero n)))
  induction i using Fin.cases with
  | zero => simpa only [firstFlatPoint,Fin.cons_zero,one_pow,one_div,torusCos_inv,
      torusCos_phase_pow,Nat.cast_ofNat,spectralA,c] using h
  | succ i => exact h

lemma rationalAt_firstFlat_deletionNode {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (deletionNode i)
      ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i) := by
  have h := (rationalAt_firstFlat_variable i).mul
    ((rationalAt_const (firstFlatEvaluation n) phase).pow 3)
  induction i using Fin.cases with
  | zero => simpa only [firstFlatPoint,Fin.cons_zero,one_mul,deletionNode] using h
  | succ i => exact h

lemma rationalAt_firstFlat_deletionBeta {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (deletionBeta i)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i) := by
  have hn : (Fin.cons (constF n phase^3) (@deletionNode n) : Fin (n+1) → SpectralField n) i≠0 := by
    induction i using Fin.cases with
    | zero => exact pow_ne_zero _ (constF_phase_ne_zero n)
    | succ i => exact mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero n))
  have h:=rationalAt_torusCos (firstFlatEvaluation n)
    (((rationalAt_firstFlat_deletionNode i).pow 2).div
      ((rationalAt_const (firstFlatEvaluation n) phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ hn) (pow_ne_zero _ (constF_phase_ne_zero n)))
  induction i using Fin.cases with
  | zero =>
      have he : (constF n phase^3)^2/constF n phase^3=constF n phase^3 := by
        field_simp
      simpa only [Fin.cons_zero,he,torusCos_phase_pow,Nat.cast_ofNat,deletionBeta,c] using h
  | succ i => exact h

def firstFlatSmallerWeights (n : ℕ) : Fin (n+1) → Fin (n+1) → Weights (SpectralField n) :=
  Fin.cons (Fin.snoc (spectralWeights n) identityWeights) nodalWeights

lemma rationalAt_firstFlat_nodalWeights {n : ℕ} (i : Fin (n+1))
    (j : Fin (n+2)) (t : Tile) :
    RationalAt (firstFlatEvaluation n).toRingHom ((nodalWeights i j).tile t)
      (((Fin.cons deletionWeights (firstFlatSmallerWeights n i) : Fin (n+2) → Weights (SpectralField n)) j).tile t) := by
  have hq:=rationalAt_const (firstFlatEvaluation n) phase
  induction j using Fin.lastCases with
  | cast j =>
      simp only [nodalWeights,Fin.snoc_castSucc,spectralWeights]
      induction j using Fin.cases with
      | zero =>
          have hv := (hq.pow 3).div (rationalAt_firstFlat_variable 0) one_ne_zero
          simp only [firstFlatPoint,Fin.cons_zero,div_one] at hv
          have h := rationalAt_torusWeights (firstFlatEvaluation n) hv
            (pow_ne_zero 3 (constF_phase_ne_zero n))
            (by rw [torusL_phase_three]; simpa only [torusL_one] using torusL_one_ne_zero n) t
          simpa [torusWeights_phase_three] using h
      | succ j =>
          have hv := (hq.pow 3).div (rationalAt_firstFlat_variable j.succ) (variableF_ne_zero j)
          simp only [firstFlatPoint,Fin.cons_succ] at hv
          have h := rationalAt_torusWeights (firstFlatEvaluation n) hv
            (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero j))
            (by rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero j) t
          induction i using Fin.cases with
          | zero => simpa [firstFlatSmallerWeights,spectralWeights] using h
          | succ i => simpa [firstFlatSmallerWeights,nodalWeights,spectralWeights] using h
  | last =>
      simp only [nodalWeights_last]
      induction i using Fin.cases with
      | zero =>
          have hv := (rationalAt_firstFlat_variable (0:Fin (n+1))).inv one_ne_zero
          simp only [firstFlatPoint,Fin.cons_zero,inv_one] at hv
          have h:=rationalAt_torusWeights (firstFlatEvaluation n) hv
            one_ne_zero (torusL_one_ne_zero n) t
          simpa only [torusWeights_one,Fin.cons_last,firstFlatSmallerWeights,
            Fin.cons_zero,Fin.snoc_last] using h
      | succ i =>
          have hv := (rationalAt_firstFlat_variable i.succ).inv (variableF_ne_zero i)
          simp only [firstFlatPoint,Fin.cons_succ] at hv
          have h:=rationalAt_torusWeights (firstFlatEvaluation n) hv
            (inv_ne_zero (variableF_ne_zero i))
            (by rw [←inverseRowDenominator_map]; exact inverseRowDenominator_map_ne_zero i) t
          simpa only [Fin.cons_last,firstFlatSmallerWeights,Fin.cons_succ,nodalWeights_last] using h


def firstFlatSmallerScalar (n : ℕ) (i : Fin (n+1)) : SpectralField n :=
  (Fin.cons ((∏ j : Fin n, (spectralA j+constF n C))*spectralNormalization n)
    nodalScalar : Fin (n+1) → SpectralField n) i







def lastEvaluation {n:ℕ} (z:SpectralField n) (hz:z≠0) : Laurent (n+1) →ₐ[ℂ] SpectralField n :=
  torusEvaluation (Fin.snoc variableF z) (fun i => Fin.lastCases (by simpa only [Fin.snoc_last] using hz) (fun j => by simpa only [Fin.snoc_castSucc] using variableF_ne_zero j) i)

lemma lastEvaluation_lift {n:ℕ} (z:SpectralField n) (hz:z≠0) (P:Laurent n) :
    lastEvaluation z hz (liftLaurent P)=evalLaurent P := by
  have he:(lastEvaluation z hz).toRingHom.comp (liftLaurentHom n)=
      algebraMap (SpectralRing n) (SpectralField n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change lastEvaluation z hz (liftLaurent (monomialL _ _))=evalLaurent (monomialL _ _)
    all_goals rw [liftLaurent_monomial,evalLaurent_monomial_product]
    all_goals simp only [lastEvaluation,torusEvaluation_monomial,Fin.prod_univ_castSucc,
      Fin.snoc_castSucc,Fin.snoc_last,zpow_zero,mul_one]
  exact DFunLike.congr_fun he P

lemma rationalAt_last_lift {n:ℕ} (z:SpectralField n) (hz:z≠0) (x:SpectralField n) :
    RationalAt (lastEvaluation z hz).toRingHom (liftSpectral n x) x := by
  obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (SpectralRing n) x
  have ha:=RationalAt.algebraMap (φ:=(lastEvaluation z hz).toRingHom) (F:=SpectralField (n+1)) (liftLaurent a)
  have hc:=RationalAt.algebraMap (φ:=(lastEvaluation z hz).toRingHom) (F:=SpectralField (n+1)) (liftLaurent b)
  change RationalAt _ (evalLaurent (liftLaurent a)) (lastEvaluation z hz (liftLaurent a)) at ha
  change RationalAt _ (evalLaurent (liftLaurent b)) (lastEvaluation z hz (liftLaurent b)) at hc
  rw [lastEvaluation_lift] at ha hc
  change RationalAt _ (liftSpectral n (evalLaurent a / evalLaurent b)) (evalLaurent a / evalLaurent b)
  rw [map_div₀,liftSpectral_evalLaurent,liftSpectral_evalLaurent]
  exact ha.div hc (map_ne_zero_of_mem_nonZeroDivisors
    (algebraMap (SpectralRing n) (SpectralField n)) (IsFractionRing.injective _ _) hb)

lemma rationalAt_last_variable {n:ℕ} (z:SpectralField n) (hz:z≠0) :
    RationalAt (lastEvaluation z hz).toRingHom (variableF (Fin.last n)) z := by
  simpa only [lastEvaluation,Fin.snoc_last] using rationalAt_variable (Fin.snoc variableF z)
    (fun i => Fin.lastCases (by simpa only [Fin.snoc_last] using hz) (fun j => by simpa only [Fin.snoc_castSucc] using variableF_ne_zero j) i) (Fin.last n)

lemma rationalAt_last_spectralA {n:ℕ} (z:SpectralField n) (hz:z≠0) :
    RationalAt (lastEvaluation z hz).toRingHom (spectralA (Fin.last n))
      (torusCos (z^2/constF n phase^3)) :=
  rationalAt_torusCos (lastEvaluation z hz)
    (((rationalAt_last_variable z hz).pow 2).div ((rationalAt_const _ phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ (constF_phase_ne_zero n)))

lemma rationalAt_last_interpolant {n:ℕ} (z:SpectralField n) (hz:z≠0) (p:Pairing (n+1)) :
    RationalAt (lastEvaluation z hz).toRingHom (rationalInterpolant n p)
      (lastValue (RingHom.id _) (torusCos (z^2/constF n phase^3)) (torusSin z)
        (rationalNodalPolynomial n) p) := by
  have he:=RationalAt.eval₂ (lastEvaluation z hz).toRingHom (liftSpectral n) (RingHom.id _)
    (rationalAt_last_lift z hz) (rationalAt_last_spectralA z hz) (rationalNodalPolynomial n p)
  unfold rationalInterpolant lastValue
  split_ifs
  · exact (rationalAt_torusSin _ (rationalAt_last_variable z hz) hz).mul he
  · simpa only [one_mul] using he

lemma rationalAt_last_weights {n:ℕ} (z:SpectralField n) (hz:z≠0)
    (hL:torusL (constF n phase^3/z)≠0) (i:Fin (n+1)) (t:Tile) :
    RationalAt (lastEvaluation z hz).toRingHom ((spectralWeights (n+1) i).tile t)
      (((Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3/z)) : Fin (n+1) → Weights (SpectralField n)) i).tile t) := by
  induction i using Fin.lastCases with
  | cast i =>
      simpa only [liftSpectral_weights_tile,Fin.snoc_castSucc] using
        rationalAt_last_lift z hz ((spectralWeights n i).tile t)
  | last =>
      simpa only [spectralWeights,Fin.snoc_last] using rationalAt_torusWeights (lastEvaluation z hz)
        (((rationalAt_const _ phase).pow 3).div (rationalAt_last_variable z hz) hz)
        (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) hz) hL t

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ResidualEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical







lemma permSpectral_rowDenominator {n:ℕ} (σ:Equiv.Perm (Fin n)) (i:Fin n) :
    permSpectral σ (evalLaurent (rowDenominator i))=evalLaurent (rowDenominator (σ i)) := by
  unfold evalLaurent
  rw [rowDenominator_map,rowDenominator_map,permSpectral_torusL,map_div₀,map_pow,permSpectral_const,permSpectral_variable]

lemma permSpectral_rowProduct {n:ℕ} (σ:Equiv.Perm (Fin n)) :
    permSpectral σ (∏i:Fin n,evalLaurent (rowDenominator i))=∏i:Fin n,evalLaurent (rowDenominator i) := by
  rw [map_prod]; simp_rw [permSpectral_rowDenominator]
  exact Equiv.prod_comp σ (fun i:Fin n => (evalLaurent (rowDenominator i):SpectralField n))







lemma torusEvaluation_permLaurent {n m:ℕ} (σ:Equiv.Perm (Fin n))
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0) (f:Laurent n) :
    torusEvaluation z hz (permLaurent σ f)=
      torusEvaluation (z ∘ σ) (fun i =>hz (σ i)) f := by
  have he:(torusEvaluation z hz).toRingHom.comp (permLaurent σ)=
      (torusEvaluation (z ∘ σ) (fun i =>hz (σ i))).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro c
      change torusEvaluation z hz (permLaurent σ (monomialL 0 c))=
        torusEvaluation (z ∘ σ) _ (monomialL 0 c)
      simp only [permLaurent_monomial,torusEvaluation_monomial,
        Function.comp_apply,Pi.zero_apply,zpow_zero,
        Finset.prod_const_one,mul_one]
    · intro e
      change torusEvaluation z hz (permLaurent σ (monomialL e 1))=
        torusEvaluation (z ∘ σ) _ (monomialL e 1)
      rw [permLaurent_monomial,torusEvaluation_monomial,torusEvaluation_monomial]
      congr 1
      simpa only [permExponent,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Function.comp_apply,Equiv.symm_apply_apply] using
        (Equiv.prod_comp σ (fun i =>z i ^ (e ∘ σ.symm) i)).symm
  exact DFunLike.congr_fun he f

lemma rationalAt_firstFlat_weights {n:ℕ} (i:Fin (n+1)) (t:Tile) :
    RationalAt (firstFlatEvaluation n).toRingHom ((spectralWeights (n+1) i).tile t)
      (((Fin.cons deletionWeights (spectralWeights n) : Fin (n+1) → Weights (SpectralField n)) i).tile t) := by
  induction i using Fin.cases with
  | zero =>
      have hz:=rationalAt_firstFlat_variable (0:Fin (n+1))
      simp only [firstFlatPoint,Fin.cons_zero] at hz
      have h:=rationalAt_torusWeights (firstFlatEvaluation n)
        (((rationalAt_const _ phase).pow 3).div hz one_ne_zero)
        (by simpa using pow_ne_zero 3 (constF_phase_ne_zero n))
        (by rw [div_one,torusL_phase_three]; simpa only [torusL_one] using torusL_one_ne_zero n) t
      simpa only [spectralWeights,Fin.cons_zero,div_one,torusWeights_phase_three] using h
  | succ i =>
      have hz:=rationalAt_firstFlat_variable i.succ
      simp only [firstFlatPoint,Fin.cons_succ] at hz
      exact rationalAt_torusWeights (firstFlatEvaluation n)
        (((rationalAt_const _ phase).pow 3).div hz (variableF_ne_zero i))
        (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero i))
        (by rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero i) t

lemma deletionBeta_ne_const {n:ℕ} (i:Fin n) (z:ℂ) : deletionBeta i≠constF n z := by
  intro h
  have hc:evalLaurent (constantL n z)=constF n z := map_constantL _ _
  rw [←betaL_map,←hc] at h
  have he:betaL i=constantL n z := IsFractionRing.injective _ _ h
  have ht:(2:ℤ) • variableExponent i≠0 := by
    intro hh
    have hi:=congrFun hh i
    simp [variableExponent] at hi
  change betaL i=monomialL 0 z at he
  have hh:=congrArg (fun P:Laurent n => P.coeff ((2:ℤ) • variableExponent i)) he
  simp only [betaL,cosineL,monomialL,AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single,Finsupp.add_apply,Finsupp.single_apply] at hh
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,
    ite_eq_right ht.symm,add_zero] at hh
  exact (pow_ne_zero 3 phase_ne_zero) ((div_eq_zero_iff).mp hh |>.resolve_right (by norm_num))

lemma firstFlatBeta_injective (n:ℕ) :
    Function.Injective (Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) := by
  intro i j h
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact (deletionBeta_ne_const j c (by simpa using h.symm)).elim
  | succ i =>
      induction j using Fin.cases with
      | zero => exact (deletionBeta_ne_const i c (by simpa using h)).elim
      | succ j => exact congrArg Fin.succ (deletionBeta_injective n (by simpa using h))

lemma firstFlatNode_sine_ne_zero {n:ℕ} (i:Fin (n+1)) :
    torusSin ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i)≠0 := by
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero,torusSin_phase_pow]
      apply (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr
      exact_mod_cast ne_of_gt sin_three_lambda_pos
  | succ i => exact deletionNode_sine_ne_zero i







lemma firstFlatNode_ne_zero {n:ℕ} (i:Fin (n+1)) :
    (Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i≠0 := by
  induction i using Fin.cases with
  | zero => exact pow_ne_zero _ (constF_phase_ne_zero n)
  | succ i => exact mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero n))

lemma firstFlatNode_cosine {n:ℕ} (i:Fin (n+1)) :
    torusCos (((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i)^2/
      constF n phase^3)=((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i) := by
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero,pow_two,mul_div_cancel_right₀ _ (pow_ne_zero _ (constF_phase_ne_zero n)),torusCos_phase_pow]
      rfl
  | succ i => rfl

lemma firstFlatNode_L {n:ℕ} (i:Fin (n+1)) :
    torusL (constF n phase^3 / ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i))≠0 := by
  induction i using Fin.cases with
  | zero =>
      rw [Fin.cons_zero,div_self (pow_ne_zero _ (constF_phase_ne_zero n))]
      exact torusL_one_ne_zero n
  | succ i =>
      have ha:constF n phase^3/deletionNode i=(variableF i)⁻¹ := by
        unfold deletionNode; field_simp [constF_phase_ne_zero]
      rw [Fin.cons_succ,ha,←inverseRowDenominator_map]
      exact inverseRowDenominator_map_ne_zero i

lemma firstFlatNode_weights {n:ℕ} (i:Fin (n+1)) :
    Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3 /
      ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i)))=
      firstFlatSmallerWeights n i := by
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero,div_self (pow_ne_zero _ (constF_phase_ne_zero n)),
        torusWeights_one,firstFlatSmallerWeights]
  | succ i => rfl

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

lemma vacantBottomExtension_smul {K:Type*} [CommRing K] {n:ℕ}
    (a:K) (v:Pairing n → K) :
    vacantBottomExtension (a • v)=a • vacantBottomExtension v := by
  funext p
  by_cases hp:p.Occupied 0 <;> simp [vacantBottomExtension,hp,Pi.smul_apply]

def firstThreePoint (n:ℕ) : Fin (n+1) → SpectralField n :=
  Fin.cons (constF n phase^3) variableF

lemma firstThreePoint_ne_zero (n:ℕ) (i:Fin (n+1)) : firstThreePoint n i≠0 := by
  induction i using Fin.cases with
  | zero => exact pow_ne_zero _ (constF_phase_ne_zero n)
  | succ i => exact variableF_ne_zero i

def firstThreeEvaluation (n:ℕ) : Laurent (n+1) →ₐ[ℂ] SpectralField n :=
  torusEvaluation (firstThreePoint n) (firstThreePoint_ne_zero n)

lemma rationalAt_firstThree_variable {n:ℕ} (i:Fin (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (variableF i) (firstThreePoint n i) :=
  rationalAt_variable _ _ i

lemma rationalAt_firstThree_spectralA {n:ℕ} (i:Fin (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (spectralA i)
      ((Fin.cons (constF n c) spectralA : Fin (n+1) → SpectralField n) i) := by
  have h:=rationalAt_torusCos (firstThreeEvaluation n)
    (((rationalAt_firstThree_variable i).pow 2).div
      ((rationalAt_const (firstThreeEvaluation n) phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ (firstThreePoint_ne_zero n i))
      (pow_ne_zero _ (constF_phase_ne_zero n)))
  induction i using Fin.cases with
  | zero =>
      have he:(constF n phase^3)^2/constF n phase^3=constF n phase^3 := by
        field_simp
      simpa only [firstThreePoint,Fin.cons_zero,he,torusCos_phase_pow,Nat.cast_ofNat,spectralA,c] using h
  | succ i => exact h

lemma rationalAt_firstThree_deletionNode {n:ℕ} (i:Fin (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (deletionNode i)
      ((Fin.cons (constF n phase^6) deletionNode : Fin (n+1) → SpectralField n) i) := by
  have h:=(rationalAt_firstThree_variable i).mul
    ((rationalAt_const (firstThreeEvaluation n) phase).pow 3)
  induction i using Fin.cases with
  | zero => simpa only [firstThreePoint,Fin.cons_zero,←pow_add,Nat.reduceAdd,deletionNode] using h
  | succ i => exact h

lemma firstThreeNode_ne_zero {n:ℕ} (i:Fin (n+1)) :
    ((Fin.cons (constF n phase^6) deletionNode : Fin (n+1) → SpectralField n) i)≠0 := by
  induction i using Fin.cases with
  | zero => exact pow_ne_zero _ (constF_phase_ne_zero n)
  | succ i => exact mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero n))

lemma torusCos_phase_nine (n:ℕ) :torusCos (constF n phase^9)= -constF n C := by
  rw [torusCos_phase_pow]
  have h:9*lambda=lambda+Real.pi := by unfold lambda; ring
  simp only [Nat.cast_ofNat,h,Real.cos_add_pi,Complex.ofReal_neg,constF,map_neg,C]

lemma rationalAt_firstThree_deletionBeta {n:ℕ} (i:Fin (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (deletionBeta i)
      ((Fin.cons (-constF n C) deletionBeta : Fin (n+1) → SpectralField n) i) := by
  have h:=rationalAt_torusCos (firstThreeEvaluation n)
    (((rationalAt_firstThree_deletionNode i).pow 2).div
      ((rationalAt_const (firstThreeEvaluation n) phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ (firstThreeNode_ne_zero i))
      (pow_ne_zero _ (constF_phase_ne_zero n)))
  induction i using Fin.cases with
  | zero =>
      have he:(constF n phase^6)^2/constF n phase^3=constF n phase^9 := by
        field_simp
      simpa only [Fin.cons_zero,he,torusCos_phase_nine,deletionBeta] using h
  | succ i => exact h

lemma rationalAt_firstThree_weights {n:ℕ} (i:Fin (n+1)) (t:Tile) :
    RationalAt (firstThreeEvaluation n).toRingHom ((spectralWeights (n+1) i).tile t)
      (((Fin.cons identityWeights (spectralWeights n) : Fin (n+1) → Weights (SpectralField n)) i).tile t) := by
  have hz:=rationalAt_firstThree_variable i
  have hq:=(rationalAt_const (firstThreeEvaluation n) phase).pow 3
  induction i using Fin.cases with
  | zero =>
      simp only [firstThreePoint,Fin.cons_zero] at hz
      have h:=hq.div hz (pow_ne_zero _ (constF_phase_ne_zero n))
      rw [div_self (pow_ne_zero _ (constF_phase_ne_zero n))] at h
      simpa only [Fin.cons_zero,torusWeights_one,spectralWeights] using
        rationalAt_torusWeights (firstThreeEvaluation n) h one_ne_zero (torusL_one_ne_zero n) t
  | succ i =>
      simp only [firstThreePoint,Fin.cons_succ] at hz
      exact rationalAt_torusWeights (firstThreeEvaluation n)
        (hq.div hz (variableF_ne_zero i))
        (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero i))
        (by rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero i) t







lemma firstThreeHead_zero {n:ℕ} (occupied:Prop) [Decidable occupied] :
    firstThreeEvaluation n (nodalHeadL (0:Fin (n+1)) occupied)=0 := by
  have h:RationalAt (firstThreeEvaluation n).toRingHom
      (reducedNodalHead (0:Fin (n+1)) occupied) 0 := by
    by_cases ho:occupied
    · simp only [reducedNodalHead,ite_eq_left ho]
      have hv:=(rationalAt_const (firstThreeEvaluation n) phase).pow 3 |>.div
        (rationalAt_firstThree_variable (0:Fin (n+1))) (pow_ne_zero _ (constF_phase_ne_zero n))
      simp only [firstThreePoint,Fin.cons_zero,div_self (pow_ne_zero _ (constF_phase_ne_zero n))] at hv
      have ht:=rationalAt_torusSin (firstThreeEvaluation n) hv one_ne_zero
      simp only [torusSin,inv_one,sub_self,zero_div] at ht
      have hh:= ((RationalAt.natCast 4).mul (rationalAt_const (firstThreeEvaluation n) (c:ℂ))).mul ht
      simpa only [mul_zero,torusSin,Nat.cast_ofNat] using hh
    · simp only [reducedNodalHead,ite_eq_right ho]
      have hh:=((rationalAt_firstThree_spectralA (0:Fin (n+1))).add
        (rationalAt_firstThree_deletionBeta (0:Fin (n+1)))).add
        (rationalAt_const (firstThreeEvaluation n) (rho:ℂ))
      simp only [Fin.cons_zero] at hh
      have he:constF n c+-constF n C+constF n rho=0 := by
        have hc:=congrArg (fun x:ℝ => constF n (x:ℂ)) c_add_rho_eq_C
        simp only [Complex.ofReal_add,constF,map_add] at hc ⊢
        linear_combination hc
      rw [he] at hh
      exact hh
  have ha:=RationalAt.algebraMap (φ:=(firstThreeEvaluation n).toRingHom)
    (F:=SpectralField (n+1)) (nodalHeadL (0:Fin (n+1)) occupied)
  change RationalAt _ (evalLaurent _) _ at ha
  rw [nodalHeadL_map] at ha
  exact ha.unique h

lemma nodalDatumL_firstThree_zero {n:ℕ} (W:Pairing n → Laurent n) (p:Pairing (n+2)) :
    firstThreeEvaluation n (nodalDatumL W 0 p)=0 := by
  simp only [nodalDatumL,map_mul,firstThreeHead_zero,mul_zero,zero_mul]

lemma rationalAt_firstThree_nodalWeights {n:ℕ} (i:Fin n)
    (j:Fin (n+2)) (t:Tile) :
    RationalAt (firstThreeEvaluation n).toRingHom ((nodalWeights i.succ j).tile t)
      (((Fin.cons identityWeights (nodalWeights i) : Fin (n+2) → Weights (SpectralField n)) j).tile t) := by
  induction j using Fin.lastCases with
  | cast j =>
      have h:=rationalAt_firstThree_weights j t
      induction j using Fin.cases with
      | zero =>
          change RationalAt (firstThreeEvaluation n).toRingHom ((spectralWeights (n+1) 0).tile t) (identityWeights.tile t)
          exact h
      | succ j =>
          simp only [nodalWeights,Fin.snoc_castSucc]
          rw [←Fin.succ_castSucc,Fin.cons_succ,Fin.snoc_castSucc]
          exact h
  | last =>
      simp only [Fin.cons_last,nodalWeights_last]
      have hv := (rationalAt_firstThree_variable i.succ).inv (variableF_ne_zero i)
      simp only [firstThreePoint,Fin.cons_succ] at hv
      exact rationalAt_torusWeights (firstThreeEvaluation n) hv
        (inv_ne_zero (variableF_ne_zero i))
        (by rw [←inverseRowDenominator_map]; exact inverseRowDenominator_map_ne_zero i) t







def firstThreePolynomial {K:Type*} [CommRing K] {n:ℕ} (C:K)
    (P:Pairing n → Polynomial K) : Pairing (n+1) → Polynomial K :=
  fun p => (Polynomial.X+Polynomial.C C)*vacantBottomExtension P p

lemma firstThreePolynomial_padBottom {K:Type*} [CommRing K] {n:ℕ} (C:K)
    (P:Pairing n → Polynomial K) (p:Pairing n) :
    firstThreePolynomial C P p.padBottom=(Polynomial.X+Polynomial.C C)*P p := by
  rw [firstThreePolynomial,vacantBottomExtension_padBottom]

lemma firstThreePolynomial_degree {K:Type*} [CommRing K] {n m:ℕ} (C:K)
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree m P) :
    LastDegree (m+1) (firstThreePolynomial C P) := by
  intro p k hk
  by_cases hp:p.Occupied 0
  · simp [firstThreePolynomial,vacantBottomExtension,hp]
  · rw [←p.padBottom_restrict hp] at hk ⊢
    rw [firstThreePolynomial_padBottom]
    let q:=p.restrict (Fin.succOrderEmb (n+1))
    have ho:(q.padBottom.Occupied (Fin.last (n+1))) ↔ q.Occupied (Fin.last n) := by
      exact q.padBottom_occupied_succ (Fin.last n)
    change (if q.padBottom.Occupied (Fin.last (n+1)) then m+1≤k else m+1<k) at hk
    rw [ho] at hk
    obtain ⟨j,rfl⟩:∃j,k=j+1 := by split_ifs at hk <;> exact ⟨k-1,by omega⟩
    have hh:(P q).coeff j=0 := hP q j (by split_ifs at hk ⊢ <;> omega)
    have hh':(P q).coeff (j+1)=0 := hP q (j+1) (by split_ifs at hk ⊢ <;> omega)
    simp [add_mul,Polynomial.coeff_X_mul,hh,hh',q]

lemma firstThreeBeta_injective (n:ℕ) :
    Function.Injective (Fin.cons (-constF n C) deletionBeta : Fin (n+1) → SpectralField n) := by
  apply Fin.cons_injective_iff.mpr
  constructor
  · rintro ⟨i,he⟩
    exact deletionBeta_ne_const i (-C) (by simpa only [Complex.ofReal_neg,constF,map_neg] using he)
  · exact deletionBeta_injective n



def pairPoint (n s:ℕ) : Fin (n+2) → SpectralField (n+1) :=
  Fin.cons (variableF 0) (Fin.cons (constF (n+1) phase^s*variableF 0) (fun i =>variableF i.succ))
lemma pairPoint_ne_zero (n s:ℕ) (i:Fin (n+2)) : pairPoint n s i≠0 := by
  induction i using Fin.cases with
  | zero => exact variableF_ne_zero 0
  | succ i => induction i using Fin.cases with
    | zero => exact mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero 0)
    | succ i => exact variableF_ne_zero i.succ

def pairEvaluation (n s:ℕ) : Laurent (n+2) →ₐ[ℂ] SpectralField (n+1) :=
  torusEvaluation (pairPoint n s) (pairPoint_ne_zero n s)

lemma rationalAt_pair_variable {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (variableF i) (pairPoint n s i) :=
  rationalAt_variable _ _ i

lemma torusL_phase_five (n:ℕ) : torusL (constF n phase^5)=0 := by
  unfold torusL
  rw [←pow_add,←pow_add]
  simp only [Nat.reduceAdd,torusSin_phase_pow]
  have he:(8:ℝ)*lambda=Real.pi := by unfold lambda; ring
  simp only [Nat.cast_ofNat,he,Real.sin_pi,Complex.ofReal_zero,constF,map_zero,mul_zero]

lemma torusL_phase_six (n:ℕ) : torusL (constF n phase^6)=0 := by
  unfold torusL
  rw [←pow_add,←pow_add]
  simp only [Nat.reduceAdd,torusSin_phase_pow]
  have he:(8:ℝ)*lambda=Real.pi := by unfold lambda; ring
  simp only [Nat.cast_ofNat,he,Real.sin_pi,Complex.ofReal_zero,constF,map_zero,zero_mul]

lemma pairEvaluation_vacantNumerator {n:ℕ} (s:ℕ) (hs:s=2 ∨ s=3) :
    pairEvaluation n s (torusNumeratorL (variableExponent (1:Fin (n+2))-variableExponent 0) (phase^3) .vacant)=0 := by
  have hv:RationalAt (pairEvaluation n s).toRingHom
      (constF (n+2) phase^3*(variableF (1:Fin (n+2))/variableF 0))
      (constF (n+1) phase^(s+3)) := by
    have hh:=((rationalAt_const (pairEvaluation n s) phase).pow 3).mul
      ((rationalAt_pair_variable s (1:Fin (n+2))).div (rationalAt_pair_variable s 0) (variableF_ne_zero 0))
    have he:constF (n+1) phase^3*(pairPoint n s 1 / pairPoint n s 0)=constF (n+1) phase^(s+3) := by
      change constF (n+1) phase^3*((constF (n+1) phase^s*variableF 0)/variableF 0)=_
      rw [mul_div_cancel_right₀ _ (variableF_ne_zero 0),pow_add,mul_comm]
    rwa [he] at hh
  have ht:=rationalAt_torusL _ hv (pow_ne_zero _ (constF_phase_ne_zero _))
  have ha:=RationalAt.algebraMap (φ:=(pairEvaluation n s).toRingHom) (F:=SpectralField (n+2))
    (torusNumeratorL (variableExponent (1:Fin (n+2))-variableExponent 0) (phase^3) .vacant)
  change RationalAt _ (evalLaurent _) _ at ha
  rw [torusNumeratorL_pair_map] at ha
  change RationalAt _ (torusL _) _ at ha
  have hh:=ha.unique ht
  rcases hs with rfl | rfl
  · simpa using hh.trans (torusL_phase_five (n+1))
  · simpa using hh.trans (torusL_phase_six (n+1))


 

 


lemma torusL_phase_small_ne_zero (m k:ℕ) (hk:k≤3) :
    torusL (constF m phase^k)≠0 := by
  unfold torusL
  rw [←pow_add,←pow_add,torusSin_phase_pow,torusSin_phase_pow]
  apply mul_ne_zero <;> apply (map_ne_zero (algebraMap ℂ (SpectralField m))).mpr
  all_goals apply Complex.ofReal_ne_zero.mpr
  all_goals apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi
  all_goals unfold lambda; push_cast; nlinarith [Real.pi_pos,show (k:ℝ)≤3 by exact_mod_cast hk, Nat.cast_nonneg (α:=ℝ) k]

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








def scalarMergeDiff {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (x y t:K) (a:Fin n → K) : Polynomial K :=
  firstScalarHom f (Fin.cons x (Fin.cons y a)) (scalarPolynomial (n+3) d rho (by exact_mod_cast d_ne_zero)) -
    Polynomial.C ((x+y+f (rho:ℂ))*(∏i,(a i+t))) *
      ((Polynomial.X+Polynomial.C t)*
        firstScalarHom f (Fin.cons t a) (scalarPolynomial (n+2) d rho (by exact_mod_cast d_ne_zero)))

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarMergeTrig
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

abbrev fcos {n:ℕ} (i:Fin n) (k:ℤ) := shiftedCosine i (phase^k)

lemma fcos_eq {n:ℕ} (i:Fin n) (k:ℤ) : fcos i k=
    torusCos (constF n (phase^k)*variableF i^2) :=
  shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)

lemma fcos_shift {n:ℕ} (i:Fin n) (k l:ℤ) :
    fcos i (k+l)=torusCos ((constF n (phase^k)*variableF i^2)*constF n (phase^l)) := by
  rw [fcos_eq,zpow_add₀ phase_ne_zero]
  simp only [constF,map_mul]
  congr 1; ring

lemma fcos_eight {n:ℕ} (i:Fin n) (k:ℤ) : fcos i (k+8)= - fcos i k := by
  rw [fcos_shift]
  simp only [zpow_ofNat,phase_eight,constF,map_neg,map_one,mul_neg,mul_one,torusCos_neg]
  rw [fcos_eq]
  rfl

lemma fcos_sub_eight {n:ℕ} (i:Fin n) (k:ℤ) : fcos i (k-8)= - fcos i k := by
  have h:=fcos_eight i (k-8)
  rw [sub_add_cancel] at h
  linear_combination h

lemma constF_d_sq (n:ℕ) : (constF n d)^2=(1/2:SpectralField n) := by
  have h:=congrArg (fun x:ℝ =>constF n (x:ℂ)) d_sq
  simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
    constF,map_pow,map_div₀,map_one,map_ofNat] using h

lemma fcos_sum_product {n:ℕ} (i:Fin n) (k:ℤ) :
    fcos i (k-2)+fcos i (k+2)=2*constF n d*fcos i k ∧
    fcos i (k-2)*fcos i (k+2)=(fcos i k)^2-(constF n d)^2 := by
  let z:=constF n (phase^k)*variableF i^2
  let w:=constF n phase^2
  have hz:z≠0:=mul_ne_zero (by simpa [constF] using (algebraMap ℂ (SpectralField n)).injective.ne (zpow_ne_zero k phase_ne_zero)) (pow_ne_zero _ (variableF_ne_zero i))
  have hw:w≠0:=pow_ne_zero _ (constF_phase_ne_zero n)
  have he₁:fcos i (k-2)=torusCos (z/w) := by
    rw [fcos_eq,zpow_sub₀ phase_ne_zero]
    simp only [zpow_ofNat,constF,map_div₀,map_pow]
    congr 1; dsimp [z,w,constF]; ring
  have he₂:fcos i (k+2)=torusCos (z*w) := by
    rw [fcos_shift]; simp [z,w,constF]
  have he₀:fcos i k=torusCos z:=shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)
  have hew:torusCos w=constF n d:=torusCos_phase_pow n 2
  rw [he₁,he₂,he₀,torusCos_sum z w hz hw,torusCos_product z w hz hw,hew]
  constructor
  · ring
  · linear_combination 2*constF_d_sq n

lemma fcos_six_ne {n:ℕ} (i:Fin n) (k:ℤ) : fcos i k≠fcos i (k+6) := by
  intro h
  have hh:=shiftedCosine_parameter i _ _ h
  rw [zpow_add₀ phase_ne_zero] at hh
  have he:phase^(6:ℤ)=1 := (mul_left_cancel₀ (zpow_ne_zero k phase_ne_zero) (by simpa using hh.symm))
  exact phase_six_ne_one (by simpa using he)

lemma fcos_ne_const {n:ℕ} (i:Fin n) (k:ℤ) (z:ℂ) : fcos i k≠constF n z := by
  intro h
  have he:(2:ℤ) • variableExponent i≠0 := by
    intro h; have hh:=congrFun h i; simp [variableExponent] at hh
  have hl:cosineL ((2:ℤ) • variableExponent i) (phase^k)=constantL n z :=
    IsFractionRing.injective (SpectralRing n) (SpectralField n) h
  change cosineL ((2:ℤ) • variableExponent i) (phase^k)=monomialL 0 z at hl
  have hc:=congrArg (fun P:Laurent n =>P.coeff ((2:ℤ) • variableExponent i)) hl
  simp only [cosineL,monomialL,AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single,Finsupp.add_apply,Finsupp.single_apply] at hc
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,
    ite_eq_right he.symm,add_zero] at hc
  exact (zpow_ne_zero k phase_ne_zero) ((div_eq_zero_iff).mp hc |>.resolve_right (by norm_num))

lemma scalar_merge_flat_constants :
    2*(d:ℂ)*(C:ℂ)=(c:ℂ)+(C:ℂ) ∧ (C:ℂ)^2-(d:ℂ)^2=(c:ℂ)*(C:ℂ) := by
  have hd:(d:ℂ)^2=1/2:=by
    have h:=congrArg (fun x:ℝ =>(x:ℂ)) d_sq
    push_cast at h
    exact h
  have hl:=flat_scalar_linear
  have hc:=flat_scalar_constant
  constructor
  · linear_combination (1-2*(d:ℂ))*hl+4*(c:ℂ)*hd
  · linear_combination -((C:ℂ)-(c:ℂ)+2*(d:ℂ)*(c:ℂ))*hl+4*(c:ℂ)^2*hd+hc

lemma fcos_flat_factor {n:ℕ} (i:Fin n) (k:ℤ) :
    (constF n C+fcos i (k-2))*(constF n C+fcos i (k+2))=
      (constF n c+fcos i k)*(constF n C+fcos i k) := by
  obtain ⟨hs,hp⟩:=fcos_sum_product i k
  obtain ⟨hl,hc⟩:=scalar_merge_flat_constants
  have hl':=congrArg (constF n) hl
  have hc':=congrArg (constF n) hc
  simp only [constF,map_mul,map_ofNat,map_add,map_sub,map_pow] at hl' hc'
  dsimp only [constF] at hs hp ⊢
  linear_combination (algebraMap ℂ (SpectralField n)) (C:ℂ)*hs+hp+fcos i k*hl'+hc'


lemma fcos_sixteen {n:ℕ} (i:Fin n) (k:ℤ) : fcos i (k+16)=fcos i k := by
  rw [show k+16=(k+8)+8 by ring,fcos_eight,fcos_eight,neg_neg]

lemma fcos_roots {n:ℕ} (i:Fin n) (k:ℤ) (z:SpectralField n) :
    discriminant (constF n d) (fcos i k) z=(z-fcos i (k-6))*(z-fcos i (k+6)) :=
  shiftedCosine_roots i k z

lemma fcos_delete_factor {n:ℕ} (i j:Fin n) (k l:ℤ) :
    (fcos i (k-2)-fcos j (l-6))*(fcos i (k-2)-fcos j (l+12))*
      (fcos i (k+2)-fcos j (l-6))*(fcos i (k+2)-fcos j (l+12))=
      (fcos i k+fcos j l)*(fcos i k+fcos j (l+6))*
      (fcos i k-fcos j (l-6))*(fcos i k-fcos j (l+12)) := by
  have hs:=roots_sum (constF n d) (fcos j l) (fcos j (l-6)) (fcos j (l+6)) (fcos_roots j l)
  have ht:=roots_sum (constF n d) (fcos j (l+6)) (fcos j l) (fcos j (l+12)) (by
    intro z; simpa only [add_sub_cancel_right, show l+6+6=l+12 by omega] using fcos_roots j (l+6) z)
  have hγ:fcos j (l-6)= -2*constF n d*fcos j l-fcos j (l+6) := by linear_combination hs
  have hσ:fcos j (l+12)= -2*constF n d*fcos j (l+6)-fcos j l := by linear_combination ht
  rw [hγ,hσ]
  have hd:=fcos_roots j l (fcos j (l+6))
  simp only [sub_self,mul_zero,discriminant] at hd
  exact scalar_merge_delete_factor_algebra _ _ _ _ _ _ (constF_d_sq n)
    (fcos_sum_product i k).1 (fcos_sum_product i k).2 hd


 

 

open scoped Classical

end

 

 

noncomputable section

lemma fcos_tuple_injective {m n:ℕ} (j:Fin n → Fin m) (hj:Function.Injective j) (l:Fin n → ℤ) :
    Function.Injective (fun v => fcos (j v) (l v)) := by
  intro v w h
  by_contra hvw
  exact shiftedCosine_ne (j v) (j w) (hj.ne hvw) _ _ (zpow_ne_zero _ phase_ne_zero) h

lemma scalarMerge_nodes_injective {m n:ℕ} (i:Fin m) (k:ℤ)
    (j:Fin n → Fin m) (hj:Function.Injective j) (hi:∀v,j v≠i) (l:Fin n → ℤ) :
    Function.Injective (Fin.cons (constF m c) (Fin.cons (fcos i (k+8)) (fun v =>fcos (j v) (l v+6)))) := by
  apply Fin.cons_injective_of_injective
  · rintro ⟨v,hv⟩
    induction v using Fin.cases with
    | zero => exact fcos_ne_const i (k+8) c hv
    | succ v => exact fcos_ne_const (j v) (l v+6) c hv
  · apply Fin.cons_injective_of_injective
    · rintro ⟨v,hv⟩
      exact shiftedCosine_ne (j v) i (hi v) _ _ (zpow_ne_zero _ phase_ne_zero) hv
    · exact fcos_tuple_injective j hj (fun v =>l v+6)


 

 

open scoped Classical

end

 

 

noncomputable section
open scoped Classical

lemma rationalAt_copy_fcos {m n:ℕ} (v:Fin m → Fin n) (i:Fin m) (k:ℤ) :
    RationalAt (copyEvaluation v).toRingHom (fcos i k) (fcos (v i) k) := by
  rw [fcos_eq,fcos_eq]
  apply rationalAt_torusCos
  · exact (rationalAt_const (copyEvaluation v) (phase^k)).mul ((rationalAt_copy_variable v i).pow 2)
  · exact mul_ne_zero (by simpa [constF] using (algebraMap ℂ (SpectralField n)).injective.ne (zpow_ne_zero k phase_ne_zero)) (pow_ne_zero _ (variableF_ne_zero _))







lemma torusEvaluation_lift {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (y:SpectralField m) (hy:y≠0) (P:Laurent n) :
    torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)
      (liftLaurent P)=torusEvaluation z hz P := by
  have he:(torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)).toRingHom.comp (liftLaurentHom n)=
      (torusEvaluation z hz).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change torusEvaluation _ _ (liftLaurent (monomialL _ _))=torusEvaluation _ _ (monomialL _ _)
    all_goals rw [liftLaurent_monomial]
    all_goals simp only [torusEvaluation_monomial,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,zpow_zero,mul_one]
  exact DFunLike.congr_fun he P

lemma torusEvaluation_lastCosine {n m:ℕ} (z:Fin (n+1) → SpectralField m) (hz:∀i,z i≠0) :
    torusEvaluation z hz (lastCosine n)=torusCos (z (Fin.last n)^2/constF m phase^3) := by
  have h:=RationalAt.algebraMap (φ:=(torusEvaluation z hz).toRingHom) (F:=SpectralField (n+1)) (lastCosine n)
  change RationalAt _ (evalLaurent (lastCosine n)) _ at h
  rw [lastCosine_map] at h
  apply h.unique
  exact rationalAt_torusCos _ (((rationalAt_variable z hz (Fin.last n)).pow 2).div
    ((rationalAt_const _ phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero m)))
    (div_ne_zero (pow_ne_zero _ (hz _)) (pow_ne_zero _ (constF_phase_ne_zero m)))

lemma torusEvaluation_lastSine {n m:ℕ} (z:Fin (n+1) → SpectralField m) (hz:∀i,z i≠0) :
    torusEvaluation z hz (lastSine n)=torusSin (z (Fin.last n)) := by
  have h:=RationalAt.algebraMap (φ:=(torusEvaluation z hz).toRingHom) (F:=SpectralField (n+1)) (lastSine n)
  change RationalAt _ (evalLaurent (lastSine n)) _ at h
  rw [evalLaurent_lastSine] at h
  exact h.unique (rationalAt_torusSin _ (rationalAt_variable z hz (Fin.last n)) (hz _))

lemma torusEvaluation_lastLaurent {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (y:SpectralField m) (hy:y≠0) (p:Pairing (n+1)) (P:Polynomial (Laurent n)) :
    torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)
      (lastLaurent p P)=
      (if p.Occupied (Fin.last n) then torusSin y else 1)*
        (P.map (torusEvaluation z hz).toRingHom).eval (torusCos (y^2/constF m phase^3)) := by
  unfold lastLaurent
  rw [map_mul]
  change _ * (torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)).toRingHom (P.eval₂ _ _) = _
  rw [Polynomial.hom_eval₂]
  have he:(torusEvaluation (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)).toRingHom.comp (liftLaurentHom n)=(torusEvaluation z hz).toRingHom :=
    RingHom.ext (torusEvaluation_lift z hz y hy)
  change _ * P.eval₂ _ _=_
  rw [he]
  change _ * P.eval₂ _ (torusEvaluation _ _ (lastCosine n))=_
  rw [torusEvaluation_lastCosine]
  simp only [Fin.snoc_last,Polynomial.eval_map]
  congr 1
  split_ifs
  · simpa only [Fin.snoc_last] using torusEvaluation_lastSine (Fin.snoc z y) (fun i =>Fin.lastCases (by simpa using hy) (fun j =>by simpa using hz j) i)
  · exact map_one _



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

lemma reducedMovingStepL_pair_zero {n:ℕ} (s:ℕ) (hs:s=2 ∨ s=3) :
    (reducedMovingStepL (1:Fin (n+2)) 0).map (pairEvaluation n s).toRingHom=0 := by
  simp only [reducedMovingStepL,show (0:Fin (n+2))≠1 by intro h; have := congrArg Fin.val h; simp at this,ite_false,
    show ¬(1:Fin (n+2))<0 from not_lt_of_ge (Fin.zero_le _)]
  rw [matrix_map_ring_smul,matrix_map_ring_smul]
  rw [show (pairEvaluation n s).toRingHom
      (torusNumeratorL (variableExponent (1:Fin (n+2))-variableExponent 0) (phase^3) .vacant)=0 from pairEvaluation_vacantNumerator s hs]
  simp

lemma nodalDatumL_pair_self_zero {n:ℕ} (W:Pairing (n+1) → Laurent (n+1))
    (s:ℕ) (hs:s=2 ∨ s=3) (p:Pairing (n+3)) :
    pairEvaluation n s (nodalDatumL W (1:Fin (n+2)) p)=0 := by
  simp only [nodalDatumL,map_mul]
  have hm:(matrixPrefix (reducedMovingStepL (1:Fin (n+2))) (n+2)).map (pairEvaluation n s).toRingHom=0 := by
    rw [matrixPrefix_map]
    exact matrixPrefix_zero_of_first _ (reducedMovingStepL_pair_zero s hs) (n+1)
  rw [show pairEvaluation n s
      ((matrixPrefix (reducedMovingStepL (1:Fin (n+2))) (n+2)).mulVec _ p)=
      ((matrixPrefix (reducedMovingStepL (1:Fin (n+2))) (n+2)).map (pairEvaluation n s).toRingHom).mulVec _ p from
      RingHom.map_mulVec _ _ _ p]
  rw [hm,Matrix.zero_mulVec]
  simp

def pairEarlierWeights (n s:ℕ) : Fin (n+2) → Weights (SpectralField (n+1)) :=
  fun j =>torusWeights (constF (n+1) phase^(pairExponent n s j)/variableF (pairIndex n j))

def pairNodeWeights (n s:ℕ) (i:Fin (n+2)) : Fin (n+3) → Weights (SpectralField (n+1)) :=
  Fin.snoc (pairEarlierWeights n s) (torusWeights (variableF (pairIndex n i))⁻¹)

lemma pairPoint_of_ne {n s:ℕ} (i:Fin (n+2)) (hi:i≠1) :
    pairPoint n s i=variableF (pairIndex n i) := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => induction i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ i => rfl

lemma pairArgument {n s:ℕ} (hs:s≤3) (i:Fin (n+2)) :
    constF (n+1) phase^3/pairPoint n s i=
      constF (n+1) phase^(pairExponent n s i)/variableF (pairIndex n i) := by
  by_cases hi:i=1
  · subst i
    change constF (n+1) phase^3/(constF (n+1) phase^s*variableF 0)=constF (n+1) phase^(if (1:Fin (n+2))=1 then 3-s else 3)/variableF 0
    rw [ite_eq_left rfl]
    have hp:constF (n+1) phase^(3-s)*constF (n+1) phase^s=constF (n+1) phase^3 := by rw [←pow_add,Nat.sub_add_cancel hs]
    apply (div_eq_div_iff (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero _)) (variableF_ne_zero _)).mpr
    rw [←hp]; ring
  · rw [pairPoint_of_ne i hi,pairExponent,ite_eq_right hi]







lemma phaseCosine {n:ℕ} (i:Fin n) (s:ℤ) :
    torusCos ((constF n phase^s*variableF i)^2/constF n phase^3)=fcos i (2*s-3) := by
  rw [fcos_eq,show 2*s-3=s*2-3 by ring,zpow_sub₀ phase_ne_zero,zpow_mul]
  simp only [constF,map_div₀,map_pow,map_zpow₀,zpow_ofNat]
  congr 1
  ring

def pairCosines (n s:ℕ) : Fin (n+2) → SpectralField (n+1) :=
  Fin.cons (fcos 0 (-3)) (Fin.cons (fcos 0 (2*(s:ℤ)-3)) (fun i =>fcos i.succ (-3)))
def pairBeta (n s:ℕ) : Fin (n+2) → SpectralField (n+1) :=
  Fin.cons (deletionBeta 0) (Fin.cons (fcos 0 (2*(s:ℤ)+3)) (fun i =>deletionBeta i.succ))

lemma pairPoint_cosine {n s:ℕ} (i:Fin (n+2)) :
    torusCos ((pairPoint n s i)^2/constF (n+1) phase^3)=pairCosines n s i := by
  induction i using Fin.cases with
  | zero => simpa only [pairPoint,pairCosines,Fin.cons_zero,zpow_zero,one_mul,Int.mul_zero,Int.zero_sub] using phaseCosine (0:Fin (n+1)) 0
  | succ i => induction i using Fin.cases with
    | zero => simpa only [pairPoint,pairCosines,Fin.cons_succ,Fin.cons_zero,zpow_natCast] using phaseCosine (0:Fin (n+1)) (s:ℤ)
    | succ i => simpa only [pairPoint,pairCosines,Fin.cons_succ,zpow_zero,one_mul,Int.mul_zero,Int.zero_sub] using phaseCosine i.succ 0

lemma pairNode_cosine {n s:ℕ} (i:Fin (n+2)) :
    torusCos ((pairPoint n s i*constF (n+1) phase^3)^2/constF (n+1) phase^3)=pairBeta n s i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => induction i using Fin.cases with
    | zero =>
      change torusCos (((constF (n+1) phase^s*variableF 0)*constF (n+1) phase^3)^2/constF (n+1) phase^3)=_
      have he:(constF (n+1) phase^s*variableF 0)*constF (n+1) phase^3=constF (n+1) phase^((s:ℤ)+3)*variableF 0 := by
        rw [zpow_add₀ (constF_phase_ne_zero _),zpow_natCast,zpow_ofNat]; ring
      rw [he,phaseCosine]
      change fcos 0 (2*((s:ℤ)+3)-3)=fcos 0 (2*(s:ℤ)+3)
      congr 1; ring
    | succ i => rfl

lemma rationalAt_pair_spectralA {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (spectralA i) (pairCosines n s i) := by
  rw [←pairPoint_cosine i]
  exact rationalAt_torusCos _ (((rationalAt_pair_variable s i).pow 2).div
    ((rationalAt_const (pairEvaluation n s) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero _)))
    (div_ne_zero (pow_ne_zero _ (pairPoint_ne_zero n s i)) (pow_ne_zero _ (constF_phase_ne_zero _)))

lemma rationalAt_pair_deletionNode {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (deletionNode i)
      (pairPoint n s i*constF (n+1) phase^3) :=
  (rationalAt_pair_variable s i).mul ((rationalAt_const (pairEvaluation n s) phase).pow 3)

lemma rationalAt_pair_deletionBeta {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (deletionBeta i) (pairBeta n s i) := by
  rw [←pairNode_cosine i]
  exact rationalAt_torusCos _ (((rationalAt_pair_deletionNode s i).pow 2).div
    ((rationalAt_const (pairEvaluation n s) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero _)))
    (div_ne_zero (pow_ne_zero _ (mul_ne_zero (pairPoint_ne_zero n s i) (pow_ne_zero _ (constF_phase_ne_zero _))))
      (pow_ne_zero _ (constF_phase_ne_zero _)))

lemma pairEvaluation_betaL {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    pairEvaluation n s (betaL i)=pairBeta n s i := by
  have h:=RationalAt.algebraMap (φ:=(pairEvaluation n s).toRingHom) (F:=SpectralField (n+2)) (betaL i)
  change RationalAt _ (evalLaurent (betaL i)) _ at h
  rw [betaL_map] at h
  exact h.unique (rationalAt_pair_deletionBeta s i)

lemma pairBeta_of_ne {n s:ℕ} (i:Fin (n+2)) (hi:i≠1) : pairBeta n s i=deletionBeta (pairIndex n i) := by
  rw [←pairNode_cosine i,pairPoint_of_ne i hi]
  rfl







def deletePoint (n:ℕ) : Fin n → SpectralField (n+1) := fun i =>variableF i.succ

def deleteWeights (n:ℕ) : Fin n → Weights (SpectralField (n+1)) :=
  fun i =>torusWeights (constF (n+1) phase^3/variableF i.succ)

lemma pairEarlier_delete (n:ℕ) : pairEarlierWeights n 3=
    Fin.cons (torusWeights (constF (n+1) phase^3*(variableF 0)⁻¹))
      (Fin.cons (torusWeights ((variableF 0)⁻¹)) (deleteWeights n)) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [pairEarlierWeights,pairExponent,pairIndex,div_eq_mul_inv]
  | succ i => induction i using Fin.cases with
    | zero => simp [pairEarlierWeights,pairExponent,pairIndex]
    | succ i =>
      have hi : i.succ.succ≠(1:Fin (n+2)) := by intro h; have := congrArg Fin.val h; simp at this
      simp [pairEarlierWeights,pairExponent,pairIndex,hi,deleteWeights]

lemma pairNode_delete {n:ℕ} (i:Fin (n+2)) : pairNodeWeights n 3 i=
    Fin.cons (torusWeights (constF (n+1) phase^3*(variableF 0)⁻¹))
      (Fin.cons (torusWeights ((variableF 0)⁻¹))
        (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))) := by
  rw [pairNodeWeights,pairEarlier_delete]
  rw [←Fin.cons_snoc_eq_snoc_cons,←Fin.cons_snoc_eq_snoc_cons]
  rfl

lemma deletePoint_node_weights {n:ℕ} (i:Fin (n+1)) :
    (fun j =>torusWeights (constF (n+1) phase^3/
      (Fin.snoc (deletePoint n) (deletionNode i) : Fin (n+1) → SpectralField (n+1)) j)) =
      copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) i := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp only [Fin.snoc_last,copiedNodeWeights]
      congr 1
      rw [deletionNode]
      field_simp [constF_phase_ne_zero,variableF_ne_zero]
  | cast j => simp only [Fin.snoc_castSucc,copiedNodeWeights,deletePoint,spectralWeights]

def deletePairScalar (n:ℕ) : SpectralField (n+1) :=
  (fcos 0 (-3)+fcos 0 3+constF (n+1) rho)*
    ∏j:Fin n,(fcos j.succ (-3)-fcos 0 (-9))*(fcos j.succ (-3)-fcos 0 9)

def mergePairScalar (n:ℕ) : SpectralField (n+1) :=
  (fcos 0 (-3)+fcos 0 1+constF (n+1) rho)*∏j:Fin n,(fcos j.succ (-3)+fcos 0 (-1))

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalTorusValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma lastValue_mul_poly {K:Type*} [CommRing K] {n:ℕ}
    (b s:K) (F:Polynomial K) (P:Pairing (n+1) → Polynomial K) :
    lastValue (RingHom.id K) b s (fun p =>F*P p)=F.eval b • lastValue (RingHom.id K) b s P := by
  funext p
  simp only [lastValue,Polynomial.eval₂_id,Polynomial.eval_mul,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring







lemma deletePoint_cosines (n:ℕ) :
    (fun i:Fin n =>torusCos ((deletePoint n i)^2/constF (n+1) phase^3))=
      fun i:Fin n =>fcos i.succ (-3) := by
  funext i
  have he:=phaseCosine i.succ 0
  norm_num only at he
  simpa only [deletePoint,zpow_zero,one_mul] using he

def deleteEvaluation (n:ℕ) : Laurent n →ₐ[ℂ] SpectralField (n+1) :=
  torusEvaluation (deletePoint n) (fun i =>variableF_ne_zero i.succ)

def deletePairPolynomial (n:ℕ) : Polynomial (SpectralField (n+1)) :=
  Polynomial.C (deletePairScalar n)*((Polynomial.X-Polynomial.C (fcos 0 (-9)))*(Polynomial.X-Polynomial.C (fcos 0 9)))

lemma deletePairPolynomial_degree (n:ℕ) : (deletePairPolynomial n).natDegree≤2 := by
  apply (Polynomial.natDegree_mul_le ..).trans
  simp only [Polynomial.natDegree_C,zero_add]
  apply (Polynomial.natDegree_mul_le ..).trans
  simp only [Polynomial.natDegree_X_sub_C]; omega

lemma deletePairPolynomial_top (n:ℕ) : (deletePairPolynomial n).coeff 2=deletePairScalar n := by
  rw [deletePairPolynomial,Polynomial.coeff_C_mul]
  have hp:(Polynomial.X-Polynomial.C (fcos (0:Fin (n+1)) (-9)))*(Polynomial.X-Polynomial.C (fcos 0 9))=
      Polynomial.X^2-Polynomial.C (fcos 0 (-9)+fcos 0 9)*Polynomial.X+Polynomial.C (fcos 0 (-9)*fcos 0 9) := by simp only [map_add,map_mul]; ring
  rw [hp]
  simp

lemma deletePairPolynomial_eval {n:ℕ} (b:SpectralField (n+1)) :
    (deletePairPolynomial n).eval b=deletePairScalar n*((b-fcos 0 (-9))*(b-fcos 0 9)) := by
  simp [deletePairPolynomial]







lemma pairBeta_head_ne {n s:ℕ} (hs:s=2 ∨ s=3) :
    deletionBeta (0:Fin (n+1))≠fcos 0 (2*(s:ℤ)+3) := by
  intro h
  rw [deletionBeta_shiftedCosine] at h
  have hh:=shiftedCosine_parameter 0 _ _ h
  rw [show 2*(s:ℤ)+3=3+2*s by ring,zpow_add₀ phase_ne_zero] at hh
  have he:phase^((2:ℤ)*s)=1 := mul_left_cancel₀ (zpow_ne_zero 3 phase_ne_zero) (by simpa using hh.symm)
  rcases hs with rfl|rfl
  · exact phase_four_ne_one (by simpa using he)
  · exact phase_six_ne_one (by simpa using he)

lemma pairBeta_injective (n s:ℕ) (hs:s=2 ∨ s=3) : Function.Injective (pairBeta n s) := by
  apply Fin.cons_injective_of_injective
  · rintro ⟨v,hv⟩
    induction v using Fin.cases with
    | zero => exact pairBeta_head_ne hs hv.symm
    | succ v => exact (deletionBeta_injective (n+1)).ne (Fin.succ_ne_zero v) hv
  · apply Fin.cons_injective_of_injective
    · rintro ⟨v,hv⟩
      change deletionBeta v.succ=fcos 0 (2*(s:ℤ)+3) at hv
      rw [deletionBeta_shiftedCosine] at hv
      exact shiftedCosine_ne v.succ 0 (Fin.succ_ne_zero v) _ _ (zpow_ne_zero _ phase_ne_zero) hv
    · exact (deletionBeta_injective (n+1)).comp (Fin.succ_injective n)









def mergeZ (n:ℕ) : SpectralField (n+1) := constF (n+1) phase/variableF 0
def mergePoint (n:ℕ) : Fin (n+1) → SpectralField (n+1) :=
  Fin.cons (constF (n+1) phase*variableF 0) (deletePoint n)
def mergeNewWeights (n:ℕ) : Fin (n+1) → Weights (SpectralField (n+1)) :=
  Fin.cons (torusWeights (constF (n+1) phase*mergeZ n)) (deleteWeights n)

lemma mergeNewWeights_phase (n:ℕ) : mergeNewWeights n=
    fun i =>torusWeights (constF (n+1) phase^mergeExponent n i/variableF i) := by
  funext i
  induction i using Fin.cases with
  | zero => simp only [mergeNewWeights,Fin.cons_zero,mergeExponent,mergeZ]; congr 1; ring
  | succ i => rfl

lemma mergeZ_ne_zero (n:ℕ) : mergeZ n≠0 := div_ne_zero (constF_phase_ne_zero _) (variableF_ne_zero _)

lemma pairEarlier_merge (n:ℕ) : pairEarlierWeights n 2=
    Fin.cons (torusWeights (constF (n+1) phase^2*mergeZ n))
      (Fin.cons (torusWeights (mergeZ n)) (deleteWeights n)) := by
  funext i
  induction i using Fin.cases with
  | zero =>
      simp only [pairEarlierWeights,pairExponent,pairIndex,Fin.cons_zero]
      rw [ite_eq_right (by intro h; have := congrArg Fin.val h; simp at this)]
      congr 1; unfold mergeZ; ring
  | succ i => induction i using Fin.cases with
    | zero => simp [pairEarlierWeights,pairExponent,pairIndex,mergeZ]
    | succ i =>
      have hi : i.succ.succ≠(1:Fin (n+2)) := by intro h; have := congrArg Fin.val h; simp at this
      simp [pairEarlierWeights,pairExponent,pairIndex,hi,deleteWeights]

lemma mergePoint_ne_zero (n:ℕ) (i:Fin (n+1)) : mergePoint n i≠0 := by
  induction i using Fin.cases with
  | zero => exact mul_ne_zero (constF_phase_ne_zero _) (variableF_ne_zero _)
  | succ i => exact variableF_ne_zero _

lemma mergePoint_weights (n:ℕ) :
    (fun i =>torusWeights (constF (n+1) phase^3/mergePoint n i))=mergeNewWeights n := by
  funext i
  induction i using Fin.cases with
  | zero =>
      change torusWeights (constF (n+1) phase^3/(constF (n+1) phase*variableF 0))=_
      change _=torusWeights (constF (n+1) phase*(constF (n+1) phase/variableF 0))
      congr 1
      field_simp [constF_phase_ne_zero,variableF_ne_zero]
  | succ i => rfl

lemma mergePoint_argument (n:ℕ) (i:Fin (n+1)) :
    constF (n+1) phase^3/mergePoint n i=constF (n+1) phase^(mergeExponent n i)/variableF i := by
  induction i using Fin.cases with
  | zero =>
      change constF (n+1) phase^3/(constF (n+1) phase*variableF 0)=constF (n+1) phase^2/variableF 0
      field_simp [constF_phase_ne_zero,variableF_ne_zero]
  | succ i => rfl

lemma mergePoint_cosines (n:ℕ) :
    (fun i =>torusCos ((mergePoint n i)^2/constF (n+1) phase^3))=
      Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3)) := by
  funext i
  induction i using Fin.cases with
  | zero =>
      have he:=phaseCosine (0:Fin (n+1)) 1
      norm_num only at he
      simpa only [mergePoint,Fin.cons_zero,zpow_one] using he
  | succ i =>
      have he:=phaseCosine i.succ 0
      norm_num only at he
      simpa only [mergePoint,deletePoint,Fin.cons_succ,zpow_zero,one_mul] using he


 

 


def mergeNodeWeights {n:ℕ} (i:Fin (n+1)) : Fin (n+2) → Weights (SpectralField (n+1)) :=
  Fin.snoc (mergeNewWeights n) (torusWeights ((variableF i)⁻¹))

lemma pairNode_merge {n:ℕ} (i:Fin (n+2)) : pairNodeWeights n 2 i=
    Fin.cons (torusWeights (constF (n+1) phase^2*mergeZ n))
      (Fin.cons (torusWeights (mergeZ n))
        (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))) := by
  rw [pairNodeWeights,pairEarlier_merge]
  rw [←Fin.cons_snoc_eq_snoc_cons,←Fin.cons_snoc_eq_snoc_cons]
  rfl

lemma mergeNode_cons {n:ℕ} (i:Fin (n+1)) : mergeNodeWeights i=
    Fin.cons (torusWeights (constF (n+1) phase*mergeZ n))
      (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) i) := by
  unfold mergeNodeWeights mergeNewWeights
  rw [←Fin.cons_snoc_eq_snoc_cons]
  rfl

lemma mergePoint_node_weights {n:ℕ} (i:Fin (n+1)) :
    (fun j =>torusWeights (constF (n+1) phase^3/
      (Fin.snoc (mergePoint n) (deletionNode i) : Fin (n+2) → SpectralField (n+1)) j)) =mergeNodeWeights i := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp only [Fin.snoc_last,mergeNodeWeights]
      congr 1
      rw [deletionNode]
      field_simp [constF_phase_ne_zero,variableF_ne_zero]
  | cast j => simpa only [Fin.snoc_castSucc,mergeNodeWeights] using congrFun (mergePoint_weights n) j







def mergeEvaluation (n:ℕ) : Laurent (n+1) →ₐ[ℂ] SpectralField (n+1) :=
  torusEvaluation (mergePoint n) (mergePoint_ne_zero n)

def mergePairPolynomial (n:ℕ) : Polynomial (SpectralField (n+1)) :=
  Polynomial.C (mergePairScalar n)*(Polynomial.X+Polynomial.C (fcos 0 (-1)))

lemma mergePairPolynomial_degree (n:ℕ) : (mergePairPolynomial n).natDegree≤1 := by
  apply (Polynomial.natDegree_mul_le ..).trans
  simp

lemma mergePairPolynomial_top (n:ℕ) : (mergePairPolynomial n).coeff 1=mergePairScalar n := by
  simp [mergePairPolynomial]

lemma mergePairPolynomial_eval {n:ℕ} (b:SpectralField (n+1)) :
    (mergePairPolynomial n).eval b=mergePairScalar n*(b+fcos 0 (-1)) := by
  simp [mergePairPolynomial]

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







lemma torusEvaluation_fieldMap {n m k:ℕ} (f:SpectralField m →+* SpectralField k)
    (hf:∀c,f (constF m c)=constF k c)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0) (P:Laurent n) :
    f (torusEvaluation z hz P)=torusEvaluation (fun i =>f (z i)) (fun i =>(map_ne_zero f).mpr (hz i)) P := by
  have he:f.comp (torusEvaluation z hz).toRingHom=
      (torusEvaluation (fun i =>f (z i)) (fun i =>(map_ne_zero f).mpr (hz i))).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change f (torusEvaluation z hz (monomialL _ _))=torusEvaluation _ _ (monomialL _ _)
    all_goals simp only [torusEvaluation_monomial,map_mul,map_prod,map_zpow₀,hf]
  exact DFunLike.congr_fun he P

def freePoint {n m:ℕ} (z:Fin n → SpectralField m) : Fin (n+1) → SpectralField (m+1) :=
  Fin.snoc (fun i =>liftSpectral m (z i)) (variableF (Fin.last m))

lemma freePoint_ne_zero {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (i:Fin (n+1)) : freePoint z i≠0 := by
  induction i using Fin.lastCases with
  | last => simpa only [freePoint,Fin.snoc_last] using variableF_ne_zero (Fin.last m)
  | cast i => simpa only [freePoint,Fin.snoc_castSucc] using (map_ne_zero (liftSpectral m)).mpr (hz i)

lemma freePoint_variable (m:ℕ) : freePoint (@variableF m)=variableF := by
  funext i; induction i using Fin.lastCases <;> simp [freePoint]

lemma freePoint_cons {n m:ℕ} (a:SpectralField m) (z:Fin n → SpectralField m) :
    freePoint (Fin.cons a z)=Fin.cons (liftSpectral m a) (freePoint z) := by
  unfold freePoint
  have he:(fun i =>liftSpectral m ((Fin.cons a z : Fin (n+1) → SpectralField m) i))=
      Fin.cons (liftSpectral m a) (fun i =>liftSpectral m (z i)) := by
    funext i; induction i using Fin.cases <;> simp
  rw [he,←Fin.cons_snoc_eq_snoc_cons]

lemma torusEvaluation_free_lastLaurent {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (p:Pairing (n+1)) (P:Polynomial (Laurent n)) :
    torusEvaluation (freePoint z) (freePoint_ne_zero z hz) (lastLaurent p P)=
      (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last m)) else 1)*
        (P.map (torusEvaluation z hz).toRingHom).eval₂ (liftSpectral m) (spectralA (Fin.last m)) := by
  dsimp only [freePoint]
  rw [torusEvaluation_lastLaurent _ (fun i =>(map_ne_zero (liftSpectral m)).mpr (hz i)) _ (variableF_ne_zero _)]
  have he:(torusEvaluation (fun i =>liftSpectral m (z i)) (fun i =>(map_ne_zero (liftSpectral m)).mpr (hz i))).toRingHom=
      (liftSpectral m).comp (torusEvaluation z hz).toRingHom := by
    apply RingHom.ext
    intro Q
    exact (torusEvaluation_fieldMap (liftSpectral m) (liftSpectral_const m) z hz Q).symm
  rw [he,Polynomial.eval_map,←Polynomial.eval₂_map]
  rfl

lemma freePoint_firstFlat (n:ℕ) : freePoint (firstFlatPoint n)=firstFlatPoint (n+1) := by
  rw [firstFlatPoint,freePoint_cons,map_one,freePoint_variable]
  rfl
lemma freePoint_firstThree (n:ℕ) : freePoint (firstThreePoint n)=firstThreePoint (n+1) := by
  rw [firstThreePoint,freePoint_cons,map_pow,liftSpectral_const,freePoint_variable]
  rfl
lemma freePoint_pair (n s:ℕ) : freePoint (pairPoint n s)=pairPoint (n+1) s := by
  unfold pairPoint
  rw [freePoint_cons,freePoint_cons]
  simp only [map_mul,map_pow,liftSpectral_const,liftSpectral_variable,Fin.castSucc_zero]
  congr 2
  funext i
  induction i using Fin.lastCases with
  | last => simp only [freePoint,Fin.snoc_last]; rfl
  | cast i => simp only [freePoint,Fin.snoc_castSucc,liftSpectral_variable]; rfl

lemma firstFlatEvaluation_lastLaurent {n:ℕ} (p:Pairing (n+2)) (P:Polynomial (Laurent (n+1))) :
    firstFlatEvaluation (n+1) (lastLaurent p P)=
      lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
        (fun _ : Pairing (n+2) =>P.map (firstFlatEvaluation n).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (firstFlatPoint n) (firstFlatPoint_ne_zero n) p P
  simpa only [freePoint_firstFlat,firstFlatEvaluation,lastValue,ite_mul,one_mul] using h

lemma firstThreeEvaluation_lastLaurent {n:ℕ} (p:Pairing (n+2)) (P:Polynomial (Laurent (n+1))) :
    firstThreeEvaluation (n+1) (lastLaurent p P)=
      lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
        (fun _ : Pairing (n+2) =>P.map (firstThreeEvaluation n).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (firstThreePoint n) (firstThreePoint_ne_zero n) p P
  simpa only [freePoint_firstThree,firstThreeEvaluation,lastValue,ite_mul,one_mul] using h


 

 


lemma lastValue_spectral (n:ℕ) :
    lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (rationalNodalPolynomial n)=rationalInterpolant n := by
  funext p; simp only [lastValue,rationalInterpolant,ite_mul,one_mul]

lemma lastValue_C_mul {K L:Type*} [CommRing K] [CommRing L] {n:ℕ}
    (f:K →+* L) (a:K) (b s:L) (P:Pairing (n+1) → Polynomial K) :
    lastValue f b s (fun p =>Polynomial.C a*P p)=f a • lastValue f b s P := by
  funext p
  simp only [lastValue,Polynomial.eval₂_mul,Polynomial.eval₂_C,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring







lemma lastValue_mul_poly_map {K L:Type*} [CommRing K] [CommRing L] {n:ℕ}
    (f:K →+* L) (Q:Polynomial K) (b s:L) (P:Pairing (n+1) → Polynomial K) :
    lastValue f b s (fun p =>Q*P p)=Q.eval₂ f b • lastValue f b s P := by
  funext p
  simp only [lastValue,Polynomial.eval₂_mul,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

lemma torusEvaluation_unit_zpow {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (u:(Laurent n)ˣ) (k:ℤ) :
    torusEvaluation z hz ((u^k:(Laurent n)ˣ):Laurent n)=(torusEvaluation z hz (u:Laurent n))^k :=
  ((torusEvaluation z hz).toMonoidHom.comp (Units.coeHom _)).map_zpow u k

lemma substitution_torusEvaluation_general {n m:ℕ} (i:Fin (n+1)) (u:(Laurent n)ˣ)
    (v:Fin (n+1) → SpectralField m) (hv:∀j,v j≠0)
    (z:Fin n → SpectralField m) (hz:∀j,z j≠0)
    (hi:v i=torusEvaluation z hz (u:Laurent n)) (hj:∀j,v (i.succAbove j)=z j)
    (f:Laurent (n+1)) :
    torusEvaluation v hv f=torusEvaluation z hz (substituteLaurent i u f) := by
  have h:(torusEvaluation v hv).toRingHom=
      (torusEvaluation z hz).toRingHom.comp (substituteLaurent i u) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change torusEvaluation v hv (monomialL _ _)=torusEvaluation z hz (substituteLaurent i u (monomialL _ _))
    all_goals rw [torusEvaluation_monomial,substituteLaurent_monomial,map_mul,
      torusEvaluation_monomial,torusEvaluation_unit_zpow,Fin.prod_univ_succAbove _ i]
    all_goals simp only [hi,hj,Fin.removeNth]
    all_goals ring
  exact DFunLike.congr_fun h f

lemma generic_substitution_zero {n m:ℕ} (i:Fin (n+1)) (u:(Laurent n)ˣ)
    (v:Fin (n+1) → SpectralField n) (hv:∀j,v j≠0)
    (hi:v i=evalLaurent (u:Laurent n)) (hj:∀j,v (i.succAbove j)=variableF j)
    (f:Laurent (n+1)) (h:torusEvaluation v hv f=0)
    (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0)
    (hzI:z i=torusEvaluation (z ∘ i.succAbove) (fun _ =>hz _) (u:Laurent n)) :
    torusEvaluation z hz f=0 := by
  rw [substitution_torusEvaluation i u v hv hi hj] at h
  have hf:substituteLaurent i u f=0 :=
    IsFractionRing.injective (SpectralRing n) (SpectralField n) (by simpa only [evalLaurent,map_zero] using h)
  rw [substitution_torusEvaluation_general i u z hz (z ∘ i.succAbove) (fun j =>hz _) hzI (fun j =>rfl),hf,map_zero]

lemma firstFlatEvaluation_zero_universal {n m:ℕ} (f:Laurent (n+1))
    (h:firstFlatEvaluation n f=0) (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0) (h0:z 0=1) :
    torusEvaluation z hz f=0 := by
  apply generic_substitution_zero 0 (monomialUnit 0 1 one_ne_zero)
    (firstFlatPoint n) (firstFlatPoint_ne_zero n) _ _ f h z hz
  · simpa [monomialUnit,torusEvaluation_monomial,constF] using h0
  · simp [firstFlatPoint,monomialUnit,evalLaurent]
  · intro j; simp [firstFlatPoint]

lemma firstThreeEvaluation_zero_universal {n m:ℕ} (f:Laurent (n+1))
    (h:firstThreeEvaluation n f=0) (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0)
    (h0:z 0=constF m phase^3) : torusEvaluation z hz f=0 := by
  apply generic_substitution_zero 0 (monomialUnit 0 (phase^3) (pow_ne_zero _ phase_ne_zero))
    (firstThreePoint n) (firstThreePoint_ne_zero n) _ _ f h z hz
  · simpa [monomialUnit,torusEvaluation_monomial,constF] using h0
  · simp [firstThreePoint,monomialUnit,evalLaurent_monomial_product,constF]
  · intro j; simp [firstThreePoint]

lemma pairEvaluation_zero_universal {n m:ℕ} (s:ℕ) (f:Laurent (n+2))
    (h:pairEvaluation n s f=0) (z:Fin (n+2) → SpectralField m) (hz:∀j,z j≠0)
    (h01:z 1=constF m phase^s*z 0) : torusEvaluation z hz f=0 := by
  apply generic_substitution_zero 1 (monomialUnit (variableExponent 0) (phase^s) (pow_ne_zero _ phase_ne_zero))
    (pairPoint n s) (pairPoint_ne_zero n s) _ _ f h z hz
  · simpa [monomialUnit,torusEvaluation_monomial,variableExponent,Pi.single_apply,constF] using h01
  · simp only [pairPoint,monomialUnit,evalLaurent_monomial_product]
    simp [variableExponent,Pi.single_apply,constF]
  · intro j
    induction j using Fin.cases with
    | zero => simp [pairPoint]
    | succ j => simp [pairPoint]

end





noncomputable section
open scoped Classical LaurentPolynomial



lemma evalLaurent_monomial_full {n:ℕ} (e:Fin n → ℤ) (c:ℂ) :
    evalLaurent (monomialL e c)=constF n c*∏j:Fin n,variableF j^(e j) := by
  exact (evalLaurent_monomial_product e c)

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
open scoped Classical LaurentPolynomial

def residualRoot {n:ℕ} (i:Fin n) (v:Fin (n+1) × Fin 4) : SpectralField (n+1) :=
  evalLaurent (monomialL (residualRootExponent i v.1 v.2) (phase^(residualRootPhase i v.1 v.2)))

lemma residualRoot_ne_zero {n:ℕ} (i:Fin n) (v:Fin (n+1) × Fin 4) : residualRoot i v≠0 := by
  unfold residualRoot
  intro h
  have he:monomialL (residualRootExponent i v.1 v.2) (phase^residualRootPhase i v.1 v.2)=0 :=
    IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1)) (by simpa only [evalLaurent,map_zero] using h)
  exact pow_ne_zero _ phase_ne_zero (AddMonoidAlgebra.single_eq_zero.mp he)

lemma residualRoot_injective {n:ℕ} (i:Fin n) : Function.Injective (residualRoot i) := by
  rintro ⟨j,k⟩ ⟨l,r⟩ h
  have he:monomialL (residualRootExponent i j k) (phase^residualRootPhase i j k)=
      monomialL (residualRootExponent i l r) (phase^residualRootPhase i l r) :=
    IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1)) h
  have hh:=AddMonoidAlgebra.single_inj.mp he
  rcases hh with ⟨hex,hphase⟩ | ⟨hz,_⟩
  · have hj:=residualRootExponent_index i j l k r hex
    subst l
    have hk:=phase_primitive.pow_inj (residualRootPhase_lt i j k) (residualRootPhase_lt i j r) hphase
    exact Prod.ext rfl (residualRootPhase_injective i j hk)
  · exact (pow_ne_zero _ phase_ne_zero hz).elim

def residualRootSet {n:ℕ} (i:Fin n) : Finset (SpectralField (n+1)) :=
  Finset.univ.image (residualRoot i)

lemma residualRootSet_card {n:ℕ} (i:Fin n) : (residualRootSet i).card=4*(n+1) := by
  rw [residualRootSet,Finset.card_image_of_injective _ (residualRoot_injective i)]
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  omega



end

 

 

noncomputable section
open scoped Classical

lemma torusSin_monomial_ne_zero {n:ℕ} (e:Fin n → ℤ) (he:e≠0) (c:ℂ) (hc:c≠0) :
    torusSin (evalLaurent (monomialL e c))≠0 := by
  apply div_ne_zero _ (mul_ne_zero (by norm_num) ((map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero))
  apply sub_ne_zero.mpr
  intro h
  rw [show (evalLaurent (monomialL e c))⁻¹=evalLaurent (monomialL (-e) c⁻¹) from map_monomialL_inv e c hc] at h
  have hh:=IsFractionRing.injective (SpectralRing n) (SpectralField n) h
  rcases AddMonoidAlgebra.single_inj.mp hh with ⟨heq,_⟩|⟨hz,_⟩
  · apply he
    funext i
    have hi:=congrFun heq i
    change e i= -e i at hi
    change e i=0
    omega
  · exact hc hz

lemma constF_mul_monomial {n:ℕ} (c d:ℂ) (e:Fin n → ℤ) :
    constF n c*evalLaurent (monomialL e d)=evalLaurent (monomialL e (c*d)) := by
  rw [←map_constantL]
  change evalLaurent (constantL n c)*evalLaurent (monomialL e d)=_
  unfold evalLaurent
  rw [←map_mul (algebraMap (SpectralRing n) (SpectralField n))]
  simp [constantL,monomialL,AddMonoidAlgebra.single_mul_single]

lemma torusL_monomial_ne_zero {n:ℕ} (e:Fin n → ℤ) (he:e≠0) (c:ℂ) (hc:c≠0) :
    torusL (evalLaurent (monomialL e c))≠0 := by
  unfold torusL
  have h (s:ℕ):constF n phase^s*evalLaurent (monomialL e c)=evalLaurent (monomialL e (phase^s*c)) := by
    change (algebraMap ℂ (SpectralField n)) phase^s*evalLaurent (monomialL e c)=_
    rw [←map_pow (algebraMap ℂ (SpectralField n))]; exact constF_mul_monomial _ _ _
  rw [h 2,h 3]
  exact mul_ne_zero (torusSin_monomial_ne_zero e he _ (mul_ne_zero (pow_ne_zero _ phase_ne_zero) hc))
    (torusSin_monomial_ne_zero e he _ (mul_ne_zero (pow_ne_zero _ phase_ne_zero) hc))

lemma monomial_ratio_regular {n:ℕ} (e f:Fin n → ℤ) (hef:e≠f) (c d:ℂ) (hc:c≠0) (hd:d≠0) :
    torusL (evalLaurent (monomialL e c)/evalLaurent (monomialL f d))≠0 := by
  rw [div_eq_mul_inv,show (evalLaurent (monomialL f d))⁻¹=evalLaurent (monomialL (-f) d⁻¹) from map_monomialL_inv f d hd]
  unfold evalLaurent
  rw [←map_mul (algebraMap (SpectralRing n) (SpectralField n))]
  rw [monomialL_mul]
  apply torusL_monomial_ne_zero _ _ _ (mul_ne_zero hc (inv_ne_zero hd))
  simpa only [←sub_eq_add_neg,sub_ne_zero] using hef

lemma flat_update_regular {n:ℕ} (i j:Fin n) (hij:i≠j) (c:ℂ) (hc:c≠0) :
    torusL ((Function.update variableF i.castSucc (constF (n+1) c)) i.castSucc/
      (Function.update variableF i.castSucc (constF (n+1) c)) j.castSucc)≠0 := by
  simp only [Function.update_self,Function.update_of_ne (fun h =>hij (Fin.castSucc_injective n h).symm)]
  change torusL (evalLaurent (monomialL 0 c)/evalLaurent (monomialL (variableExponent j.castSucc) 1))≠0
  apply monomial_ratio_regular _ _ _ c 1 hc one_ne_zero
  intro h
  have hh:=congrFun h j.castSucc
  simp [variableExponent] at hh







lemma torusEvaluation_signLaurent {n m:ℕ} (i:Fin (n+1))
    (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0) (f:Laurent (n+1)) :
    torusEvaluation z hz (signLaurent i f)=
      torusEvaluation (Function.update z i (-z i))
        (fun j =>by by_cases h:j=i <;> simp [h,hz]) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | single e c =>
    change torusEvaluation z hz (signLaurent i (monomialL e c))=
      torusEvaluation (Function.update z i (-z i)) _ (monomialL e c)
    rw [signLaurent_monomial,torusEvaluation_monomial,torusEvaluation_monomial]
    rw [Fin.prod_univ_succAbove _ i,Fin.prod_univ_succAbove _ i]
    simp only [Function.update_self,Function.update_of_ne (Fin.succAbove_ne i _),constF,map_mul,map_zpow₀,map_neg,map_one]
    rw [show -z i=(-1)*z i by ring,mul_zpow]
    ring

lemma torusEvaluation_neg_zero {n m:ℕ} (i:Fin (n+1))
    (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0) (f:Laurent (n+1))
    (hodd:signLaurent i f= -f) (h:torusEvaluation z hz f=0) :
    torusEvaluation (Function.update z i (-z i))
      (fun j =>by by_cases h:j=i <;> simp [h,hz]) f=0 := by
  rw [←torusEvaluation_signLaurent i z hz f,hodd,map_neg,h,neg_zero]







def positiveResidualRoot {n:ℕ} (i:Fin n) (j:Fin (n+1)) (b:Bool) : SpectralField (n+1) :=
  if j=i.castSucc then (if b then constF (n+1) phase^3 else 1)
  else if j=Fin.last n then (if b then (variableF j)⁻¹ else (constF (n+1) phase^3)⁻¹*variableF j)
  else if j.val < i.val then constF (n+1) phase^(if b then 3 else 2)*variableF j
  else (constF (n+1) phase^(if b then 3 else 2))⁻¹*variableF j

lemma residualRoot_values {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) :
    residualRoot i (j,k)=
      if k=0 then positiveResidualRoot i j false else
      if k=1 then -positiveResidualRoot i j false else
      if k=2 then positiveResidualRoot i j true else -positiveResidualRoot i j true := by
  have hp:=phase_more_powers
  by_cases hi:j=i.castSucc
  · fin_cases k <;> simp [residualRoot,residualRootPhase,residualRootExponent,positiveResidualRoot,hi,
      evalLaurent_monomial_product,constF,show evalLaurent (1:Laurent (n+1))=1 from map_one _,phase_eight,hp.2.1]
  · by_cases hl:j=Fin.last n
    · have hli : (Fin.last n : Fin (n+1))≠i.castSucc := Ne.symm (Fin.castSucc_ne_last i)
      fin_cases k <;> simp [residualRoot,residualRootPhase,residualRootExponent,positiveResidualRoot,hl,hli,
        evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF,phase_eight,
        hp.2.2.1,hp.2.2.2.2.1]
    · by_cases hji:j.val < i.val
      · fin_cases k <;> simp [residualRoot,residualRootPhase,residualRootExponent,positiveResidualRoot,hi,hl,hji,
          evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF,hp.1,hp.2.1]
      · fin_cases k <;> simp [residualRoot,residualRootPhase,residualRootExponent,positiveResidualRoot,hi,hl,hji,
          evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF,
          hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2]

lemma positiveResidualRoot_ne_zero {n:ℕ} (i:Fin n) (j:Fin (n+1)) (b:Bool) :
    positiveResidualRoot i j b≠0 := by
  cases b
  · simpa [residualRoot_values] using residualRoot_ne_zero i (j,0)
  · simpa [residualRoot_values] using residualRoot_ne_zero i (j,2)

lemma residualRoot_signed {n:ℕ} (i:Fin n) (v:Fin (n+1) × Fin 4) :
    ∃b:Bool,residualRoot i v=positiveResidualRoot i v.1 b ∨
      residualRoot i v= -positiveResidualRoot i v.1 b := by
  rcases v with ⟨j,k⟩
  fin_cases k
  · exact ⟨false,Or.inl (by simp [residualRoot_values])⟩
  · exact ⟨false,Or.inr (by simp [residualRoot_values])⟩
  · exact ⟨true,Or.inl (by simp [residualRoot_values])⟩
  · exact ⟨true,Or.inr (by simp [residualRoot_values])⟩

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

lemma pairEvaluation_lastLaurent {n:ℕ} (s:ℕ) (p:Pairing (n+3)) (P:Polynomial (Laurent (n+2))) :
    pairEvaluation (n+1) s (lastLaurent p P)=
      lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
        (fun _ : Pairing (n+3) =>P.map (pairEvaluation n s).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (pairPoint n s) (pairPoint_ne_zero n s) p P
  simpa only [freePoint_pair,pairEvaluation,lastValue,ite_mul,one_mul] using h

lemma freePoint_delete (n:ℕ) : freePoint (deletePoint n)=deletePoint (n+1) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp only [freePoint,Fin.snoc_last,deletePoint]; rfl
  | cast i => simp only [freePoint,Fin.snoc_castSucc,deletePoint,liftSpectral_variable]; rfl

lemma freePoint_merge (n:ℕ) : freePoint (mergePoint n)=mergePoint (n+1) := by
  rw [mergePoint,freePoint_cons,freePoint_delete]
  simp only [map_mul,liftSpectral_const,liftSpectral_variable,Fin.castSucc_zero]
  rfl

lemma deleteEvaluation_lastLaurent {n:ℕ} (p:Pairing (n+1)) (P:Polynomial (Laurent n)) :
    deleteEvaluation (n+1) (lastLaurent p P)=
      lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
        (fun _ : Pairing (n+1) =>P.map (deleteEvaluation n).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (deletePoint n) (fun i =>variableF_ne_zero i.succ) p P
  simpa only [freePoint_delete,deleteEvaluation,lastValue,ite_mul,one_mul] using h

lemma mergeEvaluation_lastLaurent {n:ℕ} (p:Pairing (n+2)) (P:Polynomial (Laurent (n+1))) :
    mergeEvaluation (n+1) (lastLaurent p P)=
      lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
        (fun _ : Pairing (n+2) =>P.map (mergeEvaluation n).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (mergePoint n) (mergePoint_ne_zero n) p P
  simpa only [freePoint_merge,mergeEvaluation,lastValue,ite_mul,one_mul] using h

lemma liftSpectral_fcos {n:ℕ} (i:Fin n) (k:ℤ) :
    liftSpectral n (fcos i k)=fcos i.castSucc k := by
  simp only [fcos_eq,torusCos]
  simp only [map_div₀,map_add,map_mul,map_pow,map_inv₀,liftSpectral_const,liftSpectral_variable,map_ofNat]

lemma deletePairPolynomial_free (n:ℕ) :
    (deletePairPolynomial n).eval₂ (liftSpectral (n+1)) (spectralA (Fin.last (n+1)))=deletePairScalar (n+1) := by
  simp only [deletePairPolynomial,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_sub,Polynomial.eval₂_X]
  unfold deletePairScalar
  simp only [map_mul,map_prod,map_add,map_sub,liftSpectral_fcos,liftSpectral_const,Fin.castSucc_zero,Fin.prod_univ_castSucc]
  have he:fcos (Fin.last (n+1)) (-3)=spectralA (Fin.last (n+1)) := by
    have h:=phaseCosine (Fin.last (n+1)) 0
    norm_num only at h
    simpa only [zpow_zero,one_mul,spectralA] using h.symm
  simp only [Fin.succ_last,he,mul_assoc]
  rfl

lemma mergePairPolynomial_free (n:ℕ) :
    (mergePairPolynomial n).eval₂ (liftSpectral (n+1)) (spectralA (Fin.last (n+1)))=mergePairScalar (n+1) := by
  simp only [mergePairPolynomial,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_add,Polynomial.eval₂_X]
  unfold mergePairScalar
  simp only [map_mul,map_prod,map_add,liftSpectral_fcos,liftSpectral_const,Fin.castSucc_zero,Fin.prod_univ_castSucc]
  have he:fcos (Fin.last (n+1)) (-3)=spectralA (Fin.last (n+1)) := by
    have h:=phaseCosine (Fin.last (n+1)) 0
    norm_num only at h
    simpa only [zpow_zero,one_mul,spectralA] using h.symm
  simp only [Fin.succ_last,he,mul_assoc]
  rfl


 

 


lemma pairPoint_weights {n s:ℕ} (hs:s≤3) :
    (fun i =>torusWeights (constF (n+1) phase^3/pairPoint n s i))=pairEarlierWeights n s :=
  funext (fun i =>congrArg torusWeights (pairArgument hs i))

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

@[simp] lemma rowReflectSpectral_spectralA {n : ℕ} (i j : Fin n) :
    rowReflectSpectral i (spectralA j) = spectralA j := by
  simp only [spectralA,rowReflectSpectral_torusCos,map_div₀,map_pow,
    rowReflectSpectral_const,rowReflectSpectral_variable]
  split_ifs
  · unfold torusCos
    field_simp [variableF_ne_zero,constF_phase_ne_zero]
    ring
  · rfl

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators LaurentPolynomial

def archRootCoefficient (b : Bool) (k : ArchShiftIndex) : ℂ :=
  if b then phase^3/(phase^archRootShift k) else phase^archRootShift k

end
 

 

noncomputable section
open scoped Classical BigOperators



def nextScalar {K : Type*} [CommRing K] (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) : Polynomial K :=
  firstScalarHom f a (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))

def rowCosineL {n : ℕ} (i : Fin n) : Laurent n :=
  cosineL ((2:ℤ) • variableExponent i) (phase^3)⁻¹

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



def arcColumn {n : ℕ} (p : Pairing n) (a b : Fin n) : Configuration n := fun i=>
  if i=a then .cup else if i=b then .vertical₀ else
  if a < i ∧ i < b then .diagonal₀ else if p.Occupied i then .diagonal₁ else .vacant

end
end CriticalStrip.Diagram

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

namespace NorthHistory
variable {N m : ℕ}

def weight (h : NorthHistory N m) : ℝ :=
  ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn h.left) *
  ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn h.right)

end NorthHistory
end
end CriticalStrip





end OAI
end


