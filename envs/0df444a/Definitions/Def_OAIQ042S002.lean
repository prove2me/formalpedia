-- Prove2me | Definitions.Def_OAIQ042S002
-- name    : OAIQ042S002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:33:14.695029+00:00
-- url     : https://prove2.me/theorems/3a0f782c-b58e-413f-9f46-966d1b20a378
-- title:
--   Definitions bundle OAIQ042S002 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 454 declarations of OpenAI's Lean: 120 definitions, 11 inductive types or structures, 15 instances and 308 theorems. The definitions and types are `OAI.CriticalStrip.CrossTopArch`, `OAI.CriticalStrip.CrossTopArch.Bounded`, `OAI.CriticalStrip.CrossTopArch.Fits`, `OAI.CriticalStrip.Diagram.BareColumn`, `OAI.CriticalStrip.Diagram.Circuit`, `OAI.CriticalStrip.Diagram.Circuit.Compatible`, `OAI.CriticalStrip.Diagram.Circuit.Vertex`, `OAI.CriticalStrip.Diagram.Circuit.boundary`, `OAI.CriticalStrip.Diagram.Circuit.eval`, `OAI.CriticalStrip.Diagram.Circuit.support`, `OAI.CriticalStrip.Diagram.Circuit.wiring`, `OAI.CriticalStrip.Diagram.ColumnChain.Compatible`, `OAI.CriticalStrip.Diagram.ColumnChain.LocallyCompatible`, `OAI.CriticalStrip.Diagram.ColumnChain.Runs`, `OAI.CriticalStrip.Diagram.ColumnChain.Vertices`, `OAI.CriticalStrip.Diagram.ColumnChain.boundary`, `OAI.CriticalStrip.Diagram.ColumnChain.support`, `OAI.CriticalStrip.Diagram.ColumnChain.weight`, `OAI.CriticalStrip.Diagram.ColumnChain.wiring`, `OAI.CriticalStrip.Diagram.ColumnCompatible`, `OAI.CriticalStrip.Diagram.ColumnSew.equivalence`, `OAI.CriticalStrip.Diagram.ColumnSew.graph`, `OAI.CriticalStrip.Diagram.ColumnSew.project`, `OAI.CriticalStrip.Diagram.CompactGate.contraction`, `OAI.CriticalStrip.Diagram.CompactGate.full`, `OAI.CriticalStrip.Diagram.CompactGate.wiring`, `OAI.CriticalStrip.Diagram.CutPatch.Adj`, `OAI.CriticalStrip.Diagram.CutPatch.BadChecks`, `OAI.CriticalStrip.Diagram.CutPatch.Compatible`, `OAI.CriticalStrip.Diagram.CutPatch.ForestConditions`, `OAI.CriticalStrip.Diagram.CutPatch.GoodChecks`, `OAI.CriticalStrip.Diagram.CutPatch.ProfileChecks`, `OAI.CriticalStrip.Diagram.CutPatch.Realizes`, `OAI.CriticalStrip.Diagram.CutPatch.active`, `OAI.CriticalStrip.Diagram.CutPatch.forest`, `OAI.CriticalStrip.Diagram.CutPatch.inputEdges`, `OAI.CriticalStrip.Diagram.CutPatch.inputOccupied`, `OAI.CriticalStrip.Diagram.CutPatch.parentTable`, `OAI.CriticalStrip.Diagram.CutPatch.profile`, `OAI.CriticalStrip.Diagram.CutPatch.rankTable` and 91 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_AugmentedColumn`, `StripMass_AugmentedTail`, `StripMass_BottomGauge`, `StripMass_ColumnSew`, `StripMass_ColumnSweep`, `StripMass_CutPatch`, `StripMass_CutStateSound`, `StripMass_DiagonalFactors`, `StripMass_FreshGate`, `StripMass_HalfTurn`, `StripMass_HoneycombClip`, `StripMass_HoneycombDictionary`, `StripMass_HoneycombTiles`, `StripMass_NodalScalarDeletion`, `StripMass_NorthBijection`, `StripMass_NorthMerging`, `StripMass_PairingDiagrams`, `StripMass_PairingSurgery`, `StripMass_PfaffianSupport`, `StripMass_PhaseAlgebra`, `StripMass_ProjectionInjection`, `StripMass_RestrictedDiagrams`, `StripMass_ReversedConvergence`, `StripMass_ScalarFlat`, `StripMass_SewnAssignment`, `StripMass_SpecializationPolynomial`, `StripMass_SplitGluing`, `StripMass_SplitProjection`, `StripMass_StepComplete`, `StripMass_StepToCut`, `StripMass_TopPadding`, `StripMass_VacuumClosure`, `StripMass_VacuumDegree`, `StripMass_WireContraction`.
--
--   **Imports.** It imports the published bundle `Def_CriticalStripMass`; the bundles `OAIQ042S000` and `OAIQ042S001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S005`, `OAIQ042S006`, `OAIQ042S007`, `OAIQ042S008` and `OAIQ042S009`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_CriticalStripMass
import Definitions.Def_OAIQ042S000
import Definitions.Def_OAIQ042S001

section
-- module Solutions.OAIQ042_SS.StripMass_PairingDiagrams
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset



structure Realizes {n : ℕ} (p q : Pairing n) (t : Configuration n) : Prop where
  west : ∀ i, (t i).Occupied 1 ↔ p.Occupied i
  east : ∀ i, (t i).Occupied 2 ↔ q.Occupied i
  south : ∀ i, i.val = 0 → ¬ (t i).Occupied 0
  north : ∀ i, i.val + 1 = n → ¬ (t i).Occupied 3
  glued : ∀ i j, i.val + 1 = j.val → ((t i).Occupied 3 ↔ (t j).Occupied 0)
  no_loop : ∀ v w, Wiring p t v w → ∃ j, q.Occupied j ∧ Reach p t v (j,2)
  output : ∀ i j, i ≠ j → (q.Adj i j ↔ Reach p t (i,2) (j,2))

 

def column {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} (w : Fin n → Weights 𝕜) :
    Matrix (Pairing n) (Pairing n) 𝕜 := by
  classical
  exact fun q p => ∑ t : Configuration n,
    if Realizes p q t then ∏ i, (w i).tile (t i) else 0


def L (u : ℝ) : ℝ := Real.sin (2 * lambda + u) * Real.sin (3 * lambda + u)
def physicalWeights (u : ℝ) : Weights ℝ :=
  let d := Real.cos (2 * lambda)
  ⟨d * Real.sin (3 * lambda - u) / L u,
   Real.sin u * Real.sin (3 * lambda - u) / L u,
   d * Real.sin u / L u,
   Real.sin (3 * lambda - u) * Real.sin (2 * lambda - u) / L u,
   Real.sin (u - lambda) * Real.sin u / L u⟩

def restrictedColumn {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} (w : Fin n → Weights 𝕜) :
    Matrix (NonemptyPairing n) (NonemptyPairing n) 𝕜 :=
  (column w).submatrix Subtype.val Subtype.val



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairingSurgery
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.tileAdjDecidable _root_.OAI.CriticalStrip.Diagram.tileOccupiedDecidable
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

theorem capRemove_vacant {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val)
    (ha : p.Occupied a) (hb : p.Occupied b) (hn : ¬ p.Adj a b) :
    ¬ (capRemove p a b hab ha hb hn).Occupied a ∧
    ¬ (capRemove p a b hab ha hb hn).Occupied b := by
  have h := adjacent_partners hab (p.partner_adj a ha) (p.partner_adj b hb) hn
  simp only [capRemove,capSplice_occupied,omitTwo_not_occupied_left,
    omitTwo_not_occupied_right,or_false,not_or]
  exact ⟨⟨h.1.symm,h.2.2.1.symm⟩,⟨h.2.1.symm,h.2.2.2.1.symm⟩⟩

 

def tileStep {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val) :
    Tile → Option (Pairing n)
  | .vacant => if ¬ p.Occupied a ∧ ¬ p.Occupied b then some p else none
  | .vertical₀ => if p.Occupied a ∧ ¬ p.Occupied b then some p else none
  | .vertical₁ => if ¬ p.Occupied a ∧ p.Occupied b then some p else none
  | .diagonal₀ => if h : p.Occupied a ∧ ¬ p.Occupied b then
      some (p.moveIntoVacancy a b hab h.2) else none
  | .diagonal₁ => if h : ¬ p.Occupied a ∧ p.Occupied b then
      some (p.moveIntoLowerVacancy a b hab h.1) else none
  | .cap => if ha : p.Occupied a then if hb : p.Occupied b then
      if hn : p.Adj a b then none else some (p.capRemove a b hab ha hb hn)
      else none else none
  | .cup => if h : ¬ p.Occupied a ∧ ¬ p.Occupied b then
      some (p.insertCup a b hab h.1 h.2) else none
  | .verticalPair => if p.Occupied a ∧ p.Occupied b then some p else none
  | .capCup => if ha : p.Occupied a then if hb : p.Occupied b then
      if hn : p.Adj a b then none else
        some ((p.capRemove a b hab ha hb hn).insertCup a b hab
          (capRemove_vacant p a b hab ha hb hn).1
          (capRemove_vacant p a b hab ha hb hn).2)
      else none else none

end Pairing
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

def injectionColumn {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) : NonemptyPairing n → 𝕜 := fun p => column w p.val (empty n)

 
def normalizedVacuum {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) : Pairing n → 𝕜 :=
  attachEmpty ((1-restrictedColumn w)⁻¹.mulVec (injectionColumn w))

end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RestrictedDiagrams
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.spectralFieldCharZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section

def scalarNormalization {𝕜 : Type*} [Field 𝕜] {n : ℕ} (dd rr : 𝕜) (a : Fin n → 𝕜) : 𝕜 :=
  (∏ i, ∏ j ∈ Finset.Ioi i, discriminant dd (a i) (a j) / (a i-a j)) *
    pfaffian (augmentedKernel dd rr a)

def spectralNormalization (n : ℕ) : SpectralField n :=
  scalarNormalization (constF n d) (constF n rho) spectralA


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



theorem upperPair_eq_iff {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    upperPair a b hab = upperPair c d hcd ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold upperPair
  split_ifs <;> simp only [Subtype.mk.injEq, Prod.mk.injEq] <;> omega

theorem permutationPair_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permutationPair σ) := by
  intro i j h
  rcases (upperPair_eq_iff _ _).mp h with h | h
  · have h₁ := σ.injective h.1
    have hv := congrArg Fin.val h₁
    apply Fin.ext
    simp only [pairFirst] at hv
    omega
  · exact False.elim (pairFirst_ne_pairSecond i j (σ.injective h.1))


 

 


theorem upperPair_value {R : Type*} {n : ℕ}
    (D : Fin n → Fin n → R) (hD : ∀ i j, D i j = D j i)
    (i j : Fin n) (h : i ≠ j) :
    D (upperPair i j h).val.1 (upperPair i j h).val.2 = D i j := by
  unfold upperPair
  split_ifs <;> simp [hD]


theorem prod_selectedPairs {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin n → Fin n → R) (hD : ∀ i j, D i j = D j i)
    (σ : Equiv.Perm (Fin n)) :
    (∏ e ∈ selectedPairs σ, D e.val.1 e.val.2) =
      ∏ i : Fin (n/2), D (σ (pairFirst n i)) (σ (pairSecond n i)) := by
  rw [selectedPairs, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i _
    exact upperPair_value D hD _ _ _
  · exact fun i _ j _ h => permutationPair_injective σ h

theorem clearedPfaffianTerm_mul_denominator {R : Type*} [CommRing R] {n : ℕ}
    (N D : Matrix (Fin n) (Fin n) R) (hD : ∀ i j, D i j = D j i)
    (σ : Equiv.Perm (Fin n)) :
    clearedPfaffianTerm N D σ *
        (∏ i : Fin (n/2), D (σ (pairFirst n i)) (σ (pairSecond n i))) =
      (∏ i : Fin (n/2), N (σ (pairFirst n i)) (σ (pairSecond n i))) *
        ∏ e : UpperPair n, D e.val.1 e.val.2 := by
  rw [clearedPfaffianTerm, mul_assoc, ← prod_selectedPairs D hD σ,
    Finset.prod_compl_mul_prod]

theorem clear_pfaffian {K : Type*} [Field K] {n : ℕ}
    (N D : Matrix (Fin n) (Fin n) K) (hD : ∀ i j, D i j = D j i)
    (hne : ∀ i j, i ≠ j → D i j ≠ 0) :
    (∏ e : UpperPair n, D e.val.1 e.val.2) *
        pfaffian (fun i j => N i j / D i j) =
      clearedPfaffian (2^(n/2) * (Nat.factorial (n/2) : K))⁻¹ N D := by
  classical
  unfold pfaffian clearedPfaffian
  rw [mul_left_comm, mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_left_comm]
  congr 1
  rw [Finset.prod_div_distrib]
  have hd : (∏ i : Fin (n/2), D (σ (pairFirst n i)) (σ (pairSecond n i))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact hne _ _ (σ.injective.ne (pairFirst_ne_pairSecond i i))
  rw [← mul_div_assoc, div_eq_iff hd]
  rw [clearedPfaffianTerm_mul_denominator N D hD σ]
  ring

theorem upperPairMap_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (upperPairMap σ) := by
  intro e f h
  rcases (upperPair_eq_iff _ _).mp h with h | h
  · apply Subtype.ext
    exact Prod.ext (σ.injective h.1) (σ.injective h.2)
  · have h₁ := σ.injective h.1
    have h₂ := σ.injective h.2
    have hef := e.property
    rw [h₁, h₂] at hef
    exact False.elim (lt_asymm hef f.property)

def upperPairPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (UpperPair n) :=
  Equiv.ofBijective (upperPairMap σ)
    ⟨upperPairMap_injective σ, Finite.surjective_of_injective (upperPairMap_injective σ)⟩

 
theorem prod_upperPair_reindex {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin n → Fin n → R) (hD : ∀ i j, D i j = D j i) (σ : Equiv.Perm (Fin n)) :
    (∏ e : UpperPair n, D (σ e.val.1) (σ e.val.2)) =
      ∏ e : UpperPair n, D e.val.1 e.val.2 := by
  refine Fintype.prod_equiv (upperPairPerm σ) _ _ ?_
  intro e
  exact (upperPair_value D hD _ _ (σ.injective.ne (ne_of_lt e.property))).symm







theorem scalarNumerator_eval {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (a : Fin n → K)
    (hD : ∀ i j, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0) :
    MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) =
      (∏ e : UpperPair (n+n%2), augmentedDenominator (f dd) a e.val.1 e.val.2) *
        pfaffian (augmentedKernel (f dd) (f rr) a) := by
  rw [scalarNumerator, map_clearedPfaffian, map_augmentedNumerator, map_augmentedDenominator]
  simp only [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    map_inv₀, map_mul, map_pow, map_ofNat, map_natCast]
  have hn : ∀ i j, i ≠ j → augmentedDenominator (f dd) a i j ≠ 0 := by
    intro i j hij
    unfold augmentedDenominator
    split_ifs with hi hj <;> try exact one_ne_zero
    apply hD
    intro h
    exact hij (Fin.ext (congrArg (fun k : Fin n => k.val) h))
  rw [← clear_pfaffian _ _ (augmentedDenominator_symm _ _) hn]
  congr 2
  ext i j
  exact (augmentedKernel_eq _ _ _ i j).symm



theorem scalarNumerator_eval_reindex {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (a : Fin n → K)
    (hD : ∀ i j, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.eval₂Hom f (a ∘ σ) (scalarNumerator n dd rr) =
      (Equiv.Perm.sign σ : ℤ) * MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) := by
  have hDσ : ∀ i j, i ≠ j → discriminant (f dd) ((a ∘ σ) i) ((a ∘ σ) j) ≠ 0 := by
    intro i j hij
    exact hD _ _ (σ.injective.ne hij)
  rw [scalarNumerator_eval f n dd rr _ hDσ, scalarNumerator_eval f n dd rr _ hD,
    augmentedDenominator_reindex, augmentedKernel_reindex,
    prod_upperPair_reindex _ (augmentedDenominator_symm _ _), pfaffian_reindex,
    augmentedPerm_sign]
  ring



theorem scalarNumerator_rename {n : ℕ} (dd rr : ℂ) (hdd : dd ≠ 0)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.rename σ (scalarNumerator n dd rr) =
      (Equiv.Perm.sign σ : ℤ) * scalarNumerator n dd rr := by
  apply IsFractionRing.injective (CosineRing n) (CosineField n)
  rw [← eval₂_cosineCoeff, MvPolynomial.eval₂Hom_rename, map_mul, map_intCast]
  exact scalarNumerator_eval_reindex (cosineCoeff n) n dd rr cosineVar
    (fun i j _ => discriminant_cosineVar_ne dd hdd i j) σ

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



theorem scalarNumerator_vandermonde_dvd (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) :
    (∏ e : UpperPair n, (MvPolynomial.X e.val.1 - MvPolynomial.X e.val.2 : CosineRing n)) ∣
      scalarNumerator n dd rr := by
  let : UniqueFactorizationMonoid (CosineRing n) := MvPolynomial.uniqueFactorizationMonoid (Fin n)
  let : DecompositionMonoid (CosineRing n) := UniqueFactorizationMonoid.instDecompositionMonoid
  apply Fintype.prod_dvd_of_isRelPrime
    (s := fun e : UpperPair n => (MvPolynomial.X e.val.1 - MvPolynomial.X e.val.2 : CosineRing n))
    (fun e f hef => cosine_differences_relPrime e f hef)
  intro e
  apply cosine_difference_dvd_of_swap _ _ _ (ne_of_lt e.property)
  rw [scalarNumerator_rename dd rr hdd, Equiv.Perm.sign_swap (ne_of_lt e.property)]
  simp








def scalarPolynomial (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) : CosineRing n :=
  Classical.choose (scalarNumerator_vandermonde_dvd n dd rr hdd)

end

 

 

noncomputable section
open Finset
open scoped Classical

lemma map_pfaffian {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (M : Matrix (Fin n) (Fin n) K) :
    f (pfaffian M)=pfaffian (M.map f) := by
  simp only [pfaffian,map_mul,map_inv₀,map_pow,map_ofNat,map_natCast,map_sum,
    map_intCast,map_prod,Matrix.map_apply]

lemma map_augmentedKernel {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (dd rr : K) (a : Fin n → K) :
    (augmentedKernel dd rr a).map f=augmentedKernel (f dd) (f rr) (fun i => f (a i)) := by
  ext i j
  change f (augmentedKernel dd rr a i j)=_
  unfold augmentedKernel
  split_ifs <;> simp [discriminant,map_div₀,map_pow,map_ofNat]

lemma map_scalarNormalization {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (dd rr : K) (a : Fin n → K) :
    f (scalarNormalization dd rr a)=scalarNormalization (f dd) (f rr) (fun i => f (a i)) := by
  simp only [scalarNormalization,map_mul,map_pfaffian,map_augmentedKernel,map_prod,
    map_div₀,discriminant,map_sub,map_add,map_pow,map_ofNat]

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

instance instFintypeShape : Fintype Shape := ⟨{.vacant,.single₀,.single₁,.paired,.separate}, by intro s; cases s <;> simp⟩

def inputEdges : Shape → Finset (Fin 6 × Fin 6)
  | .vacant => ∅
  | .single₀ => {(0,4)}
  | .single₁ => {(1,5)}
  | .paired => {(0,1)}
  | .separate => {(0,4),(1,5)}

def Adj (a : Shape) (t : Tile) (v w : Fin 6) : Prop :=
  (v,w) ∈ inputEdges a ∨ (w,v) ∈ inputEdges a ∨
    ∃ i j : Fin 4, t.Adj i j ∧ v = tilePort i ∧ w = tilePort j

instance instDecidableRelFinOfNatNatAdj (a : Shape) (t : Tile) : DecidableRel (Adj a t) := fun _ _ => by
  unfold Adj; infer_instance

def inputOccupied (a : Shape) (i : Fin 2) : Prop :=
  ∃ j, (tilePort (Fin.castLE (by decide) i),j) ∈ inputEdges a ∨
    (j,tilePort (Fin.castLE (by decide) i)) ∈ inputEdges a

instance instDecidableInputOccupied (a : Shape) (i : Fin 2) : Decidable (inputOccupied a i) := by
  unfold inputOccupied; infer_instance

def Compatible (a : Shape) (t : Tile) : Prop :=
  ∀ i : Fin 2, inputOccupied a i ↔ t.Occupied (Fin.castLE (by decide) i)

instance instDecidableCompatible (a : Shape) (t : Tile) : Decidable (Compatible a t) := by
  unfold Compatible; infer_instance

def active (a : Shape) (t : Tile) (i : Fin 4) : Prop :=
  ∃ w, Adj a t (boundary i) w

instance instDecidableActive (a : Shape) (t : Tile) (i : Fin 4) : Decidable (active a t i) := by
  unfold active; infer_instance

def profile : Shape → Tile → Option (Finset (Fin 4 × Fin 4))
  | .vacant, .vacant => some ∅
  | .vacant, .cup => some {(0,1)}
  | .single₀, .vertical₀ => some {(0,2)}
  | .single₀, .diagonal₀ => some {(1,2)}
  | .single₁, .vertical₁ => some {(1,3)}
  | .single₁, .diagonal₁ => some {(0,3)}
  | .paired, .verticalPair => some {(0,1)}
  | .separate, .cap => some {(2,3)}
  | .separate, .verticalPair => some {(0,2),(1,3)}
  | .separate, .capCup => some {(0,1),(2,3)}
  | _,_ => none

def rootTable : Shape → Tile → Fin 6 → Fin 6
  | .vacant, .vacant => ![0,1,2,3,4,5]
  | .vacant, .vertical₀ => ![0,1,0,3,4,5]
  | .vacant, .vertical₁ => ![0,1,2,1,4,5]
  | .vacant, .diagonal₀ => ![0,1,2,0,4,5]
  | .vacant, .diagonal₁ => ![0,1,1,3,4,5]
  | .vacant, .cap => ![0,0,2,3,4,5]
  | .vacant, .cup => ![0,1,2,2,4,5]
  | .vacant, .verticalPair => ![0,1,0,1,4,5]
  | .vacant, .capCup => ![0,0,2,2,4,5]
  | .single₀, .vacant => ![0,1,2,3,0,5]
  | .single₀, .vertical₀ => ![0,1,0,3,0,5]
  | .single₀, .vertical₁ => ![0,1,2,1,0,5]
  | .single₀, .diagonal₀ => ![0,1,2,0,0,5]
  | .single₀, .diagonal₁ => ![0,1,1,3,0,5]
  | .single₀, .cap => ![0,0,2,3,0,5]
  | .single₀, .cup => ![0,1,2,2,0,5]
  | .single₀, .verticalPair => ![0,1,0,1,0,5]
  | .single₀, .capCup => ![0,0,2,2,0,5]
  | .single₁, .vacant => ![0,1,2,3,4,1]
  | .single₁, .vertical₀ => ![0,1,0,3,4,1]
  | .single₁, .vertical₁ => ![0,1,2,1,4,1]
  | .single₁, .diagonal₀ => ![0,1,2,0,4,1]
  | .single₁, .diagonal₁ => ![0,1,1,3,4,1]
  | .single₁, .cap => ![0,0,2,3,4,0]
  | .single₁, .cup => ![0,1,2,2,4,1]
  | .single₁, .verticalPair => ![0,1,0,1,4,1]
  | .single₁, .capCup => ![0,0,2,2,4,0]
  | .paired, .vacant => ![0,0,2,3,4,5]
  | .paired, .vertical₀ => ![0,0,0,3,4,5]
  | .paired, .vertical₁ => ![0,0,2,0,4,5]
  | .paired, .diagonal₀ => ![0,0,2,0,4,5]
  | .paired, .diagonal₁ => ![0,0,0,3,4,5]
  | .paired, .cap => ![0,0,2,3,4,5]
  | .paired, .cup => ![0,0,2,2,4,5]
  | .paired, .verticalPair => ![0,0,0,0,4,5]
  | .paired, .capCup => ![0,0,2,2,4,5]
  | .separate, .vacant => ![0,1,2,3,0,1]
  | .separate, .vertical₀ => ![0,1,0,3,0,1]
  | .separate, .vertical₁ => ![0,1,2,1,0,1]
  | .separate, .diagonal₀ => ![0,1,2,0,0,1]
  | .separate, .diagonal₁ => ![0,1,1,3,0,1]
  | .separate, .cap => ![0,0,2,3,0,0]
  | .separate, .cup => ![0,1,2,2,0,1]
  | .separate, .verticalPair => ![0,1,0,1,0,1]
  | .separate, .capCup => ![0,0,2,2,0,0]

def parentTable : Shape → Tile → Fin 6 → Fin 6
  | .vacant, .vacant => ![0,1,2,3,4,5]
  | .vacant, .vertical₀ => ![0,1,0,3,4,5]
  | .vacant, .vertical₁ => ![0,1,2,1,4,5]
  | .vacant, .diagonal₀ => ![0,1,2,0,4,5]
  | .vacant, .diagonal₁ => ![0,1,1,3,4,5]
  | .vacant, .cap => ![0,0,2,3,4,5]
  | .vacant, .cup => ![0,1,2,2,4,5]
  | .vacant, .verticalPair => ![0,1,0,1,4,5]
  | .vacant, .capCup => ![0,0,2,2,4,5]
  | .single₀, .vacant => ![0,1,2,3,0,5]
  | .single₀, .vertical₀ => ![0,1,0,3,0,5]
  | .single₀, .vertical₁ => ![0,1,2,1,0,5]
  | .single₀, .diagonal₀ => ![0,1,2,0,0,5]
  | .single₀, .diagonal₁ => ![0,1,1,3,0,5]
  | .single₀, .cap => ![0,0,2,3,0,5]
  | .single₀, .cup => ![0,1,2,2,0,5]
  | .single₀, .verticalPair => ![0,1,0,1,0,5]
  | .single₀, .capCup => ![0,0,2,2,0,5]
  | .single₁, .vacant => ![0,1,2,3,4,1]
  | .single₁, .vertical₀ => ![0,1,0,3,4,1]
  | .single₁, .vertical₁ => ![0,1,2,1,4,1]
  | .single₁, .diagonal₀ => ![0,1,2,0,4,1]
  | .single₁, .diagonal₁ => ![0,1,1,3,4,1]
  | .single₁, .cap => ![0,0,2,3,4,1]
  | .single₁, .cup => ![0,1,2,2,4,1]
  | .single₁, .verticalPair => ![0,1,0,1,4,1]
  | .single₁, .capCup => ![0,0,2,2,4,1]
  | .paired, .vacant => ![0,0,2,3,4,5]
  | .paired, .vertical₀ => ![0,0,0,3,4,5]
  | .paired, .vertical₁ => ![0,0,2,1,4,5]
  | .paired, .diagonal₀ => ![0,0,2,0,4,5]
  | .paired, .diagonal₁ => ![0,0,1,3,4,5]
  | .paired, .cap => ![0,0,2,3,4,5]
  | .paired, .cup => ![0,0,2,2,4,5]
  | .paired, .verticalPair => ![0,0,0,1,4,5]
  | .paired, .capCup => ![0,0,2,2,4,5]
  | .separate, .vacant => ![0,1,2,3,0,1]
  | .separate, .vertical₀ => ![0,1,0,3,0,1]
  | .separate, .vertical₁ => ![0,1,2,1,0,1]
  | .separate, .diagonal₀ => ![0,1,2,0,0,1]
  | .separate, .diagonal₁ => ![0,1,1,3,0,1]
  | .separate, .cap => ![0,0,2,3,0,1]
  | .separate, .cup => ![0,1,2,2,0,1]
  | .separate, .verticalPair => ![0,1,0,1,0,1]
  | .separate, .capCup => ![0,0,2,2,0,1]

def rankTable : Shape → Tile → Fin 6 → ℕ
  | .vacant, .vacant => ![0,0,0,0,0,0]
  | .vacant, .vertical₀ => ![0,0,1,0,0,0]
  | .vacant, .vertical₁ => ![0,0,0,1,0,0]
  | .vacant, .diagonal₀ => ![0,0,0,1,0,0]
  | .vacant, .diagonal₁ => ![0,0,1,0,0,0]
  | .vacant, .cap => ![0,1,0,0,0,0]
  | .vacant, .cup => ![0,0,0,1,0,0]
  | .vacant, .verticalPair => ![0,0,1,1,0,0]
  | .vacant, .capCup => ![0,1,0,1,0,0]
  | .single₀, .vacant => ![0,0,0,0,1,0]
  | .single₀, .vertical₀ => ![0,0,1,0,1,0]
  | .single₀, .vertical₁ => ![0,0,0,1,1,0]
  | .single₀, .diagonal₀ => ![0,0,0,1,1,0]
  | .single₀, .diagonal₁ => ![0,0,1,0,1,0]
  | .single₀, .cap => ![0,1,0,0,1,0]
  | .single₀, .cup => ![0,0,0,1,1,0]
  | .single₀, .verticalPair => ![0,0,1,1,1,0]
  | .single₀, .capCup => ![0,1,0,1,1,0]
  | .single₁, .vacant => ![0,0,0,0,0,1]
  | .single₁, .vertical₀ => ![0,0,1,0,0,1]
  | .single₁, .vertical₁ => ![0,0,0,1,0,1]
  | .single₁, .diagonal₀ => ![0,0,0,1,0,1]
  | .single₁, .diagonal₁ => ![0,0,1,0,0,1]
  | .single₁, .cap => ![0,1,0,0,0,2]
  | .single₁, .cup => ![0,0,0,1,0,1]
  | .single₁, .verticalPair => ![0,0,1,1,0,1]
  | .single₁, .capCup => ![0,1,0,1,0,2]
  | .paired, .vacant => ![0,1,0,0,0,0]
  | .paired, .vertical₀ => ![0,1,1,0,0,0]
  | .paired, .vertical₁ => ![0,1,0,2,0,0]
  | .paired, .diagonal₀ => ![0,1,0,1,0,0]
  | .paired, .diagonal₁ => ![0,1,2,0,0,0]
  | .paired, .cap => ![0,1,0,0,0,0]
  | .paired, .cup => ![0,1,0,1,0,0]
  | .paired, .verticalPair => ![0,1,1,2,0,0]
  | .paired, .capCup => ![0,1,0,1,0,0]
  | .separate, .vacant => ![0,0,0,0,1,1]
  | .separate, .vertical₀ => ![0,0,1,0,1,1]
  | .separate, .vertical₁ => ![0,0,0,1,1,1]
  | .separate, .diagonal₀ => ![0,0,0,1,1,1]
  | .separate, .diagonal₁ => ![0,0,1,0,1,1]
  | .separate, .cap => ![0,1,0,0,1,2]
  | .separate, .cup => ![0,0,0,1,1,1]
  | .separate, .verticalPair => ![0,0,1,1,1,1]
  | .separate, .capCup => ![0,1,0,1,1,2]

def ForestConditions (a : Shape) (t : Tile) : Prop :=
  (∀ v w, Adj a t v w → rootTable a t v = rootTable a t w) ∧
  (∀ v, v ≠ rootTable a t v → Adj a t v (parentTable a t v)) ∧
  (∀ v, v ≠ rootTable a t v → rankTable a t (parentTable a t v) < rankTable a t v)

instance instDecidableForestConditions (a : Shape) (t : Tile) : Decidable (ForestConditions a t) := by
  unfold ForestConditions; infer_instance

theorem forestConditions (a : Shape) (t : Tile) : ForestConditions a t := by
  cases a <;> cases t <;> decide

def forest (a : Shape) (t : Tile) : ConnectivityCertificate (Adj a t) where
  root := rootTable a t
  parent := parentTable a t
  rank := rankTable a t
  edge_root := (forestConditions a t).1
  parent_edge := (forestConditions a t).2.1
  parent_rank := (forestConditions a t).2.2

theorem adj_symmetric (a : Shape) (t : Tile) : Std.Symm (Adj a t) := by
  constructor
  intro v w h
  rcases h with h | h | ⟨i,j,h,rfl,rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨j,i,h.symm,rfl,rfl⟩)

theorem reach_iff (a : Shape) (t : Tile) (v w : Fin 6) :
    Relation.ReflTransGen (Adj a t) v w ↔ rootTable a t v = rootTable a t w :=
  (forest a t).reach_iff (adj_symmetric a t) v w

def GoodChecks (a : Shape) (t : Tile) (d : Finset (Fin 4 × Fin 4)) : Prop :=
  Compatible a t ∧ (∀ i, active a t i ↔ boundarySupport d i) ∧
  (∀ v w, Adj a t v w → ∃ i, active a t i ∧ rootTable a t v = rootTable a t (boundary i)) ∧
  (∀ i j, i ≠ j → (boundaryAdj d i j ↔ rootTable a t (boundary i) = rootTable a t (boundary j)))

def BadChecks (a : Shape) (t : Tile) : Prop :=
  ¬ Compatible a t ∨ ∃ v w, Adj a t v w ∧
    ∀ i, active a t i → rootTable a t v ≠ rootTable a t (boundary i)

instance instDecidableGoodChecks (a : Shape) (t : Tile) (d : Finset (Fin 4 × Fin 4)) : Decidable (GoodChecks a t d) := by
  unfold GoodChecks; infer_instance
instance instDecidableBadChecks (a : Shape) (t : Tile) : Decidable (BadChecks a t) := by
  unfold BadChecks; infer_instance

def ProfileChecks (a : Shape) (t : Tile) : Prop :=
  match profile a t with
  | some d => GoodChecks a t d
  | none => BadChecks a t

instance instDecidableProfileChecks (a : Shape) (t : Tile) : Decidable (ProfileChecks a t) := by
  unfold ProfileChecks; split <;> infer_instance

theorem profileChecks (a : Shape) (t : Tile) : ProfileChecks a t := by
  cases a <;> cases t <;> decide

structure Realizes (a : Shape) (t : Tile) (d : Finset (Fin 4 × Fin 4)) : Prop where
  compatible : Compatible a t
  occupied : ∀ i, active a t i ↔ boundarySupport d i
  no_loop : ∀ v w, Adj a t v w → ∃ i, active a t i ∧ Relation.ReflTransGen (Adj a t) v (boundary i)
  output : ∀ i j, i ≠ j → (boundaryAdj d i j ↔ Relation.ReflTransGen (Adj a t) (boundary i) (boundary j))

theorem realizes_of_profile {a : Shape} {t : Tile} {d : Finset (Fin 4 × Fin 4)}
    (h : profile a t = some d) : Realizes a t d := by
  have hp := profileChecks a t
  simp only [ProfileChecks,h] at hp
  exact ⟨hp.1,hp.2.1,fun v w hvw => by
    obtain ⟨i,hi,he⟩ := hp.2.2.1 v w hvw
    exact ⟨i,hi,(reach_iff a t v (boundary i)).mpr he⟩,
    fun i j hij => (hp.2.2.2 i j hij).trans (reach_iff a t _ _).symm⟩

theorem none_has_closed {a : Shape} {t : Tile} (h : profile a t = none)
    (hc : Compatible a t) :
    ∃ v w, Adj a t v w ∧ ∀ i, active a t i → ¬ Relation.ReflTransGen (Adj a t) v (boundary i) := by
  have hp := profileChecks a t
  simp only [ProfileChecks,h] at hp
  rcases hp with hp | ⟨v,w,hvw,hout⟩
  · exact (hp hc).elim
  · exact ⟨v,w,hvw,fun i hi hh => hout i hi ((reach_iff a t _ _).mp hh)⟩

end
end CriticalStrip.Diagram.CutPatch

 

 

namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical
namespace Pairing

theorem adj_omit_decomposition {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    p.Adj i j ↔ (p.omitTwo a b).Adj i j ∨
      (i=a ∧ p.Adj a j) ∨ (j=a ∧ p.Adj a i) ∨
      (i=b ∧ p.Adj b j) ∨ (j=b ∧ p.Adj b i) := by
  rw [omitTwo_adj]
  constructor
  · intro h
    by_cases hia : i=a
    · exact Or.inr (Or.inl ⟨hia,hia ▸ h⟩)
    by_cases hja : j=a
    · exact Or.inr (Or.inr (Or.inl ⟨hja,hja ▸ adj_symm h⟩))
    by_cases hib : i=b
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hib,hib ▸ h⟩)))
    by_cases hjb : j=b
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hjb,hjb ▸ adj_symm h⟩)))
    exact Or.inl ⟨h,hia,hib,hja,hjb⟩
  · rintro (⟨h,_⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩)
    · exact h
    · exact h
    · exact adj_symm h
    · exact h
    · exact adj_symm h


def cutLabels {n : ℕ} (p : Pairing n) (a b : Fin n) : Fin 4 → Fin n :=
  ![a,b,p.partnerOrSelf a,p.partnerOrSelf b]

theorem tileStep_none_iff {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) :
    p.tileStep a b hab t = none ↔ CutPatch.profile (p.cutShape a b) t = none := by
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;>
    by_cases hn : p.Adj a b <;> cases t <;> simp [tileStep,cutShape,ha,hb,hn,CutPatch.profile]


 

 


theorem adj_decompose_partners {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    p.Adj i j ↔ (p.omitTwo a b).Adj i j ∨
      (p.Occupied a ∧ ((i=a ∧ j=p.partnerOrSelf a) ∨ (j=a ∧ i=p.partnerOrSelf a))) ∨
      (p.Occupied b ∧ ((i=b ∧ j=p.partnerOrSelf b) ∨ (j=b ∧ i=p.partnerOrSelf b))) := by
  rw [adj_omit_decomposition]
  simp only [adj_partnerOrSelf]
  tauto

theorem omitTwo_swap_invariant {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    (p.omitTwo a b).Adj (Equiv.swap a b i) (Equiv.swap a b j) ↔
      (p.omitTwo a b).Adj i j := by
  by_cases hia : i=a <;> by_cases hib : i=b <;>
    by_cases hja : j=a <;> by_cases hjb : j=b <;>
    simp [Equiv.swap_apply_def,hia,hib,hja,hjb,omitTwo_adj]

theorem partnerOrSelf_ne {n : ℕ} (p : Pairing n) (a : Fin n) (ha : p.Occupied a) :
    p.partnerOrSelf a ≠ a := by
  intro he
  have hh := (adj_partnerOrSelf p a (p.partnerOrSelf a)).mpr ⟨ha,rfl⟩
  rw [he] at hh
  exact p.adj_irrefl a hh

theorem partnerOrSelf_ne_of_vacant {n : ℕ} (p : Pairing n) (a b : Fin n)
    (ha : p.Occupied a) (hb : ¬ p.Occupied b) : p.partnerOrSelf a ≠ b := by
  intro he
  have hh := (adj_partnerOrSelf p a (p.partnerOrSelf a)).mpr ⟨ha,rfl⟩
  rw [he] at hh
  exact hb ⟨a,adj_symm hh⟩

theorem swap_eq_partner_iff {n : ℕ} (p : Pairing n) (a b i : Fin n)
    (ha : p.Occupied a) (hb : ¬ p.Occupied b) :
    Equiv.swap a b i = p.partnerOrSelf a ↔ i = p.partnerOrSelf a := by
  have hx := p.partnerOrSelf_ne a ha
  have hy := p.partnerOrSelf_ne_of_vacant a b ha hb
  rw [← Equiv.eq_symm_apply]
  simp [Equiv.swap_apply_def,hx,hy]

theorem swap_eq_partner_iff_lower {n : ℕ} (p : Pairing n) (a b i : Fin n)
    (ha : ¬ p.Occupied a) (hb : p.Occupied b) :
    Equiv.swap a b i = p.partnerOrSelf b ↔ i = p.partnerOrSelf b := by
  rw [Equiv.swap_comm]
  exact swap_eq_partner_iff p b a i hb ha

 

def cutRelation {n : ℕ} (p : Pairing n) (a b : Fin n)
    (d : Finset (Fin 4 × Fin 4)) (i j : Fin n) : Prop :=
  (p.omitTwo a b).Adj i j ∨
    ∃ r s, CutPatch.boundaryAdj d r s ∧ p.cutLabels a b r = i ∧ p.cutLabels a b s = j

theorem cutRelation_empty {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    p.cutRelation a b ∅ i j ↔ (p.omitTwo a b).Adj i j := by
  simp [cutRelation,CutPatch.boundaryAdj]

theorem cutRelation_single {n : ℕ} (p : Pairing n) (a b i j : Fin n) (r s : Fin 4) :
    p.cutRelation a b {(r,s)} i j ↔ (p.omitTwo a b).Adj i j ∨
      (i=p.cutLabels a b r ∧ j=p.cutLabels a b s) ∨
      (i=p.cutLabels a b s ∧ j=p.cutLabels a b r) := by
  simp only [cutRelation,CutPatch.boundaryAdj,mem_singleton,Prod.mk.injEq]
  constructor
  · rintro (h|⟨x,y,(⟨rfl,rfl⟩|⟨rfl,rfl⟩),hi,hj⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hi.symm,hj.symm⟩)
    · exact Or.inr (Or.inr ⟨hi.symm,hj.symm⟩)
  · rintro (h|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r,s,Or.inl ⟨rfl,rfl⟩,rfl,rfl⟩
    · exact Or.inr ⟨s,r,Or.inr ⟨rfl,rfl⟩,rfl,rfl⟩

theorem cutRelation_union {n : ℕ} (p : Pairing n) (a b i j : Fin n)
    (d e : Finset (Fin 4 × Fin 4)) :
    p.cutRelation a b (d ∪ e) i j ↔
      p.cutRelation a b d i j ∨ p.cutRelation a b e i j := by
  simp only [cutRelation,CutPatch.boundaryAdj,mem_union]
  constructor
  · rintro (h|⟨x,y,h,hi,hj⟩)
    · exact Or.inl (Or.inl h)
    · rcases h with (h|h) | (h|h)
      · exact Or.inl (Or.inr ⟨x,y,Or.inl h,hi,hj⟩)
      · exact Or.inr (Or.inr ⟨x,y,Or.inl h,hi,hj⟩)
      · exact Or.inl (Or.inr ⟨x,y,Or.inr h,hi,hj⟩)
      · exact Or.inr (Or.inr ⟨x,y,Or.inr h,hi,hj⟩)
  · rintro ((h|⟨x,y,h,hi,hj⟩)|(h|⟨x,y,h,hi,hj⟩))
    · exact Or.inl h
    · exact Or.inr ⟨x,y,h.imp Or.inl Or.inl,hi,hj⟩
    · exact Or.inl h
    · exact Or.inr ⟨x,y,h.imp Or.inr Or.inr,hi,hj⟩

end Pairing
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CutStateSound
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Patch.glued_symm
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

theorem tileStep_sound_vacant {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : ¬ p.Occupied a) (hb : ¬ p.Occupied b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  cases t <;> simp [tileStep,cutShape,ha,hb,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [insertCup_adj,cutRelation_single,cutRelation_empty,cutLabels,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  all_goals simp only [ha,hb,false_and,or_false] at hp
  all_goals try { exact hp }
  all_goals itauto

theorem tileStep_sound_single₀ {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : p.Occupied a) (hb : ¬ p.Occupied b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  have hs := adj_decompose_partners p a b (Equiv.swap a b i) (Equiv.swap a b j)
  rw [omitTwo_swap_invariant] at hs
  cases t <;> simp [tileStep,cutShape,ha,hb,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [moveIntoVacancy_adj,cutRelation_single,cutLabels,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  all_goals simp only [ha,hb,false_and,true_and,or_false] at hp
  all_goals try { simpa only [ha,hb,true_and,false_and,or_false,false_or,Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left,Equiv.swap_apply_right,and_comm,swap_eq_partner_iff p a b i ha hb,
      swap_eq_partner_iff p a b j ha hb] using hs }
  all_goals itauto

theorem tileStep_sound_single₁ {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : ¬ p.Occupied a) (hb : p.Occupied b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  have hs := adj_decompose_partners p a b (Equiv.swap a b i) (Equiv.swap a b j)
  rw [omitTwo_swap_invariant] at hs
  cases t <;> simp [tileStep,cutShape,ha,hb,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [moveIntoLowerVacancy_adj,cutRelation_single,cutLabels,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  all_goals simp only [ha,hb,false_and,true_and,false_or] at hp
  all_goals try { simpa only [ha,hb,true_and,false_and,or_false,false_or,Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left,Equiv.swap_apply_right,and_comm,swap_eq_partner_iff_lower p a b i ha hb,
      swap_eq_partner_iff_lower p a b j ha hb] using hs }
  all_goals itauto

theorem tileStep_sound_paired {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : p.Occupied a) (hb : p.Occupied b) (hn : p.Adj a b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  have hpa : p.partnerOrSelf a = b := ((adj_partnerOrSelf p a b).mp hn).2.symm
  have hpb : p.partnerOrSelf b = a := ((adj_partnerOrSelf p b a).mp (adj_symm hn)).2.symm
  cases t <;> simp [tileStep,cutShape,ha,hb,hn,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [cutRelation_single,cutLabels,Matrix.cons_val_zero,Matrix.cons_val_one]
  all_goals simp only [ha,hb,hpa,hpb,true_and] at hp
  all_goals itauto

theorem tileStep_sound_separate {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : p.Occupied a) (hb : p.Occupied b) (hn : ¬ p.Adj a b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  cases t <;> simp [tileStep,cutShape,ha,hb,hn,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [insertCup_adj,capRemove_adj,Finset.insert_eq,cutRelation_union,
    cutRelation_single,cutLabels,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  all_goals simp only [ha,hb,true_and] at hp
  all_goals try { simp only [and_comm, or_assoc, or_left_comm, or_comm] }
  all_goals itauto

theorem tileStep_sound {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  by_cases ha : p.Occupied a
  · by_cases hb : p.Occupied b
    · by_cases hn : p.Adj a b
      · exact tileStep_sound_paired p a b hab t q d ha hb hn hq hd i j
      · exact tileStep_sound_separate p a b hab t q d ha hb hn hq hd i j
    · exact tileStep_sound_single₀ p a b hab t q d ha hb hq hd i j
  · by_cases hb : p.Occupied b
    · exact tileStep_sound_single₁ p a b hab t q d ha hb hq hd i j
    · exact tileStep_sound_vacant p a b hab t q d ha hb hq hd i j

end Pairing
end

 

 

noncomputable section
namespace Pairing

theorem adj_trans_eq {n : ℕ} {p : Pairing n} {i j k : Fin n}
    (h : p.Adj i j) (g : p.Adj j k) : i = k :=
  adj_unique (adj_symm h) g

theorem reach_adj_iff {n : ℕ} (p : Pairing n) (i j : Fin n) :
    Relation.ReflTransGen p.Adj i j ↔ i=j ∨ p.Adj i j := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail j k h hjk ih =>
      rcases ih with rfl | h
      · exact Or.inr hjk
      · exact Or.inl (adj_trans_eq h hjk)
  · rintro (rfl|h)
    · exact .refl
    · exact .single h

end Pairing

namespace Patch
variable {A I : Type*} {n : ℕ}
variable (r : A → A → Prop) (s : Fin n → Fin n → Prop)
  (a : I → A) (b : I → Fin n) (active : I → Prop)
  (d : I → I → Prop) (q : Pairing n)
variable (hd : ∀ i j, d i j → active i ∧ active j)
  (ha : ∀ i, active i → ∃ j, d i j)
  (hr : ∀ i j, Relation.ReflTransGen r (a i) (a j) ↔ i=j ∨ d i j)
  (hq : ∀ x y, q.Adj x y ↔ s x y ∨ ∃ i j, d i j ∧ b i=x ∧ b j=y)

include hd hr hq in
theorem pairing_adj_compressed {x y : Fin n} (h : q.Adj x y) :
    compressed r s a b active x y := by
  rcases (hq x y).mp h with hxy | ⟨i,j,hdi,rfl,rfl⟩
  · exact Or.inl hxy
  · exact Or.inr ⟨i,j,(hd i j hdi).1,(hd i j hdi).2,(hr i j).mpr (Or.inr hdi),rfl,rfl⟩

include ha hr hq in
theorem compressed_pairing {x y : Fin n} (h : compressed r s a b active x y) :
    (x=y ∨ q.Adj x y) ∧ q.Occupied x := by
  rcases h with h | ⟨i,j,hi,hj,h,rfl,rfl⟩
  · have h' := (hq x y).mpr (Or.inl h)
    exact ⟨Or.inr h',⟨y,h'⟩⟩
  · rcases (hr i j).mp h with rfl | h
    · obtain ⟨k,hk⟩ := ha i hi
      exact ⟨Or.inl rfl,⟨b k,(hq _ _).mpr (Or.inr ⟨i,k,hk,rfl,rfl⟩)⟩⟩
    · have h' := (hq _ _).mpr (Or.inr ⟨i,j,h,rfl,rfl⟩)
      exact ⟨Or.inr h',⟨b j,h'⟩⟩

include hd ha hr hq in
theorem compressed_reach_pairing (x y : Fin n) :
    Relation.ReflTransGen (compressed r s a b active) x y ↔ x=y ∨ q.Adj x y := by
  constructor
  · intro h
    apply (q.reach_adj_iff x y).mp
    induction h with
    | refl => exact .refl
    | @tail j k h hjk ih =>
      rcases (compressed_pairing r s a b active d q ha hr hq hjk).1 with rfl | h
      · exact ih
      · exact ih.tail h
  · rintro (rfl|h)
    · exact .refl
    · exact .single (pairing_adj_compressed r s a b active d q hd hr hq h)

include ha hr hq in
theorem compressed_drains_pairing : drains (compressed r s a b active) q.Occupied := by
  intro x y h
  exact ⟨x,(compressed_pairing r s a b active d q ha hr hq h).2,.refl⟩

include hd ha hr hq in
theorem glued_reach_pairing (x y : Fin n) :
    Relation.ReflTransGen (glued r s a b active) (.inr x) (.inr y) ↔ x=y ∨ q.Adj x y := by
  rw [exterior_reach_iff]
  exact compressed_reach_pairing r s a b active d q hd ha hr hq x y

include ha hr hq in
theorem glued_drains_pairing
    (hlocal : ∀ x y, r x y → ∃ i, active i ∧ Relation.ReflTransGen r x (a i)) :
    drains (glued r s a b active) (exteriorOutput q.Occupied) := by
  apply (drains_glued_iff r s a b active q.Occupied).mpr
  exact ⟨hlocal,compressed_drains_pairing r s a b active d q ha hr hq⟩

end Patch

 

 


 

structure GraphRealizes {V : Type*} {n : ℕ} (r : V → V → Prop)
    (boundary : Fin n → V) (p : Pairing n) : Prop where
  no_loop : ∀ v w, r v w → ∃ i, p.Occupied i ∧ Relation.ReflTransGen r v (boundary i)
  reach : ∀ i j, Relation.ReflTransGen r (boundary i) (boundary j) ↔ i=j ∨ p.Adj i j

namespace CutPatch

theorem Realizes.reach {s : Shape} {t : Tile} {d : Finset (Fin 4 × Fin 4)}
    (h : Realizes s t d) (i j : Fin 4) :
    Relation.ReflTransGen (Adj s t) (boundary i) (boundary j) ↔ i=j ∨ boundaryAdj d i j := by
  by_cases hij : i=j
  · subst j
    exact ⟨fun _ => Or.inl rfl,fun _ => .refl⟩
  · simp only [hij,false_or]
    exact (h.output i j hij).symm

theorem Realizes.edge_active {s : Shape} {t : Tile} {d : Finset (Fin 4 × Fin 4)}
    (h : Realizes s t d) (i j : Fin 4) (hd : boundaryAdj d i j) :
    active s t i ∧ active s t j := by
  exact ⟨(h.occupied i).mpr ⟨j,hd⟩,
    (h.occupied j).mpr ⟨i,hd.elim Or.inr Or.inl⟩⟩

end CutPatch

namespace Pairing

def cutGraph {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    Sum (Fin 6) (Fin n) → Sum (Fin 6) (Fin n) → Prop :=
  Patch.glued (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj
    CutPatch.boundary (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t)

theorem cutGraph_realizes {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (hq : p.tileStep a b hab t = some q) :
    GraphRealizes (p.cutGraph a b t) Sum.inr q := by
  have hne : CutPatch.profile (p.cutShape a b) t ≠ none := by
    intro hh
    have := (p.tileStep_none_iff a b hab t).mpr hh
    rw [hq] at this
    cases this
  obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp hne
  have hh := CutPatch.realizes_of_profile hd
  have ha : ∀ i, CutPatch.active (p.cutShape a b) t i → ∃ j, CutPatch.boundaryAdj d i j :=
    fun i hi => (hh.occupied i).mp hi
  have hq' : ∀ x y, q.Adj x y ↔ (p.omitTwo a b).Adj x y ∨
      ∃ i j, CutPatch.boundaryAdj d i j ∧ p.cutLabels a b i=x ∧ p.cutLabels a b j=y :=
    p.tileStep_sound a b hab t q d hq hd
  have hhloop := Patch.glued_drains_pairing
    (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj CutPatch.boundary
    (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t)
    (CutPatch.boundaryAdj d) q ha hh.reach hq' hh.no_loop
  constructor
  · intro v w hvw
    obtain ⟨z,hz,hr⟩ := hhloop v w hvw
    cases z with
    | inl z => exact hz.elim
    | inr z => exact ⟨z,hz,hr⟩
  · exact Patch.glued_reach_pairing
      (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj CutPatch.boundary
      (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t)
      (CutPatch.boundaryAdj d) q hh.edge_active ha hh.reach hq'

end Pairing

 

 


namespace Graph

namespace BoundaryEquiv
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
  {a : Fin n → V} {b : Fin n → W}

theorem realizes (e : BoundaryEquiv r s a b) {p : Pairing n}
    (h : GraphRealizes r a p) : GraphRealizes s b p := by
  constructor
  · intro v w hvw
    obtain ⟨x,hx⟩ := e.inv_used v ⟨w,hvw⟩
    obtain ⟨i,hi,hr⟩ := h.no_loop (e.invFun v) x hx
    refine ⟨i,hi,?_⟩
    have hmap := Graph.map_reach e.toFun e.map_edge hr
    rw [e.map_boundary] at hmap
    exact (e.inv_retract v ⟨w,hvw⟩).trans hmap
  · intro i j
    constructor
    · intro hh
      have hm := Graph.map_reach e.invFun e.inv_edge hh
      rw [e.inv_boundary,e.inv_boundary] at hm
      exact (h.reach i j).mp hm
    · intro hh
      have hm := Graph.map_reach e.toFun e.map_edge ((h.reach i j).mpr hh)
      rwa [e.map_boundary,e.map_boundary] at hm

theorem realizes_iff (e : BoundaryEquiv r s a b) {p : Pairing n} :
    GraphRealizes r a p ↔ GraphRealizes s b p :=
  ⟨e.realizes,e.symm.realizes⟩

end BoundaryEquiv
end Graph

 

 

open Finset
open scoped Classical

namespace Pairing

def stepWiring {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    StepVertex n → StepVertex n → Prop
  | .old i, .old j => p.Adj i j
  | .box k, .box l => t.Adj k l
  | .old i, .box k | .box k, .old i =>
      (i=a ∧ k=0 ∧ p.Occupied a) ∨ (i=b ∧ k=1 ∧ p.Occupied b)
  | .old i, .out j | .out j, .old i =>
      i=j ∧ i≠a ∧ i≠b ∧ p.Occupied i
  | .box k, .out i | .out i, .box k =>
      (i=a ∧ k=2 ∧ t.Occupied 2) ∨ (i=b ∧ k=3 ∧ t.Occupied 3)
  | .out _, .out _ => False

def stepToCut {n : ℕ} (_p : Pairing n) (a b : Fin n) : StepVertex n → Sum (Fin 6) (Fin n)
  | .old i => if i=a then .inl 0 else if i=b then .inl 1 else .inr i
  | .box k => .inl (CutPatch.tilePort k)
  | .out i => .inr i

theorem stepWiring_symm {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    {v w : StepVertex n} (h : p.stepWiring a b t v w) : p.stepWiring a b t w v := by
  cases v <;> cases w <;> try exact h
  · exact adj_symm h
  · exact h.elim Or.inr Or.inl

instance stepWiring_isSymm {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    Std.Symm (p.stepWiring a b t) := ⟨fun _ _ => stepWiring_symm p a b t⟩

theorem cutGraph_symm {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    {v w : Sum (Fin 6) (Fin n)} (h : p.cutGraph a b t v w) : p.cutGraph a b t w v := by
  cases v with
  | inl v =>
    cases w with
    | inl w => exact (CutPatch.adj_symmetric _ _).symm _ _ h
    | inr w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact ⟨i,hi,rfl,rfl⟩
  | inr v =>
    cases w with
    | inl w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact ⟨i,hi,rfl,rfl⟩
    | inr w => exact adj_symm h

instance cutGraph_isSymm {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    Std.Symm (p.cutGraph a b t) := ⟨fun _ _ => cutGraph_symm p a b t⟩

end Pairing

namespace CutPatch

theorem active_zero (s : Shape) (t : Tile) : active s t 0 ↔ t.Occupied 2 := by
  cases s <;> cases t <;> decide

theorem active_one (s : Shape) (t : Tile) : active s t 1 ↔ t.Occupied 3 := by
  cases s <;> cases t <;> decide

theorem active_two (s : Shape) (t : Tile) : active s t 2 ↔ s=.single₀ ∨ s=.separate := by
  cases s <;> cases t <;> decide

theorem active_three (s : Shape) (t : Tile) : active s t 3 ↔ s=.single₁ ∨ s=.separate := by
  cases s <;> cases t <;> decide

theorem input_occupied_zero (s : Shape) : inputOccupied s 0 ↔
    s=.single₀ ∨ s=.paired ∨ s=.separate := by cases s <;> decide

theorem input_occupied_one (s : Shape) : inputOccupied s 1 ↔
    s=.single₁ ∨ s=.paired ∨ s=.separate := by cases s <;> decide

end CutPatch

namespace Pairing

theorem cutShape_input_zero {n : ℕ} (p : Pairing n) (a b : Fin n) :
    CutPatch.inputOccupied (p.cutShape a b) 0 ↔ p.Occupied a := by
  rw [CutPatch.input_occupied_zero]
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn]

theorem cutShape_input_one {n : ℕ} (p : Pairing n) (a b : Fin n) :
    CutPatch.inputOccupied (p.cutShape a b) 1 ↔ p.Occupied b := by
  rw [CutPatch.input_occupied_one]
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn]

theorem cutShape_compatible {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    CutPatch.Compatible (p.cutShape a b) t ↔
      (p.Occupied a ↔ t.Occupied 0) ∧ (p.Occupied b ↔ t.Occupied 1) := by
  simp only [CutPatch.Compatible,Fin.forall_fin_two,cutShape_input_zero,cutShape_input_one]
  rfl

theorem cutShape_active_two {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    CutPatch.active (p.cutShape a b) t 2 ↔ p.Occupied a ∧ ¬ p.Adj a b := by
  rw [CutPatch.active_two]
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn]
  exact (hb ⟨a,adj_symm hn⟩).elim

theorem cutShape_active_three {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    CutPatch.active (p.cutShape a b) t 3 ↔ p.Occupied b ∧ ¬ p.Adj a b := by
  rw [CutPatch.active_three]
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn]
  exact (ha ⟨b,hn⟩).elim

end Pairing
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_StepToCut
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Patch.glued_symm
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

theorem inlinePrivate74_cut_input_left {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (ha : p.Occupied a) (hn : ¬p.Adj a b) : CutPatch.Adj (p.cutShape a b) t 0 4 := by
  by_cases hb : p.Occupied b <;> simp only [cutShape,ha,hb,hn,ite_true,ite_false]
  all_goals exact Or.inl (by simp [CutPatch.inputEdges])

theorem inlinePrivate74_cut_input_right {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hb : p.Occupied b) (hn : ¬p.Adj a b) : CutPatch.Adj (p.cutShape a b) t 1 5 := by
  by_cases ha : p.Occupied a <;> simp only [cutShape,ha,hb,hn,ite_true,ite_false]
  all_goals exact Or.inl (by simp [CutPatch.inputEdges])

theorem inlinePrivate74_cut_input_paired {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hn : p.Adj a b) : CutPatch.Adj (p.cutShape a b) t 0 1 := by
  have ha : p.Occupied a := ⟨b,hn⟩
  have hb : p.Occupied b := ⟨a,adj_symm hn⟩
  simp only [cutShape,ha,hb,hn,ite_true]
  exact Or.inl (by simp [CutPatch.inputEdges])

theorem cutReach_left {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (j : Fin n) (h : p.Adj a j) :
    Relation.ReflTransGen (p.cutGraph a b t) (.inl 0) (p.stepToCut a b (.old j)) := by
  have ha : p.Occupied a := ⟨j,h⟩
  have hja : j≠a := by rintro rfl; exact p.adj_irrefl _ h
  by_cases hjb : j=b
  · subst j
    simp only [stepToCut,Ne.symm hab,ite_false,ite_true]
    exact .single (inlinePrivate74_cut_input_paired p a b t h)
  · have hn : ¬p.Adj a b := fun hh => hjb (adj_unique h hh)
    have hj : p.partnerOrSelf a=j := ((p.adj_partnerOrSelf a j).mp h).2.symm
    simp only [stepToCut,hja,hjb,ite_false]
    refine (Relation.ReflTransGen.single (show p.cutGraph a b t (.inl 0) (.inl 4) from inlinePrivate74_cut_input_left p a b t ha hn)).tail ?_
    exact ⟨2,(p.cutShape_active_two a b t).mpr ⟨ha,hn⟩,rfl,by simp [cutLabels,hj]⟩

theorem cutReach_right {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (j : Fin n) (h : p.Adj b j) :
    Relation.ReflTransGen (p.cutGraph a b t) (.inl 1) (p.stepToCut a b (.old j)) := by
  have hb : p.Occupied b := ⟨j,h⟩
  have hjb : j≠b := by rintro rfl; exact p.adj_irrefl _ h
  by_cases hja : j=a
  · subst j
    simp only [stepToCut,ite_true]
    exact .single ((CutPatch.adj_symmetric _ _).symm _ _ (inlinePrivate74_cut_input_paired p a b t (adj_symm h)))
  · have hn : ¬p.Adj a b := fun hh => hja (adj_unique h (adj_symm hh))
    have hj : p.partnerOrSelf b=j := ((p.adj_partnerOrSelf b j).mp h).2.symm
    simp only [stepToCut,hja,hjb,ite_false]
    refine (Relation.ReflTransGen.single (show p.cutGraph a b t (.inl 1) (.inl 5) from inlinePrivate74_cut_input_right p a b t hb hn)).tail ?_
    exact ⟨3,(p.cutShape_active_three a b t).mpr ⟨hb,hn⟩,rfl,by simp [cutLabels,hj]⟩

theorem cutReach_old_edge {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (i j : Fin n) (h : p.Adj i j) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b (.old i)) (p.stepToCut a b (.old j)) := by
  by_cases hia : i=a
  · subst i
    simp only [stepToCut,ite_true]
    exact cutReach_left p a b hab t j h
  by_cases hib : i=b
  · subst i
    simpa only [stepToCut,Ne.symm hab,ite_false,ite_true] using cutReach_right p a b hab t j h
  by_cases hja : j=a
  · subst j
    have hh := symm (cutReach_left p a b hab t i (adj_symm h))
    simpa only [stepToCut,ite_true] using hh
  by_cases hjb : j=b
  · subst j
    have hh := symm (cutReach_right p a b hab t i (adj_symm h))
    simpa only [stepToCut,Ne.symm hab,ite_false,ite_true] using hh
  simp only [stepToCut,hia,hib,hja,hjb,ite_false]
  exact .single ((omitTwo_adj p a b i j).mpr ⟨h,hia,hib,hja,hjb⟩)

theorem cutReach_box_output {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (k : Fin 4) (i : Fin n) (h : p.stepWiring a b t (.box k) (.out i)) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b (.box k)) (p.stepToCut a b (.out i)) := by
  rcases h with ⟨rfl,rfl,h⟩ | ⟨rfl,rfl,h⟩
  · exact .single ⟨0,(CutPatch.active_zero _ _).mpr h,rfl,by simp [cutLabels]⟩
  · exact .single ⟨1,(CutPatch.active_one _ _).mpr h,rfl,by simp [cutLabels]⟩

theorem cutReach_old_box {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (i : Fin n) (k : Fin 4) (h : p.stepWiring a b t (.old i) (.box k)) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b (.old i)) (p.stepToCut a b (.box k)) := by
  rcases h with ⟨rfl,rfl,h⟩ | ⟨rfl,rfl,h⟩
  · simp only [stepToCut,ite_true]; exact .refl
  · simp only [stepToCut,Ne.symm hab,ite_false,ite_true]; exact .refl

theorem cutReach_old_output {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (i j : Fin n) (h : p.stepWiring a b t (.old i) (.out j)) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b (.old i)) (p.stepToCut a b (.out j)) := by
  obtain ⟨rfl,hia,hib,hi⟩ := h
  simp only [stepToCut,hia,hib,ite_false]
  exact .refl

theorem stepToCut_edge {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (v w : StepVertex n) (h : p.stepWiring a b t v w) :
    Relation.ReflTransGen (p.cutGraph a b t) (p.stepToCut a b v) (p.stepToCut a b w) := by
  cases v with
  | old i =>
    cases w with
    | old j => exact cutReach_old_edge p a b hab t i j h
    | box k => exact cutReach_old_box p a b hab t i k h
    | out j => exact cutReach_old_output p a b t i j h
  | box k =>
    cases w with
    | old i => exact symm (cutReach_old_box p a b hab t i k h)
    | box l => exact .single (Or.inr (Or.inr ⟨k,l,h,rfl,rfl⟩))
    | out i => exact cutReach_box_output p a b t k i h
  | out i =>
    cases w with
    | old j => exact symm (cutReach_old_output p a b t j i h)
    | box k => exact symm (cutReach_box_output p a b t k i h)
    | out j => exact h.elim







theorem partnerOrSelf_occupied {n : ℕ} (p : Pairing n) (a : Fin n) (ha : p.Occupied a) :
    p.Occupied (p.partnerOrSelf a) :=
  ⟨a,adj_symm ((adj_partnerOrSelf p a _).mpr ⟨ha,rfl⟩)⟩

theorem partnerOrSelf_away_left {n : ℕ} (p : Pairing n) (a b : Fin n)
    (ha : p.Occupied a) (hn : ¬p.Adj a b) : p.partnerOrSelf a ≠ b := by
  intro h
  exact hn ((adj_partnerOrSelf p a b).mpr ⟨ha,h.symm⟩)

theorem step_input_left {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (ha : p.Occupied a) :
    Relation.ReflTransGen (p.stepWiring a b t) (.box 0) (.old (p.partnerOrSelf a)) := by
  refine (Relation.ReflTransGen.single (show p.stepWiring a b t (.box 0) (.old a) from Or.inl ⟨rfl,rfl,ha⟩)).tail ?_
  exact (adj_partnerOrSelf p a _).mpr ⟨ha,rfl⟩

theorem step_input_right {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hb : p.Occupied b) :
    Relation.ReflTransGen (p.stepWiring a b t) (.box 1) (.old (p.partnerOrSelf b)) := by
  refine (Relation.ReflTransGen.single (show p.stepWiring a b t (.box 1) (.old b) from Or.inr ⟨rfl,rfl,hb⟩)).tail ?_
  exact (adj_partnerOrSelf p b _).mpr ⟨hb,rfl⟩

theorem step_input_paired {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hn : p.Adj a b) : Relation.ReflTransGen (p.stepWiring a b t) (.box 0) (.box 1) := by
  have h₁ : p.stepWiring a b t (.box 0) (.old a) := Or.inl ⟨rfl,rfl,⟨b,hn⟩⟩
  have h₂ : p.stepWiring a b t (.old a) (.old b) := hn
  have h₃ : p.stepWiring a b t (.old b) (.box 1) := Or.inr ⟨rfl,rfl,⟨a,adj_symm hn⟩⟩
  exact ((Relation.ReflTransGen.single h₁).tail h₂).tail h₃

theorem cut_input_cases {n : ℕ} (p : Pairing n) (a b : Fin n) (v w : Fin 6)
    (h : (v,w) ∈ CutPatch.inputEdges (p.cutShape a b)) :
    (v=0 ∧ w=4 ∧ p.Occupied a) ∨ (v=1 ∧ w=5 ∧ p.Occupied b) ∨
      (v=0 ∧ w=1 ∧ p.Adj a b) := by
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn,CutPatch.inputEdges,Prod.mk.injEq] at h ⊢ <;> itauto

theorem stepReach_input_edge {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v w : Fin 6) (h : (v,w) ∈ CutPatch.inputEdges (p.cutShape a b)) :
    Relation.ReflTransGen (p.stepWiring a b t) (p.cutToStep a b (.inl v)) (p.cutToStep a b (.inl w)) := by
  rcases cut_input_cases p a b v w h with ⟨rfl,rfl,ha⟩ | ⟨rfl,rfl,hb⟩ | ⟨rfl,rfl,hn⟩
  · exact step_input_left p a b t ha
  · exact step_input_right p a b t hb
  · exact step_input_paired p a b t hn

theorem stepReach_interface {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (i : Fin 4) (hi : CutPatch.active (p.cutShape a b) t i) :
    Relation.ReflTransGen (p.stepWiring a b t)
      (p.cutToStep a b (.inl (CutPatch.boundary i))) (p.cutToStep a b (.inr (p.cutLabels a b i))) := by
  fin_cases i
  · exact .single (Or.inl ⟨rfl,rfl,(CutPatch.active_zero _ _).mp hi⟩)
  · exact .single (Or.inr ⟨rfl,rfl,(CutPatch.active_one _ _).mp hi⟩)
  · obtain ⟨ha,hn⟩ := (p.cutShape_active_two a b t).mp hi
    exact .single ⟨rfl,p.partnerOrSelf_ne a ha,p.partnerOrSelf_away_left a b ha hn,
      p.partnerOrSelf_occupied a ha⟩
  · obtain ⟨hb,hn⟩ := (p.cutShape_active_three a b t).mp hi
    have hna : ¬p.Adj b a := fun hh => hn (adj_symm hh)
    exact .single ⟨rfl,p.partnerOrSelf_away_left b a hb hna,p.partnerOrSelf_ne b hb,
      p.partnerOrSelf_occupied b hb⟩

theorem stepReach_omitted {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (i j : Fin n) (h : (p.omitTwo a b).Adj i j) :
    Relation.ReflTransGen (p.stepWiring a b t) (.out i) (.out j) := by
  obtain ⟨h,hia,hib,hja,hjb⟩ := (omitTwo_adj p a b i j).mp h
  have h₁ : p.stepWiring a b t (.out i) (.old i) := ⟨rfl,hia,hib,⟨j,h⟩⟩
  have h₂ : p.stepWiring a b t (.old i) (.old j) := h
  have h₃ : p.stepWiring a b t (.old j) (.out j) := ⟨rfl,hja,hjb,⟨i,adj_symm h⟩⟩
  exact ((Relation.ReflTransGen.single h₁).tail h₂).tail h₃

theorem cutToStep_edge {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v w : Sum (Fin 6) (Fin n)) (h : p.cutGraph a b t v w) :
    Relation.ReflTransGen (p.stepWiring a b t) (p.cutToStep a b v) (p.cutToStep a b w) := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      rcases h with h | h | ⟨i,j,h,rfl,rfl⟩
      · exact stepReach_input_edge p a b t v w h
      · exact symm (stepReach_input_edge p a b t w v h)
      · simp only [cutToStep_tilePort]
        exact .single h
    | inr w =>
      obtain ⟨i,hi,rfl,rfl⟩ := h
      exact stepReach_interface p a b t i hi
  | inr v =>
    cases w with
    | inl w =>
      obtain ⟨i,hi,rfl,rfl⟩ := h
      exact symm (stepReach_interface p a b t i hi)
    | inr w => exact stepReach_omitted p a b t v w h

end Pairing
end

 

 

noncomputable section
open scoped Classical

namespace Pairing

theorem stepToCut_old_injective {n : ℕ} (p : Pairing n) (a b : Fin n) :
    Function.Injective (fun i => p.stepToCut a b (.old i)) := by
  intro i j h
  by_cases hia : i=a <;> by_cases hib : i=b <;>
    by_cases hja : j=a <;> by_cases hjb : j=b <;>
    simp_all [stepToCut]

theorem cutGraph_used_old {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (i : Fin n) (hi : p.Occupied i) : Graph.Used (p.cutGraph a b t) (p.stepToCut a b (.old i)) := by
  obtain ⟨j,hj⟩ := hi
  apply Graph.used_of_reach_ne (p.cutReach_old_edge a b hab t i j hj)
  intro hh
  have := p.stepToCut_old_injective a b hh
  subst j
  exact p.adj_irrefl i hj

theorem stepWiring_old_used {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (i : Fin n) : Graph.Used (p.stepWiring a b t) (.old i) ↔ p.Occupied i := by
  constructor
  · rintro ⟨v,hv⟩
    cases v with
    | old j => exact ⟨j,hv⟩
    | box k => rcases hv with ⟨rfl,_,h⟩ | ⟨rfl,_,h⟩ <;> exact h
    | out j => exact hv.2.2.2
  · rintro ⟨j,hj⟩
    exact ⟨.old j,hj⟩

theorem stepToCut_used {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (v : StepVertex n) (hv : Graph.Used (p.stepWiring a b t) v) :
    Graph.Used (p.cutGraph a b t) (p.stepToCut a b v) := by
  cases v with
  | old i => exact p.cutGraph_used_old a b hab t i ((p.stepWiring_old_used a b t i).mp hv)
  | box k =>
    obtain ⟨w,hw⟩ := hv
    cases w with
    | old i =>
      rcases hw with ⟨hia,hk,ha⟩ | ⟨hib,hk,hb⟩
      · subst i k
        simpa [stepToCut,CutPatch.tilePort] using p.cutGraph_used_old a b hab t a ha
      · subst i k
        simpa [stepToCut,hab.symm,CutPatch.tilePort] using p.cutGraph_used_old a b hab t b hb
    | box l => exact ⟨.inl (CutPatch.tilePort l),Or.inr (Or.inr ⟨k,l,hw,rfl,rfl⟩)⟩
    | out i =>
      apply Graph.used_of_reach_ne (p.stepToCut_edge a b hab t (.box k) (.out i) hw)
      simp [stepToCut]
  | out i =>
    obtain ⟨w,hw⟩ := hv
    cases w with
    | old j =>
      obtain ⟨rfl,hja,hjb,hj⟩ := hw
      simpa [stepToCut,hja,hjb] using p.cutGraph_used_old a b hab t j hj
    | box k =>
      apply Graph.used_of_reach_ne (p.stepToCut_edge a b hab t (.out i) (.box k) hw)
      simp [stepToCut]
    | out j => exact hw.elim

theorem cutToStep_edge_ne {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v w : Sum (Fin 6) (Fin n)) (h : p.cutGraph a b t v w) :
    p.cutToStep a b v ≠ p.cutToStep a b w := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      rcases h with h | h | ⟨i,j,h,rfl,rfl⟩
      · rcases p.cut_input_cases a b v w h with ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ <;>
          simp [cutToStep]
      · rcases p.cut_input_cases a b w v h with ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ <;>
          simp [cutToStep]
      · simp only [cutToStep_tilePort,ne_eq,StepVertex.box.injEq]
        intro hh
        subst j
        exact t.adj_irrefl i h
    | inr w =>
      obtain ⟨i,_,rfl,rfl⟩ := h
      fin_cases i <;> simp [cutToStep,CutPatch.boundary]
  | inr v =>
    cases w with
    | inl w =>
      obtain ⟨i,_,rfl,rfl⟩ := h
      fin_cases i <;> simp [cutToStep,CutPatch.boundary]
    | inr w =>
      simp only [cutToStep,ne_eq,StepVertex.out.injEq]
      intro hh
      subst w
      exact (p.omitTwo a b).adj_irrefl v h

theorem cutToStep_used {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v : Sum (Fin 6) (Fin n)) (hv : Graph.Used (p.cutGraph a b t) v) :
    Graph.Used (p.stepWiring a b t) (p.cutToStep a b v) := by
  obtain ⟨w,hw⟩ := hv
  exact Graph.used_of_reach_ne (p.cutToStep_edge a b t v w hw) (p.cutToStep_edge_ne a b t v w hw)

end Pairing

 

 


namespace CutPatch

theorem adj_four_active : ∀ (s : Shape) (t : Tile) (v : Fin 6), Adj s t 4 v → active s t 2 := by
  decide

theorem adj_five_active : ∀ (s : Shape) (t : Tile) (v : Fin 6), Adj s t 5 v → active s t 3 := by
  decide

end CutPatch

namespace Pairing

theorem cutGraph_used_four {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (h : Graph.Used (p.cutGraph a b t) (.inl 4)) : CutPatch.active (p.cutShape a b) t 2 := by
  obtain ⟨w,hw⟩ := h
  cases w with
  | inl w => exact CutPatch.adj_four_active _ _ w hw
  | inr w =>
    obtain ⟨i,hi,hb,_⟩ := hw
    fin_cases i <;> simp_all [CutPatch.boundary]

theorem cutGraph_used_five {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (h : Graph.Used (p.cutGraph a b t) (.inl 5)) : CutPatch.active (p.cutShape a b) t 3 := by
  obtain ⟨w,hw⟩ := h
  cases w with
  | inl w => exact CutPatch.adj_five_active _ _ w hw
  | inr w =>
    obtain ⟨i,hi,hb,_⟩ := hw
    fin_cases i <;> simp_all [CutPatch.boundary]

theorem stepToCut_retract {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v : StepVertex n) (hv : Graph.Used (p.stepWiring a b t) v) :
    Relation.ReflTransGen (p.stepWiring a b t) v (p.cutToStep a b (p.stepToCut a b v)) := by
  cases v with
  | old i =>
    have hi := (p.stepWiring_old_used a b t i).mp hv
    by_cases hia : i=a
    · subst i
      simp only [stepToCut,ite_true,cutToStep,Matrix.cons_val_zero]
      exact .single (Or.inl ⟨rfl,rfl,hi⟩)
    · by_cases hib : i=b
      · subst i
        simp only [stepToCut,hia,ite_false,ite_true,cutToStep,Matrix.cons_val_one,
          Matrix.cons_val_zero]
        exact .single (Or.inr ⟨rfl,rfl,hi⟩)
      · simp only [stepToCut,hia,hib,ite_false,cutToStep]
        exact .single ⟨rfl,hia,hib,hi⟩
  | box k => rw [stepToCut,cutToStep_tilePort]
  | out i => exact .refl

theorem cutToStep_retract {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (v : Sum (Fin 6) (Fin n)) (hv : Graph.Used (p.cutGraph a b t) v) :
    Relation.ReflTransGen (p.cutGraph a b t) v (p.stepToCut a b (p.cutToStep a b v)) := by
  cases v with
  | inl k =>
    fin_cases k
    · exact .refl
    · exact .refl
    · exact .refl
    · exact .refl
    · have hi := p.cutGraph_used_four a b t hv
      obtain ⟨ha,hn⟩ := (p.cutShape_active_two a b t).mp hi
      have hpa := p.partnerOrSelf_ne a ha
      have hpb := p.partnerOrSelf_away_left a b ha hn
      change Relation.ReflTransGen (p.cutGraph a b t) (.inl 4)
        (p.stepToCut a b (.old (p.partnerOrSelf a)))
      simp only [stepToCut,hpa,hpb,ite_false]
      exact .single ⟨2,hi,rfl,rfl⟩
    · have hi := p.cutGraph_used_five a b t hv
      obtain ⟨hb,hn⟩ := (p.cutShape_active_three a b t).mp hi
      have hpb := p.partnerOrSelf_ne b hb
      have hna : ¬ p.Adj b a := fun hh => hn (adj_symm hh)
      have hpa := p.partnerOrSelf_away_left b a hb hna
      change Relation.ReflTransGen (p.cutGraph a b t) (.inl 5)
        (p.stepToCut a b (.old (p.partnerOrSelf b)))
      simp only [stepToCut,hpa,hpb,ite_false]
      exact .single ⟨3,hi,rfl,rfl⟩
  | inr i => exact .refl

def stepCutEquiv {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile) :
    Graph.BoundaryEquiv (p.stepWiring a b t) (p.cutGraph a b t) StepVertex.out Sum.inr where
  toFun := p.stepToCut a b
  invFun := p.cutToStep a b
  map_edge := p.stepToCut_edge a b hab t
  inv_edge := p.cutToStep_edge a b t
  map_boundary := fun _ => rfl
  inv_boundary := fun _ => rfl
  map_used := p.stepToCut_used a b hab t
  inv_used := p.cutToStep_used a b t
  retract := p.stepToCut_retract a b t
  inv_retract := p.cutToStep_retract a b t

theorem stepWiring_realizes {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (hq : p.tileStep a b hab t = some q) :
    GraphRealizes (p.stepWiring a b t) StepVertex.out q := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  exact (p.stepCutEquiv a b hne t).symm.realizes (p.cutGraph_realizes a b hab t q hq)


 

 



theorem ext_adj {n : ℕ} {p q : Pairing n} (h : ∀ i j, p.Adj i j ↔ q.Adj i j) : p=q := by
  apply Subtype.ext
  ext e
  constructor
  · intro he
    rcases (h e.1 e.2).mp (Or.inl he) with hh | hh
    · exact hh
    · have hp := p.property.1 _ he
      have hq := q.property.1 _ hh
      exact (lt_asymm hp hq).elim
  · intro he
    rcases (h e.1 e.2).mpr (Or.inl he) with hh | hh
    · exact hh
    · have hp := q.property.1 _ he
      have hq := p.property.1 _ hh
      exact (lt_asymm hp hq).elim

theorem graphRealizes {n : ℕ} (p : Pairing n) : GraphRealizes p.Adj id p where
  no_loop := fun v w h => ⟨v,⟨w,h⟩,.refl⟩
  reach := p.reach_adj_iff

end Pairing

namespace GraphRealizes

theorem unique {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p q : Pairing n} (hp : GraphRealizes r a p) (hq : GraphRealizes r a q) : p=q := by
  apply Pairing.ext_adj
  intro i j
  by_cases hij : i=j
  · subst j; simp only [p.adj_irrefl,q.adj_irrefl]
  · have hh := (hp.reach i j).symm.trans (hq.reach i j)
    simpa only [hij,false_or] using hh

 

theorem compressed_eq {V B : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (s : B → B → Prop) (b : Fin n → B) :
    Patch.compressed r s a b p.Occupied = Patch.compressed p.Adj s id b p.Occupied := by
  funext x y
  apply propext
  simp only [Patch.compressed,h.reach,Pairing.reach_adj_iff,id_eq]

theorem drains_glued_iff {V B : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (s : B → B → Prop) (b : Fin n → B)
    (out : B → Prop) :
    Patch.drains (Patch.glued r s a b p.Occupied) (Patch.exteriorOutput out) ↔
      Patch.drains (Patch.glued p.Adj s id b p.Occupied) (Patch.exteriorOutput out) := by
  rw [Patch.drains_glued_iff,Patch.drains_glued_iff,h.compressed_eq s b]
  have hp := p.graphRealizes
  exact ⟨fun hh => ⟨hp.no_loop,hh.2⟩,fun hh => ⟨h.no_loop,hh.2⟩⟩

end GraphRealizes

namespace Patch

theorem realizes_iff_drains {V B : Type*} {n m : ℕ} (r : V → V → Prop)
    (s : B → B → Prop) (a : Fin n → V) (b : Fin n → B) (active : Fin n → Prop)
    (c : Fin m → B) (q : Pairing m) :
    GraphRealizes (glued r s a b active) (fun i => .inr (c i)) q ↔
      drains (glued r s a b active) (exteriorOutput (fun x => ∃ i, q.Occupied i ∧ x=c i)) ∧
      (∀ i j, Relation.ReflTransGen (compressed r s a b active) (c i) (c j) ↔ i=j ∨ q.Adj i j) := by
  constructor
  · intro h
    constructor
    · intro v w hvw
      obtain ⟨i,hi,hr⟩ := h.no_loop v w hvw
      exact ⟨.inr (c i),⟨i,hi,rfl⟩,hr⟩
    · intro i j
      exact (exterior_reach_iff r s a b active).symm.trans (h.reach i j)
  · rintro ⟨hd,hr⟩
    constructor
    · intro v w hvw
      obtain ⟨x,hx,hvx⟩ := hd v w hvw
      cases x with
      | inl x => exact hx.elim
      | inr x =>
        obtain ⟨i,hi,rfl⟩ := hx
        exact ⟨i,hi,hvx⟩
    · intro i j
      exact (exterior_reach_iff r s a b active).trans (hr i j)

end Patch

namespace GraphRealizes

theorem substitute_iff {V B : Type*} {n m : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (s : B → B → Prop) (b : Fin n → B)
    (c : Fin m → B) (q : Pairing m) :
    GraphRealizes (Patch.glued r s a b p.Occupied) (fun i => .inr (c i)) q ↔
      GraphRealizes (Patch.glued p.Adj s id b p.Occupied) (fun i => .inr (c i)) q := by
  rw [Patch.realizes_iff_drains,Patch.realizes_iff_drains,h.compressed_eq s b,h.drains_glued_iff s b]

end GraphRealizes
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_StepComplete
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Patch.glued_symm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace GraphRealizes

theorem boundary_used_iff {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (ha : Function.Injective a) (i : Fin n) :
    Graph.Used r (a i) ↔ p.Occupied i := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨j,hj,hr⟩ := h.no_loop (a i) w hw
    rcases (h.reach i j).mp hr with hh | hh
    · exact hh ▸ hj
    · exact ⟨j,hh⟩
  · rintro ⟨j,hj⟩
    apply Graph.used_of_reach_ne ((h.reach i j).mpr (Or.inr hj))
    intro hh
    have he := ha hh
    subst j
    exact p.adj_irrefl i hj

end GraphRealizes

namespace Pairing

theorem tileStep_compatible {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (hq : p.tileStep a b hab t = some q) : CutPatch.Compatible (p.cutShape a b) t := by
  have hn : CutPatch.profile (p.cutShape a b) t ≠ none := by
    intro hh
    have := (p.tileStep_none_iff a b hab t).mpr hh
    rw [hq] at this
    cases this
  obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp hn
  exact (CutPatch.realizes_of_profile hd).compatible

theorem cutGraph_profile_ne_none {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    (hc : CutPatch.Compatible (p.cutShape a b) t) (q : Pairing n)
    (hq : GraphRealizes (p.cutGraph a b t) Sum.inr q) :
    CutPatch.profile (p.cutShape a b) t ≠ none := by
  intro hh
  obtain ⟨v,w,hvw,hout⟩ := CutPatch.none_has_closed hh hc
  obtain ⟨j,_,hr⟩ := hq.no_loop (.inl v) (.inl w) hvw
  obtain ⟨i,hi,hi',_⟩ := Patch.reach_to_exterior
    (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj
    CutPatch.boundary (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t) hr
  exact hout i hi hi'

theorem tileStep_iff {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n) :
    p.tileStep a b hab t = some q ↔
      CutPatch.Compatible (p.cutShape a b) t ∧ GraphRealizes (p.stepWiring a b t) StepVertex.out q := by
  constructor
  · intro hq
    exact ⟨p.tileStep_compatible a b hab t q hq,p.stepWiring_realizes a b hab t q hq⟩
  · rintro ⟨hc,hq⟩
    have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
    have hg := (p.stepCutEquiv a b hne t).realizes hq
    have hn : p.tileStep a b hab t ≠ none := by
      intro hh
      exact p.cutGraph_profile_ne_none a b t hc q hg ((p.tileStep_none_iff a b hab t).mp hh)
    obtain ⟨r,hr⟩ := Option.ne_none_iff_exists'.mp hn
    have he := (p.stepWiring_realizes a b hab t r hr).unique hq
    exact he ▸ hr

theorem stepWiring_out_used {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) (i : Fin n) :
    Graph.Used (p.stepWiring a b t) (.out i) ↔
      (i=a ∧ t.Occupied 2) ∨ (i=b ∧ t.Occupied 3) ∨
        (i≠a ∧ i≠b ∧ p.Occupied i) := by
  constructor
  · rintro ⟨w,hw⟩
    cases w with
    | old j =>
      obtain ⟨rfl,hja,hjb,hj⟩ := hw
      exact Or.inr (Or.inr ⟨hja,hjb,hj⟩)
    | box k =>
      rcases hw with ⟨hi,_,h⟩ | ⟨hi,_,h⟩
      · exact Or.inl ⟨hi,h⟩
      · exact Or.inr (Or.inl ⟨hi,h⟩)
    | out j => exact hw.elim
  · rintro (⟨h,ht⟩ | ⟨h,ht⟩ | ⟨hia,hib,hi⟩)
    · exact ⟨.box 2,Or.inl ⟨h,rfl,ht⟩⟩
    · exact ⟨.box 3,Or.inr ⟨h,rfl,ht⟩⟩
    · exact ⟨.old i,rfl,hia,hib,hi⟩

def stepSupport {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) (i : Fin n) : Prop :=
  if i=a then t.Occupied 2 else if i=b then t.Occupied 3 else p.Occupied i

theorem tileStep_support {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (hq : p.tileStep a b hab t = some q) (i : Fin n) :
    q.Occupied i ↔ p.stepSupport a b t i := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  rw [← (p.stepWiring_realizes a b hab t q hq).boundary_used_iff (fun _ _ h => StepVertex.out.inj h) i,
    p.stepWiring_out_used]
  by_cases hia : i=a <;> by_cases hib : i=b <;> simp_all [stepSupport]

end Pairing






def gateWiring {n : ℕ} (a b : Fin n) (t : Tile) : GateExterior n → GateExterior n → Prop
  | .inl k, .inl l => t.Adj k l
  | .inr _, .inr _ => False
  | .inl k, .inr i | .inr i, .inl k =>
      (i=a ∧ k=2 ∧ t.Occupied 2) ∨ (i=b ∧ k=3 ∧ t.Occupied 3)

def stepVertexEquiv (n : ℕ) : StepVertex n ≃ Sum (Fin n) (GateExterior n) where
  toFun
    | .old i => .inl i
    | .box k => .inr (.inl k)
    | .out i => .inr (.inr i)
  invFun
    | .inl i => .old i
    | .inr (.inl k) => .box k
    | .inr (.inr i) => .out i
  left_inv := fun v => by cases v <;> rfl
  right_inv := fun v => by rcases v with i | (k | i) <;> rfl

namespace Pairing

theorem stepWiring_glued {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile)
    (v w : StepVertex n) : p.stepWiring a b t v w ↔
      Patch.glued p.Adj (gateWiring a b t) id (gateInput a b) p.Occupied
        (stepVertexEquiv n v) (stepVertexEquiv n w) := by
  cases v <;> cases w <;> simp only [stepVertexEquiv,Equiv.coe_fn_mk,stepWiring,
    Patch.glued,gateWiring,id_eq]
  · rename_i i k
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [gateInput,and_comm,eq_comm]
  · rename_i i j
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [gateInput,and_comm,eq_comm]
  · rename_i k i
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [gateInput,and_comm,eq_comm]
  · rename_i j i
    by_cases hia : i=a <;> by_cases hib : i=b <;>
      simp_all [gateInput,and_comm,eq_comm]

def stepGluedEquiv {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a≠b) (t : Tile) :
    Graph.BoundaryEquiv (p.stepWiring a b t)
      (Patch.glued p.Adj (gateWiring a b t) id (gateInput a b) p.Occupied)
      StepVertex.out (fun i => .inr (.inr i)) :=
  Graph.BoundaryEquiv.ofEquiv (stepVertexEquiv n) (p.stepWiring_glued a b hab t) (fun _ => rfl)

end Pairing

 

theorem graph_gate_step_iff {V : Type*} {n : ℕ} {r : V → V → Prop} {boundary : Fin n → V}
    {p : Pairing n} (hp : GraphRealizes r boundary p) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n) :
    (CutPatch.Compatible (p.cutShape a b) t ∧
      GraphRealizes (Patch.glued r (gateWiring a b t) boundary (gateInput a b) p.Occupied)
        (fun i => .inr (.inr i)) q) ↔ p.tileStep a b hab t = some q := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  rw [hp.substitute_iff,← (p.stepGluedEquiv a b hne t).realizes_iff,← p.tileStep_iff]







namespace GraphRealizes

theorem drainsBoundary {V : Type*} {n : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) : Graph.DrainsBoundary r a := by
  intro v w hvw
  obtain ⟨i,_,hi⟩ := h.no_loop v w hvw
  exact ⟨i,hi⟩

theorem substitute_drains_iff {V B : Type*} {n m : ℕ} {r : V → V → Prop} {a : Fin n → V}
    {p : Pairing n} (h : GraphRealizes r a p) (s : B → B → Prop) (b : Fin n → B) (c : Fin m → B) :
    Graph.DrainsBoundary (Patch.glued r s a b p.Occupied) (fun i => .inr (c i)) ↔
      Graph.DrainsBoundary (Patch.glued p.Adj s id b p.Occupied) (fun i => .inr (c i)) := by
  rw [Graph.drains_glued_exterior_iff,Graph.drains_glued_exterior_iff,h.drains_glued_iff]

end GraphRealizes

namespace Pairing

theorem tileStep_ne_none_of_drains {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile)
    (hc : CutPatch.Compatible (p.cutShape a b) t)
    (hd : Graph.DrainsBoundary (p.stepWiring a b t) StepVertex.out) :
    p.tileStep a b hab t ≠ none := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  have hg := (p.stepCutEquiv a b hne t).drains hd
  intro hh
  have hp := (p.tileStep_none_iff a b hab t).mp hh
  obtain ⟨v,w,hvw,hout⟩ := CutPatch.none_has_closed hp hc
  obtain ⟨j,hr⟩ := hg (.inl v) (.inl w) hvw
  obtain ⟨i,hi,hi',_⟩ := Patch.reach_to_exterior
    (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj
    CutPatch.boundary (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t) hr
  exact hout i hi hi'

end Pairing

theorem graph_gate_step_exists {V : Type*} {n : ℕ} {r : V → V → Prop} {boundary : Fin n → V}
    {p : Pairing n} (hp : GraphRealizes r boundary p) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile)
    (hc : CutPatch.Compatible (p.cutShape a b) t)
    (hd : Graph.DrainsBoundary
      (Patch.glued r (gateWiring a b t) boundary (gateInput a b) p.Occupied)
      (fun i => .inr (.inr i))) : ∃ q, p.tileStep a b hab t = some q := by
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  have hd' := (hp.substitute_drains_iff (gateWiring a b t) (gateInput a b) Sum.inr).mp hd
  have hd'' := (p.stepGluedEquiv a b hne t).symm.drains hd'
  exact Option.ne_none_iff_exists'.mp (p.tileStep_ne_none_of_drains a b hab t hc hd'')


 

 


structure Gate (n : ℕ) where
  left : Fin n
  right : Fin n
  adjacent : left.val+1=right.val
  tile : Tile

inductive Circuit (n : ℕ) where
  | nil : Circuit n
  | snoc : Circuit n → Gate n → Circuit n

namespace Circuit
variable {n : ℕ}

def Vertex : Circuit n → Type
  | .nil => Fin n
  | .snoc c _ => Sum c.Vertex (GateExterior n)

def boundary : (c : Circuit n) → Fin n → c.Vertex
  | .nil => id
  | .snoc _ _ => fun i => .inr (.inr i)

def support (p : Pairing n) : Circuit n → Fin n → Prop
  | .nil => p.Occupied
  | .snoc c g => fun i => if i=g.left then g.tile.Occupied 2
      else if i=g.right then g.tile.Occupied 3 else support p c i

def wiring (p : Pairing n) : (c : Circuit n) → c.Vertex → c.Vertex → Prop
  | .nil => p.Adj
  | .snoc c g => Patch.glued (wiring p c) (gateWiring g.left g.right g.tile)
      c.boundary (gateInput g.left g.right) (support p c)

def Compatible (p : Pairing n) : Circuit n → Prop
  | .nil => True
  | .snoc c g => Compatible p c ∧
      (support p c g.left ↔ g.tile.Occupied 0) ∧
      (support p c g.right ↔ g.tile.Occupied 1)

def eval (p : Pairing n) : Circuit n → Option (Pairing n)
  | .nil => some p
  | .snoc c g => (eval p c).bind (fun q => q.tileStep g.left g.right g.adjacent g.tile)

theorem eval_sound (p : Pairing n) (c : Circuit n) (q : Pairing n)
    (h : eval p c = some q) :
    Compatible p c ∧ GraphRealizes (wiring p c) c.boundary q ∧ support p c=q.Occupied := by
  induction c generalizing q with
  | nil =>
    have he : p=q := Option.some.inj h
    subst q
    exact ⟨trivial,p.graphRealizes,rfl⟩
  | snoc c g ih =>
    cases hp : eval p c with
    | none => simp [eval,hp] at h
    | some r =>
      have hstep : r.tileStep g.left g.right g.adjacent g.tile = some q := by
        simpa only [eval,hp,Option.bind_some] using h
      obtain ⟨hc,hr,hs⟩ := ih r hp
      have hsc := r.tileStep_compatible g.left g.right g.adjacent g.tile q hstep
      have hsc' := (r.cutShape_compatible g.left g.right g.tile).mp hsc
      refine ⟨⟨hc,?_,?_⟩,?_,?_⟩
      · simpa only [hs] using hsc'.1
      · simpa only [hs] using hsc'.2
      · change GraphRealizes (Patch.glued (wiring p c) (gateWiring g.left g.right g.tile)
          c.boundary (gateInput g.left g.right) (support p c)) (fun i => .inr (.inr i)) q
        rw [hs]
        exact ((graph_gate_step_iff hr g.left g.right g.adjacent g.tile q).mpr hstep).2
      · funext i
        apply propext
        change (if i=g.left then g.tile.Occupied 2 else
          if i=g.right then g.tile.Occupied 3 else support p c i) ↔ q.Occupied i
        rw [hs]
        exact (r.tileStep_support g.left g.right g.adjacent g.tile q hstep i).symm

end Circuit
end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_WireContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

namespace Graph



namespace WireContraction
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
  {a : Fin n → V} {b : Fin n → W} [Std.Symm r] [Std.Symm s]

theorem realizes (e : WireContraction r s a b) {p : Pairing n}
    (h : GraphRealizes r a p) : GraphRealizes s b p := by
  constructor
  · intro v w hvw
    obtain ⟨i,hi,hr⟩ := h.no_loop (e.core v) (e.core w) (e.core_edge v w hvw)
    have hm := Graph.map_reach e.project e.map_edge hr
    rw [e.section_eq,e.map_boundary] at hm
    exact ⟨i,hi,hm⟩
  · intro i j
    constructor
    · intro hr
      by_cases hij : i=j
      · exact Or.inl hij
      · exact (h.reach i j).mp (e.lift_boundary_reach hij hr)
    · intro hh
      have hm := Graph.map_reach e.project e.map_edge ((h.reach i j).mpr hh)
      rwa [e.map_boundary,e.map_boundary] at hm

theorem realizes_inv (e : WireContraction r s a b) {p : Pairing n}
    (h : GraphRealizes s b p) : GraphRealizes r a p := by
  constructor
  · intro v w hvw
    obtain ⟨x,hx⟩ := e.map_used v ⟨w,hvw⟩
    obtain ⟨i,hi,hr⟩ := h.no_loop (e.project v) x hx
    have hm := Graph.map_reach e.core (fun v w hvw => .single (e.core_edge v w hvw)) hr
    have hb := (h.boundary_used_iff e.boundary_injective i).mpr hi
    exact ⟨i,hi,((e.retract v ⟨w,hvw⟩).trans hm).trans (e.boundary_retract i hb)⟩
  · intro i j
    constructor
    · intro hr
      have hm := Graph.map_reach e.project e.map_edge hr
      rw [e.map_boundary,e.map_boundary] at hm
      exact (h.reach i j).mp hm
    · intro hh
      rcases hh with hij | hadj
      · subst j; exact .refl
      · have hij : i≠j := by intro hh; subst j; exact p.adj_irrefl i hadj
        exact e.lift_boundary_reach hij ((h.reach i j).mpr (Or.inr hadj))

theorem realizes_iff (e : WireContraction r s a b) {p : Pairing n} :
    GraphRealizes r a p ↔ GraphRealizes s b p := ⟨e.realizes,e.realizes_inv⟩

end WireContraction
end Graph

 

 

section LocalContractions
open scoped Classical

namespace CompactGate
variable {V : Type*} {n : ℕ}

def wiring (r : V → V → Prop) (boundary : Fin n → V) (active : Fin n → Prop)
    (a b : Fin n) (t : Tile) : Sum V (Fin 4) → Sum V (Fin 4) → Prop
  | .inl v, .inl w => r v w
  | .inr k, .inr l => t.Adj k l
  | .inl v, .inr k | .inr k, .inl v =>
      (v=boundary a ∧ k=0 ∧ active a) ∨ (v=boundary b ∧ k=1 ∧ active b)

instance wiring_symm (r : V → V → Prop) [Std.Symm r] (old : Fin n → V)
    (active : Fin n → Prop) (a b : Fin n) (t : Tile) :
    Std.Symm (wiring r old active a b t) := by
  constructor
  intro v w h
  cases v <;> cases w <;> try exact h
  · change r _ _ at h ⊢; exact symm h
  · exact h.elim Or.inr Or.inl

end CompactGate

instance gateWiring_symm {n : ℕ} (a b : Fin n) (t : Tile) : Std.Symm (gateWiring a b t) := by
  constructor
  intro v w h
  rcases v with k | i <;> rcases w with l | j <;> try exact h
  exact h.elim Or.inr Or.inl

namespace CompactGate
variable {V : Type*} {n : ℕ} {r : V → V → Prop} [Std.Symm r]
  {old : Fin n → V} {p : Pairing n}

abbrev full (a b : Fin n) (t : Tile) :=
  Patch.glued r (gateWiring a b t) old (gateInput a b) p.Occupied

omit [Std.Symm r] in
lemma core_edge (a b : Fin n) (hab : a≠b) (t : Tile) (v w : Sum V (Fin 4))
    (h : wiring r old p.Occupied a b t v w) : full (r:=r) (old:=old) (p:=p) a b t (core v) (core w) := by
  cases v with
  | inl v =>
    cases w with
    | inl w => exact h
    | inr k =>
      rcases h with ⟨rfl,rfl,ha⟩ | ⟨rfl,rfl,hb⟩
      · exact ⟨a,ha,rfl,by simp [gateInput]⟩
      · exact ⟨b,hb,rfl,by simp [gateInput,hab.symm]⟩
  | inr k =>
    cases w with
    | inl v =>
      rcases h with ⟨rfl,rfl,ha⟩ | ⟨rfl,rfl,hb⟩
      · exact ⟨a,ha,by simp [gateInput],rfl⟩
      · exact ⟨b,hb,by simp [gateInput,hab.symm],rfl⟩
    | inr l => exact h

omit [Std.Symm r] in
lemma project_edge (a b : Fin n) (hab : a≠b) (t : Tile)
    (v w : Sum V (GateExterior n)) (h : full (r:=r) (old:=old) (p:=p) a b t v w) :
    Relation.ReflTransGen (wiring r old p.Occupied a b t) (project old a b v) (project old a b w) := by
  rcases v with v | (k | i) <;> rcases w with w | (l | j)
  · exact .single h
  · obtain ⟨i,hi,rfl,he⟩ := h
    rcases (gateInput_eq_box a b i hab l).mp he.symm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .single (Or.inl ⟨rfl,rfl,hi⟩)
    · exact .single (Or.inr ⟨rfl,rfl,hi⟩)
  · obtain ⟨i,hi,rfl,he⟩ := h
    obtain ⟨rfl,hia,hib⟩ := (gateInput_eq_out a b i j).mp he.symm
    simp only [project,boundary,ite_eq_right hia,ite_eq_right hib]
    exact .refl
  · obtain ⟨i,hi,he,rfl⟩ := h
    rcases (gateInput_eq_box a b i hab k).mp he.symm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact .single (Or.inl ⟨rfl,rfl,hi⟩)
    · exact .single (Or.inr ⟨rfl,rfl,hi⟩)
  · exact .single h
  · rcases h with ⟨hia,rfl,_⟩ | ⟨hib,rfl,_⟩
    · subst j; simp only [project,boundary_left]; exact .refl
    · subst j; simp only [project,boundary_right old a b hab]; exact .refl
  · obtain ⟨j,hj,he,rfl⟩ := h
    obtain ⟨rfl,hia,hib⟩ := (gateInput_eq_out a b j i).mp he.symm
    simp only [project,boundary,ite_eq_right hia,ite_eq_right hib]
    exact .refl
  · rcases h with ⟨hia,rfl,_⟩ | ⟨hib,rfl,_⟩
    · subst i; simp only [project,boundary_left]; exact .refl
    · subst i; simp only [project,boundary_right old a b hab]; exact .refl
  · exact h.elim

omit [Std.Symm r] in
lemma used_old_iff (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (t : Tile) (v : V) :
    Graph.Used (wiring r old p.Occupied a b t) (.inl v) ↔ Graph.Used r v := by
  constructor
  · rintro ⟨w,hw⟩
    cases w with
    | inl w => exact ⟨w,hw⟩
    | inr k =>
      rcases hw with ⟨rfl,_,ha⟩ | ⟨rfl,_,hb⟩
      · exact (hp.boundary_used_iff hinj a).mpr ha
      · exact (hp.boundary_used_iff hinj b).mpr hb
  · rintro ⟨w,hw⟩; exact ⟨.inl w,hw⟩

omit [Std.Symm r] in
lemma used_output_iff (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (hab : a≠b) (t : Tile) (i : Fin n) :
    Graph.Used (wiring r old p.Occupied a b t) (boundary old a b i) ↔ p.stepSupport a b t i := by
  by_cases hia : i=a
  · subst i
    rw [boundary_left]
    simp only [Pairing.stepSupport,ite_true,eq_self]
    constructor
    · rintro ⟨v,hv⟩
      cases v with
      | inl v => rcases hv with ⟨_,h,_⟩ | ⟨_,h,_⟩ <;> have hh := congrArg Fin.val h <;> norm_num at hh
      | inr k => exact ⟨k,hv⟩
    · rintro ⟨k,hk⟩; exact ⟨.inr k,hk⟩
  · by_cases hib : i=b
    · subst i
      rw [boundary_right old a b hab]
      simp only [Pairing.stepSupport,ite_eq_right hia,ite_true,eq_self]
      constructor
      · rintro ⟨v,hv⟩
        cases v with
        | inl v => rcases hv with ⟨_,h,_⟩ | ⟨_,h,_⟩ <;> have hh := congrArg Fin.val h <;> norm_num at hh
        | inr k => exact ⟨k,hv⟩
      · rintro ⟨k,hk⟩; exact ⟨.inr k,hk⟩
    · simp only [boundary,ite_eq_right hia,ite_eq_right hib,Pairing.stepSupport]
      rw [used_old_iff hp hinj,hp.boundary_used_iff hinj]

omit [Std.Symm r] in
lemma output_edge (a b : Fin n) (hab : a≠b) (t : Tile) (i : Fin n)
    (hi : p.stepSupport a b t i) :
    full (r:=r) (old:=old) (p:=p) a b t (core (boundary old a b i)) (.inr (.inr i)) := by
  by_cases hia : i=a
  · subst i
    rw [boundary_left]
    exact Or.inl ⟨rfl,rfl,by simpa [Pairing.stepSupport] using hi⟩
  · by_cases hib : i=b
    · subst i
      simp only [Pairing.stepSupport,ite_eq_right hia,ite_true,eq_self] at hi
      simpa only [boundary_right old a b hab,core,full,Patch.glued,gateWiring] using
        (Or.inr ⟨rfl,rfl,hi⟩ : (b=a ∧ (3:Fin 4)=2 ∧ t.Occupied 2) ∨ (b=b ∧ (3:Fin 4)=3 ∧ t.Occupied 3))
    · simp only [boundary,ite_eq_right hia,ite_eq_right hib,core,full,Patch.glued]
      exact ⟨i,by simpa [Pairing.stepSupport,hia,hib] using hi,rfl,by simp [gateInput,hia,hib]⟩

omit [Std.Symm r] in
lemma full_used_out (a b : Fin n) (hab : a≠b) (t : Tile) (i : Fin n)
    (h : Graph.Used (full (r:=r) (old:=old) (p:=p) a b t) (.inr (.inr i))) :
    p.stepSupport a b t i := by
  obtain ⟨v,hv⟩ := h
  rcases v with v | (k | j)
  · obtain ⟨j,hj,he,_⟩ := hv
    obtain ⟨rfl,hja,hjb⟩ := (gateInput_eq_out a b j i).mp he.symm
    simpa [Pairing.stepSupport,hja,hjb] using hj
  · rcases hv with ⟨rfl,_,ht⟩ | ⟨rfl,_,ht⟩
    · simpa [Pairing.stepSupport] using ht
    · simpa [Pairing.stepSupport,hab.symm] using ht
  · exact hv.elim

omit [Std.Symm r] in
lemma project_used (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (hab : a≠b) (t : Tile) (v : Sum V (GateExterior n))
    (h : Graph.Used (full (r:=r) (old:=old) (p:=p) a b t) v) :
    Graph.Used (wiring r old p.Occupied a b t) (project old a b v) := by
  rcases v with v | (k | i)
  · apply (used_old_iff hp hinj a b t v).mpr
    obtain ⟨w,hw⟩ := h
    cases w with
    | inl w => exact ⟨w,hw⟩
    | inr w =>
      obtain ⟨i,hi,rfl,_⟩ := hw
      exact (hp.boundary_used_iff hinj i).mpr hi
  · obtain ⟨w,hw⟩ := h
    rcases w with w | (l | j)
    · obtain ⟨i,hi,he,rfl⟩ := hw
      rcases (gateInput_eq_box a b i hab k).mp he.symm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨.inl (old i),Or.inl ⟨rfl,rfl,hi⟩⟩
      · exact ⟨.inl (old i),Or.inr ⟨rfl,rfl,hi⟩⟩
    · exact ⟨.inr l,hw⟩
    · rcases hw with ⟨_,rfl,ht⟩ | ⟨_,rfl,ht⟩ <;>
        obtain ⟨l,hl⟩ := ht <;> exact ⟨.inr l,hl⟩
  · exact (used_output_iff hp hinj a b hab t i).mpr (full_used_out a b hab t i h)

 def contraction (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (hab : a≠b) (t : Tile) :
    Graph.WireContraction (full (r:=r) (old:=old) (p:=p) a b t)
      (wiring r old p.Occupied a b t) (fun i => .inr (.inr i)) (boundary old a b) where
  project := project old a b
  core := core
  section_eq := project_core old a b
  map_edge := project_edge a b hab t
  core_edge := core_edge a b hab t
  map_boundary := fun _ => rfl
  boundary_injective := boundary_injective old hinj a b
  map_used := project_used hp hinj a b hab t
  retract := by
    intro v hv
    rcases v with v | (k | i)
    · exact .refl
    · exact .refl
    · exact .single (symm (output_edge a b hab t i (full_used_out a b hab t i hv)))
  boundary_retract := fun i hi => .single (output_edge a b hab t i
    ((used_output_iff hp hinj a b hab t i).mp hi))

 theorem realizes_iff (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (a b : Fin n) (hab : a≠b) (t : Tile) (q : Pairing n) :
    GraphRealizes (full (r:=r) (old:=old) (p:=p) a b t) (fun i => .inr (.inr i)) q ↔
      GraphRealizes (wiring r old p.Occupied a b t) (boundary old a b) q :=
  (contraction hp hinj a b hab t).realizes_iff

end CompactGate
end LocalContractions





open scoped Classical

namespace CompactGate
variable {V : Type*} {n : ℕ} (r : V → V → Prop) (old : Fin n → V)
  (active : Fin n → Prop) (a b : Fin n) (t : Tile)

lemma reach_exit (v : V) {z : Sum V (Fin 4)}
    (hr : Relation.ReflTransGen (wiring r old active a b t) (.inl v) z) :
    (∃ i, Relation.ReflTransGen r v (old i)) ∨
      localEnd r v z := by
  induction hr with
  | refl => exact Or.inr .refl
  | @tail x y h hxy ih =>
    rcases ih with hi | hi
    · exact Or.inl hi
    · cases x with
      | inr k => exact hi.elim
      | inl w =>
        cases y with
        | inl u => exact Or.inr (hi.tail hxy)
        | inr k =>
          rcases hxy with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩
          · exact Or.inl ⟨a,hi⟩
          · exact Or.inl ⟨b,hi⟩

lemma drains_local (hd : Graph.DrainsBoundary (wiring r old active a b t) (boundary old a b)) :
    Graph.DrainsBoundary r old := by
  intro v w hvw
  obtain ⟨i,hi⟩ := hd (.inl v) (.inl w) hvw
  have he := reach_exit r old active a b t v hi
  rcases he with he | he
  · exact he
  · by_cases hia : i=a
    · simp only [boundary,ite_eq_left hia,localEnd] at he
    · by_cases hib : i=b
      · simp only [boundary,ite_eq_right hia,ite_eq_left hib,localEnd] at he
      · exact ⟨i,by simpa only [boundary,ite_eq_right hia,ite_eq_right hib,localEnd] using he⟩

end CompactGate

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
namespace FreshGate
variable {V : Type*} {n : ℕ}


namespace Ports
variable {r : V → V → Prop} {old : Fin n → V} (f : Ports r old)

def wiring (active : Fin n → Prop) (a b : Fin n) (t : Tile) (v w : V) : Prop :=
  CompactGate.wiring r old active a b t (f.core v) (f.core w)

lemma core_project_used (active : Fin n → Prop) (a b : Fin n) (t : Tile)
    (v : Sum V (Fin 4)) (hv : Graph.Used (CompactGate.wiring r old active a b t) v) :
    f.core (f.project v)=v := by
  cases v with
  | inr k => exact f.core_port k
  | inl v =>
    have hn : f.select v=none := by
      obtain ⟨w,hw⟩ := hv
      cases w with
      | inl w => exact f.edge_none v w hw
      | inr k =>
        rcases hw with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> exact f.old_none _
    simp [project,core,hn]

instance wiring_symm [Std.Symm r] (active : Fin n → Prop) (a b : Fin n) (t : Tile) :
    Std.Symm (f.wiring active a b t) := by
  constructor
  intro v w h
  change CompactGate.wiring r old active a b t (f.core v) (f.core w) at h
  change CompactGate.wiring r old active a b t (f.core w) (f.core v)
  exact symm h

 def contraction [Std.Symm r] (hinj : Function.Injective old)
    (active : Fin n → Prop) (a b : Fin n) (t : Tile) :
    Graph.WireContraction (CompactGate.wiring r old active a b t)
      (f.wiring active a b t) (CompactGate.boundary old a b) (f.boundary a b) where
  project := f.project
  core := f.core
  section_eq := f.project_core
  map_edge := by
    intro v w h
    apply Relation.ReflTransGen.single
    change CompactGate.wiring r old active a b t (f.core (f.project v)) (f.core (f.project w))
    rw [f.core_project_used active a b t v ⟨w,h⟩,
      f.core_project_used active a b t w ⟨v,symm h⟩]
    exact h
  core_edge := fun _ _ h => h
  map_boundary := fun _ => rfl
  boundary_injective := by
    intro i j hij
    apply CompactGate.boundary_injective old hinj a b
    have he := congrArg f.core hij
    simpa only [f.core_boundary] using he
  map_used := by
    intro v ⟨w,h⟩
    refine ⟨f.project w,?_⟩
    change CompactGate.wiring r old active a b t (f.core (f.project v)) (f.core (f.project w))
    rw [f.core_project_used active a b t v ⟨w,h⟩,
      f.core_project_used active a b t w ⟨v,symm h⟩]
    exact h
  retract := by
    intro v hv
    rw [f.core_project_used active a b t v hv]
  boundary_retract := by
    intro i _
    rw [f.core_boundary]

 theorem realizes_iff [Std.Symm r] (hinj : Function.Injective old)
    (active : Fin n → Prop) (a b : Fin n) (t : Tile) (q : Pairing n) :
    GraphRealizes (CompactGate.wiring r old active a b t) (CompactGate.boundary old a b) q ↔
      GraphRealizes (f.wiring active a b t) (f.boundary a b) q :=
  (f.contraction hinj active a b t).realizes_iff

end Ports
end FreshGate
namespace PartialColumn

abbrev V (n : ℕ) := Sum (Fin (n+1)) (Vertex n)

def wiring {n : ℕ} (p : Pairing n) (t : Configuration n) (k : ℕ) : V n → V n → Prop
  | .inl i, .inl j => p.padBottom.Adj i j
  | .inl i, .inr (j,a) | .inr (j,a), .inl i =>
      j.val<k ∧ i=j.succ ∧ a=1 ∧ p.Occupied j
  | .inr (i,a), .inr (j,b) =>
      (i=j ∧ i.val<k ∧ (t i).Adj a b) ∨
      (a=3 ∧ b=0 ∧ i.val+1=j.val ∧ j.val<k ∧ (t i).Occupied 3) ∨
      (b=3 ∧ a=0 ∧ j.val+1=i.val ∧ i.val<k ∧ (t j).Occupied 3)

def boundary {n : ℕ} (k : ℕ) (hk : k≤n) (i : Fin (n+1)) : V n :=
  if hi : i.val<k then .inr (⟨i.val,lt_of_lt_of_le hi hk⟩,2)
  else if h : i.val=k ∧ 0<k then .inr (⟨k-1,by omega⟩,3)
  else .inl i

@[simp] theorem boundary_zero {n : ℕ} (i : Fin (n+1)) : boundary 0 (Nat.zero_le n) i=.inl i := by
  simp [boundary]

instance wiring_symm {n : ℕ} (p : Pairing n) (t : Configuration n) (k : ℕ) :
    Std.Symm (wiring p t k) := by
  constructor
  rintro (i|⟨i,a⟩) (j|⟨j,b⟩) h
  · exact Pairing.adj_symm h
  · exact h
  · exact h
  · rcases h with ⟨rfl,hi,hab⟩ | h | h
    · exact Or.inl ⟨rfl,hi,hab.elim Or.inr Or.inl⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

 theorem boundary_injective {n : ℕ} (k : ℕ) (hk : k≤n) : Function.Injective (boundary k hk) := by
  intro i j hij
  apply Fin.ext
  by_cases hi : i.val<k <;> by_cases hj : j.val<k <;>
    by_cases hi' : i.val=k ∧ 0<k <;> by_cases hj' : j.val=k ∧ 0<k <;>
    simp_all [boundary]

 def select {n : ℕ} (row : Fin n) : V n → Option (Fin 4)
  | .inl _ => none
  | .inr (i,a) => if i=row then some a else none

 def ports {n : ℕ} (p : Pairing n) (t : Configuration n) (row : Fin n) :
    FreshGate.Ports (wiring p t row.val) (boundary row.val (Nat.le_of_lt row.isLt)) where
  port := fun a => .inr (row,a)
  select := select row
  select_port := fun a => by simp [select]
  of_some := by
    rintro (i|⟨i,a⟩) b h
    · simp [select] at h
    · by_cases hi : i=row
      · subst i; simpa [select] using h
      · simp [select,hi] at h
  old_none := by
    intro i
    by_cases hi : i.val < row.val
    · simp only [boundary,dite_eq_left hi,select]
      apply ite_eq_right
      intro he
      have hh := congrArg Fin.val he
      dsimp at hh
      omega
    · by_cases hh : i.val=row.val ∧ 0 < row.val
      · simp only [boundary,dite_eq_right hi,dite_eq_left hh,select]
        apply ite_eq_right
        intro he
        have hh := congrArg Fin.val he
        dsimp at hh
        omega
      · simp [boundary,hi,hh,select]
  edge_none := by
    rintro (i|⟨i,a⟩) (j|⟨j,b⟩) h
    · rfl
    · rfl
    · have hi := h.1
      simp only [select]
      apply ite_eq_right
      intro he; subst i; omega
    · have hi : i.val < row.val := by
        rcases h with ⟨_,hi,_⟩ | ⟨_,_,hij,hj,_⟩ | ⟨_,_,_,hi,_⟩ <;> omega
      simp only [select]
      apply ite_eq_right
      intro he; subst i; omega

section RowTransitions
variable {n : ℕ} (p : Pairing n) (t : Configuration n) (row : Fin n)

@[simp] lemma right_boundary : boundary row.val (Nat.le_of_lt row.isLt) row.succ = .inl row.succ := by
  simp [boundary]

lemma left_boundary_zero (h : row.val=0) :
    boundary row.val (Nat.le_of_lt row.isLt) row.castSucc = .inl row.castSucc := by
  simp [boundary,h]

lemma left_boundary_pos (h : 0 < row.val) :
    boundary row.val (Nat.le_of_lt row.isLt) row.castSucc = .inr (prev row h,3) := by
  simp [boundary,h,prev]

lemma left_support_zero (h : row.val=0) :
    ¬support p t row.val (Nat.le_of_lt row.isLt) row.castSucc := by
  have hh : row.castSucc=(0:Fin (n+1)) := Fin.ext h
  simp [support,h,hh]

lemma left_support_pos (h : 0 < row.val) :
    support p t row.val (Nat.le_of_lt row.isLt) row.castSucc ↔ (t (prev row h)).Occupied 3 := by
  simp [support,h,prev]

lemma boundary_step (i : Fin (n+1)) :
    (ports p t row).boundary row.castSucc row.succ i = boundary (row.val+1) row.isLt i := by
  have ha : row.castSucc≠row.succ := by intro hh; have he := congrArg Fin.val hh; dsimp at he; omega
  by_cases hia : i=row.castSucc
  · subst i
    simp [FreshGate.Ports.boundary,CompactGate.boundary,FreshGate.Ports.project,ports,boundary]
  · by_cases hib : i=row.succ
    · subst i
      simp [FreshGate.Ports.boundary,CompactGate.boundary,FreshGate.Ports.project,ports,boundary,ha.symm]
    · have hia' : i.val≠row.val := fun h => hia (Fin.ext h)
      have hib' : i.val≠row.val+1 := fun h => hib (Fin.ext h)
      have hlt : i.val < row.val+1 ↔ i.val < row.val := by omega
      have hp : ¬(i.val=row.val ∧ 0 < row.val) := by omega
      have hp' : ¬(i.val=row.val+1 ∧ 0 < row.val+1) := by omega
      simp only [FreshGate.Ports.boundary,CompactGate.boundary,ite_eq_right hia,ite_eq_right hib,
        FreshGate.Ports.project,boundary,hlt]
      by_cases hi : i.val < row.val <;> simp [hi,hia',hib']

lemma support_step (i : Fin (n+1)) :
    (if i=row.castSucc then (t row).Occupied 2 else
       if i=row.succ then (t row).Occupied 3 else support p t row.val (Nat.le_of_lt row.isLt) i) ↔
      support p t (row.val+1) row.isLt i := by
  have ha : row.castSucc≠row.succ := by intro hh; have he := congrArg Fin.val hh; dsimp at he; omega
  by_cases hia : i=row.castSucc
  · subst i; simp [support]
  · by_cases hib : i=row.succ
    · subst i; simp [support,ha.symm]
    · have hia' : i.val≠row.val := fun h => hia (Fin.ext h)
      have hib' : i.val≠row.val+1 := fun h => hib (Fin.ext h)
      have hlt : i.val < row.val+1 ↔ i.val < row.val := by omega
      have hp : ¬(i.val=row.val ∧ 0 < row.val) := by omega
      have hp' : ¬(i.val=row.val+1 ∧ 0 < row.val+1) := by omega
      simp only [ite_eq_right hia,ite_eq_right hib,support,hlt]
      by_cases hi : i.val < row.val <;> simp [hi,hia',hib']

lemma core_initial (i : Fin (n+1)) : (ports p t row).core (.inl i)=.inl (.inl i) := rfl
lemma core_box (i : Fin n) (a : Fin 4) : (ports p t row).core (.inr (i,a))=
    if i=row then .inr a else .inl (.inr (i,a)) := by
  by_cases hi : i=row <;> simp [FreshGate.Ports.core,ports,select,hi]

 abbrev nextWiring := (ports p t row).wiring (support p t row.val (Nat.le_of_lt row.isLt))
  row.castSucc row.succ (t row)

lemma next_initial (i j : Fin (n+1)) :
    nextWiring p t row (.inl i) (.inl j) ↔ wiring p t (row.val+1) (.inl i) (.inl j) := by
  rfl

lemma next_mixed (i : Fin (n+1)) (j : Fin n) (b : Fin 4) :
    nextWiring p t row (.inl i) (.inr (j,b)) ↔ wiring p t (row.val+1) (.inl i) (.inr (j,b)) := by
  by_cases hj : j=row
  · subst j
    simp only [nextWiring,FreshGate.Ports.wiring,core_initial,core_box,CompactGate.wiring]
    rw [right_boundary,right_support]
    by_cases hrow : row.val=0
    · rw [left_boundary_zero row hrow]
      simp [left_support_zero p t row hrow,wiring]
    · rw [left_boundary_pos row (by omega),left_support_pos p t row (by omega)]
      simp [wiring]
  · have hlt : j.val < row.val+1 ↔ j.val < row.val := by
      have hne : j.val≠row.val := fun he => hj (Fin.ext he)
      omega
    simp [nextWiring,FreshGate.Ports.wiring,core_initial,core_box,hj,CompactGate.wiring,wiring,hlt]

lemma next_new_new (a b : Fin 4) :
    nextWiring p t row (.inr (row,a)) (.inr (row,b)) ↔
      wiring p t (row.val+1) (.inr (row,a)) (.inr (row,b)) := by
  simp [nextWiring,FreshGate.Ports.wiring,core_box,CompactGate.wiring,wiring]

lemma next_new_old (j : Fin n) (hj : j≠row) (a b : Fin 4) :
    nextWiring p t row (.inr (row,a)) (.inr (j,b)) ↔
      wiring p t (row.val+1) (.inr (row,a)) (.inr (j,b)) := by
  simp only [nextWiring,FreshGate.Ports.wiring,core_box,ite_eq_right hj,CompactGate.wiring]
  rw [right_boundary]
  have hforward : ¬(row.val+1=j.val ∧ j.val < row.val+1) := by omega
  by_cases hrow : row.val=0
  · rw [left_boundary_zero row hrow]
    simp [wiring,hj.symm,hrow]
    omega
  · have hpos : 0 < row.val := by omega
    rw [left_boundary_pos row hpos,left_support_pos p t row hpos]
    by_cases he : j=prev row hpos
    · subst j
      have hback := prev_val_add row hpos
      have hf : ¬(row.val+1=(prev row hpos).val) := by omega
      simp [wiring,hj.symm,hback,hf,and_comm,and_left_comm]
    · have hb : ¬(j.val+1=row.val) := by
        intro hh
        apply he
        apply Fin.ext
        simp only [prev]
        omega
      simp [wiring,hj.symm,hb]
      omega

lemma next_old_old (i j : Fin n) (hi : i≠row) (hj : j≠row) (a b : Fin 4) :
    nextWiring p t row (.inr (i,a)) (.inr (j,b)) ↔
      wiring p t (row.val+1) (.inr (i,a)) (.inr (j,b)) := by
  have hi' : i.val≠row.val := fun he => hi (Fin.ext he)
  have hj' : j.val≠row.val := fun he => hj (Fin.ext he)
  have hli : i.val < row.val+1 ↔ i.val < row.val := by omega
  have hlj : j.val < row.val+1 ↔ j.val < row.val := by omega
  simp [nextWiring,FreshGate.Ports.wiring,core_box,hi,hj,CompactGate.wiring,wiring,hli,hlj]

lemma next_iff (v w : V n) : nextWiring p t row v w ↔ wiring p t (row.val+1) v w := by
  rcases v with i | ⟨i,a⟩ <;> rcases w with j | ⟨j,b⟩
  · exact next_initial p t row i j
  · exact next_mixed p t row i j b
  · constructor
    · intro h; exact symm ((next_mixed p t row j i a).mp (symm h))
    · intro h; exact symm ((next_mixed p t row j i a).mpr (symm h))
  · by_cases hi : i=row
    · subst i
      by_cases hj : j=row
      · subst j; exact next_new_new p t row a b
      · exact next_new_old p t row j hj a b
    · by_cases hj : j=row
      · subst j
        constructor
        · intro h; exact symm ((next_new_old p t row i hi b a).mp (symm h))
        · intro h; exact symm ((next_new_old p t row i hi b a).mpr (symm h))
      · exact next_old_old p t row i j hi hj a b

lemma next_eq : nextWiring p t row = wiring p t (row.val+1) := by
  funext v w
  exact propext (next_iff p t row v w)

end RowTransitions

variable {n : ℕ} (hn : 0<n) (p : Pairing n) (t : Configuration n)

def fullBoundary : Fin (n+1) → Vertex n :=
  Fin.lastCases (⟨n-1,by omega⟩,3) (fun i => (i,2))

def fullProject : V n → Vertex n
  | .inr v => v
  | .inl i => Fin.cases (⟨0,hn⟩,0) (fun j => (j,1)) i

lemma full_box {i j : Fin n} {a b : Fin 4}
    (h : wiring p t n (.inr (i,a)) (.inr (j,b))) : Wiring p t (i,a) (j,b) := by
  rcases h with ⟨hij,_,hab⟩ | ⟨ha,hb,hij,_,ht⟩ | ⟨hb,ha,hij,_,ht⟩
  · exact Or.inl ⟨hij,hab⟩
  · exact Or.inr (Or.inr (Or.inl ⟨ha,hb,hij,ht⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb,ha,hij,ht⟩))

lemma full_initial_zero (v : V n) : ¬ wiring p t n (.inl 0) v := by
  rcases v with i | ⟨j,a⟩
  · exact p.padBottom_not_adj_zero i
  · rintro ⟨_,he,_,_⟩
    have hh := congrArg Fin.val he
    simp at hh

lemma full_mixed {i : Fin (n+1)} {j : Fin n} {a : Fin 4}
    (h : wiring p t n (.inl i) (.inr (j,a))) :
    fullProject hn (.inl i)=(j,a) ∧ p.Occupied j := by
  obtain ⟨_,rfl,rfl,hp⟩ := h
  exact ⟨rfl,hp⟩

lemma full_map_edge (v w : V n) (h : wiring p t n v w) :
    Reach p t (fullProject hn v) (fullProject hn w) := by
  rcases v with i | ⟨i,a⟩ <;> rcases w with j | ⟨j,b⟩
  · induction i using Fin.cases with
    | zero => exact (p.padBottom_not_adj_zero j h).elim
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (p.padBottom_not_adj_zero' i.succ h).elim
      | succ j => exact .single (Or.inr (Or.inl ⟨rfl,rfl,(p.padBottom_adj_succ i j).mp h⟩))
  · rw [(full_mixed hn p t h).1]; exact .refl
  · have hh := (full_mixed hn p t (symm h)).1
    change Reach p t (i,a) (fullProject hn (.inl j))
    rw [hh]; exact .refl
  · exact .single (full_box p t h)

lemma full_inv_edge (v w : Vertex n) (h : Wiring p t v w) :
    Relation.ReflTransGen (wiring p t n) (.inr v) (.inr w) := by
  rcases v with ⟨i,a⟩; rcases w with ⟨j,b⟩
  rcases h with ⟨hij,hab⟩ | ⟨rfl,rfl,hp⟩ | ⟨ha,hb,hij,ht⟩ | ⟨hb,ha,hij,ht⟩
  · exact .single (Or.inl ⟨hij,i.isLt,hab⟩)
  · have hi : wiring p t n (.inr (i,1)) (.inl i.succ) := ⟨i.isLt,rfl,rfl,⟨j,hp⟩⟩
    have hij : wiring p t n (.inl i.succ) (.inl j.succ) := (p.padBottom_adj_succ i j).mpr hp
    have hj : wiring p t n (.inl j.succ) (.inr (j,1)) := ⟨j.isLt,rfl,rfl,⟨i,Pairing.adj_symm hp⟩⟩
    exact ((Relation.ReflTransGen.single hi).tail hij).tail hj
  · exact .single (Or.inr (Or.inl ⟨ha,hb,hij,j.isLt,ht⟩))
  · exact .single (Or.inr (Or.inr ⟨hb,ha,hij,i.isLt,ht⟩))

lemma full_map_used (v : V n) (h : Graph.Used (wiring p t n) v) :
    Graph.Used (Wiring p t) (fullProject hn v) := by
  obtain ⟨w,hw⟩ := h
  rcases v with i | ⟨i,a⟩ <;> rcases w with j | ⟨j,b⟩
  · induction i using Fin.cases with
    | zero => exact (p.padBottom_not_adj_zero j hw).elim
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (p.padBottom_not_adj_zero' i.succ hw).elim
      | succ j => exact ⟨(j,1),Or.inr (Or.inl ⟨rfl,rfl,(p.padBottom_adj_succ i j).mp hw⟩)⟩
  · obtain ⟨he,k,hpk⟩ := full_mixed hn p t hw
    rw [he]
    obtain ⟨_,rfl,rfl,_⟩ := hw
    exact ⟨(k,1),Or.inr (Or.inl ⟨rfl,rfl,hpk⟩)⟩
  · obtain ⟨_,rfl,rfl,⟨k,hpk⟩⟩ := hw
    exact ⟨(k,1),Or.inr (Or.inl ⟨rfl,rfl,hpk⟩)⟩
  · exact ⟨(j,b),full_box p t hw⟩

lemma full_inv_used (v : Vertex n) (h : Graph.Used (Wiring p t) v) :
    Graph.Used (wiring p t n) (.inr v) := by
  obtain ⟨⟨j,b⟩,hw⟩ := h
  rcases v with ⟨i,a⟩
  rcases hw with ⟨hij,hab⟩ | ⟨rfl,rfl,hp⟩ | ⟨ha,hb,hij,ht⟩ | ⟨hb,ha,hij,ht⟩
  · exact ⟨.inr (j,b),Or.inl ⟨hij,i.isLt,hab⟩⟩
  · exact ⟨.inl i.succ,i.isLt,rfl,rfl,⟨j,hp⟩⟩
  · exact ⟨.inr (j,b),Or.inr (Or.inl ⟨ha,hb,hij,j.isLt,ht⟩)⟩
  · exact ⟨.inr (j,b),Or.inr (Or.inr ⟨hb,ha,hij,i.isLt,ht⟩)⟩

lemma full_boundary (i : Fin (n+1)) : boundary n le_rfl i=.inr (fullBoundary hn i) := by
  induction i using Fin.lastCases with
  | last => simp [boundary,fullBoundary,hn]
  | cast i => simp [boundary,fullBoundary,i.isLt]

lemma full_retract (v : V n) (h : Graph.Used (wiring p t n) v) :
    Relation.ReflTransGen (wiring p t n) v (.inr (fullProject hn v)) := by
  cases v with
  | inr v => exact .refl
  | inl i =>
    induction i using Fin.cases with
    | zero => obtain ⟨w,hw⟩ := h; exact (full_initial_zero p t w hw).elim
    | succ i =>
      have hp : p.Occupied i := by
        obtain ⟨w,hw⟩ := h
        rcases w with j | ⟨j,b⟩
        · exact (p.padBottom_occupied_succ i).mp ⟨j,hw⟩
        · obtain ⟨_,he,rfl,hp⟩ := hw
          have hij : i=j := Fin.succ_injective _ he
          exact hij ▸ hp
      exact .single ⟨i.isLt,rfl,rfl,hp⟩

def fullEquiv : Graph.BoundaryEquiv (wiring p t n) (Wiring p t) (boundary n le_rfl) (fullBoundary hn) where
  toFun := fullProject hn
  invFun := Sum.inr
  map_edge := full_map_edge hn p t
  inv_edge := full_inv_edge p t
  map_boundary := fun i => by rw [full_boundary hn]; rfl
  inv_boundary := fun i => (full_boundary hn i).symm
  map_used := full_map_used hn p t
  inv_used := full_inv_used p t
  retract := full_retract hn p t
  inv_retract := fun _ _ => .refl

end PartialColumn
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ColumnSweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
namespace PartialColumn
section ColumnGeometry
open scoped Classical
section BoundaryTracking
variable {n : ℕ}

 def baseProject : V n → Fin (n+1)
  | .inl i => i
  | .inr _ => 0

lemma base_edge {p : Pairing n} {t : Configuration n} {v w : V n} (h : wiring p t 0 v w) :
    p.padBottom.Adj (baseProject v) (baseProject w) := by
  rcases v with i | ⟨i,a⟩ <;> rcases w with j | ⟨j,b⟩
  · exact h
  all_goals simp [wiring] at h

lemma base_used {p : Pairing n} {t : Configuration n} {v : V n}
    (h : Graph.Used (wiring p t 0) v) : v=.inl (baseProject v) := by
  obtain ⟨w,hw⟩ := h
  cases v with
  | inl i => rfl
  | inr v => cases w <;> simp [wiring] at hw

 def baseEquiv (p : Pairing n) (t : Configuration n) :
    Graph.BoundaryEquiv (wiring p t 0) p.padBottom.Adj (boundary 0 (Nat.zero_le n)) id where
  toFun := baseProject
  invFun := Sum.inl
  map_edge := fun _ _ h => .single (base_edge h)
  inv_edge := fun _ _ h => .single h
  map_boundary := fun i => by simp [baseProject]
  inv_boundary := fun i => by simp
  map_used := fun _ ⟨w,hw⟩ => ⟨baseProject w,base_edge hw⟩
  inv_used := fun _ ⟨w,hw⟩ => ⟨.inl w,hw⟩
  retract := fun _ hv => by rw [base_used hv]; exact .refl
  inv_retract := fun _ _ => .refl

lemma base_realizes (p : Pairing n) (t : Configuration n) :
    GraphRealizes (wiring p t 0) (boundary 0 (Nat.zero_le n)) p.padBottom :=
  (baseEquiv p t).symm.realizes p.padBottom.graphRealizes

 def gate (t : Configuration n) (row : Fin n) : Gate (n+1) :=
  ⟨row.castSucc,row.succ,by simp,t row⟩

 def circuit (t : Configuration n) : (k : ℕ) → k≤n → Circuit (n+1)
  | 0,_ => .nil
  | k+1,hk => .snoc (circuit t k (by omega)) (gate t ⟨k,hk⟩)

lemma circuit_support (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n) :
    Circuit.support p.padBottom (circuit t k hk) = support p t k hk := by
  induction k with
  | zero => funext i; simp [circuit,Circuit.support,support]
  | succ k ih =>
    funext i
    apply propext
    change (if i=(⟨k,hk⟩:Fin n).castSucc then (t ⟨k,hk⟩).Occupied 2 else
      if i=(⟨k,hk⟩:Fin n).succ then (t ⟨k,hk⟩).Occupied 3 else
      Circuit.support p.padBottom (circuit t k (by omega)) i) ↔ support p t (k+1) hk i
    rw [ih]
    exact support_step p t ⟨k,hk⟩ i

lemma circuit_sound (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n)
    (q : Pairing (n+1)) (he : Circuit.eval p.padBottom (circuit t k hk)=some q) :
    GraphRealizes (wiring p t k) (boundary k hk) q := by
  induction k generalizing q with
  | zero => have hq : p.padBottom=q := Option.some.inj he; subst q; exact base_realizes p t
  | succ k ih =>
    let row : Fin n := ⟨k,hk⟩
    let c := circuit t k (by omega)
    change (Circuit.eval p.padBottom c).bind
      (fun r => r.tileStep row.castSucc row.succ (by simp [row]) (t row))=some q at he
    cases hr : Circuit.eval p.padBottom c with
    | none => simp [hr] at he
    | some r =>
      have hstep : r.tileStep row.castSucc row.succ (by simp [row]) (t row)=some q := by
        simpa only [hr,Option.bind_some] using he
      have hp := ih (by omega) r hr
      have hs : support p t k (by omega)=r.Occupied := by
        rw [←circuit_support p t k (by omega)]
        exact (Circuit.eval_sound p.padBottom c r hr).2.2
      have hne : row.castSucc≠row.succ := by intro hh; have hf := congrArg Fin.val hh; dsimp at hf; omega
      have hc := ((graph_gate_step_iff hp row.castSucc row.succ (by simp) (t row) q).mpr hstep).2
      have hc' := (CompactGate.realizes_iff hp (boundary_injective k (by omega))
        row.castSucc row.succ hne (t row) q).mp hc
      rw [←hs] at hc'
      have hn := ((ports p t row).realizes_iff (boundary_injective k (by omega))
        (support p t k (by omega)) row.castSucc row.succ (t row) q).mp hc'
      change GraphRealizes (nextWiring p t row) ((ports p t row).boundary row.castSucc row.succ) q at hn
      rw [next_eq p t row,funext (boundary_step p t row)] at hn
      exact hn

lemma circuit_exists (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n)
    (hc : Circuit.Compatible p.padBottom (circuit t k hk))
    (hd : Graph.DrainsBoundary (wiring p t k) (boundary k hk)) :
    ∃ q, Circuit.eval p.padBottom (circuit t k hk)=some q := by
  induction k with
  | zero => exact ⟨p.padBottom,rfl⟩
  | succ k ih =>
    let row : Fin n := ⟨k,hk⟩
    let hkn : k≤n := by omega
    let c := circuit t k hkn
    change Circuit.Compatible p.padBottom c ∧
      (Circuit.support p.padBottom c row.castSucc ↔ (t row).Occupied 0) ∧
      (Circuit.support p.padBottom c row.succ ↔ (t row).Occupied 1) at hc
    obtain ⟨hc,hl,hr⟩ := hc
    have hdnext : Graph.DrainsBoundary (nextWiring p t row)
        ((ports p t row).boundary row.castSucc row.succ) := by
      rw [next_eq,funext (boundary_step p t row)]
      exact hd
    have hcompact := ((ports p t row).contraction (boundary_injective k hkn)
      (support p t k hkn) row.castSucc row.succ (t row)).drains_inv hdnext
    have hold := CompactGate.drains_local (wiring p t k) (boundary k hkn)
      (support p t k hkn) row.castSucc row.succ (t row) hcompact
    obtain ⟨r,he⟩ := ih hkn hc hold
    have hp := circuit_sound p t k hkn r he
    have hs : support p t k hkn=r.Occupied := by
      rw [←circuit_support]
      exact (Circuit.eval_sound p.padBottom c r he).2.2
    have hcomp : CutPatch.Compatible (r.cutShape row.castSucc row.succ) (t row) := by
      rw [r.cutShape_compatible]
      rw [circuit_support p t k hkn,hs] at hl hr
      exact ⟨hl,hr⟩
    have hne : row.castSucc≠row.succ := by
      intro hh; have hf := congrArg Fin.val hh; dsimp at hf; omega
    rw [hs] at hcompact
    have hfull := (CompactGate.contraction hp (boundary_injective k hkn)
      row.castSucc row.succ hne (t row)).drains_inv hcompact
    obtain ⟨q,hq⟩ := graph_gate_step_exists hp row.castSucc row.succ (by simp) (t row) hcomp hfull
    refine ⟨q,?_⟩
    change (Circuit.eval p.padBottom c).bind
      (fun r => r.tileStep row.castSucc row.succ (by simp) (t row))=some q
    have he' : Circuit.eval p.padBottom c=some r := he
    simpa only [he',Option.bind_some] using hq

lemma circuit_iff (p : Pairing n) (t : Configuration n) (k : ℕ) (hk : k≤n)
    (q : Pairing (n+1)) : Circuit.eval p.padBottom (circuit t k hk)=some q ↔
      Circuit.Compatible p.padBottom (circuit t k hk) ∧
      GraphRealizes (wiring p t k) (boundary k hk) q := by
  constructor
  · intro h
    exact ⟨(Circuit.eval_sound p.padBottom (circuit t k hk) q h).1,circuit_sound p t k hk q h⟩
  · rintro ⟨hc,hq⟩
    obtain ⟨r,hr⟩ := circuit_exists p t k hk hc hq.drainsBoundary
    have he := (circuit_sound p t k hk r hr).unique hq
    exact he ▸ hr

end BoundaryTracking

section InputCompatibility
variable {n : ℕ} (p : Pairing n) (t : Configuration n)

def inputCompatible (row : Fin n) : Prop :=
  (support p t row.val (Nat.le_of_lt row.isLt) row.castSucc ↔ (t row).Occupied 0) ∧
  (support p t row.val (Nat.le_of_lt row.isLt) row.succ ↔ (t row).Occupied 1)

lemma circuit_compatible_iff (k : ℕ) (hk : k≤n) :
    Circuit.Compatible p.padBottom (circuit t k hk) ↔
      ∀ row : Fin n, row.val<k → inputCompatible p t row := by
  induction k with
  | zero => simp [circuit,Circuit.Compatible]
  | succ k ih =>
    change (Circuit.Compatible p.padBottom (circuit t k (by omega)) ∧
      (Circuit.support p.padBottom (circuit t k (by omega)) (⟨k,hk⟩:Fin n).castSucc ↔ (t ⟨k,hk⟩).Occupied 0) ∧
      (Circuit.support p.padBottom (circuit t k (by omega)) (⟨k,hk⟩:Fin n).succ ↔ (t ⟨k,hk⟩).Occupied 1)) ↔ _
    rw [ih,circuit_support]
    change ((∀ row : Fin n, row.val<k → inputCompatible p t row) ∧ inputCompatible p t ⟨k,hk⟩) ↔ _
    constructor
    · rintro ⟨hc,hr⟩ row hrow
      by_cases h : row.val<k
      · exact hc row h
      · have he : row=(⟨k,hk⟩:Fin n) := Fin.ext (by dsimp; omega)
        exact he ▸ hr
    · intro hc
      exact ⟨fun row hr => hc row (by omega),hc ⟨k,hk⟩ (by simp)⟩

structure InputConditions : Prop where
  west : ∀ i, (t i).Occupied 1 ↔ p.Occupied i
  south : ∀ i, i.val=0 → ¬(t i).Occupied 0
  glued : ∀ i j, i.val+1=j.val → ((t i).Occupied 3 ↔ (t j).Occupied 0)

lemma all_input_iff : (∀ row, inputCompatible p t row) ↔ InputConditions p t := by
  constructor
  · intro hc
    constructor
    · intro i; exact ((right_support p t i).symm.trans (hc i).2).symm
    · intro i hi hocc
      exact left_support_zero p t i hi ((hc i).1.mpr hocc)
    · intro i j hij
      have hj : 0<j.val := by omega
      have he : prev j hj=i := Fin.ext (by simp only [prev]; omega)
      have hh := (left_support_pos p t j hj).symm.trans (hc j).1
      simpa only [he] using hh
  · intro hc row
    refine ⟨?_,(right_support p t row).trans (hc.west row).symm⟩
    by_cases hz : row.val=0
    · exact ⟨fun h => (left_support_zero p t row hz h).elim,
        fun h => (hc.south row hz h).elim⟩
    · have hp : 0 < row.val := by omega
      exact (left_support_pos p t row hp).trans (hc.glued (prev row hp) row (prev_val_add row hp))

lemma full_compatible_iff : Circuit.Compatible p.padBottom (circuit t n le_rfl) ↔ InputConditions p t := by
  rw [circuit_compatible_iff]
  exact (show (∀ row : Fin n, row.val<n → inputCompatible p t row) ↔ ∀ row, inputCompatible p t row
    from ⟨fun h row => h row row.isLt, fun h row _ => h row⟩).trans (all_input_iff p t)

end InputCompatibility

variable {n : ℕ} (hn : 0<n) (p q : Pairing n) (t : Configuration n)

lemma fullBoundary_injective : Function.Injective (fullBoundary hn) := by
  intro i j he
  apply boundary_injective n le_rfl
  rw [full_boundary hn,full_boundary hn,he]

lemma east_used (i : Fin n) : Graph.Used (Wiring p t) (i,2) ↔ (t i).Occupied 2 := by
  constructor
  · rintro ⟨⟨j,b⟩,hw⟩
    rcases hw with ⟨_,ht⟩ | hh | hh | hh
    · exact ⟨b,ht⟩
    all_goals simp at hh
  · rintro ⟨b,hb⟩; exact ⟨(i,b),Or.inl ⟨rfl,hb⟩⟩

lemma north_isolated (i : Fin n) (hi : i.val+1=n) (ht : ¬(t i).Occupied 3)
    (v : Vertex n) : ¬Wiring p t (i,3) v := by
  intro hw
  rcases hw with ⟨_,ht'⟩ | hh | ⟨_,_,hij,_⟩ | hh
  · exact ht ⟨v.2,ht'⟩
  · simp at hh
  · have hv:=v.1.isLt; dsimp at hij; omega
  · simp at hh

lemma graph_of_realizes (h : Realizes p q t) : GraphRealizes (Wiring p t) (fullBoundary hn) q.padTop := by
  constructor
  · intro v w hvw
    obtain ⟨i,hi,hr⟩ := h.no_loop v w hvw
    exact ⟨i.castSucc,(q.padTop_occupied_castSucc i).mpr hi,by simpa [fullBoundary,Reach] using hr⟩
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      have hi : (⟨n-1,by omega⟩:Fin n).val+1=n := by dsimp; omega
      have hh (v : Vertex n) := Relation.reflTransGen_iff_eq (b:=v) (north_isolated p t ⟨n-1,by omega⟩ hi (h.north _ hi))
      induction j using Fin.lastCases with
      | last => exact ⟨fun _ => Or.inl rfl,fun _ => .refl⟩
      | cast j =>
        simp only [fullBoundary,Fin.lastCases_last,Fin.lastCases_castSucc]
        rw [hh _]
        simp [(Fin.castSucc_ne_last j).symm]
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [fullBoundary,Fin.lastCases_last,Fin.lastCases_castSucc]
        constructor
        · intro hr
          have hi : (⟨n-1,by omega⟩:Fin n).val+1=n := by dsimp; omega
          have he := (Relation.reflTransGen_iff_eq
            (north_isolated p t ⟨n-1,by omega⟩ hi (h.north _ hi))).mp (reach_symm hr)
          have hf := congrArg Prod.snd he
          simp at hf
        · intro he; simp at he
      | cast j =>
        simp only [fullBoundary,Fin.lastCases_castSucc,Fin.castSucc_inj,Pairing.padTop_adj_castSucc]
        by_cases hij : i=j
        · subst j; exact ⟨fun _ => Or.inl rfl,fun _ => .refl⟩
        · simp only [hij,false_or]
          exact (h.output i j hij).symm

lemma realizes_of_graph (hc : InputConditions p t)
    (h : GraphRealizes (Wiring p t) (fullBoundary hn) q.padTop) : Realizes p q t := by
  refine ⟨hc.west,?_,hc.south,?_,hc.glued,?_,?_⟩
  · intro i
    have hh := h.boundary_used_iff (fullBoundary_injective hn) i.castSucc
    simpa only [fullBoundary,Fin.lastCases_castSucc,east_used,Pairing.padTop_occupied_castSucc] using hh
  · intro i hi ht
    have he : i=(⟨n-1,by omega⟩:Fin n) := Fin.ext (by dsimp; omega)
    obtain ⟨b,hb⟩ := ht
    have hu : Graph.Used (Wiring p t) (fullBoundary hn (Fin.last n)) := by
      rw [he] at hb
      simp only [fullBoundary,Fin.lastCases_last]
      exact ⟨(⟨n-1,by omega⟩,b),Or.inl ⟨rfl,hb⟩⟩
    exact q.padTop_not_occupied_last ((h.boundary_used_iff (fullBoundary_injective hn) _).mp hu)
  · intro v w hvw
    obtain ⟨i,hi,hr⟩ := h.no_loop v w hvw
    induction i using Fin.lastCases with
    | last => exact (q.padTop_not_occupied_last hi).elim
    | cast i => exact ⟨i,(q.padTop_occupied_castSucc i).mp hi,by simpa [fullBoundary,Reach] using hr⟩
  · intro i j hij
    have hh := h.reach i.castSucc j.castSucc
    simpa only [fullBoundary,Fin.lastCases_castSucc,Fin.castSucc_inj,Pairing.padTop_adj_castSucc,
      hij,false_or,Reach] using hh.symm

lemma realizes_graph_iff : Realizes p q t ↔ InputConditions p t ∧
    GraphRealizes (Wiring p t) (fullBoundary hn) q.padTop :=
  ⟨fun h => ⟨⟨h.west,h.south,h.glued⟩,graph_of_realizes hn p q t h⟩,
   fun h => realizes_of_graph hn p q t h.1 h.2⟩

include hn in
lemma column_eval_iff : Circuit.eval p.padBottom (circuit t n le_rfl)=some q.padTop ↔ Realizes p q t := by
  rw [circuit_iff,full_compatible_iff,(fullEquiv hn p t).realizes_iff]
  exact (realizes_graph_iff hn p q t).symm

end ColumnGeometry

open Finset
open scoped Classical

end PartialColumn
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ColumnSew
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

 
def BareColumn {n : ℕ} (t : Configuration n) (v w : Vertex n) : Prop :=
  (v.1=w.1 ∧ (t v.1).Adj v.2 w.2) ∨
  (v.2=3 ∧ w.2=0 ∧ v.1.val+1=w.1.val ∧ (t v.1).Occupied 3) ∨
  (w.2=3 ∧ v.2=0 ∧ w.1.val+1=v.1.val ∧ (t w.1).Occupied 3)

namespace ColumnSew
variable {n : ℕ} (p : Pairing n) (t : Configuration n)

def graph : Sum (Fin n) (Vertex n) → Sum (Fin n) (Vertex n) → Prop :=
  Patch.glued p.Adj (BareColumn t) id (fun i=>(i,1)) p.Occupied

def project : Sum (Fin n) (Vertex n) → Vertex n
  | .inl i => (i,1)
  | .inr v => v

lemma bare_sub {v w : Vertex n} (h : BareColumn t v w) : Wiring p t v w := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

lemma west (i : Fin n) (hi : p.Occupied i) :
    graph p t (.inl i) (.inr (i,1)) := ⟨i,hi,rfl,rfl⟩

lemma west' (i : Fin n) (hi : p.Occupied i) :
    graph p t (.inr (i,1)) (.inl i) := ⟨i,hi,rfl,rfl⟩

lemma project_edge {v w} (h : graph p t v w) :
    Relation.ReflTransGen (Wiring p t) (project v) (project w) := by
  cases v with
  | inl i =>
    cases w with
    | inl j => exact .single (Or.inr (Or.inl ⟨rfl,rfl,h⟩))
    | inr w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact .refl
  | inr v =>
    cases w with
    | inl j => obtain ⟨i,hi,rfl,rfl⟩ := h; exact .refl
    | inr w => exact .single (bare_sub p t h)

lemma include_edge {v w} (h : Wiring p t v w) :
    Relation.ReflTransGen (graph p t) (.inr v) (.inr w) := by
  rcases h with h | h | h | h
  · exact .single (Or.inl h)
  · rcases v with ⟨i,a⟩; rcases w with ⟨j,b⟩
    obtain ⟨rfl,rfl,hij⟩ := h
    exact ((Relation.ReflTransGen.single (west' p t i ⟨j,hij⟩)).tail (show graph p t (.inl i) (.inl j) from hij)).tail
      (west p t j ⟨i,Pairing.adj_symm hij⟩)
  · exact .single (Or.inr (Or.inl h))
  · exact .single (Or.inr (Or.inr h))

lemma old_used (i : Fin n) (hi : Graph.Used (graph p t) (.inl i)) : p.Occupied i := by
  obtain ⟨j,hj⟩ := hi
  cases j with
  | inl j => exact ⟨j,hj⟩
  | inr j => obtain ⟨i,hi,rfl,rfl⟩ := hj; exact hi

lemma wiring_west_used (i : Fin n) (hi : p.Occupied i) :
    Graph.Used (Wiring p t) (i,1) := by
  obtain ⟨j,hj⟩ := hi
  exact ⟨(j,1),Or.inr (Or.inl ⟨rfl,rfl,hj⟩)⟩

lemma project_used (v) (hv : Graph.Used (graph p t) v) :
    Graph.Used (Wiring p t) (project v) := by
  cases v with
  | inl i => exact wiring_west_used p t i (old_used p t i hv)
  | inr v =>
    obtain ⟨w,hw⟩ := hv
    cases w with
    | inl i => obtain ⟨i,hi,rfl,rfl⟩ := hw; exact wiring_west_used p t i hi
    | inr w => exact ⟨w,bare_sub p t hw⟩

lemma include_used (v : Vertex n) (hv : Graph.Used (Wiring p t) v) :
    Graph.Used (graph p t) (.inr v) := by
  obtain ⟨w,h⟩ := hv
  rcases h with h | h | h | h
  · exact ⟨.inr w,Or.inl h⟩
  · rcases v with ⟨i,a⟩; rcases w with ⟨j,b⟩
    obtain ⟨rfl,rfl,hij⟩ := h
    exact ⟨.inl i,west' p t i ⟨j,hij⟩⟩
  · exact ⟨.inr w,Or.inr (Or.inl h)⟩
  · exact ⟨.inr w,Or.inr (Or.inr h)⟩

 

def equivalence : Graph.BoundaryEquiv (graph p t) (Wiring p t)
    (fun i=>.inr (i,2)) (fun i=>(i,2)) where
  toFun := project
  invFun := Sum.inr
  map_edge := fun _ _ => project_edge p t
  inv_edge := fun _ _ => include_edge p t
  map_boundary := fun _=>rfl
  inv_boundary := fun _=>rfl
  map_used := project_used p t
  inv_used := include_used p t
  retract := by
    intro v hv
    cases v with
    | inl i => exact .single (west p t i (old_used p t i hv))
    | inr v => exact .refl
  inv_retract := fun _ _=>.refl

end ColumnSew

 
structure ColumnCompatible {n : ℕ} (west : Fin n → Prop) (t : Configuration n) : Prop where
  west : ∀ i, (t i).Occupied 1 ↔ west i
  south : ∀ i, i.val=0 → ¬(t i).Occupied 0
  north : ∀ i, i.val+1=n → ¬(t i).Occupied 3
  glued : ∀ i j, i.val+1=j.val → ((t i).Occupied 3 ↔ (t j).Occupied 0)

lemma realizes_iff_column_graph {n : ℕ} (p q : Pairing n) (t : Configuration n) :
    Realizes p q t ↔ ColumnCompatible p.Occupied t ∧
      GraphRealizes (Wiring p t) (fun i=>(i,2)) q := by
  constructor
  · intro h
    refine ⟨⟨h.west,h.south,h.north,h.glued⟩,h.no_loop,?_⟩
    intro i j
    by_cases hij : i=j
    · subst j; exact ⟨fun _=>Or.inl rfl,fun _=>.refl⟩
    · simpa only [Reach,hij,false_or] using (h.output i j hij).symm
  · rintro ⟨hc,h⟩
    refine ⟨hc.west,?_,hc.south,hc.north,hc.glued,h.no_loop,?_⟩
    · intro i
      exact (PartialColumn.east_used p t i).symm.trans
        (h.boundary_used_iff (fun _ _ he=>congrArg Prod.fst he) i)
    · intro i j hij
      simpa only [Reach,hij,false_or] using (h.reach i j).symm



lemma realizes_exists_of_drains {n : ℕ} (hn : 0<n) (p : Pairing n) (t : Configuration n)
    (hc : ColumnCompatible p.Occupied t)
    (hd : Graph.DrainsBoundary (Wiring p t) (fun i=>(i,2))) :
    ∃ q, Realizes p q t := by
  have hd' : Graph.DrainsBoundary (Wiring p t) (PartialColumn.fullBoundary hn) := by
    intro v w hvw
    obtain ⟨i,hi⟩ := hd v w hvw
    exact ⟨i.castSucc,by simpa only [PartialColumn.fullBoundary,Fin.lastCases_castSucc] using hi⟩
  have hc' := (PartialColumn.full_compatible_iff p t).mpr
    (show PartialColumn.InputConditions p t from ⟨hc.west,hc.south,hc.glued⟩)
  obtain ⟨q,hq⟩ := PartialColumn.circuit_exists p t n le_rfl hc'
    ((PartialColumn.fullEquiv hn p t).symm.drains hd')
  have hs := (Circuit.eval_sound p.padBottom (PartialColumn.circuit t n le_rfl) q hq).2.2
  have hlast : ¬q.Occupied (Fin.last n) := by
    rw [←hs,PartialColumn.circuit_support]
    simp only [PartialColumn.support,Fin.val_last,lt_self_iff_false,dite_false,
      true_and,dite_eq_left hn]
    exact hc.north _ (by dsimp; omega)
  let q' := q.restrict Fin.castSuccOrderEmb
  refine ⟨q',(PartialColumn.column_eval_iff hn p q' t).mp ?_⟩
  rw [Pairing.padTop_restrict q hlast]
  exact hq

end

 

 

noncomputable section
open scoped Classical BigOperators

 

namespace ColumnChain
variable {n : ℕ}

def Vertices : List (Configuration n) → Type
  | [] => Fin n
  | _::ts => Sum (Vertices ts) (Vertex n)

def boundary : (ts : List (Configuration n)) → Fin n → Vertices ts
  | [] => id
  | _::_ => fun i => .inr (i,2)

def support (p : Pairing n) : List (Configuration n) → Fin n → Prop
  | [] => p.Occupied
  | t::_ => fun i => (t i).Occupied 2

def wiring (p : Pairing n) : (ts : List (Configuration n)) → Vertices ts → Vertices ts → Prop
  | [] => p.Adj
  | t::ts => Patch.glued (wiring p ts) (BareColumn t) (boundary ts)
      (fun i=>(i,1)) (support p ts)

def Compatible (p : Pairing n) : List (Configuration n) → Prop
  | [] => True
  | t::ts => Compatible p ts ∧ ColumnCompatible (support p ts) t

def Runs (p : Pairing n) : List (Configuration n) → Pairing n → Prop
  | [],q => p=q
  | t::ts,q => ∃ r, Runs p ts r ∧ Realizes r q t

lemma runs_sound (p : Pairing n) (ts : List (Configuration n)) (q : Pairing n)
    (h : Runs p ts q) : Compatible p ts ∧
      GraphRealizes (wiring p ts) (boundary ts) q ∧ support p ts=q.Occupied := by
  induction ts generalizing q with
  | nil =>
    have he : p=q := h
    subst q
    exact ⟨trivial,p.graphRealizes,rfl⟩
  | cons t ts ih =>
    obtain ⟨r,hr,hq⟩ := h
    obtain ⟨hc,hg,hs⟩ := ih r hr
    obtain ⟨hct,hgt⟩ := (realizes_iff_column_graph r q t).mp hq
    refine ⟨⟨hc,by simpa only [hs] using hct⟩,?_,?_⟩
    · change GraphRealizes (Patch.glued (wiring p ts) (BareColumn t) (boundary ts)
        (fun i=>(i,1)) (support p ts)) (fun i=>.inr (i,2)) q
      rw [hs,hg.substitute_iff]
      exact (ColumnSew.equivalence r t).symm.realizes hgt
    · funext i
      exact propext (hq.east i)

end ColumnChain
end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedTail
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.cutGraph_isSymm _root_.OAI.CriticalStrip.Diagram.Pairing.stepWiring_isSymm _root_.OAI.CriticalStrip.Diagram.PartialColumn.wiring_symm _root_.OAI.CriticalStrip.Diagram.spectralFieldCharZero
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



def nodalScalar {n : ℕ} (i : Fin n) : SpectralField n :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
    (Fin.snoc spectralA (deletionBeta i))
      (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))

def nodalVacuum {n : ℕ} (i : Fin n) (p : Pairing (n+1)) : SpectralField n :=
  nodalScalar i * normalizedVacuum (nodalWeights i) p

 

def rationalVacuum (n : ℕ) (p : Pairing n) : SpectralField n :=
  spectralNormalization n * normalizedVacuum (spectralWeights n) p

 

def rationalNodalPolynomial (n : ℕ) (p : Pairing (n+1)) : Polynomial (SpectralField n) :=
  if p.Occupied (Fin.last n) then
    Lagrange.interpolate univ deletionBeta
      (fun i => nodalVacuum i p / torusSin (deletionNode i))
  else
    Polynomial.C (rationalVacuum n (p.restrict Fin.castSuccOrderEmb)) *
      Lagrange.nodal univ deletionBeta +
        Lagrange.interpolate univ deletionBeta (fun i => nodalVacuum i p)

 

def rationalInterpolant (n : ℕ) (p : Pairing (n+1)) : SpectralField (n+1) :=
  (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1) *
    (rationalNodalPolynomial n p).eval₂ (liftSpectral n) (spectralA (Fin.last n))



end
end CriticalStrip.Diagram

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






lemma rho_eq_inv_two_C : rho=1/(2*C) := by
  rw [rho,C,lambda,Real.cos_pi_div_eight]
  congr 1
  ring

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

lemma rho_eq_two_c_d : rho=2*c*d := by
  have hc : 2*C*c=d := by
    have h₁:=Real.cos_add lambda (3*lambda)
    have h₂:=Real.cos_sub lambda (3*lambda)
    have he₁ : lambda+3*lambda=Real.pi/2 := by simp [lambda]; ring
    have he₂ : lambda-3*lambda=-(2*lambda) := by ring
    rw [he₁,Real.cos_pi_div_two] at h₁
    rw [he₂,Real.cos_neg] at h₂
    change 0=C*c-Real.sin lambda*Real.sin (3*lambda) at h₁
    change d=C*c+Real.sin lambda*Real.sin (3*lambda) at h₂
    linarith
  rw [rho_eq_inv_two_C]
  apply (div_eq_iff (by intro h; rw [h,zero_mul] at hc; exact d_ne_zero hc.symm)).mpr
  linear_combination -2*d*hc-2*d_sq






open scoped Classical


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

@[simp] theorem rationalInterpolant_eq_lastValue (n : ℕ) :
    rationalInterpolant n =
      lastValue (liftSpectral n) (spectralA (Fin.last n))
        (torusSin (variableF (Fin.last n))) (rationalNodalPolynomial n) := by
  funext p
  simp only [rationalInterpolant, lastValue]
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

@[simp] lemma torusSin_one (n : ℕ) : torusSin (1:SpectralField n)=0 := by
  simp [torusSin]

lemma sin_two_lambda_eq_d : Real.sin (2*lambda)=d := by
  rw [show 2*lambda=Real.pi/4 by simp [lambda]; ring,d,
    show 2*lambda=Real.pi/4 by simp [lambda]; ring,Real.sin_pi_div_four,Real.cos_pi_div_four]

lemma sin_five_lambda_eq : Real.sin (5*lambda)=Real.sin (3*lambda) := by
  rw [show 5*lambda=Real.pi-3*lambda by simp [lambda]; ring,Real.sin_pi_sub]








open Finset
open scoped Classical

 
def vacantBottomExtension {M : Type*} [Zero M] {n : ℕ}
    (v : Pairing n → M) (p : Pairing (n+1)) : M :=
  if p.Occupied 0 then 0 else v (p.restrict (Fin.succOrderEmb n))

@[simp] theorem vacantBottomExtension_padBottom {M : Type*} [Zero M] {n : ℕ}
    (v : Pairing n → M) (p : Pairing n) : vacantBottomExtension v p.padBottom = v p := by
  simp only [vacantBottomExtension, Pairing.padBottom_not_occupied_zero, ite_false]
  simp [Pairing.padBottom, Pairing.restrict_map]

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
open scoped BigOperators Classical

 

abbrev SourcePairing (n : ℕ) := {p : Pairing (n+1) // p.Occupied (Fin.last n)}

@[simp] lemma SourcePairing.occupied {n : ℕ} (p : SourcePairing n) :
    p.val.Occupied (Fin.last n) := p.property

lemma SourcePairing.ne_empty {n : ℕ} (p : SourcePairing n) : p.val ≠ empty (n+1) := by
  intro h
  exact empty_not_occupied (Fin.last n) (h ▸ p.property)

def sourceTopEquiv (n : ℕ) : SourcePairing n ≃ Pairing.TopOccupiedNonempty n where
  toFun p := ⟨⟨p.val, p.ne_empty⟩, not_not.mpr p.property⟩
  invFun p := ⟨p.val.val, not_not.mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sourceTopSplit (n : ℕ) : NonemptyPairing n ⊕ SourcePairing n ≃ NonemptyPairing (n+1) :=
  (Equiv.sumCongr (Equiv.refl _) (sourceTopEquiv n)).trans (Pairing.nonemptyTopSplit n)

@[simp] lemma sourceTopSplit_inl {n : ℕ} (p : NonemptyPairing n) :
    sourceTopSplit n (Sum.inl p) = Pairing.nonemptyPadTop p := rfl

@[simp] lemma sourceTopSplit_inr_val {n : ℕ} (p : SourcePairing n) :
    (sourceTopSplit n (Sum.inr p)).val = p.val := rfl



def vacantTopEquiv (n : ℕ) :
    Pairing n ≃ {p : Pairing (n+1) // ¬p.Occupied (Fin.last n)} where
  toFun p := ⟨p.padTop, p.padTop_not_occupied_last⟩
  invFun p := p.val.restrict Fin.castSuccOrderEmb
  left_inv _ := Pairing.restrict_map _ _
  right_inv p := Subtype.ext (Pairing.padTop_restrict _ p.property)

def pairingTopSplit (n : ℕ) : Pairing n ⊕ SourcePairing n ≃ Pairing (n+1) :=
  (Equiv.sumCongr (vacantTopEquiv n)
    (Equiv.subtypeEquivRight (fun _ => not_not.symm))).trans
      (Equiv.sumCompl (fun p : Pairing (n+1) => ¬p.Occupied (Fin.last n)))

@[simp] lemma pairingTopSplit_inl {n : ℕ} (p : Pairing n) :
    pairingTopSplit n (Sum.inl p) = p.padTop := rfl

@[simp] lemma pairingTopSplit_inr {n : ℕ} (p : SourcePairing n) :
    pairingTopSplit n (Sum.inr p) = p.val := rfl



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

def join {n : ℕ} (p q : Pairing n) (i j : Fin n) : Prop := p.Adj i j ∨ q.Adj i j



def GluesAt {n : ℕ} (root : Fin n) (p q : Pairing n) : Prop :=
  p.Occupied root ∧ (∀ i, p.Occupied i ↔ q.Occupied i) ∧ Graph.DrainsAt (join p q) root

end Pairing



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthMerging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators







def reflectionMonomial (n : ℕ) : Multiplicative (Fin n → ℤ) →* Laurent n where
  toFun e := monomialL (-e.toAdd) (phase ^ (3 * ∑ i, e.toAdd i))
  map_one' := by simp [monomialL]; rfl
  map_mul' e f := by
    change monomialL (-(e.toAdd+f.toAdd))
        (phase ^ (3 * ∑ i, (e.toAdd i+f.toAdd i))) = _
    rw [Finset.sum_add_distrib, mul_add, zpow_add₀ phase_ne_zero, neg_add]
    exact (AddMonoidAlgebra.single_mul_single _ _ _ _).symm

def reflectLaurent (n : ℕ) : Laurent n →+* Laurent n :=
  (AddMonoidAlgebra.lift ℂ (Laurent n) (Fin n → ℤ) (reflectionMonomial n)).toRingHom

@[simp] lemma reflectLaurent_monomial {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    reflectLaurent n (monomialL e z) = monomialL (-e) (z * phase ^ (3 * ∑ i, e i)) := by
  change AddMonoidAlgebra.lift ℂ _ _ (reflectionMonomial n) (AddMonoidAlgebra.single e z) = _
  rw [AddMonoidAlgebra.lift_single]
  change z • AddMonoidAlgebra.single (-e) _ = AddMonoidAlgebra.single (-e) _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul]
  rfl

lemma reflectLaurent_involutive (n : ℕ) : Function.Involutive (reflectLaurent n) := by
  have h : (reflectLaurent n).comp (reflectLaurent n) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change reflectLaurent n (reflectLaurent n (monomialL _ _)) = monomialL _ _
    all_goals rw [reflectLaurent_monomial, reflectLaurent_monomial]
    all_goals simp only [neg_neg, Pi.neg_apply, Finset.sum_neg_distrib, mul_neg,
      mul_assoc, ←zpow_add₀ phase_ne_zero, add_neg_cancel, zpow_zero, mul_one]
  intro f
  exact DFunLike.congr_fun h f

def reflectSpectral (n : ℕ) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing n) (SpectralField n)).comp (reflectLaurent n))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (reflectLaurent_involutive n).injective)

@[simp] lemma reflectSpectral_evalLaurent {n : ℕ} (f : Laurent n) :
    reflectSpectral n (evalLaurent f) = evalLaurent (reflectLaurent n f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma reflectSpectral_const (n : ℕ) (z : ℂ) :
    reflectSpectral n (constF n z) = constF n z := by
  have hc : constF n z = evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc, reflectSpectral_evalLaurent]
  change evalLaurent (reflectLaurent n (monomialL 0 z)) = evalLaurent (monomialL 0 z)
  rw [reflectLaurent_monomial]
  simp

@[simp] lemma reflectSpectral_variable {n : ℕ} (i : Fin n) :
    reflectSpectral n (variableF i) = constF n phase ^ 3 / variableF i := by
  change reflectSpectral n (evalLaurent (monomialL (variableExponent i) 1)) = _
  rw [reflectSpectral_evalLaurent, reflectLaurent_monomial]
  simp only [variableExponent, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, one_mul, mul_one]
  change evalLaurent (monomialL (-variableExponent i) (phase^3)) = _
  rw [evalLaurent, map_monomialL_neg_variable]
  simp [constF, div_eq_mul_inv]

@[simp] lemma reflectSpectral_torusSin {n : ℕ} (z : SpectralField n) :
    reflectSpectral n (torusSin z) = torusSin (reflectSpectral n z) := by
  simp [torusSin, map_div₀, map_inv₀, map_ofNat]

@[simp] lemma reflectSpectral_torusCos {n : ℕ} (z : SpectralField n) :
    reflectSpectral n (torusCos z) = torusCos (reflectSpectral n z) := by
  simp [torusCos, map_div₀, map_inv₀, map_ofNat]

@[simp] lemma reflectSpectral_torusL {n : ℕ} (z : SpectralField n) :
    reflectSpectral n (torusL z) = torusL (reflectSpectral n z) := by simp [torusL]

@[simp] lemma reflectSpectral_torusWeights {n : ℕ} (z : SpectralField n) :
    (torusWeights z).map (reflectSpectral n) = torusWeights (reflectSpectral n z) := by
  simp [Weights.map, torusWeights, map_div₀]

@[simp] lemma reflectSpectral_spectralA {n : ℕ} (i : Fin n) :
    reflectSpectral n (spectralA i) = spectralA i := by
  simp only [spectralA, reflectSpectral_torusCos, map_div₀, map_pow,
    reflectSpectral_const, reflectSpectral_variable]
  unfold torusCos
  field_simp [variableF_ne_zero, constF_phase_ne_zero]
  ring

@[simp] lemma reflectSpectral_normalization (n : ℕ) :
    reflectSpectral n (spectralNormalization n) = spectralNormalization n := by
  simp only [spectralNormalization, map_scalarNormalization, reflectSpectral_const,
    reflectSpectral_spectralA]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitProjection
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

@[simp] lemma insertCup_occupied {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬p.Occupied a) (hb : ¬p.Occupied b) (i : Fin n) :
    (p.insertCup a b hab ha hb).Occupied i ↔ i=a ∨ i=b ∨ p.Occupied i := by
  simp [Occupied,insertCup_adj,exists_or]

end Pairing






lemma sin_lambda_eq_c : Real.sin lambda = c := by
  rw [← Real.cos_pi_div_two_sub]
  congr 1
  unfold lambda
  ring

lemma sin_three_lambda_eq_C : Real.sin (3*lambda) = C := by
  rw [← Real.cos_pi_div_two_sub]
  congr 1
  unfold lambda
  ring

lemma sin_four_lambda_eq_one : Real.sin (4*lambda)=1 := by
  rw [show 4*lambda=Real.pi/2 by unfold lambda; ring,Real.sin_pi_div_two]

lemma d_mul_c_div_C : d*c/C=rho^2 := by
  have hr := rho_eq_two_c_d
  have hC := rho_eq_inv_two_C
  calc
    d*c/C = (rho/2)/C := by rw [hr]; ring
    _ = rho*(1/(2*C)) := by ring
    _ = rho^2 := by rw [←hC]; ring

lemma d_sq_div_C : d^2/C=rho := by
  rw [d_sq,rho_eq_inv_two_C]
  ring

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ProjectionInjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators



def extendSource {K : Type*} [Zero K] {n : ℕ} (v : SourcePairing n → K) : Pairing (n+1) → K :=
  fun p => if h : p.Occupied (Fin.last n) then v ⟨p,h⟩ else 0

@[simp] lemma extendSource_apply {K : Type*} [Zero K] {n : ℕ}
    (v : SourcePairing n → K) (p : SourcePairing n) : extendSource v p.val=v p := by
  simp [extendSource,p.property]






def twistedReflectionMonomial {n : ℕ} (k : Fin n → ℤ) :
    Multiplicative (Fin n → ℤ) →* Laurent n where
  toFun e := monomialL (-e.toAdd) (∏ i, phase ^ (k i * e.toAdd i))
  map_one' := by simp [monomialL]; rfl
  map_mul' e f := by
    change monomialL (-(e.toAdd+f.toAdd)) (∏ i,phase^(k i*(e.toAdd i+f.toAdd i))) = _
    simp only [mul_add,zpow_add₀ phase_ne_zero,Finset.prod_mul_distrib,neg_add]
    exact (AddMonoidAlgebra.single_mul_single _ _ _ _).symm

def twistedReflectLaurent {n : ℕ} (k : Fin n → ℤ) : Laurent n →+* Laurent n :=
  (AddMonoidAlgebra.lift ℂ (Laurent n) (Fin n → ℤ) (twistedReflectionMonomial k)).toRingHom

@[simp] lemma twistedReflectLaurent_monomial {n : ℕ} (k : Fin n → ℤ)
    (e : Fin n → ℤ) (z : ℂ) :
    twistedReflectLaurent k (monomialL e z) = monomialL (-e) (z * ∏ i,phase^(k i*e i)) := by
  change AddMonoidAlgebra.lift ℂ _ _ (twistedReflectionMonomial k) (AddMonoidAlgebra.single e z) = _
  rw [AddMonoidAlgebra.lift_single]
  change z • AddMonoidAlgebra.single (-e) _ = AddMonoidAlgebra.single (-e) _
  rw [AddMonoidAlgebra.smul_single,smul_eq_mul]
  rfl

lemma twistedReflectLaurent_involutive {n : ℕ} (k : Fin n → ℤ) :
    Function.Involutive (twistedReflectLaurent k) := by
  have h : (twistedReflectLaurent k).comp (twistedReflectLaurent k) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change twistedReflectLaurent k (twistedReflectLaurent k (monomialL _ _)) = monomialL _ _
    all_goals rw [twistedReflectLaurent_monomial,twistedReflectLaurent_monomial]
    all_goals simp only [neg_neg,Pi.neg_apply,mul_neg,mul_assoc,←Finset.prod_mul_distrib,
      ←zpow_add₀ phase_ne_zero,add_neg_cancel,zpow_zero,Finset.prod_const_one,mul_one]
  exact fun f => DFunLike.congr_fun h f

def twistedReflectSpectral {n : ℕ} (k : Fin n → ℤ) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K:=SpectralField n)
    (g:=(algebraMap (SpectralRing n) (SpectralField n)).comp (twistedReflectLaurent k))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (twistedReflectLaurent_involutive k).injective)

@[simp] lemma twistedReflectSpectral_evalLaurent {n : ℕ} (k : Fin n → ℤ) (f : Laurent n) :
    twistedReflectSpectral k (evalLaurent f)=evalLaurent (twistedReflectLaurent k f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma twistedReflectSpectral_const {n : ℕ} (k : Fin n → ℤ) (z : ℂ) :
    twistedReflectSpectral k (constF n z)=constF n z := by
  have hc : constF n z=evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,twistedReflectSpectral_evalLaurent]
  change evalLaurent (twistedReflectLaurent k (monomialL 0 z)) = evalLaurent (monomialL 0 z)
  rw [twistedReflectLaurent_monomial]
  simp only [Pi.zero_apply,mul_zero,zpow_zero,Finset.prod_const_one,mul_one,neg_zero]

@[simp] lemma twistedReflectSpectral_variable {n : ℕ} (k : Fin n → ℤ) (i : Fin n) :
    twistedReflectSpectral k (variableF i)=constF n phase ^ k i / variableF i := by
  change twistedReflectSpectral k (evalLaurent (monomialL (variableExponent i) 1)) = _
  rw [twistedReflectSpectral_evalLaurent,twistedReflectLaurent_monomial]
  have he : (∏ j,phase^(k j * variableExponent i j))=phase^k i := by
    simp [variableExponent,Pi.single_apply]
  rw [he,one_mul,evalLaurent,map_monomialL_neg_variable]
  simp only [constF,map_zpow₀,div_eq_mul_inv]



def pairReflection (n s : ℕ) : SpectralField (n+1) →+* SpectralField (n+1) :=
  twistedReflectSpectral (Fin.cons (3-(s:ℤ)) (fun _ : Fin n =>3))

@[simp] lemma pairReflection_const (n s : ℕ) (z : ℂ) :
    pairReflection n s (constF (n+1) z)=constF (n+1) z := twistedReflectSpectral_const _ z

@[simp] lemma pairReflection_variable_zero (n s : ℕ) :
    pairReflection n s (variableF 0)=constF (n+1) phase^(3-(s:ℤ))/variableF 0 :=
  twistedReflectSpectral_variable _ _

@[simp] lemma pairReflection_variable_succ (n s : ℕ) (i : Fin n) :
    pairReflection n s (variableF i.succ)=constF (n+1) phase^3/variableF i.succ :=
  twistedReflectSpectral_variable _ _

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

def rowReflectionMonomial {n : ℕ} (i : Fin n) :
    Multiplicative (Fin n → ℤ) →* Laurent n where
  toFun e := monomialL (reflectExponentAt i e.toAdd) (phase ^ (3 * e.toAdd i))
  map_one' := by simp [monomialL]; rfl
  map_mul' e f := by
    change monomialL (reflectExponentAt i (e.toAdd+f.toAdd))
        (phase ^ (3 * (e.toAdd i+f.toAdd i))) = _
    rw [mul_add, zpow_add₀ phase_ne_zero, reflectExponentAt_add]
    exact (AddMonoidAlgebra.single_mul_single _ _ _ _).symm

def rowReflectLaurent {n : ℕ} (i : Fin n) : Laurent n →+* Laurent n :=
  (AddMonoidAlgebra.lift ℂ (Laurent n) (Fin n → ℤ) (rowReflectionMonomial i)).toRingHom

@[simp] lemma rowReflectLaurent_monomial {n : ℕ} (i : Fin n) (e : Fin n → ℤ) (z : ℂ) :
    rowReflectLaurent i (monomialL e z) =
      monomialL (reflectExponentAt i e) (z * phase ^ (3 * e i)) := by
  change AddMonoidAlgebra.lift ℂ _ _ (rowReflectionMonomial i) (AddMonoidAlgebra.single e z) = _
  rw [AddMonoidAlgebra.lift_single]
  change z • AddMonoidAlgebra.single _ _ = AddMonoidAlgebra.single _ _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul]
  rfl

lemma rowReflectLaurent_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (rowReflectLaurent i) := by
  have h : (rowReflectLaurent i).comp (rowReflectLaurent i) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change rowReflectLaurent i (rowReflectLaurent i (monomialL _ _)) = monomialL _ _
    all_goals rw [rowReflectLaurent_monomial,rowReflectLaurent_monomial]
    all_goals simp only [reflectExponentAt_involutive,reflectExponentAt_same,mul_neg,
      mul_assoc,← zpow_add₀ phase_ne_zero,add_neg_cancel,zpow_zero,mul_one]
  exact fun f => DFunLike.congr_fun h f

def rowReflectSpectral {n : ℕ} (i : Fin n) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing n) (SpectralField n)).comp (rowReflectLaurent i))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (rowReflectLaurent_involutive i).injective)

@[simp] lemma rowReflectSpectral_evalLaurent {n : ℕ} (i : Fin n) (f : Laurent n) :
    rowReflectSpectral i (evalLaurent f) = evalLaurent (rowReflectLaurent i f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma rowReflectSpectral_const {n : ℕ} (i : Fin n) (z : ℂ) :
    rowReflectSpectral i (constF n z) = constF n z := by
  have hc : constF n z = evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,rowReflectSpectral_evalLaurent]
  change evalLaurent (rowReflectLaurent i (monomialL 0 z)) = evalLaurent (monomialL 0 z)
  rw [rowReflectLaurent_monomial]
  simp

@[simp] lemma rowReflectSpectral_variable {n : ℕ} (i j : Fin n) :
    rowReflectSpectral i (variableF j) =
      if j=i then constF n phase ^ 3 / variableF j else variableF j := by
  change rowReflectSpectral i (evalLaurent (monomialL (variableExponent j) 1)) = _
  rw [rowReflectSpectral_evalLaurent,rowReflectLaurent_monomial]
  by_cases h:j=i
  · subst j
    have he : reflectExponentAt i (variableExponent i) = -variableExponent i := by
      ext k; by_cases hh:k=i <;> simp [reflectExponentAt,variableExponent,hh]
    rw [he]
    simp only [variableExponent,Pi.single_eq_same,one_mul,mul_one,ite_true,zpow_ofNat]
    change evalLaurent (monomialL (-variableExponent i) (phase^3)) = _
    rw [evalLaurent,map_monomialL_neg_variable]
    simp [constF,div_eq_mul_inv]
  · have he : reflectExponentAt i (variableExponent j) = variableExponent j := by
      ext k
      by_cases hh:k=i
      · subst k; simp [reflectExponentAt,variableExponent,Ne.symm h]
      · simp [reflectExponentAt,hh]
    rw [he]
    simp only [variableExponent,Pi.single_apply,ite_eq_right (Ne.symm h),mul_zero,zpow_zero,
      one_mul,ite_eq_right h]
    rfl

@[simp] lemma rowReflectSpectral_torusSin {n : ℕ} (i : Fin n) (z : SpectralField n) :
    rowReflectSpectral i (torusSin z) = torusSin (rowReflectSpectral i z) := by
  simp [torusSin,map_div₀,map_inv₀,map_ofNat]
@[simp] lemma rowReflectSpectral_torusCos {n : ℕ} (i : Fin n) (z : SpectralField n) :
    rowReflectSpectral i (torusCos z) = torusCos (rowReflectSpectral i z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]
@[simp] lemma rowReflectSpectral_torusL {n : ℕ} (i : Fin n) (z : SpectralField n) :
    rowReflectSpectral i (torusL z) = torusL (rowReflectSpectral i z) := by simp [torusL]
@[simp] lemma rowReflectSpectral_torusWeights {n : ℕ} (i : Fin n) (z : SpectralField n) :
    (torusWeights z).map (rowReflectSpectral i) = torusWeights (rowReflectSpectral i z) := by
  simp [Weights.map,torusWeights,map_div₀]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BottomGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

 
def occupancyGauge {K : Type*} [One K] {n : ℕ} (a : K) (p : Pairing n) (i : Fin n) : K :=
  if p.Occupied i then a else 1

@[simp] lemma occupancyGauge_empty {K : Type*} [One K] {n : ℕ} (a : K) (i : Fin n) :
    occupancyGauge a (empty n) i = 1 := by simp [occupancyGauge]

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
open Finset _root_.Matrix

 

def northInjectionWeights {K : Type*} [One K] [Zero K] : Weights K := ⟨1,1,0,0,0⟩

def sourceFullSplit (n : ℕ) : Pairing n ⊕ SourcePairing n ≃ Pairing (n+1) where
  toFun := Sum.elim Pairing.padTop Subtype.val
  invFun p := if h : p.Occupied (Fin.last n) then Sum.inr ⟨p,h⟩ else
    Sum.inl (p.restrict Fin.castSuccOrderEmb)
  left_inv p := by
    cases p with
    | inl p =>
      change (if h : p.padTop.Occupied (Fin.last n) then Sum.inr (⟨p.padTop,h⟩ : SourcePairing n) else
        Sum.inl (Pairing.restrict Fin.castSuccOrderEmb p.padTop))=Sum.inl p
      rw [dite_eq_right (Pairing.padTop_not_occupied_last p)]
      exact congrArg Sum.inl (Pairing.restrict_map _ _)
    | inr p =>
      change (if h : p.val.Occupied (Fin.last n) then Sum.inr ⟨p.val,h⟩ else
        Sum.inl (Pairing.restrict Fin.castSuccOrderEmb p.val))=Sum.inr p
      rw [dite_eq_left p.property]
  right_inv p := by
    change Sum.elim Pairing.padTop Subtype.val
      (if h : p.Occupied (Fin.last n) then Sum.inr ⟨p,h⟩ else
        Sum.inl (Pairing.restrict Fin.castSuccOrderEmb p))=p
    split_ifs with h
    · rfl
    · exact Pairing.padTop_restrict p h

@[simp] lemma sourceFullSplit_inl {n : ℕ} (p : Pairing n) :
    sourceFullSplit n (.inl p)=p.padTop := rfl
@[simp] lemma sourceFullSplit_inr {n : ℕ} (p : SourcePairing n) :
    sourceFullSplit n (.inr p)=p.val := rfl

def augmentVector {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K) :
    Pairing (n+1) → K := fun p=>Sum.elim v z ((sourceFullSplit n).symm p)

@[simp] lemma augmentVector_split {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K)
    (p : Pairing n ⊕ SourcePairing n) :
    augmentVector v z (sourceFullSplit n p)=Sum.elim v z p := by
  simp only [augmentVector,Equiv.symm_apply_apply]

@[simp] lemma augmentVector_padTop {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K)
    (p : Pairing n) : augmentVector v z p.padTop=v p := augmentVector_split v z (.inl p)

@[simp] lemma augmentVector_source {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K)
    (p : SourcePairing n) : augmentVector v z p.val=z p := augmentVector_split v z (.inr p)

@[simp] lemma augmentVector_empty {K : Type*} {n : ℕ} (v : Pairing n → K) (z : SourcePairing n → K) :
    augmentVector v z (empty (n+1))=v (empty n) := by
  rw [←Pairing.padTop_empty,augmentVector_padTop]

end

 

 

noncomputable section
open scoped BigOperators Classical
namespace ColumnChain
section RingCoefficients
variable {K : Type*} [CommRing K] {n : ℕ}

def weight (w : Fin n → Weights K) : List (Configuration n) → K
  | [] => 1
  | t::ts => (∏ i,(w i).tile (t i))*weight w ts

end RingCoefficients






end ColumnChain
end

 

 

noncomputable section
open scoped Classical
namespace ColumnChain
variable {n : ℕ}



lemma read_ge (ts : List (Configuration n)) (k : ℕ) (hk : ts.length≤k) :
    read ts k=fun _=>.vacant := by
  simp only [read,List.getElem?_eq_none hk,Option.getD_none]

lemma support_empty_read (ts : List (Configuration n)) (i : Fin n) :
    support (empty n) ts i ↔ (read ts 0 i).Occupied 2 := by
  cases ts with
  | nil => simp only [support,read_nil]; exact ⟨fun h=>(empty_not_occupied i h).elim,
      fun h=>(Tile.vacant_not_occupied 2 h).elim⟩
  | cons => rfl

 
structure LocallyCompatible (ts : List (Configuration n)) : Prop where
  horizontal : ∀ k i, (read ts (k+1) i).Occupied 2 ↔ (read ts k i).Occupied 1
  south : ∀ k i, i.val=0 → ¬(read ts k i).Occupied 0
  north : ∀ k i, i.val+1=n → ¬(read ts k i).Occupied 3
  vertical : ∀ k i j, i.val+1=j.val →
    ((read ts k i).Occupied 3 ↔ (read ts k j).Occupied 0)

lemma compatible_empty_iff (ts : List (Configuration n)) :
    Compatible (empty n) ts ↔ LocallyCompatible ts := by
  induction ts with
  | nil =>
    refine ⟨fun _=>⟨?_,?_,?_,?_⟩,fun _=>trivial⟩ <;> simp [Tile.vacant_not_occupied]
  | cons t ts ih =>
    constructor
    · rintro ⟨hc,ht⟩
      obtain ⟨hh,hs,hn,hv⟩ := ih.mp hc
      refine ⟨?_,?_,?_,?_⟩
      · intro k i
        cases k with
        | zero => exact (support_empty_read ts i).symm.trans (ht.west i).symm
        | succ k => exact hh k i
      · intro k i hi
        cases k with
        | zero => exact ht.south i hi
        | succ k => exact hs k i hi
      · intro k i hi
        cases k with
        | zero => exact ht.north i hi
        | succ k => exact hn k i hi
      · intro k i j hij
        cases k with
        | zero => exact ht.glued i j hij
        | succ k => exact hv k i j hij
    · intro h
      refine ⟨ih.mpr ⟨fun k i=>h.horizontal (k+1) i,fun k i=>h.south (k+1) i,
        fun k i=>h.north (k+1) i,fun k i j=>h.vertical (k+1) i j⟩,?_,?_,?_,?_⟩
      · intro i
        exact (h.horizontal 0 i).symm.trans (support_empty_read ts i).symm
      · exact h.south 0
      · exact h.north 0
      · exact h.vertical 0

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


lemma ValidTriangle.not_three {a b m : Prop} (h : ValidTriangle a b m) : ¬(a ∧ b ∧ m) := by
  unfold ValidTriangle at h
  tauto

lemma ValidTriangle.one_off {a b m : Prop} (h : ValidTriangle a b m) (ha : a) :
    (b ∧ ¬m) ∨ (¬b ∧ m) := by
  unfold ValidTriangle at h
  tauto

namespace Tile



lemma physical_up (t : Tile) (h : t ≠ .verticalPair) :
    ValidTriangle (t.Occupied 0) (t.Occupied 1) t.middle := by
  revert t
  unfold ValidTriangle
  decide

lemma physical_down (t : Tile) (h : t ≠ .verticalPair) :
    ValidTriangle (t.Occupied 2) (t.Occupied 3) t.middle := by
  revert t
  unfold ValidTriangle
  decide

end Tile
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram Diagram.PathGraph

namespace HoneycombAssignment
variable {N : ℕ}

lemma down_neighbors (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) (w : Triangle) :
    D.graph.Adj (down i j) w ↔ j<N ∧
      ((w=up i j ∧ (D.tile (i,j)).middle) ∨
       (w=up (i+1) j ∧ (D.tile (i,j)).Occupied 2) ∨
       (j+1<N ∧ w=up i (j+1) ∧ (D.tile (i,j)).Occupied 3)) := by
  have hs : ∀ v w, D.graph.Adj v w ↔ D.graph.Adj w v := fun _ _ => ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩
  have hm := tileGraph_middle N D.tile i j
  have he := tileGraph_west N D.tile (i+1) j
  have hn := tileGraph_south N D.tile i (j+1) (by omega)
  simp only [add_sub_cancel_right] at he hn
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    rcases (adjacent_down_iff i j w).mp (tileGraph_allowed N D.tile h).1 with rfl | rfl | rfl
    · exact Or.inl ⟨rfl,(hm.mp (D.graph.symm.symm _ _ h)).2⟩
    · exact Or.inr (Or.inl ⟨rfl,(D.horizontal i j).mpr (he.mp (D.graph.symm.symm _ _ h)).2⟩)
    · have h' := hn.mp (D.graph.symm.symm _ _ h)
      exact Or.inr (Or.inr ⟨h'.1,rfl,(D.vertical i j h'.1).mpr h'.2⟩)
  · rintro ⟨hj,⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨hn',rfl,h⟩⟩
    · exact D.graph.symm.symm _ _ (hm.mpr ⟨hj,h⟩)
    · exact D.graph.symm.symm _ _ (he.mpr ⟨hj,(D.horizontal i j).mp h⟩)
    · exact D.graph.symm.symm _ _ (hn.mpr ⟨hn',(D.vertical i j hn').mp h⟩)

end HoneycombAssignment

namespace HoneycombAssignment
variable {N : ℕ}

lemma two (D : HoneycombAssignment N) : AtMostTwo D.graph.Adj := by
  intro v x y z hx hy hz hn
  rcases v with ⟨i,j,b⟩
  cases b
  · have h := (Tile.physical_down (D.tile (i,j)) (D.physical (i,j))).not_three
    apply atMostTwo_of_three (a := up i j) (b := up (i+1) j) (c := up i (j+1))
      (A := (D.tile (i,j)).middle) (B := (D.tile (i,j)).Occupied 2) (C := (D.tile (i,j)).Occupied 3)
      (by tauto) (fun w hw => ?_) hx hy hz hn
    rcases (D.down_neighbors i j w).mp hw with ⟨_,h⟩
    exact h.imp id (Or.imp id (fun h => ⟨h.2.1,h.2.2⟩))
  · have h := (Tile.physical_up (D.tile (i,j)) (D.physical (i,j))).not_three
    apply atMostTwo_of_three (a := down i j) (b := down (i-1) j) (c := down i (j-1))
      (A := (D.tile (i,j)).middle) (B := (D.tile (i,j)).Occupied 1) (C := (D.tile (i,j)).Occupied 0)
      (by tauto) (fun w hw => ?_) hx hy hz hn
    rcases (D.up_neighbors i j w).mp hw with ⟨_,h⟩
    exact h.imp id (Or.imp id (fun h => ⟨h.2.1,h.2.2⟩))

lemma bottom_one (D : HoneycombAssignment N) {i : ℤ} (hb : (D.tile (i,0)).Occupied 0) :
    AtMostOne D.graph.Adj (up i 0) := by
  intro x y hx hy
  have h := (Tile.physical_up (D.tile (i,0)) (D.physical (i,0))).one_off hb
  rw [D.up_neighbors] at hx hy
  simp only [lt_self_iff_false,false_and,or_false] at hx hy
  rcases hx.2 with ⟨rfl,hx⟩ | ⟨rfl,hx⟩ <;>
    rcases hy.2 with ⟨rfl,hy⟩ | ⟨rfl,hy⟩ <;> tauto

lemma bottom_used (D : HoneycombAssignment N) (hN : 1≤N) {i : ℤ}
    (hb : (D.tile (i,0)).Occupied 0) : ∃ w, D.graph.Adj (up i 0) w := by
  have h := (Tile.physical_up (D.tile (i,0)) (D.physical (i,0))).one_off hb
  rcases h with ⟨hw,hm⟩ | ⟨hw,hm⟩
  · exact ⟨down (i-1) 0,(D.up_neighbors i 0 _).mpr ⟨by omega,Or.inr (Or.inl ⟨rfl,hw⟩)⟩⟩
  · exact ⟨down i 0,(D.up_neighbors i 0 _).mpr ⟨by omega,Or.inl ⟨rfl,hm⟩⟩⟩

lemma top_one (D : HoneycombAssignment N) (hN : 1≤N) {i : ℤ}
    (ht : (D.tile (i,N-1)).Occupied 3) : AtMostOne D.graph.Adj (down i (N-1)) := by
  intro x y hx hy
  have h := Tile.physical_down (D.tile (i,N-1)) (D.physical (i,N-1))
  unfold ValidTriangle at h
  rw [D.down_neighbors] at hx hy
  have hn : ¬(N-1+1<N) := by omega
  simp only [hn,false_and,or_false] at hx hy
  rcases hx.2 with ⟨rfl,hx⟩ | ⟨rfl,hx⟩ <;>
    rcases hy.2 with ⟨rfl,hy⟩ | ⟨rfl,hy⟩ <;> tauto

lemma top_used (D : HoneycombAssignment N) (hN : 1≤N) {i : ℤ}
    (ht : (D.tile (i,N-1)).Occupied 3) : ∃ w, D.graph.Adj (down i (N-1)) w := by
  have h := Tile.physical_down (D.tile (i,N-1)) (D.physical (i,N-1))
  have h' : (D.tile (i,N-1)).middle ∨ (D.tile (i,N-1)).Occupied 2 := by
    unfold ValidTriangle at h
    tauto
  rcases h' with hm | he
  · exact ⟨up i (N-1),(D.down_neighbors i (N-1) _).mpr ⟨by omega,Or.inl ⟨rfl,hm⟩⟩⟩
  · exact ⟨up (i+1) (N-1),(D.down_neighbors i (N-1) _).mpr ⟨by omega,Or.inr (Or.inl ⟨rfl,he⟩)⟩⟩

end HoneycombAssignment






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



lemma ext_graph_boundary (D E : HoneycombAssignment N) (hN : 1≤N)
    (hg : D.graph=E.graph)
    (hb : ∀ i, (D.tile (i,0)).Occupied 0 ↔ (E.tile (i,0)).Occupied 0)
    (ht : ∀ i, (D.tile (i,N-1)).Occupied 3 ↔ (E.tile (i,N-1)).Occupied 3) : D=E := by
  apply ext
  funext ⟨i,j⟩
  by_cases hj : j<N
  · have hm : (D.tile (i,j)).middle=(E.tile (i,j)).middle := by
      apply Bool.eq_iff_iff.mpr
      have hu := tileGraph_middle N D.tile i j
      have hv := tileGraph_middle N E.tile i j
      change (D.graph.Adj (up i j) (down i j) ↔ _) at hu
      change (E.graph.Adj (up i j) (down i j) ↔ _) at hv
      rw [hg] at hu
      exact (by simpa only [hj,true_and] using hu.symm.trans hv)
    have hw (i : ℤ) : (D.tile (i,j)).Occupied 1 ↔ (E.tile (i,j)).Occupied 1 := by
      have hu := tileGraph_west N D.tile i j
      have hv := tileGraph_west N E.tile i j
      change (D.graph.Adj (up i j) (down (i-1) j) ↔ _) at hu
      change (E.graph.Adj (up i j) (down (i-1) j) ↔ _) at hv
      rw [hg] at hu
      simpa only [hj,true_and] using hu.symm.trans hv
    have hs (j : ℕ) (hj : j<N) (hpos : 0<j) :
        (D.tile (i,j)).Occupied 0 ↔ (E.tile (i,j)).Occupied 0 := by
      have hu := tileGraph_south N D.tile i j hpos
      have hv := tileGraph_south N E.tile i j hpos
      change (D.graph.Adj (up i j) (down i (j-1)) ↔ _) at hu
      change (E.graph.Adj (up i j) (down i (j-1)) ↔ _) at hv
      rw [hg] at hu
      simpa only [hj,true_and] using hu.symm.trans hv
    apply Tile.physical_ext (D.physical (i,j)) (E.physical (i,j)) ?_ hm
    intro p
    fin_cases p
    · by_cases h₀ : j=0
      · subst j; exact hb i
      · exact hs j hj (by omega)
    · exact hw i
    · exact (D.horizontal i j).trans ((hw (i+1)).trans (E.horizontal i j).symm)
    · by_cases hn : j+1=N
      · have he : j=N-1 := by omega
        subst j
        exact ht i
      · have hnext : j+1<N := by omega
        exact (D.vertical i j hnext).trans ((hs (j+1) hnext (by omega)).trans (E.vertical i j hnext).symm)
  · rw [D.outside i j (by omega),E.outside i j (by omega)]

end HoneycombAssignment

namespace WireConfiguration
variable {N : ℕ} {b : BoundaryPort}

lemma toAssignment_bottom (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) :
    ((D.toAssignment hN hb).tile (i,0)).Occupied 0 ↔ i=0 ∨ b=.bottom i := by
  simpa only [toAssignment,south,ite_true] using (D.physicalTile_spec hN hb i 0).2.1

lemma toAssignment_top (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) (i : ℤ) :
    ((D.toAssignment hN hb).tile (i,N-1)).Occupied 3 ↔ b=.top i := by
  simpa only [toAssignment,north,show N-1+1=N by omega,ite_true] using
    (D.physicalTile_spec hN hb i (N-1)).2.2.2.2.1

end WireConfiguration



namespace HoneycombConfiguration
variable {N : ℕ} {b : BoundaryPort}


def toWire (D : HoneycombConfiguration N b) (hN : 1≤N) : WireConfiguration N (b.vertex N) where
  graph := D.toHoneycombAssignment.graph
  allowed _ _ h := tileGraph_allowed N D.tile h
  two := D.toHoneycombAssignment.two
  source_one := D.toHoneycombAssignment.bottom_one ((D.bottom 0).mpr (Or.inl rfl))
  finish_one := by
    cases b with
    | bottom i => exact D.toHoneycombAssignment.bottom_one ((D.bottom i).mpr (Or.inr rfl))
    | top i => exact D.toHoneycombAssignment.top_one hN ((D.top i).mpr rfl)
  source_used := D.toHoneycombAssignment.bottom_used hN ((D.bottom 0).mpr (Or.inl rfl))
  finish_used := by
    cases b with
    | bottom i => exact D.toHoneycombAssignment.bottom_used hN ((D.bottom i).mpr (Or.inr rfl))
    | top i => exact D.toHoneycombAssignment.top_used hN ((D.top i).mpr rfl)
  drains := D.drains

def ofWire (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : HoneycombConfiguration N b where
  toHoneycombAssignment := D.toAssignment hN hb
  bottom := D.toAssignment_bottom hN hb
  top := D.toAssignment_top hN hb
  drains v w h := by
    have hg := D.toAssignment_graph hN hb
    rw [hg] at h ⊢
    exact D.drains v w h

@[simp] lemma toWire_ofWire (D : WireConfiguration N (b.vertex N)) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : (ofWire D hN hb).toWire hN=D := by
  apply WireConfiguration.ext
  exact D.toAssignment_graph hN hb

@[simp] lemma ofWire_toWire (D : HoneycombConfiguration N b) (hN : 1≤N)
    (hb : b ≠ .bottom 0) : ofWire (D.toWire hN) hN hb=D := by
  apply ext
  apply HoneycombAssignment.ext_graph_boundary _ _ hN
  · exact (D.toWire hN).toAssignment_graph hN hb
  · intro i
    exact ((D.toWire hN).toAssignment_bottom hN hb i).trans (D.bottom i).symm
  · intro i
    exact ((D.toWire hN).toAssignment_top hN hb i).trans (D.top i).symm



end HoneycombConfiguration

 

 


namespace Diagram

 

lemma physicalWeights_two_lambda :
    physicalWeights (2*lambda) = (⟨rho^2,rho^2,rho,0,rho^2⟩ : Weights ℝ) := by
  have hL : L (2*lambda)=C := by
    unfold L
    rw [show 2*lambda+2*lambda=4*lambda by ring,
      show 3*lambda+2*lambda=5*lambda by ring,
      sin_four_lambda_eq_one,sin_five_lambda_eq,sin_three_lambda_eq_C,one_mul]
  unfold physicalWeights
  dsimp only
  change (⟨d * _ / _,_,_,_,_⟩ : Weights ℝ) = _
  rw [hL,show 3*lambda-2*lambda=lambda by ring,show 2*lambda-2*lambda=0 by ring,
    show 2*lambda-lambda=lambda by ring,sin_lambda_eq_c,sin_two_lambda_eq_d,
    Real.sin_zero,mul_zero,zero_div,d_mul_c_div_C,show c*d=d*c by ring,
    d_mul_c_div_C]
  change (⟨rho^2,rho^2,d*d/C,0,rho^2⟩ : Weights ℝ) = _
  rw [←pow_two,d_sq_div_C]

end Diagram

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

lemma L_reflection (u : ℝ) : L (3*lambda-u)=L u := by
  have ha : 2*lambda+(3*lambda-u)=Real.pi-(3*lambda+u) := by unfold lambda; ring
  have hb : 3*lambda+(3*lambda-u)=Real.pi-(2*lambda+u) := by unfold lambda; ring
  unfold L
  rw [ha,hb,Real.sin_pi_sub,Real.sin_pi_sub,mul_comm]

lemma physicalWeights_reflection (u : ℝ) :
    physicalWeights (3*lambda-u)=
      ⟨(physicalWeights u).U,(physicalWeights u).B,(physicalWeights u).A,
        (physicalWeights u).F,(physicalWeights u).E⟩ := by
  unfold physicalWeights
  dsimp only
  rw [L_reflection,show 3*lambda-(3*lambda-u)=u by ring,
    show 2*lambda-(3*lambda-u)=u-lambda by ring,
    show (3*lambda-u)-lambda=2*lambda-u by ring]
  congr 1 <;> ring

end

 

 

noncomputable section
open scoped Classical
namespace Tile



lemma horizontal_weight (w : Weights ℝ) (t : Tile) :
    (⟨w.U,w.B,w.A,w.F,w.E⟩ : Weights ℝ).tile t.horizontal = w.tile t := by
  cases t <;> rfl

lemma physical_horizontal_weight (u : ℝ) (t : Tile) :
    (physicalWeights (3*lambda-u)).tile t.horizontal=(physicalWeights u).tile t := by
  rw [physicalWeights_reflection,horizontal_weight]

lemma physical_horizontal_weight_two (t : Tile) :
    (physicalWeights (2*lambda)).tile t.horizontal=(physicalWeights lambda).tile t := by
  simpa only [show 3*lambda-lambda=2*lambda by ring] using physical_horizontal_weight lambda t



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





namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical






namespace PaddedColumn
variable {n : ℕ}
abbrev V (n : ℕ) := ℕ × Vertex n

def wiring (ts : List (Configuration n)) : V n → V n → Prop
  | (k,i,a),(l,j,b) =>
    (k=l ∧ BareColumn (ColumnChain.read ts k) (i,a) (j,b)) ∨
    (i=j ∧ a=2 ∧ b=1 ∧ l+1=k ∧ (ColumnChain.read ts k i).Occupied 2) ∨
    (i=j ∧ a=1 ∧ b=2 ∧ k+1=l ∧ (ColumnChain.read ts l j).Occupied 2)

def boundary (i : Fin n) : V n := (0,i,2)

lemma boundary_injective : Function.Injective (boundary (n:=n)) := by
  intro i j h; exact congrArg (fun x=>x.2.1) h

def active (ts : List (Configuration n)) (i : Fin n) : Prop :=
  (ColumnChain.read ts 0 i).Occupied 2

lemma wiring_nil (v w : V n) : ¬wiring [] v w := by
  rcases v with ⟨k,i,a⟩
  rcases w with ⟨l,j,b⟩
  simp only [wiring,ColumnChain.read_nil,BareColumn]
  have he (a b : Fin 4) : ¬Tile.vacant.Adj a b := by
    exact fun h=>Tile.vacant_not_occupied a ⟨b,h⟩
  simp [he,Tile.vacant_not_occupied]

lemma empty_realizes : GraphRealizes (wiring ([] : List (Configuration n))) boundary (empty n) := by
  constructor
  · exact fun v w h=>(wiring_nil v w h).elim
  · intro i j
    constructor
    · intro hr
      have hn (v w : V n) (h : Relation.ReflTransGen (wiring []) v w) : v=w := by
        induction h with
        | refl => rfl
        | @tail v w h h₁ ih => exact (wiring_nil v w h₁).elim
      have he := hn _ _ hr
      exact Or.inl (boundary_injective he)
    · rintro (rfl | h)
      · exact .refl
      · exact (empty_not_occupied i ⟨j,h⟩).elim

 
def addColumn (n : ℕ) : Sum (V n) (Vertex n) ≃ V n where
  toFun
    | .inl (k,v) => (k+1,v)
    | .inr v => (0,v)
  invFun
    | (0,v) => .inr v
    | (k+1,v) => .inl (k,v)
  left_inv := by rintro (⟨k,v⟩|v) <;> rfl
  right_inv := by rintro ⟨k,v⟩; cases k <;> rfl

lemma wiring_step (t : Configuration n) (ts : List (Configuration n))
    (v w : Sum (V n) (Vertex n)) :
    Patch.glued (wiring ts) (BareColumn t) boundary (fun i=>(i,1)) (active ts) v w ↔
      wiring (t::ts) (addColumn n v) (addColumn n w) := by
  cases v with
  | inl v =>
    rcases v with ⟨k,i,a⟩
    cases w with
    | inl w =>
      rcases w with ⟨l,j,b⟩
      simp [Patch.glued,wiring,addColumn]
    | inr w =>
      rcases w with ⟨j,b⟩
      by_cases hij : i=j
      · subst j
        simp [Patch.glued,wiring,addColumn,boundary,active,and_assoc,and_left_comm,and_comm]
        intro h _ _; subst h; rfl
      · simp [Patch.glued,wiring,addColumn,boundary,active,hij,Ne.symm hij]
  | inr v =>
    rcases v with ⟨i,a⟩
    cases w with
    | inl w =>
      rcases w with ⟨l,j,b⟩
      by_cases hij : i=j
      · subst j
        simp [Patch.glued,wiring,addColumn,boundary,active,and_assoc,and_left_comm,and_comm]
        intro h _ _; subst h; rfl
      · simp [Patch.glued,wiring,addColumn,boundary,active,hij,Ne.symm hij]
    | inr w =>
      rcases w with ⟨j,b⟩
      simp [Patch.glued,wiring,addColumn,BareColumn]

def stepEquivalence (t : Configuration n) (ts : List (Configuration n)) :
    Graph.BoundaryEquiv
      (Patch.glued (wiring ts) (BareColumn t) boundary (fun i=>(i,1)) (active ts))
      (wiring (t::ts)) (fun i=>.inr (i,2)) boundary :=
  Graph.BoundaryEquiv.ofEquiv (addColumn n) (wiring_step t ts) (fun _=>rfl)

 

theorem runs_realizes (ts : List (Configuration n)) (q : Pairing n)
    (h : ColumnChain.Runs (empty n) ts q) : GraphRealizes (wiring ts) boundary q := by
  induction ts generalizing q with
  | nil => exact h ▸ empty_realizes
  | cons t ts ih =>
    obtain ⟨p,hp,ht⟩ := h
    have hg := ih p hp
    have he : active ts=p.Occupied := by
      funext i
      exact propext ((ColumnChain.support_empty_read ts i).symm.trans
        (by rw [(ColumnChain.runs_sound _ _ _ hp).2.2]))
    apply (stepEquivalence t ts).realizes
    rw [he,hg.substitute_iff]
    exact (ColumnSew.equivalence p t).symm.realizes ((realizes_iff_column_graph p q t).mp ht).2

end PaddedColumn
end
end CriticalStrip.Diagram





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


@[simp] lemma turn_weight (w : Weights ℝ) (t : Tile) : w.tile t.turn=w.tile t := by
  cases t <;> rfl

end Diagram.Tile

 

def turnTriangle (N : ℕ) (b : ℤ) (v : Triangle) : Triangle :=
  (b-v.1,N-1-v.2.1,!v.2.2)

lemma turnTriangle_in_strip (N : ℕ) (b : ℤ) {v : Triangle} (hv : v.2.1<N) :
    (turnTriangle N b v).2.1<N := by dsimp [turnTriangle]; omega

lemma turnTriangle_turnTriangle (N : ℕ) (b : ℤ) {v : Triangle} (hv : v.2.1<N) :
    turnTriangle N b (turnTriangle N b v)=v := by
  rcases v with ⟨i,j,c⟩
  simp only [turnTriangle,Bool.not_not]
  have hj : N-1-(N-1-j)=j := by dsimp at hv; omega
  simp [hj]

namespace HoneycombAssignment
variable {N : ℕ}

 
def turn (D : HoneycombAssignment N) (b : ℤ) : HoneycombAssignment N where
  tile q := if q.2<N then (D.tile (b-q.1,N-1-q.2)).turn else .vacant
  physical q := by
    split
    · exact (Tile.turn_physical _).mpr (D.physical _)
    · decide
  outside i j hj := ite_eq_right (by omega)
  horizontal i j := by
    by_cases hj : j<N
    · simp only [hj,ite_true,Tile.turn_occupied_two,Tile.turn_occupied_one]
      have hh:=D.horizontal (b-(i+1)) (N-1-j)
      simpa only [show b-(i+1)+1=b-i by omega] using hh.symm
    · simp only [hj,ite_false,Tile.vacant_not_occupied]
  vertical i j hj := by
    have hj' : j<N := by omega
    have hh:=D.vertical (b-i) (N-1-(j+1)) (by omega)
    simp only [hj,hj',ite_true,Tile.turn_occupied_zero,Tile.turn_occupied_three]
    simpa only [show N-1-(j+1)+1=N-1-j by omega] using hh.symm

lemma turn_tile (D : HoneycombAssignment N) (b : ℤ) (i : ℤ) (j : ℕ) (hj : j<N) :
    (D.turn b).tile (i,j)=(D.tile (b-i,N-1-j)).turn := by simp [turn,hj]

lemma turn_turn (D : HoneycombAssignment N) (b : ℤ) : (D.turn b).turn b=D := by
  apply ext
  funext ⟨i,j⟩
  by_cases hj : j<N
  · have hj' : N-1-j<N := by omega
    rw [(D.turn b).turn_tile b i j hj,D.turn_tile b (b-i) (N-1-j) hj',
      Tile.turn_turn,show b-(b-i)=i by omega,show N-1-(N-1-j)=j by omega]
  · rw [(D.turn b).turn b |>.outside i j (by omega),D.outside i j (by omega)]

lemma turn_up_adj (D : HoneycombAssignment N) (b i : ℤ) (j : ℕ) (w : Triangle)
    (hj : j<N) (hw : w.2.1<N) :
    (D.turn b).graph.Adj (up i j) w ↔
      D.graph.Adj (turnTriangle N b (up i j)) (turnTriangle N b w) := by
  rcases w with ⟨k,l,c⟩
  rw [(D.turn b).up_neighbors]
  change (_ ∧ _) ↔ D.graph.Adj (down (b-i) (N-1-j)) (turnTriangle N b (k,l,c))
  rw [D.down_neighbors,D.turn_tile b i j hj,Tile.turn_middle,Tile.turn_occupied_one,
    Tile.turn_occupied_zero]
  have hj' : N-1-j<N := by omega
  simp only [hj,hj',true_and,up,down,turnTriangle,Prod.mk.injEq]
  have hl : l<N := hw
  cases c <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.true_eq_false,
    and_true,and_false,false_and,or_false]
  apply or_congr
  · apply and_congr_left
    intro _
    omega
  · apply or_congr
    · apply and_congr_left
      intro _
      omega
    · simp only [←and_assoc]
      apply and_congr_left
      intro _
      omega

lemma turn_adj (D : HoneycombAssignment N) (b : ℤ) {v w : Triangle}
    (hv : v.2.1<N) (hw : w.2.1<N) :
    (D.turn b).graph.Adj v w ↔ D.graph.Adj (turnTriangle N b v) (turnTriangle N b w) := by
  rcases v with ⟨i,j,c⟩
  cases c
  · rcases w with ⟨k,l,d⟩
    cases d
    · constructor
      · intro h
        have hh:=(tileGraph_allowed N (D.turn b).tile h).1
        simp [adjacent,upDownAdjacent] at hh
      · intro h
        have hh:=(tileGraph_allowed N D.tile h).1
        simp [turnTriangle,adjacent,upDownAdjacent] at hh
    · exact (show (D.turn b).graph.Adj (down i j) (up k l) ↔
          (D.turn b).graph.Adj (up k l) (down i j) from
          ⟨(D.turn b).graph.symm.symm _ _,(D.turn b).graph.symm.symm _ _⟩).trans
        ((D.turn_up_adj b k l (down i j) hw hv).trans
          ⟨D.graph.symm.symm _ _,D.graph.symm.symm _ _⟩)
  · exact D.turn_up_adj b i j w hv hw

lemma turn_edge (D : HoneycombAssignment N) (b : ℤ) {v w : Triangle}
    (h : D.graph.Adj v w) :
    (D.turn b).graph.Adj (turnTriangle N b v) (turnTriangle N b w) := by
  have hh:=tileGraph_allowed N D.tile h
  apply (D.turn_adj b (turnTriangle_in_strip N b hh.2.1)
    (turnTriangle_in_strip N b hh.2.2)).mpr
  simpa only [turnTriangle_turnTriangle N b hh.2.1,
    turnTriangle_turnTriangle N b hh.2.2] using h

lemma turn_reach (D : HoneycombAssignment N) (b : ℤ) {v w : Triangle}
    (h : Relation.ReflTransGen D.graph.Adj v w) :
    Relation.ReflTransGen (D.turn b).graph.Adj (turnTriangle N b v) (turnTriangle N b w) :=
  Graph.map_reach (turnTriangle N b) (fun _ _ e=>.single (D.turn_edge b e)) h

lemma turn_drains (D : HoneycombAssignment N) (b : ℤ) {root : Triangle}
    (h : Graph.DrainsAt D.graph.Adj root) :
    Graph.DrainsAt (D.turn b).graph.Adj (turnTriangle N b root) := by
  intro v w hvw
  have hh:=tileGraph_allowed N (D.turn b).tile hvw
  have e:=(D.turn_adj b hh.2.1 hh.2.2).mp hvw
  simpa only [turnTriangle_turnTriangle N b hh.2.1] using
    D.turn_reach b (h _ _ e)

end HoneycombAssignment

 

structure TopArchConfiguration (N : ℕ) (a b : ℤ) extends HoneycombAssignment N where
  bottom : ∀i, ¬(tile (i,0)).Occupied 0
  top : ∀i, (tile (i,N-1)).Occupied 3 ↔ i=a ∨ i=b
  drains : Graph.DrainsAt toHoneycombAssignment.graph.Adj (down b (N-1))

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

@[ext] lemma ext {D E : TopArchConfiguration N a b}
    (h : D.toHoneycombAssignment=E.toHoneycombAssignment) : D=E := by
  cases D; cases E; cases h; rfl

 
def toArch (D : TopArchConfiguration N a b) (hN : 1≤N) :
    HoneycombConfiguration N (.bottom (b-a)) where
  toHoneycombAssignment := D.toHoneycombAssignment.turn b
  bottom i := by
    rw [D.toHoneycombAssignment.turn_tile b i 0 (by omega),Tile.turn_occupied_zero]
    simp only [Nat.sub_zero,D.top,BoundaryPort.bottom.injEq]
    omega
  top i := by
    rw [D.toHoneycombAssignment.turn_tile b i (N-1) (by omega),
      show N-1-(N-1)=0 from Nat.sub_self _,Tile.turn_occupied_three]
    simp only [D.bottom,false_iff]
    exact BoundaryPort.noConfusion
  drains := by
    have hh:=D.toHoneycombAssignment.turn_drains b D.drains
    simpa only [Graph.DrainsAt,turnTriangle,down,up,sub_self,Nat.sub_self,Bool.not_false] using hh

def ofArch (D : HoneycombConfiguration N (.bottom (b-a))) (hN : 1≤N) :
    TopArchConfiguration N a b where
  toHoneycombAssignment := D.toHoneycombAssignment.turn b
  bottom i := by
    rw [D.toHoneycombAssignment.turn_tile b i 0 (by omega),Tile.turn_occupied_zero,Nat.sub_zero,
      D.top]
    exact BoundaryPort.noConfusion
  top i := by
    rw [D.toHoneycombAssignment.turn_tile b i (N-1) (by omega),
      Nat.sub_self,Tile.turn_occupied_three,D.bottom]
    simp only [BoundaryPort.bottom.injEq]
    omega
  drains := by
    have hh:=D.toHoneycombAssignment.turn_drains b D.drains
    simpa only [turnTriangle,down,up,sub_zero,Nat.sub_zero,Bool.not_true] using hh

@[simp] lemma ofArch_toArch (D : TopArchConfiguration N a b) (hN : 1≤N) :
    ofArch (D.toArch hN) hN=D := by
  apply ext
  exact D.toHoneycombAssignment.turn_turn b

end TopArchConfiguration
end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace PaddedColumn
variable {n : ℕ}

 

theorem runs_exists (hn : 0<n) (ts : List (Configuration n))
    (hc : ColumnChain.Compatible (empty n) ts)
    (hd : Graph.DrainsBoundary (wiring ts) boundary) :
    ∃ q, ColumnChain.Runs (empty n) ts q := by
  induction ts with
  | nil => exact ⟨empty n,rfl⟩
  | cons t ts ih =>
    obtain ⟨hc,ht⟩:=hc
    have hd' := (stepEquivalence t ts).symm.drains hd
    have hl := Graph.glued_drains_local (wiring ts) (BareColumn t) boundary
      (fun i=>(i,1)) (active ts) (fun i=>(i,2)) hd'
    obtain ⟨p,hp⟩:=ih hc hl
    have hg:=runs_realizes ts p hp
    have he : active ts=p.Occupied := by
      funext i
      exact propext ((ColumnChain.support_empty_read ts i).symm.trans
        (by rw [(ColumnChain.runs_sound _ _ _ hp).2.2]))
    rw [he] at hd'
    have ht' : ColumnCompatible p.Occupied t := by
      simpa only [(ColumnChain.runs_sound _ _ _ hp).2.2] using ht
    have hdr := (hg.substitute_drains_iff (BareColumn t) (fun i=>(i,1)) (fun i=>(i,2))).mp hd'
    obtain ⟨q,hq⟩:=realizes_exists_of_drains hn p t ht' ((ColumnSew.equivalence p t).drains hdr)
    exact ⟨q,p,hp,hq⟩

end PaddedColumn
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace NorthExtension

 
def tile (a b i : ℤ) : Tile :=
  if i=a then .vertical₀ else if i=b then .cap else
    if a< i ∧ i<b then .diagonal₁ else .vacant

lemma physical (a b i : ℤ) : tile a b i≠.verticalPair := by
  unfold tile
  split_ifs <;> decide

lemma south (a b i : ℤ) (_h : a<b) :
    (tile a b i).Occupied 0 ↔ i=a ∨ i=b := by
  unfold tile
  split_ifs with ha hb hi
  · simp only [ha,true_or]; decide
  · simp only [hb,or_true]; decide
  · simp only [ha,hb,false_or]; decide
  · simp only [ha,hb,false_or]; decide

lemma west (a b i : ℤ) (h : a<b) :
    (tile a b i).Occupied 1 ↔ a< i ∧ i≤b := by
  unfold tile
  split_ifs with ha hb hi
  · subst i
    have hh : ¬a<a := by omega
    simp only [hh,false_and]
    decide
  · subst i
    simp only [h,le_refl,and_self]
    decide
  · have hb' : i≤b := le_of_lt hi.2
    simp only [hi.1,hb',and_self]
    decide
  · have hi' : ¬(a< i ∧ i≤b) := by omega
    simp only [hi']
    decide

lemma east (a b i : ℤ) (h : a<b) :
    (tile a b i).Occupied 2 ↔ a≤ i ∧ i<b := by
  unfold tile
  split_ifs with ha hb hi
  · subst i
    simp only [h,le_refl,and_self]
    decide
  · subst i
    have hh : ¬b<b := by omega
    simp only [hh,and_false]
    decide
  · have ha' : a≤ i := le_of_lt hi.1
    simp only [ha',hi.2,and_self]
    decide
  · have hi' : ¬(a≤ i ∧ i<b) := by omega
    simp only [hi']
    decide

end NorthExtension

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

 

def extend (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) :
    HoneycombAssignment (N+1) where
  tile q := if q.2=N then NorthExtension.tile a b q.1 else D.tile q
  physical q := by split; exact NorthExtension.physical _ _ _; exact D.physical q
  outside i j hj := by
    rw [ite_eq_right (by omega)]
    exact D.outside i j (by omega)
  horizontal i j := by
    by_cases hj : j=N
    · simp only [hj,ite_true,NorthExtension.east a b i hab,
        NorthExtension.west a b (i+1) hab]
      omega
    · simpa only [hj,ite_false] using D.horizontal i j
  vertical i j hj := by
    have hn : j<N := by omega
    have hn' : j≠N := by omega
    simp only [hn',ite_false]
    by_cases he : j+1=N
    · rw [ite_eq_left he,NorthExtension.south _ _ _ hab]
      have he' : j=N-1 := by omega
      exact he' ▸ D.top i
    · rw [ite_eq_right he]
      exact D.vertical i j (by omega)

@[simp] lemma extend_last (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) (i : ℤ) :
    (D.extend hN hab).tile (i,N)=NorthExtension.tile a b i := by simp [extend]

lemma extend_base (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (i : ℤ) (j : ℕ) (hj : j<N) : (D.extend hN hab).tile (i,j)=D.tile (i,j) :=
  ite_eq_right (by omega)

@[simp] lemma extend_restrict (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b) :
    (D.extend hN hab).restrict N (by omega)=D.toHoneycombAssignment := by
  apply HoneycombAssignment.ext
  funext ⟨i,j⟩
  by_cases hj : j<N
  · rw [HoneycombAssignment.restrict_tile _ _ _ i j hj,D.extend_base hN hab i j hj]
  · rw [HoneycombAssignment.outside _ i j (by omega),D.outside i j (by omega)]

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


namespace Diagram.Tile
@[simp] lemma turn_nonvacant (t : Tile) : t.turn≠.vacant ↔ t≠.vacant := by cases t <;> decide
end Diagram.Tile

namespace HoneycombAssignment
variable {N : ℕ}


def Fits (D : HoneycombAssignment N) (m : ℕ) : Prop :=
  ∀q : Cell,D.tile q≠.vacant → -(m:ℤ)≤q.1 ∧ q.1<(m:ℤ)

lemma Fits.vacant_left {D : HoneycombAssignment N} {m k : ℕ} (h : D.Fits m) (hk : m≤k)
    (j : ℕ) : D.tile (-1-(k:ℤ),j)=.vacant := by
  by_contra he
  have hh:=(h _ he).1
  omega

lemma Fits.vacant_right {D : HoneycombAssignment N} {m k : ℕ} (h : D.Fits m) (hk : m≤k)
    (j : ℕ) : D.tile ((k:ℤ),j)=.vacant := by
  by_contra he
  have hh:=(h _ he).2
  omega

def leftClip (D : HoneycombAssignment N) (m : ℕ) : Fin m → Configuration N :=
  fun k j=>D.tile (-1-(k.val:ℤ),j.val)

def rightClip (D : HoneycombAssignment N) (m : ℕ) : Fin m → Configuration N :=
  fun k j=>(D.tile ((k.val:ℤ),j.val)).horizontal

lemma read_leftClip (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m) (k : ℕ) (j : Fin N) :
    ColumnChain.read (List.ofFn (D.leftClip m)) k j=D.tile (-1-(k:ℤ),j.val) := by
  by_cases hk : k < m
  · simp only [ColumnChain.read,List.getElem?_ofFn,hk,dite_eq_left,Option.getD_some,leftClip]
  · rw [ColumnChain.read_ge _ k (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hk),
      h.vacant_left (by omega)]

lemma read_rightClip (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m) (k : ℕ) (j : Fin N) :
    ColumnChain.read (List.ofFn (D.rightClip m)) k j=(D.tile ((k:ℤ),j.val)).horizontal := by
  by_cases hk : k < m
  · simp only [ColumnChain.read,List.getElem?_ofFn,hk,dite_eq_left,Option.getD_some,rightClip]
  · rw [ColumnChain.read_ge _ k (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hk),
      h.vacant_right (by omega)]
    rfl

end HoneycombAssignment

end

 

 

noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Graph

lemma glued_drainsAt_halves {V W I : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (root : I)
    (h : DrainsAt (Patch.glued r s a b active) (.inr (b root))) :
    DrainsBoundary r a ∧ DrainsBoundary s b := by
  constructor
  · intro v w hvw
    obtain ⟨i,hi,hr,_⟩:=Patch.reach_to_exterior r s a b active (h (.inl v) (.inl w) hvw)
    exact ⟨i,hr⟩
  · intro v w hvw
    exact glued_reach_right_boundary r s a b active root (h (.inr v) (.inr w) hvw)

end Diagram.Graph

end

 

 

noncomputable section
open scoped Classical BigOperators
open Diagram

namespace SewnRectangle
variable {N : ℕ}

def leftWeights (N : ℕ) : Fin (N+1) → Weights ℝ :=
  Fin.snoc (fun _ : Fin N=>physicalWeights (2*Diagram.lambda)) northInjectionWeights

def rightWeights (N : ℕ) : Fin (N+1) → Weights ℝ :=
  Fin.snoc (fun _ : Fin N=>physicalWeights Diagram.lambda) northInjectionWeights

end SewnRectangle

 

 


namespace Diagram.ColumnChain
lemma weight_ofFn {K : Type*} [CommRing K] {n m : ℕ}
    (w : Fin n → Weights K) (h : Fin m → Configuration n) :
    weight w (List.ofFn h)=∏ k, ∏ j,(w j).tile (h k j) := by
  induction m with
  | zero => simp [weight]
  | succ m ih => rw [List.ofFn_succ,weight,ih,Fin.prod_univ_succ]
end Diagram.ColumnChain


namespace HoneycombAssignment
variable {N : ℕ}

lemma physical_tile_weight_ne_zero (D : HoneycombAssignment N) (q : Cell) :
    (physicalWeights (2*Diagram.lambda)).tile (D.tile q) ≠ 0 := by
  have ht := D.physical q
  have hr : Diagram.rho≠0 := by simpa only [Diagram.rho,rho] using (ne_of_gt rho_pos)
  rw [physicalWeights_two_lambda]
  generalize D.tile q=t at *
  cases t <;> simp_all [Weights.tile]
end HoneycombAssignment

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

lemma extend_left_north_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (hb : 0≤b) (k : ℕ) :
    (northInjectionWeights : Weights ℝ).tile ((D.extend hN hab).tile (-1-(k:ℤ),N))=1 := by
  rw [D.extend_last hN hab]
  unfold NorthExtension.tile
  split_ifs with h₁ h₂ h₃ <;> first | omega | rfl

lemma extend_right_north_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a<0) (k : ℕ) :
    (northInjectionWeights : Weights ℝ).tile ((D.extend hN hab).tile ((k:ℤ),N)).horizontal=1 := by
  rw [D.extend_last hN hab]
  unfold NorthExtension.tile
  split_ifs with h₁ h₂ h₃ <;> first | omega | rfl

lemma leftClip_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (hb : 0≤b) (m : ℕ) :
    ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn ((D.extend hN hab).leftClip m))=
      ∏ k : Fin m,∏ j : Fin N,
        (physicalWeights (2*Diagram.lambda)).tile (D.tile (-1-(k.val:ℤ),j.val)) := by
  rw [ColumnChain.weight_ofFn]
  apply Finset.prod_congr rfl
  intro k _
  rw [Fin.prod_univ_castSucc]
  simp only [SewnRectangle.leftWeights,Fin.snoc_last,Fin.snoc_castSucc,
    HoneycombAssignment.leftClip,Fin.val_castSucc,Fin.val_last]
  rw [D.extend_left_north_weight hN hab hb k.val,mul_one]
  apply Finset.prod_congr rfl
  intro j _
  rw [D.extend_base hN hab _ _ j.isLt]

lemma rightClip_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a<0) (m : ℕ) :
    ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn ((D.extend hN hab).rightClip m))=
      ∏ k : Fin m,∏ j : Fin N,
        (physicalWeights (2*Diagram.lambda)).tile (D.tile ((k.val:ℤ),j.val)) := by
  rw [ColumnChain.weight_ofFn]
  apply Finset.prod_congr rfl
  intro k _
  rw [Fin.prod_univ_castSucc]
  simp only [SewnRectangle.rightWeights,Fin.snoc_last,Fin.snoc_castSucc,
    HoneycombAssignment.rightClip,Fin.val_castSucc,Fin.val_last]
  rw [D.extend_right_north_weight hN hab ha k.val,mul_one]
  apply Finset.prod_congr rfl
  intro j _
  rw [D.extend_base hN hab _ _ j.isLt,←Tile.physical_horizontal_weight_two,Tile.horizontal_involutive]



lemma clips_weight_ne_zero (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a<0) (hb : 0≤b) (m : ℕ) :
    ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn ((D.extend hN hab).leftClip m))≠0 ∧
    ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn ((D.extend hN hab).rightClip m))≠0 := by
  rw [D.leftClip_weight hN hab hb,D.rightClip_weight hN hab ha]
  constructor <;> apply Finset.prod_ne_zero_iff.mpr <;> intro k _ <;>
    apply Finset.prod_ne_zero_iff.mpr <;> intro j _ <;>
    exact HoneycombAssignment.physical_tile_weight_ne_zero _ _

end TopArchConfiguration
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



structure CrossTopArch (N : ℕ) where
  left : ℕ
  right : ℕ
  arch : TopArchConfiguration N (-1-(left:ℤ)) right

namespace CrossTopArch
variable {N : ℕ}

@[ext] lemma ext {D E : CrossTopArch N} (h : D.arch.tile=E.arch.tile) : D=E := by
  have hl := (D.arch.top (-1-(D.left:ℤ))).mpr (Or.inl rfl)
  have hr := (D.arch.top D.right).mpr (Or.inr rfl)
  rw [h,E.arch.top] at hl hr
  have h₁ : D.left=E.left := by omega
  have h₂ : D.right=E.right := by omega
  cases D with
  | mk l r D =>
    cases E with
    | mk l' r' E =>
      dsimp at h₁ h₂; subst l' r'
      congr 1
      exact TopArchConfiguration.ext (HoneycombAssignment.ext h)

def Fits (D : CrossTopArch N) (m : ℕ) : Prop := D.arch.toHoneycombAssignment.Fits m


abbrev Bounded (N m : ℕ) := {D : CrossTopArch N // D.Fits m}

end CrossTopArch

 

structure NorthHistory (N m : ℕ) where
  left : Fin m → Configuration (N+1)
  right : Fin m → Configuration (N+1)
  nzleft : ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn left)≠0
  nzright : ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn right)≠0
  realizes : ∃p q : Pairing (N+1),
    ColumnChain.Runs (empty (N+1)) (List.ofFn left) p ∧
    ColumnChain.Runs (empty (N+1)) (List.ofFn right) q ∧ p.GluesAt (Fin.last N) q

namespace NorthHistory
variable {N m : ℕ}

@[ext] lemma ext {D E : NorthHistory N m} (hl : D.left=E.left) (hr : D.right=E.right) : D=E := by
  cases D; cases E; cases hl; cases hr; rfl

end NorthHistory
end
end CriticalStrip





end OAI
end


