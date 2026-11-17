-- Prove2me | solution 1 for APFPaper5.K1.SharedOnlyWitness.shared_only_family_meets_K1
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:48:35.653171+00:00
-- url     : https://prove2.me/submissions/0d83f6df-1e3d-43e5-b490-e3ce8833ac0e

import Definitions.Def_APFPaper5_K1_shared_only_witness_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_shared_only_witness
title: A counted family with no record of negative cost exists: two distinctions with one record both need and one record each, every record costing 1; every premise of the pass-29 K1 statement holds there, and so its conclusion does
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 21:44 HST: "Derive all items stil owed for k1". Item owed since pass 29: a
 typed world in which the last premise of counted_family_satisfies_K1_of_nonneg_shared holds.
 Thm_APFPaper5_K1_cost_book, Thm_APFPaper5_K1_interface_cost_book, Thm_APFPaper5_K1_interface_bridge_witness
 (this seat). Builder seat: familyCost_weighted, APFB05.weighted_record_model_satisfies_floor,
 recordModel_supportNovel_of_needs_own_record.
standing: A WORLD. It shows the pass-29 K1 statement is not empty. It is not a claim about any physical
 interface.
what this file says:
 1. book_univ_two. For two distinctions, the record both need costs what the two cost apart, less what
    they cost together, less what the empty family costs.
 2. pairCost values: the empty family costs 0, each distinction 2, the two together 3.
 3. shared_only_family_meets_K1. In this world B05 holds as declared, the family of the two distinctions
    is counted, no record needed by both has negative cost (it costs 1), and the table of shared costs is
    bilinear with a nonnegative and faithful diagonal.
what this file does NOT say: that the declared inputs force this world. No lane. No claim that the transfer
 is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_interface_cost_book_Vocabulary
import Theorems.Thm_APFPaper5_K1_counted_family_satisfies_K1_of_nonneg_shared
import Definitions.Def_APFPaper5_K1_interface_bridge_witness_Vocabulary
import Theorems.Thm_APFPaper5_K1_BridgeWitness_exactly_served
import Theorems.Thm_APFPaper5_K1_weighted_marginal_ge
import Theorems.Thm_APFB05_weighted_record_model_satisfies_floor
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1

/-- For two distinctions, the record both need costs what the two cost apart, less what they cost
together, less what the empty family costs. -/
theorem book_univ_two (f : Finset (Fin 2) → ℝ) :
    book f Finset.univ = f {0} + f {1} - f Finset.univ - f ∅ := by
  have hss : (Finset.univ : Finset (Fin 2)).ssubsets = {∅, {0}, {1}} := by decide
  have h := bookCost_eq (addsOverRest f) Finset.univ
  rw [hss, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h
  have h0 := book_empty f
  have h1 := book_singleton f 0
  have h2 := book_singleton f 1
  have c0 : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
  have c1 : ({1} : Finset (Fin 2))ᶜ = {0} := by decide
  rw [c0] at h1
  rw [c1] at h2
  have hg : addsOverRest f Finset.univ = f Finset.univ - f ∅ := by simp [addsOverRest]
  unfold book at h0 h1 h2 ⊢
  rw [h, hg, h0, h1, h2]
  ring

namespace SharedOnlyWitness

open BridgeWitness



theorem pairCost_eq_card (S : Finset (Fin 2)) :
    pairCost S = (((S.biUnion (fam (ι := Fin 2))).card : ℕ) : ℝ) := by
  show familyCost (D := Fin 2) (P := Finset (Option (Fin 2))) (R := Finset (Option (Fin 2)))
    (Record := Option (Fin 2)) (fun p => p) (fun r => ∑ a ∈ r, w a)
    (fun p => (↑p : Set (Option (Fin 2))))
    (fun _ sigma d => (↑(fam d) : Set (Option (Fin 2))) ⊆ sigma) (fun _ _ _ => True)
    (S.image fun i : Fin 2 => i) = _
  rw [Finset.image_id', familyCost_weighted]
  simp [w]

theorem pairCost_empty : pairCost ∅ = 0 := by
  rw [pairCost_eq_card]
  simp

theorem pairCost_zero : pairCost {0} = 2 := by
  rw [pairCost_eq_card]
  have h : ((({0} : Finset (Fin 2)).biUnion (fam (ι := Fin 2))).card) = 2 := by decide
  rw [h]
  norm_num

theorem pairCost_one : pairCost {1} = 2 := by
  rw [pairCost_eq_card]
  have h : ((({1} : Finset (Fin 2)).biUnion (fam (ι := Fin 2))).card) = 2 := by decide
  rw [h]
  norm_num

theorem pairCost_univ : pairCost Finset.univ = 3 := by
  rw [pairCost_eq_card]
  have h : (((Finset.univ : Finset (Fin 2)).biUnion (fam (ι := Fin 2))).card) = 3 := by decide
  rw [h]
  norm_num

/-- The record both distinctions need costs 1. -/
theorem shared_record_costs_one : book pairCost Finset.univ = 1 := by
  rw [book_univ_two, pairCost_zero, pairCost_one, pairCost_univ, pairCost_empty]
  norm_num

/-- Every premise of the pass-29 K1 statement holds in this world, and so its conclusion does. -/
theorem shared_only_family_meets_K1 :
    IsBilinear (VP := Fin 2 → ℝ) (VE := Fin 2 → ℝ)
        (tableForm (fun i j : Fin 2 => sharedCost pairCost {i} {j})) ∧
      FaithfulNonnegDiagonal (tableForm (fun i j : Fin 2 => sharedCost pairCost {i} {j}))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      familyCost (D := Fin 2) (P := Finset (Option (Fin 2))) (R := Finset (Option (Fin 2)))
        (Record := Option (Fin 2)) (fun p => p) (fun r => ∑ a ∈ r, w a)
        (fun p => (↑p : Set (Option (Fin 2))))
        (fun _ sigma d => (↑(fam d) : Set (Option (Fin 2))) ⊆ sigma) (fun _ _ _ => True)
        (Finset.univ.image (fun i : Fin 2 => i)) ≤ C := ⟨_, le_refl _⟩
  have hfeas : familyFeasible (fun p : Finset (Option (Fin 2)) => (↑p : Set (Option (Fin 2))))
      (fun (_ : Finset (Option (Fin 2))) (sigma : Set (Option (Fin 2))) (d : Fin 2) =>
        (↑(fam d) : Set (Option (Fin 2))) ⊆ sigma)
      (fun (_ : Finset (Option (Fin 2))) (_ : Fin 2) (_ : Set (Option (Fin 2))) => True)
      (Finset.univ.image (fun i : Fin 2 => i)) := by
    obtain ⟨p, _, hp⟩ := exactly_served (Finset.univ.image (fun i : Fin 2 => i))
    exact ⟨p, hp⟩
  have hneeds : ∀ i : Fin 2,
      ¬ fam i ⊆ ((({i} : Finset (Fin 2))ᶜ).image (fun i : Fin 2 => i)).biUnion fam := by
    decide
  have hshared : ∀ T : Finset (Fin 2), 2 ≤ T.card → 0 ≤ book pairCost T := by
    intro T hT
    have hle : T.card ≤ 2 := by simpa using Finset.card_le_univ T
    have hT' : T = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin]
      omega
    rw [hT', shared_record_costs_one]
    norm_num
  have key := counted_family_satisfies_K1_of_nonneg_shared (D := Fin 2) (ι := Fin 2)
    (fun p : Finset (Option (Fin 2)) => p) (fun r : Finset (Option (Fin 2)) => ∑ a ∈ r, w a)
    (fun p : Finset (Option (Fin 2)) => (↑p : Set (Option (Fin 2))))
    (fun (_ : Finset (Option (Fin 2))) (sigma : Set (Option (Fin 2))) (d : Fin 2) =>
      (↑(fam d) : Set (Option (Fin 2))) ⊆ sigma)
    (fun (_ : Finset (Option (Fin 2))) (_ : Fin 2) (_ : Set (Option (Fin 2))) => True)
    (fun _ => True) C 1
    (APFB05.weighted_record_model_satisfies_floor (Context := Unit) w fam 1 one_pos
      (fun a => by simp [w]) (fun _ => C))
    (fun i : Fin 2 => i) (And.intro hfeas hC) (fun _ => trivial)
    (fun i => recordModel_supportNovel_of_needs_own_record w fam 1 one_pos
      (fun a => by simp [w]) _ i (hneeds i))
    hshared
  exact key

end SharedOnlyWitness

end APFPaper5.K1


theorem solution :
And
  (@APFPaper5.K1.IsBilinear.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
      Real.semiring (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
      Real.semiring (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@APFPaper5.K1.tableForm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      fun (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
      @APFPaper5.K1.sharedCost.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        APFPaper5.K1.SharedOnlyWitness.pairCost
        (@Singleton.singleton.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Finset.instSingleton.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) i)
        (@Singleton.singleton.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Finset.instSingleton.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) j)))
  (@APFPaper5.K1.FaithfulNonnegDiagonal.{0, 0}
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
      Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
      Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
    (@APFPaper5.K1.tableForm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      fun (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
      @APFPaper5.K1.sharedCost.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        APFPaper5.K1.SharedOnlyWitness.pairCost
        (@Singleton.singleton.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Finset.instSingleton.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) i)
        (@Singleton.singleton.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Finset.instSingleton.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) j))
    (@LinearEquiv.refl.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
      Real.semiring
      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommMonoid)
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
        Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring)))) := by
  exact @APFPaper5.K1.SharedOnlyWitness.shared_only_family_meets_K1
