-- Prove2me | solution 1 for APFPaper5.K1.ledger_party_score_meets_K1_explicit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:40:32.690727+00:00
-- url     : https://prove2.me/submissions/fad04411-e72c-4c08-8e3e-50101a857525

import Definitions.Def_APFPaper5_K1_LedgerPartyScore
import Definitions.Def_APFPaper5_K1_LedgerScore
import Theorems.Thm_APFPaper5_K1_partyTo_book_iff
import Theorems.Thm_APFPaper5_K1_partyScore_book
import Theorems.Thm_APFPaper5_K1_partyScore_book_meets_K1
import Theorems.Thm_APFPaper5_K1_partyScore_book_faithful_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_eq_partyScore_of_no_joint
import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper5_K1_interface_region_satisfies_K1_of_floor
import Theorems.Thm_APFPaper1_RecordLedger_bill_eq_sum
import Theorems.Thm_APFPaper1_RecordLedger_maintained_eq_kept
import Theorems.Thm_APFPaper1_RecordLedger_needsFin_subset_of_sufficient
import Theorems.Thm_APFB05_overfull_chain_not_admissible
import Theorems.Thm_APFB05_no_admissible_family_contains_overfull_chain
import Theorems.Thm_APFB05_no_room_for_new_record
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4

open APFPaper1 APFPaper1.Source APFPaper5 APFPaper5.K1

theorem APFPaper5.K1.ledger_party_score_meets_K1_explicit :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3} {ι : Type apfNative_u_4}
  [inst : Fintype.{apfNative_u_4} ι] [inst_1 : DecidableEq.{apfNative_u_4 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : Fintype.{apfNative_u_3} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (dist : ι → D)
  (hown :
    ∀ (i : ι),
      @Exists.{apfNative_u_3 + 1} Record fun (a : Record) =>
        And
          (@LT.lt.{0} NNReal (@Preorder.toLT.{0} NNReal (@PartialOrder.toPreorder.{0} NNReal NNReal.instPartialOrder))
            (@OfNat.ofNat.{0} NNReal (nat_lit 0) (@Zero.toOfNat0.{0} NNReal NNReal.instZero))
            (@APFPaper1.RecordLedger.cost.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L a))
          (And
            (@Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
              (@Set.instMembership.{apfNative_u_3} Record)
              (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L
                (@Singleton.singleton.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
                  (@Finset.instSingleton.{apfNative_u_1} D) (dist i)))
              a)
            (Not
              (@Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
                (@Set.instMembership.{apfNative_u_3} Record)
                (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L
                  (@Finset.image.{apfNative_u_4, apfNative_u_1} ι D inst_2 dist
                    (@Finset.erase.{apfNative_u_4} ι inst_1 (@Finset.univ.{apfNative_u_4} ι inst) i)))
                a)))),
  And
    (@APFPaper5.K1.IsBilinear.{apfNative_u_4, apfNative_u_4} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_4} ι inst
        (@APFPaper5.K1.ledgerPartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
          inst_1 inst_2 inst_3 L dist)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u_4, apfNative_u_4} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_4} ι inst
        (@APFPaper5.K1.ledgerPartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
          inst_1 inst_2 inst_3 L dist))
      (@LinearEquiv.refl.{0, apfNative_u_4} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by
  intro D P Record ι inst inst_1 inst_2 inst_3 L dist hown
  classical
  have gen : ∀ (w : Record → ℝ) (hw : ∀ a, 0 ≤ w a) (keeps : Finset ι → Record → Bool)
      (hown : ∀ i, ∃ a, 0 < w a ∧ PartyTo keeps i a ∧ ∀ j, PartyTo keeps j a → j = i),
      IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (partyScore w keeps)) ∧
      FaithfulNonnegDiagonal (tableForm (partyScore w keeps)) (LinearEquiv.refl ℝ (ι → ℝ)) := by
    intro w hw keeps hown
    have hbil : ∀ G : ι → ι → ℝ, IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) := by
      intro G
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
        simp only [tableForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib] <;>
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    have key : ∀ x : ι → ℝ, tableForm (partyScore w keeps) x x =
        ∑ a, w a * (∑ i, x i * ind (partyMark keeps i a)) ^ 2 := by
      intro x
      simp only [tableForm, partyScore, atomTable, sq, Finset.mul_sum, Finset.sum_mul]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring
    refine ⟨hbil _, fun x => ?_, fun x hx => ?_⟩
    · rw [LinearEquiv.refl_apply, key]
      exact Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (sq_nonneg _)
    · rw [LinearEquiv.refl_apply, key] at hx
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => mul_nonneg (hw a) (sq_nonneg _))).mp hx
      funext i
      show x i = 0
      obtain ⟨a, hwa, hpa, huniq⟩ := hown i
      have h1 := hz a (Finset.mem_univ _)
      have h2 : (∑ j, x j * ind (partyMark keeps j a)) = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · linarith
        · exact pow_eq_zero_iff two_ne_zero |>.mp h
      rw [Finset.sum_eq_single i] at h2
      · have : partyMark keeps i a = true := by simp [partyMark, hpa]
        simpa [ind, this] using h2
      · intro j _ hj
        have hnp : ¬ PartyTo keeps j a := fun hp => hj (huniq j hp)
        have : partyMark keeps j a = false := by simp [partyMark, hnp]
        simp [ind, this]
      · simp
  have mono : ∀ S T : Finset D, S ⊆ T → familyNeeds L S ⊆ familyNeeds L T := by
    intro S T hST a ha p hp
    exact ha p (fun d hd => hp d (hST hd))
  have hk : ∀ (S : Finset ι) (a : Record), ledgerKeeps L dist S a = true ↔ a ∈ familyNeeds L (S.image dist) := by
    intro S a
    simp only [ledgerKeeps, decide_eq_true_eq]
  have hk' : ∀ (S : Finset ι) (a : Record), ledgerKeeps L dist S a = false ↔ a ∉ familyNeeds L (S.image dist) := by
    intro S a
    simp only [ledgerKeeps, decide_eq_false_iff_not]
  apply gen (fun a => ((L.cost a : NNReal) : ℝ)) (fun a => NNReal.coe_nonneg _) (ledgerKeeps L dist)
  intro i
  obtain ⟨a, hc, hin, hnot⟩ := hown i
  refine ⟨a, hc, ⟨Finset.univ.erase i, ?_, ?_⟩, ?_⟩
  · rw [hk, Finset.insert_erase (Finset.mem_univ i)]
    exact mono _ _ (by intro d hd; simp at hd; subst hd; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)) hin
  · rw [hk']; exact hnot
  · intro j ⟨S, h1, h2⟩
    by_contra hji
    rw [hk] at h1
    rw [hk'] at h2
    by_cases hiS : i ∈ S
    · exact h2 (mono _ _ (by intro d hd; simp at hd; subst hd; exact Finset.mem_image_of_mem _ hiS) hin)
    · apply hnot
      refine mono _ _ ?_ h1
      apply Finset.image_subset_image
      intro t ht
      rw [Finset.mem_insert] at ht
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rcases ht with rfl | ht
      · exact Ne.symm (Ne.symm hji)
      · exact fun h => hiS (h ▸ ht)

theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3} {ι : Type apfNative_u_4}
  [inst : Fintype.{apfNative_u_4} ι] [inst_1 : DecidableEq.{apfNative_u_4 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : Fintype.{apfNative_u_3} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (dist : ι → D)
  (hown :
    ∀ (i : ι),
      @Exists.{apfNative_u_3 + 1} Record fun (a : Record) =>
        And
          (@LT.lt.{0} NNReal (@Preorder.toLT.{0} NNReal (@PartialOrder.toPreorder.{0} NNReal NNReal.instPartialOrder))
            (@OfNat.ofNat.{0} NNReal (nat_lit 0) (@Zero.toOfNat0.{0} NNReal NNReal.instZero))
            (@APFPaper1.RecordLedger.cost.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L a))
          (And
            (@Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
              (@Set.instMembership.{apfNative_u_3} Record)
              (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L
                (@Singleton.singleton.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
                  (@Finset.instSingleton.{apfNative_u_1} D) (dist i)))
              a)
            (Not
              (@Membership.mem.{apfNative_u_3, apfNative_u_3} Record (Set.{apfNative_u_3} Record)
                (@Set.instMembership.{apfNative_u_3} Record)
                (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L
                  (@Finset.image.{apfNative_u_4, apfNative_u_1} ι D inst_2 dist
                    (@Finset.erase.{apfNative_u_4} ι inst_1 (@Finset.univ.{apfNative_u_4} ι inst) i)))
                a)))),
  And
    (@APFPaper5.K1.IsBilinear.{apfNative_u_4, apfNative_u_4} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_4} ι inst
        (@APFPaper5.K1.ledgerPartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
          inst_1 inst_2 inst_3 L dist)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u_4, apfNative_u_4} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u_4} ι inst
        (@APFPaper5.K1.ledgerPartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst
          inst_1 inst_2 inst_3 L dist))
      (@LinearEquiv.refl.{0, apfNative_u_4} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u_4, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u_4, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by
  intro D P Record ι inst inst_1 inst_2 inst_3 L dist hown
  classical
  have gen : ∀ (w : Record → ℝ) (hw : ∀ a, 0 ≤ w a) (keeps : Finset ι → Record → Bool)
      (hown : ∀ i, ∃ a, 0 < w a ∧ PartyTo keeps i a ∧ ∀ j, PartyTo keeps j a → j = i),
      IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (partyScore w keeps)) ∧
      FaithfulNonnegDiagonal (tableForm (partyScore w keeps)) (LinearEquiv.refl ℝ (ι → ℝ)) := by
    intro w hw keeps hown
    have hbil : ∀ G : ι → ι → ℝ, IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) := by
      intro G
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
        simp only [tableForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib] <;>
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    have key : ∀ x : ι → ℝ, tableForm (partyScore w keeps) x x =
        ∑ a, w a * (∑ i, x i * ind (partyMark keeps i a)) ^ 2 := by
      intro x
      simp only [tableForm, partyScore, atomTable, sq, Finset.mul_sum, Finset.sum_mul]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => by ring
    refine ⟨hbil _, fun x => ?_, fun x hx => ?_⟩
    · rw [LinearEquiv.refl_apply, key]
      exact Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (sq_nonneg _)
    · rw [LinearEquiv.refl_apply, key] at hx
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => mul_nonneg (hw a) (sq_nonneg _))).mp hx
      funext i
      show x i = 0
      obtain ⟨a, hwa, hpa, huniq⟩ := hown i
      have h1 := hz a (Finset.mem_univ _)
      have h2 : (∑ j, x j * ind (partyMark keeps j a)) = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · linarith
        · exact pow_eq_zero_iff two_ne_zero |>.mp h
      rw [Finset.sum_eq_single i] at h2
      · have : partyMark keeps i a = true := by simp [partyMark, hpa]
        simpa [ind, this] using h2
      · intro j _ hj
        have hnp : ¬ PartyTo keeps j a := fun hp => hj (huniq j hp)
        have : partyMark keeps j a = false := by simp [partyMark, hnp]
        simp [ind, this]
      · simp
  have mono : ∀ S T : Finset D, S ⊆ T → familyNeeds L S ⊆ familyNeeds L T := by
    intro S T hST a ha p hp
    exact ha p (fun d hd => hp d (hST hd))
  have hk : ∀ (S : Finset ι) (a : Record), ledgerKeeps L dist S a = true ↔ a ∈ familyNeeds L (S.image dist) := by
    intro S a
    simp only [ledgerKeeps, decide_eq_true_eq]
  have hk' : ∀ (S : Finset ι) (a : Record), ledgerKeeps L dist S a = false ↔ a ∉ familyNeeds L (S.image dist) := by
    intro S a
    simp only [ledgerKeeps, decide_eq_false_iff_not]
  apply gen (fun a => ((L.cost a : NNReal) : ℝ)) (fun a => NNReal.coe_nonneg _) (ledgerKeeps L dist)
  intro i
  obtain ⟨a, hc, hin, hnot⟩ := hown i
  refine ⟨a, hc, ⟨Finset.univ.erase i, ?_, ?_⟩, ?_⟩
  · rw [hk, Finset.insert_erase (Finset.mem_univ i)]
    exact mono _ _ (by intro d hd; simp at hd; subst hd; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)) hin
  · rw [hk']; exact hnot
  · intro j ⟨S, h1, h2⟩
    by_contra hji
    rw [hk] at h1
    rw [hk'] at h2
    by_cases hiS : i ∈ S
    · exact h2 (mono _ _ (by intro d hd; simp at hd; subst hd; exact Finset.mem_image_of_mem _ hiS) hin)
    · apply hnot
      refine mono _ _ ?_ h1
      apply Finset.image_subset_image
      intro t ht
      rw [Finset.mem_insert] at ht
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rcases ht with rfl | ht
      · exact Ne.symm (Ne.symm hji)
      · exact fun h => hiS (h ▸ ht)


