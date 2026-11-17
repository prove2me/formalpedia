-- Prove2me | solution 2 for APFPaper5.K1.ledger_counted_family_party_score_satisfies_K1_explicit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:40:33.783325+00:00
-- url     : https://prove2.me/submissions/16a65c26-e936-4518-94c5-ffd5833c89e7

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

theorem APFPaper5.K1.ledger_counted_family_party_score_satisfies_K1_explicit :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3} {ι : Type apfNative_u_4}
  [inst : Fintype.{apfNative_u_4} ι] [inst_1 : DecidableEq.{apfNative_u_4 + 1} ι]
  [inst_2 : DecidableEq.{apfNative_u_1 + 1} D] [inst_3 : Fintype.{apfNative_u_3} Record]
  [inst_4 : DecidableEq.{apfNative_u_3 + 1} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (tested : D → Prop)
  (C eps : Real)
  (hB05 :
    @APFB05.MarginalFloor.{0, apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_3} Unit (fun (x : Unit) => D)
      (fun (x : Unit) => P) (fun (x : Unit) => Finset.{apfNative_u_3} Record) (fun (x : Unit) => Record)
      (fun (g : Unit) => inst_2)
      (fun (x : Unit) =>
        @APFPaper1.RecordLedger.wholeResource.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.calibration.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.maintained.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.sufficient.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) =>
        @APFPaper1.RecordLedger.usesToRealize.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => tested) (fun (x : Unit) => C) fun (x : Unit) => eps)
  (havail : @APFPaper5.K1.LedgerAvailable.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record inst_4 L C)
  (dist : ι → D)
  (hcounted :
    @APFPaper5.K1.LedgerCounted.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst inst_1
      inst_2 L tested C dist),
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
  intro D P Record ι inst inst_1 inst_2 inst_3 inst_4 L tested C eps hB05 havail dist hcounted
  classical
  obtain ⟨hU, -, hnov⟩ := hcounted
  have needs_sub : ∀ (p : P) (sigma : Set Record) (d : D), L.sufficient p sigma d →
      ∀ a ∈ L.needsFin d, a ∈ sigma := by
    intro p sigma d hs a ha
    unfold RecordLedger.needsFin at ha
    split_ifs at ha with h
    · exact h.mem_toFinset.mp ha p sigma hs
    · simp at ha
  have bill : ∀ p : P, (L.calibration (L.wholeResource p) : ℝ) = ∑ a ∈ L.kept p, (L.cost a : ℝ) := by
    intro p; simp [RecordLedger.calibration, RecordLedger.wholeResource]
  have hown : ∀ i, ∃ a, 0 < L.cost a ∧ a ∈ familyNeeds L {dist i} ∧
      a ∉ familyNeeds L ((Finset.univ.erase i).image dist) := by
    intro i
    set T := (Finset.univ.erase i).image dist with hT
    have hUT : Finset.univ.image dist = insert (dist i) T := by
      rw [hT, ← Finset.image_insert, Finset.insert_erase (Finset.mem_univ i)]
    have hTU : T ⊆ Finset.univ.image dist := by rw [hUT]; exact Finset.subset_insert _ _
    obtain ⟨pU, hkU, hsU⟩ := havail _ hU
    have servT : ∀ e ∈ T, ∃ sigma : Set Record,
        sigma ⊆ L.maintained pU ∧ L.sufficient pU sigma e ∧ L.usesToRealize pU e sigma :=
      fun e he => hsU e (hTU he)
    have lb : ∀ p : P, (∀ e ∈ T, ∃ sigma : Set Record,
        sigma ⊆ L.maintained p ∧ L.sufficient p sigma e ∧ L.usesToRealize p e sigma) →
        ∑ a ∈ T.biUnion L.needsFin, (L.cost a : ℝ) ≤ L.calibration (L.wholeResource p) := by
      intro p hp
      rw [bill]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        rw [Finset.mem_biUnion] at ha
        obtain ⟨e, he, hae⟩ := ha
        obtain ⟨sigma, hsub, hs, -⟩ := hp e he
        exact hsub (needs_sub p sigma e hs a hae)
      · intros; exact NNReal.coe_nonneg _
    have hTadm : familyAdmissible L.wholeResource L.calibration L.maintained L.sufficient
        L.usesToRealize C T := by
      refine ⟨⟨pU, servT⟩, le_trans ?_ hU.2⟩
      unfold familyCost
      apply csInf_le_csInf
      · exact ⟨0, by rintro c ⟨p, -, rfl⟩; exact NNReal.coe_nonneg _⟩
      · exact ⟨_, pU, hsU, rfl⟩
      · rintro c ⟨p, hp, rfl⟩; exact ⟨p, fun e he => hp e (hTU he), rfl⟩
    obtain ⟨pT, hkT, hsT⟩ := havail T hTadm
    by_contra hno
    push_neg at hno
    obtain ⟨eta, heta, hnovp⟩ := hnov i
    have hfc : ∑ a ∈ T.biUnion L.needsFin, (L.cost a : ℝ) ≤
        familyCost L.wholeResource L.calibration L.maintained L.sufficient L.usesToRealize T := by
      unfold familyCost
      apply le_csInf
      · exact ⟨_, pU, servT, rfl⟩
      · rintro c ⟨p, hp, rfl⟩
        exact lb p hp
    have hdiff : ∑ a ∈ (Finset.univ.image dist).biUnion L.needsFin \ T.biUnion L.needsFin,
        (L.cost a : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_sdiff] at ha
      obtain ⟨haU, haT⟩ := ha
      by_contra hc
      have hpos : 0 < L.cost a := pos_iff_ne_zero.mpr (fun h => hc (by rw [h]; simp))
      have hai : a ∈ L.needsFin (dist i) := by
        rw [Finset.mem_biUnion] at haU
        obtain ⟨d, hd, had⟩ := haU
        rw [hUT, Finset.mem_insert] at hd
        rcases hd with rfl | hd
        · exact had
        · exact absurd (Finset.mem_biUnion.mpr ⟨d, hd, had⟩) haT
      have hmem : a ∈ familyNeeds L {dist i} := by
        intro p hp
        obtain ⟨sigma, hsub, hs, -⟩ := hp (dist i) (Finset.mem_singleton_self _)
        exact hsub (needs_sub p sigma _ hs a hai)
      have hk := hno a hpos hmem pT hsT
      rw [hkT] at hk
      exact haT hk
    have hb : (L.calibration (L.wholeResource pU) : ℝ) ≤
        familyCost L.wholeResource L.calibration L.maintained L.sufficient L.usesToRealize T + eta := by
      rw [bill, hkU, ← Finset.sum_sdiff (Finset.biUnion_subset_biUnion_of_subset_left _ hTU), hdiff]
      linarith
    obtain ⟨s, h1, h2, -⟩ := hsU (dist i) (by rw [hUT]; exact Finset.mem_insert_self _ _)
    exact hnovp pU servT hb ⟨s, h1, h2⟩
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
  [inst_4 : DecidableEq.{apfNative_u_3 + 1} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (tested : D → Prop)
  (C eps : Real)
  (hB05 :
    @APFB05.MarginalFloor.{0, apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_3} Unit (fun (x : Unit) => D)
      (fun (x : Unit) => P) (fun (x : Unit) => Finset.{apfNative_u_3} Record) (fun (x : Unit) => Record)
      (fun (g : Unit) => inst_2)
      (fun (x : Unit) =>
        @APFPaper1.RecordLedger.wholeResource.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.calibration.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.maintained.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => @APFPaper1.RecordLedger.sufficient.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) =>
        @APFPaper1.RecordLedger.usesToRealize.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)
      (fun (x : Unit) => tested) (fun (x : Unit) => C) fun (x : Unit) => eps)
  (havail : @APFPaper5.K1.LedgerAvailable.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record inst_4 L C)
  (dist : ι → D)
  (hcounted :
    @APFPaper5.K1.LedgerCounted.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P Record ι inst inst_1
      inst_2 L tested C dist),
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
  intro D P Record ι inst inst_1 inst_2 inst_3 inst_4 L tested C eps hB05 havail dist hcounted
  classical
  obtain ⟨hU, -, hnov⟩ := hcounted
  have needs_sub : ∀ (p : P) (sigma : Set Record) (d : D), L.sufficient p sigma d →
      ∀ a ∈ L.needsFin d, a ∈ sigma := by
    intro p sigma d hs a ha
    unfold RecordLedger.needsFin at ha
    split_ifs at ha with h
    · exact h.mem_toFinset.mp ha p sigma hs
    · simp at ha
  have bill : ∀ p : P, (L.calibration (L.wholeResource p) : ℝ) = ∑ a ∈ L.kept p, (L.cost a : ℝ) := by
    intro p; simp [RecordLedger.calibration, RecordLedger.wholeResource]
  have hown : ∀ i, ∃ a, 0 < L.cost a ∧ a ∈ familyNeeds L {dist i} ∧
      a ∉ familyNeeds L ((Finset.univ.erase i).image dist) := by
    intro i
    set T := (Finset.univ.erase i).image dist with hT
    have hUT : Finset.univ.image dist = insert (dist i) T := by
      rw [hT, ← Finset.image_insert, Finset.insert_erase (Finset.mem_univ i)]
    have hTU : T ⊆ Finset.univ.image dist := by rw [hUT]; exact Finset.subset_insert _ _
    obtain ⟨pU, hkU, hsU⟩ := havail _ hU
    have servT : ∀ e ∈ T, ∃ sigma : Set Record,
        sigma ⊆ L.maintained pU ∧ L.sufficient pU sigma e ∧ L.usesToRealize pU e sigma :=
      fun e he => hsU e (hTU he)
    have lb : ∀ p : P, (∀ e ∈ T, ∃ sigma : Set Record,
        sigma ⊆ L.maintained p ∧ L.sufficient p sigma e ∧ L.usesToRealize p e sigma) →
        ∑ a ∈ T.biUnion L.needsFin, (L.cost a : ℝ) ≤ L.calibration (L.wholeResource p) := by
      intro p hp
      rw [bill]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        rw [Finset.mem_biUnion] at ha
        obtain ⟨e, he, hae⟩ := ha
        obtain ⟨sigma, hsub, hs, -⟩ := hp e he
        exact hsub (needs_sub p sigma e hs a hae)
      · intros; exact NNReal.coe_nonneg _
    have hTadm : familyAdmissible L.wholeResource L.calibration L.maintained L.sufficient
        L.usesToRealize C T := by
      refine ⟨⟨pU, servT⟩, le_trans ?_ hU.2⟩
      unfold familyCost
      apply csInf_le_csInf
      · exact ⟨0, by rintro c ⟨p, -, rfl⟩; exact NNReal.coe_nonneg _⟩
      · exact ⟨_, pU, hsU, rfl⟩
      · rintro c ⟨p, hp, rfl⟩; exact ⟨p, fun e he => hp e (hTU he), rfl⟩
    obtain ⟨pT, hkT, hsT⟩ := havail T hTadm
    by_contra hno
    push_neg at hno
    obtain ⟨eta, heta, hnovp⟩ := hnov i
    have hfc : ∑ a ∈ T.biUnion L.needsFin, (L.cost a : ℝ) ≤
        familyCost L.wholeResource L.calibration L.maintained L.sufficient L.usesToRealize T := by
      unfold familyCost
      apply le_csInf
      · exact ⟨_, pU, servT, rfl⟩
      · rintro c ⟨p, hp, rfl⟩
        exact lb p hp
    have hdiff : ∑ a ∈ (Finset.univ.image dist).biUnion L.needsFin \ T.biUnion L.needsFin,
        (L.cost a : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_sdiff] at ha
      obtain ⟨haU, haT⟩ := ha
      by_contra hc
      have hpos : 0 < L.cost a := pos_iff_ne_zero.mpr (fun h => hc (by rw [h]; simp))
      have hai : a ∈ L.needsFin (dist i) := by
        rw [Finset.mem_biUnion] at haU
        obtain ⟨d, hd, had⟩ := haU
        rw [hUT, Finset.mem_insert] at hd
        rcases hd with rfl | hd
        · exact had
        · exact absurd (Finset.mem_biUnion.mpr ⟨d, hd, had⟩) haT
      have hmem : a ∈ familyNeeds L {dist i} := by
        intro p hp
        obtain ⟨sigma, hsub, hs, -⟩ := hp (dist i) (Finset.mem_singleton_self _)
        exact hsub (needs_sub p sigma _ hs a hai)
      have hk := hno a hpos hmem pT hsT
      rw [hkT] at hk
      exact haT hk
    have hb : (L.calibration (L.wholeResource pU) : ℝ) ≤
        familyCost L.wholeResource L.calibration L.maintained L.sufficient L.usesToRealize T + eta := by
      rw [bill, hkU, ← Finset.sum_sdiff (Finset.biUnion_subset_biUnion_of_subset_left _ hTU), hdiff]
      linarith
    obtain ⟨s, h1, h2, -⟩ := hsU (dist i) (by rw [hUT]; exact Finset.mem_insert_self _ _)
    exact hnovp pU servT hb ⟨s, h1, h2⟩
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


