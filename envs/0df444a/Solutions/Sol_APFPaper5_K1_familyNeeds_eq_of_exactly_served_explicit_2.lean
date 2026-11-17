-- Prove2me | solution 2 for APFPaper5.K1.familyNeeds_eq_of_exactly_served_explicit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:40:31.612995+00:00
-- url     : https://prove2.me/submissions/0e27aaac-83a4-4fb1-a28b-7813b4d476b3

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
universe apfNative_u_1 apfNative_u_2 apfNative_u_3

open APFPaper1 APFPaper1.Source APFPaper5 APFPaper5.K1

theorem APFPaper5.K1.familyNeeds_eq_of_exactly_served_explicit :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3}
  [inst : DecidableEq.{apfNative_u_3 + 1} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (S : Finset.{apfNative_u_1} D)
  (hS :
    @Exists.{apfNative_u_2 + 1} P fun (p : P) =>
      And
        (@Eq.{apfNative_u_3 + 1} (Finset.{apfNative_u_3} Record)
          (@APFPaper1.RecordLedger.kept.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p)
          (@Finset.biUnion.{apfNative_u_1, apfNative_u_3} D Record inst S
            (@APFPaper1.RecordLedger.needsFin.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)))
        (∀ (d : D),
          @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
                (@Finset.instSetLike.{apfNative_u_1} D))
              S d →
            @Exists.{apfNative_u_3 + 1} (Set.{apfNative_u_3} Record) fun (sigma : Set.{apfNative_u_3} Record) =>
              And
                (@LE.le.{apfNative_u_3} (Set.{apfNative_u_3} Record) (@Set.instLE.{apfNative_u_3} Record) sigma
                  (@APFPaper1.RecordLedger.maintained.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p))
                (And
                  (@APFPaper1.RecordLedger.sufficient.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p sigma
                    d)
                  (@APFPaper1.RecordLedger.usesToRealize.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p d
                    sigma)))),
  @Eq.{apfNative_u_3 + 1} (Set.{apfNative_u_3} Record)
    (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L S)
    (@SetLike.coe.{apfNative_u_3, apfNative_u_3} (Finset.{apfNative_u_3} Record) Record
      (@Finset.instSetLike.{apfNative_u_3} Record)
      (@Finset.biUnion.{apfNative_u_1, apfNative_u_3} D Record inst S
        (@APFPaper1.RecordLedger.needsFin.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L))) := by
  intro D P Record inst L S hS
  obtain ⟨p, hk, hserve⟩ := hS
  ext a
  constructor
  · intro ha
    have h1 : a ∈ L.kept p := ha p hserve
    rw [hk] at h1
    exact_mod_cast h1
  · intro ha
    have ha' : a ∈ S.biUnion L.needsFin := by exact_mod_cast ha
    rw [Finset.mem_biUnion] at ha'
    obtain ⟨d, hd, had⟩ := ha'
    intro q hq
    obtain ⟨sigma, hsub, hsuff, -⟩ := hq d hd
    have hn : a ∈ L.needs d := by
      unfold RecordLedger.needsFin at had
      split_ifs at had with h
      · exact h.mem_toFinset.mp had
      · simp at had
    exact hsub (hn q sigma hsuff)

theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3}
  [inst : DecidableEq.{apfNative_u_3 + 1} Record]
  (L : APFPaper1.RecordLedger.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record) (S : Finset.{apfNative_u_1} D)
  (hS :
    @Exists.{apfNative_u_2 + 1} P fun (p : P) =>
      And
        (@Eq.{apfNative_u_3 + 1} (Finset.{apfNative_u_3} Record)
          (@APFPaper1.RecordLedger.kept.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p)
          (@Finset.biUnion.{apfNative_u_1, apfNative_u_3} D Record inst S
            (@APFPaper1.RecordLedger.needsFin.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L)))
        (∀ (d : D),
          @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
                (@Finset.instSetLike.{apfNative_u_1} D))
              S d →
            @Exists.{apfNative_u_3 + 1} (Set.{apfNative_u_3} Record) fun (sigma : Set.{apfNative_u_3} Record) =>
              And
                (@LE.le.{apfNative_u_3} (Set.{apfNative_u_3} Record) (@Set.instLE.{apfNative_u_3} Record) sigma
                  (@APFPaper1.RecordLedger.maintained.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p))
                (And
                  (@APFPaper1.RecordLedger.sufficient.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p sigma
                    d)
                  (@APFPaper1.RecordLedger.usesToRealize.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L p d
                    sigma)))),
  @Eq.{apfNative_u_3 + 1} (Set.{apfNative_u_3} Record)
    (@APFPaper5.K1.familyNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L S)
    (@SetLike.coe.{apfNative_u_3, apfNative_u_3} (Finset.{apfNative_u_3} Record) Record
      (@Finset.instSetLike.{apfNative_u_3} Record)
      (@Finset.biUnion.{apfNative_u_1, apfNative_u_3} D Record inst S
        (@APFPaper1.RecordLedger.needsFin.{apfNative_u_1, apfNative_u_2, apfNative_u_3} D P Record L))) := by
  intro D P Record inst L S hS
  obtain ⟨p, hk, hserve⟩ := hS
  ext a
  constructor
  · intro ha
    have h1 : a ∈ L.kept p := ha p hserve
    rw [hk] at h1
    exact_mod_cast h1
  · intro ha
    have ha' : a ∈ S.biUnion L.needsFin := by exact_mod_cast ha
    rw [Finset.mem_biUnion] at ha'
    obtain ⟨d, hd, had⟩ := ha'
    intro q hq
    obtain ⟨sigma, hsub, hsuff, -⟩ := hq d hd
    have hn : a ∈ L.needs d := by
      unfold RecordLedger.needsFin at had
      split_ifs at had with h
      · exact h.mem_toFinset.mp had
      · simp at had
    exact hsub (hn q sigma hsuff)


