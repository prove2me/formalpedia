-- Prove2me | solution 1 for APFPaper5.K1.interface_sharedCost_families
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:59:08.260916+00:00
-- url     : https://prove2.me/submissions/0dcbefd0-9b10-4b22-a6bb-92d24d0bc1a1

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_interface_bridge_families
title: The shared cost of two families is the total cost of the records both need, and where each distinction needs exactly one record of its own costing one unit it is the number of distinctions the two families share
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST 19:51: "Let's tie it all the way in - tee up the rulings needed here".
 Thm_APFPaper5_K1_interface_bridge (this seat, pass 26). Builder seat: Def_APFPaper5_K1_SharedCount (the
 shared count, ADOPTED by the author on 2026-11-12 as the K layer's score on the record-book side) and
 Thm_APFPaper5_K1_shared_count_card (the shared count of two families is the size of their intersection).
standing: CONDITIONAL THEOREMS on the same hypotheses as the bridge (hbill, hkept, hneed adopted readings
 and a typing clause; exact service of the families concerned). Written to inform call 1 of
 TEE_UP_K1_tie_in_2026-11-14. Nothing here is a ruling.
what this file says:
 1. interface_sharedCost_families. For two families and their union, each exactly served, the shared cost
    is the total cost of the records that both families need.
 2. interface_sharedCost_eq_shared_count. If each distinction needs exactly one record, different
    distinctions need different records, and every record costs one unit, the shared cost of two families
    is the number of distinctions in both. That number is the adopted shared count.
what this file does NOT say: that the shared cost is the K layer's score off the record-book side. That
 is the author's call. No lane. No claim that the transfer is forced, that the carrier gap is closed or
 narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper5_K1_interface_region_satisfies_K1_of_floor

set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1

section
variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record) (cost : Record → NNReal)

/-- The shared cost of two families is the total cost of the records both need. -/
theorem interface_sharedCost_families [DecidableEq D]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S T : Finset D)
    (hS : ExactlyServed maintained sufficient usesToRealize kept fam S)
    (hT : ExactlyServed maintained sufficient usesToRealize kept fam T)
    (hST : ExactlyServed maintained sufficient usesToRealize kept fam (S ∪ T)) :
    sharedCost (familyCost wholeResource calibration maintained sufficient usesToRealize) S T =
      ∑ a ∈ S.biUnion fam ∩ T.biUnion fam, (cost a : ℝ) := by
  have e1 := familyCost_eq_sum_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed S hS
  have e2 := familyCost_eq_sum_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed T hT
  have e3 := familyCost_eq_sum_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam cost hbill hkept hneed (S ∪ T) hST
  rw [Finset.union_biUnion] at e3
  have hsum : ∑ a ∈ S.biUnion fam ∪ T.biUnion fam, (cost a : ℝ) +
      ∑ a ∈ S.biUnion fam ∩ T.biUnion fam, (cost a : ℝ) =
      ∑ a ∈ S.biUnion fam, (cost a : ℝ) + ∑ a ∈ T.biUnion fam, (cost a : ℝ) :=
    Finset.sum_union_inter
  unfold sharedCost
  rw [e1, e2, e3]
  linarith

/-- With one unit-cost record of its own for each distinction, the shared cost of two families is the
number of distinctions in both. -/
theorem interface_sharedCost_eq_shared_count [DecidableEq D]
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ∑ r ∈ kept p, (cost r : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (own : D → Record) (hown : Function.Injective own) (hfam : ∀ d, fam d = {own d})
    (hunit : ∀ a, cost a = 1)
    (S T : Finset D)
    (hS : ExactlyServed maintained sufficient usesToRealize kept fam S)
    (hT : ExactlyServed maintained sufficient usesToRealize kept fam T)
    (hST : ExactlyServed maintained sufficient usesToRealize kept fam (S ∪ T)) :
    sharedCost (familyCost wholeResource calibration maintained sufficient usesToRealize) S T =
      ((S ∩ T).card : ℝ) := by
  have hb : ∀ U : Finset D, U.biUnion fam = U.image own := by
    intro U
    have hf : fam = fun d => ({own d} : Finset Record) := funext hfam
    rw [hf, Finset.biUnion_singleton]
  rw [interface_sharedCost_families wholeResource calibration maintained sufficient usesToRealize
    kept fam cost hbill hkept hneed S T hS hT hST, hb S, hb T, ← Finset.image_inter _ _ hown]
  simp [hunit, Finset.card_image_of_injective _ hown]

end

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  [inst : DecidableEq.{apfNative_u_4 + 1} Record] (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (kept : P → Finset.{apfNative_u_4} Record)
  (fam : D → Finset.{apfNative_u_4} Record) (cost : Record → NNReal) [inst_1 : DecidableEq.{apfNative_u_1 + 1} D]
  (hbill :
    ∀ (p : P),
      @Eq.{1} Real (NNReal.toReal (calibration (wholeResource p)))
        (@Finset.sum.{apfNative_u_4, 0} Record Real Real.instAddCommMonoid (kept p) fun (r : Record) =>
          NNReal.toReal (cost r)))
  (hkept :
    ∀ (p : P),
      @Eq.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) (maintained p)
        (@SetLike.coe.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
          (@Finset.instSetLike.{apfNative_u_4} Record) (kept p)))
  (hneed :
    ∀ (p : P) (sigma : Set.{apfNative_u_4} Record) (d : D),
      sufficient p sigma d →
        @LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record)
          (@SetLike.coe.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
            (@Finset.instSetLike.{apfNative_u_4} Record) (fam d))
          sigma)
  (S T : Finset.{apfNative_u_1} D)
  (hS :
    @APFPaper5.K1.ExactlyServed.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record inst maintained sufficient
      usesToRealize kept fam S)
  (hT :
    @APFPaper5.K1.ExactlyServed.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record inst maintained sufficient
      usesToRealize kept fam T)
  (hST :
    @APFPaper5.K1.ExactlyServed.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record inst maintained sufficient
      usesToRealize kept fam
      (@Union.union.{apfNative_u_1} (Finset.{apfNative_u_1} D) (@Finset.instUnion.{apfNative_u_1} D inst_1) S T)),
  @Eq.{1} Real
    (@APFPaper5.K1.sharedCost.{apfNative_u_1} D inst_1
      (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
        wholeResource calibration maintained sufficient usesToRealize)
      S T)
    (@Finset.sum.{apfNative_u_4, 0} Record Real Real.instAddCommMonoid
      (@Inter.inter.{apfNative_u_4} (Finset.{apfNative_u_4} Record) (@Finset.instInter.{apfNative_u_4} Record inst)
        (@Finset.biUnion.{apfNative_u_1, apfNative_u_4} D Record inst S fam)
        (@Finset.biUnion.{apfNative_u_1, apfNative_u_4} D Record inst T fam))
      fun (a : Record) => NNReal.toReal (cost a)) := by
  exact @APFPaper5.K1.interface_sharedCost_families
