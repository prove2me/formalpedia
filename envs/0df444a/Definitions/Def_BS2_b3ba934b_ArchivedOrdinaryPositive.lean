-- Prove2me | Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryPositive
-- name    : BS2_b3ba934b_ArchivedOrdinaryPositive
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:00:52.111168+00:00
-- url     : https://prove2.me/theorems/3d6a219e-ac85-4b4d-84fb-99ab59d229a5
-- title:
--   Sensitivity separation: ArchivedOrdinaryPositive (complete source module)
-- statement:
--   Complete Lean source module `ArchivedOrdinaryPositive` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ArchivedOrdinaryPositive.lean; original SHA-256 fc53638cb208a82b9c570d5a870784e1f4ce129d367f911ddebb17fe423e94cf; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/
import Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryCaps

open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_CompactBooleanTransfer_ordinary_positive_of_cases.lean -/
set_option autoImplicit false
set_option Elab.async false
section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)



end Tournament









@[simp] theorem mem_childLift {J I : Type} (j : J) (A : Finset I) (p : J × I) :
    p ∈ childLift j A ↔ p.1 = j ∧ p.2 ∈ A := by
  rcases p with ⟨k, a⟩
  unfold childLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hp⟩
    change (j, b) = (k, a) at hp
    cases hp
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp] theorem childLift_card {J I : Type} (j : J) (A : Finset I) :
    (childLift j A).card = A.card := Finset.card_map _







end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)

include hF in
theorem failedGuards_subset {Gi Gj : Fin n} (hG : Gj ≤ Gi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    failedGuards T label F Gi x i ⊆ failedGuards T label F Gj x i := by
  intro j hj
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F Gi x i j).mp hj
  exact (mem_failedGuards T label F Gj x i j).mpr ⟨hij, hF.accepts_of_le hG hon⟩

include hF in
theorem tolerantRow_nested {Ai Aj Gi Gj : Fin n} {qi qj : ℕ}
    (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hq : qj ≤ qi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : tolerantRow T label F Aj Gj qj x i = true) :
    tolerantRow T label F Ai Gi qi x i = true := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F Aj Gj qj x i).mp hi
  exact (tolerantRow_true T label F Ai Gi qi x i).mpr
    ⟨fun c => hF.accepts_of_le hA (ht c),
      (Finset.card_le_card (failedGuards_subset T label F hF hG x i)).trans (hg.trans hq)⟩

end Nesting



section JointCandidates
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
  (x : ((Fin k × Fin r) × I) → Bool)

include hF hA hG in

theorem tolerant_target_weak_false {qi qj : ℕ} (hq : qj ≤ qi) (hr : 0 < r)
    (hx : tolerantFamily T label F Ai Gi qi x = false) {i : Fin k}
    (hi : i ∈ tolerantTargets T label F Aj Gj qj x) :
    F Ai (recursiveChild x i (missingWitness F Aj x hr i)) = false := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  cases hw : F Ai (recursiveChild x i (missingWitness F Aj x hr i))
  · rfl
  · have hrow : tolerantRow T label F Ai Gi qi x i = true := by
      apply (tolerantRow_true T label F Ai Gi qi x i).mpr
      constructor
      · intro c
        by_cases hc : c = missingWitness F Aj x hr i
        · simpa only [hc] using hw
        · exact hF.accepts_of_le hA (missingWitness_other_true F Aj x hr i hmiss c hc)
      · exact (Finset.card_le_card (failedGuards_subset T label F hF hG x i)).trans
          (hguards.trans hq)
    have hoff := (tolerantFamily_false T label F Ai Gi qi x).mp hx i
    simp [hoff] at hrow

include hF hA hG in

theorem tolerant_guard_sets_eq (q : ℕ)
    (hx : tolerantFamily T label F Ai Gi q x = false) {i : Fin k}
    (hi : i ∈ tolerantGuards T label F Aj Gj q x) :
    failedGuards T label F Gi x i = failedGuards T label F Gj x i := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  have htargets : ∀ c, F Ai (recursiveChild x i c) = true :=
    fun c => hF.accepts_of_le hA ((missingTargets_empty F Aj x i).mp hmiss c)
  have hcount : q < (failedGuards T label F Gi x i).card := by
    by_contra hn
    have hrow := (tolerantRow_true T label F Ai Gi q x i).mpr ⟨htargets, by omega⟩
    have hoff := (tolerantFamily_false T label F Ai Gi q x).mp hx i
    simp [hoff] at hrow
  exact Finset.eq_of_subset_of_card_le (failedGuards_subset T label F hF hG x i) (by omega)

include hF hA hG in

theorem no_guard_candidate_of_strict {qi qj : ℕ} (hq : qj < qi)
    (hx : tolerantFamily T label F Ai Gi qi x = false) {i : Fin k}
    (hi : i ∈ tolerantGuards T label F Aj Gj qj x) : False := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  have hrow : tolerantRow T label F Ai Gi qi x i = true := by
    apply (tolerantRow_true T label F Ai Gi qi x i).mpr
    refine ⟨fun c => hF.accepts_of_le hA ((missingTargets_empty F Aj x i).mp hmiss c), ?_⟩
    have hh := Finset.card_le_card (failedGuards_subset T label F hF hG x i)
    omega
  have hoff := (tolerantFamily_false T label F Ai Gi qi x).mp hx i
  simp [hoff] at hrow

end JointCandidates





end Sensitivity2075
end
end z29

section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]



@[simp] theorem mem_flipsTo (f : (I → Bool) → Bool) (b : Bool) (x : I → Bool)
    (a : I) : a ∈ flipsTo f b x ↔ f (_root_.OAI.Paper320.flip x {a}) = b := by
  simp [flipsTo]



















theorem family_nested {n k r : ℕ} {J : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (J → Bool) → Bool) (hF : NestedFamily F)
    {Ai Aj Gi Gj : Fin n} {qi qj : ℕ}
    (hA : Ai ≤ Aj) (hG : Gj ≤ Gi) (hq : qj ≤ qi)
    (x : ((Fin k × Fin r) × J) → Bool)
    (hx : tolerantFamily T label F Aj Gj qj x = true) :
    tolerantFamily T label F Ai Gi qi x = true := by
  obtain ⟨v, hv⟩ := (tolerantFamily_true T label F Aj Gj qj x).mp hx
  exact (tolerantFamily_true T label F Ai Gi qi x).mpr
    ⟨v, tolerantRow_nested T label F hF hA hG hq x v hv⟩



end ZT
end
end z30

section z31

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k r : ℕ} {I : Type} [Fintype I]



@[simp] theorem childFlipsTo_card (F : Fin n → (I → Bool) → Bool) (a : Fin n) (b : Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) (c : Fin r) :
    (childFlipsTo F a b x v c).card = (flipsTo (F a) b (recursiveChild x v c)).card := by
  simp [childFlipsTo]

@[simp] theorem mem_childFlipsTo_same (F : Fin n → (I → Bool) → Bool) (a : Fin n) (b : Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) (c : Fin r) (z : I) :
    ((v,c),z) ∈ childFlipsTo F a b x v c ↔
      F a (_root_.OAI.Paper320.flip (recursiveChild x v c) {z}) = b := by
  simp [childFlipsTo]

















end ZT
end
end z31

section z32
set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)



end OAI.Paper320.Tournament
namespace SensitivityQ



theorem card_bound_arithmetic (m q : ℕ) (hc : m.choose 2 ≤ m * (q+1)) :
    m ≤ 2*q+3 := by
  have hd : m * (m-1) ≤ 2*(m*(q+1))+1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have hm : 2*q+4 ≤ m := by omega
  have hs : 2*q+3 ≤ m-1 := by omega
  have hmul := Nat.mul_le_mul_left m hs
  nlinarith

theorem guards_card {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    (tolerantGuards T label F A G q x).card ≤ 2*q+3 := by
  let GC := tolerantGuards T label F A G q x
  have hlocal : ∀ i ∈ GC, (GC.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have hsub : GC.filter (T.Adj i) ⊆ failedGuards T label F G x i := by
      intro j hj
      obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
      exact (mem_failedGuards T label F G x i j).mpr ⟨hij,
        hF.accepts_of_le hGA ((missingTargets_empty F A x j).mp
          (Finset.mem_filter.mp hj).2.1 _)⟩
    have hc := Finset.card_le_card hsub
    have he := (Finset.mem_filter.mp hi).2.2
    omega
  apply card_bound_arithmetic
  calc
    GC.card.choose 2 = ∑ i ∈ GC, (GC.filter (T.Adj i)).card := by
      rw [T.sum_outdegree_eq, T.card_internalEdges]
    _ ≤ ∑ _i ∈ GC, (q+1) := Finset.sum_le_sum hlocal
    _ = GC.card * (q+1) := by simp

theorem guard_charge {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (c e : ℕ) :
    let GC := tolerantGuards T label F A G q x
    (∑ i ∈ GC, ∑ j ∈ failedGuards T label F G x i,
      if j ∈ GC then e else c) =
      (GC.card*(q+1)-GC.card.choose 2)*c + GC.card.choose 2*e := by
  let GC := tolerantGuards T label F A G q x
  let B := failedGuards T label F G x
  have hinside : ∀ i, (B i).filter (fun j => j ∈ GC) = GC.filter (T.Adj i) := by
    intro i
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hb, hj⟩
      exact ⟨hj, ((mem_failedGuards T label F G x i j).mp hb).1⟩
    · rintro ⟨hj, hij⟩
      exact ⟨(mem_failedGuards T label F G x i j).mpr ⟨hij,
        hF.accepts_of_le hGA ((missingTargets_empty F A x j).mp
          (Finset.mem_filter.mp hj).2.1 _)⟩, hj⟩
  have htotal : (∑ i ∈ GC, (B i).card) = GC.card*(q+1) := by
    calc
      _ = ∑ _i ∈ GC, (q+1) := Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2.2)
      _ = _ := by simp
  have hin : (∑ i ∈ GC, ((B i).filter fun j => j ∈ GC).card) = GC.card.choose 2 := by
    simp only [hinside]
    rw [T.sum_outdegree_eq, T.card_internalEdges]
  have hout : (∑ i ∈ GC, ((B i).filter fun j => j ∉ GC).card) =
      GC.card*(q+1)-GC.card.choose 2 := by
    have hh : (∑ i ∈ GC, ((B i).filter fun j => j ∈ GC).card) +
        (∑ i ∈ GC, ((B i).filter fun j => j ∉ GC).card) = GC.card*(q+1) := by
      rw [← Finset.sum_add_distrib, ← htotal]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.card_filter_add_card_filter_not (s := B i) (fun j => j ∈ GC)
    omega
  change (∑ i ∈ GC, ∑ j ∈ B i, if j ∈ GC then e else c) =
    (GC.card*(q+1)-GC.card.choose 2)*c + GC.card.choose 2*e
  calc
    _ = ∑ i ∈ GC, (((B i).filter fun j => j ∈ GC).card*e +
        ((B i).filter fun j => j ∉ GC).card*c) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hin, hout]
      omega





theorem source_card_arithmetic (m q : ℕ) (hc : m.choose 2 ≤ m*q) :
    m ≤ 2*q+1 := by
  have hd : m*(m-1) ≤ 2*(m*q)+1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have hm : 2*q+2 ≤ m := by omega
  have hs : 2*q+1 ≤ m-1 := by omega
  have hmul := Nat.mul_le_mul_left m hs
  nlinarith

theorem positiveTargets_card {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (A G : Fin n) (hGA : G ≤ A)
    (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (positiveTargets T label F A G q x hr).card ≤ 2*q+1 := by
  let S := positiveTargets T label F A G q x hr
  have hgate : ∀ j ∈ S, ∀ c, F G (recursiveChild x j c) = true := by
    intro j hj c
    obtain ⟨hj, hgate⟩ := Finset.mem_filter.mp hj
    by_cases hc : c = missingWitness F A x hr j
    · simpa only [hc] using hgate
    · exact hF.accepts_of_le hGA
        (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hj).2.1 c hc)
  have hlocal : ∀ i ∈ S, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    have hsub : S.filter (T.Adj i) ⊆ failedGuards T label F G x i := by
      intro j hj
      obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
      exact (mem_failedGuards T label F G x i j).mpr ⟨hij, hgate j hj _⟩
    exact (Finset.card_le_card hsub).trans
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2
  apply source_card_arithmetic
  calc
    S.card.choose 2 = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
      rw [T.sum_outdegree_eq, T.card_internalEdges]
    _ ≤ ∑ _i ∈ S, q := Finset.sum_le_sum hlocal
    _ = S.card*q := by simp

theorem positiveTargets_guards_coupling {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    ((positiveTargets T label F A G q x hr).card +
      (tolerantGuards T label F A G q x).card).choose 2 ≤
      q * (positiveTargets T label F A G q x hr).card +
      (q+1) * (tolerantGuards T label F A G q x).card := by
  let P := positiveTargets T label F A G q x hr
  let GC := tolerantGuards T label F A G q x
  let S := P ∪ GC
  have hdis : Disjoint P GC := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiGC
    have hone : (missingTargets F A x i).card = 1 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hiP).1).2.1
    have hempty : missingTargets F A x i = ∅ :=
      (Finset.mem_filter.mp hiGC).2.1
    simp only [hempty, Finset.card_empty] at hone
    omega
  have hgate : ∀ j ∈ S, ∀ c, F G (recursiveChild x j c) = true := by
    intro j hj c
    rcases Finset.mem_union.mp hj with hjP | hjGC
    · obtain ⟨hjTC, hpass⟩ := Finset.mem_filter.mp hjP
      by_cases hc : c = missingWitness F A x hr j
      · simpa only [hc] using hpass
      · exact hF.accepts_of_le hGA
          (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hjTC).2.1 c hc)
    · exact hF.accepts_of_le hGA
        ((missingTargets_empty F A x j).mp (Finset.mem_filter.mp hjGC).2.1 c)
  have hsub (i : Fin k) : S.filter (T.Adj i) ⊆ failedGuards T label F G x i := by
    intro j hj
    obtain ⟨hjS, hij⟩ := Finset.mem_filter.mp hj
    exact (mem_failedGuards T label F G x i j).mpr ⟨hij, hgate j hjS _⟩
  have hlocalP : ∀ i ∈ P, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    exact (Finset.card_le_card (hsub i)).trans
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2
  have hlocalGC : ∀ i ∈ GC, (S.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have he : (failedGuards T label F G x i).card = q+1 :=
      (Finset.mem_filter.mp hi).2.2
    exact (Finset.card_le_card (hsub i)).trans (Nat.le_of_eq he)
  change (P.card + GC.card).choose 2 ≤ q*P.card + (q+1)*GC.card
  calc
    (P.card + GC.card).choose 2 = S.card.choose 2 := by
      rw [show S.card = P.card + GC.card from Finset.card_union_of_disjoint hdis]
    _ = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
      rw [T.sum_outdegree_eq, T.card_internalEdges]
    _ = (∑ i ∈ P, (S.filter (T.Adj i)).card) +
        ∑ i ∈ GC, (S.filter (T.Adj i)).card := Finset.sum_union hdis
    _ ≤ (∑ _i ∈ P, q) + ∑ _i ∈ GC, (q+1) :=
      Nat.add_le_add (Finset.sum_le_sum hlocalP) (Finset.sum_le_sum hlocalGC)
    _ = q*P.card + (q+1)*GC.card := by simp [Nat.mul_comm]

end SensitivityQ
namespace SensitivitySourceZero






















end SensitivitySourceZero
end
end z32

section z33

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem up_subset_repairs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F t g q x = false) :
    flipsTo (tolerantFamily T label F t g q) true x ⊆
      targetRepairs T label F t g q x ∪ guardRepairs T label F t g q x := by
  rintro ⟨⟨w,c⟩,a⟩ hp
  obtain ⟨v,hv⟩ := (tolerantFamily_true T label F t g q _).mp
    ((mem_flipsTo _ _ _ _).mp hp)
  have hoff := (tolerantFamily_false T label F t g q x).mp hx v
  rcases _root_.ThreeBoundOrdinaryArchive.Paley11987Verified.Sensitivity2075.tolerant_repair_cases T label F t g q x v w c a hoff hv with
    ⟨hT, hw, hfalse, htrue⟩ | ⟨hG, hadj, hc, htrue, hfalse⟩
  · subst w
    have hc := missingWitness_unique F t x (by decide) v
      (Finset.mem_filter.mp hT).2.1 c hfalse
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hT,?_⟩
    rw [← hc]
    exact (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr htrue
  · subst c
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hG,Finset.mem_biUnion.mpr ⟨w,?_,?_⟩⟩
    · exact (mem_failedGuards T label F g x v w).mpr ⟨hadj,htrue⟩
    · exact (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr hfalse

theorem sum_binary_weights {V : Type} [DecidableEq V] (S : Finset V)
    (p : V → Prop) [DecidablePred p] (a b : ℕ) :
    (∑ v ∈ S, if p v then a else b) =
      (S.filter p).card*a+(S.card-(S.filter p).card)*b := by
  have hsplit : (∑ v ∈ S, if p v then a else b) =
      (∑ v ∈ S.filter p, a)+(∑ v ∈ S.filter (fun v => ¬p v), b) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hp : p v <;> simp [hp]
  rw [hsplit]
  simp only [Finset.sum_const, smul_eq_mul]
  have hcard := Finset.card_filter_add_card_filter_not (s := S) p
  congr 1
  congr 1
  omega

theorem targetRepairs_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga)
    (qa q : ℕ) (hq : q ≤ qa) (a b : ℕ)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    (targetRepairs T label F tb gb q x).card ≤
      (positiveTargets T label F tb gb q x (by decide)).card*a+
      ((tolerantTargets T label F tb gb q x).card-
        (positiveTargets T label F tb gb q x (by decide)).card)*b := by
  let S := tolerantTargets T label F tb gb q x
  let tw := missingWitness F tb x (by decide)
  let p := fun v => F gb (recursiveChild x v (tw v)) = true
  have hsum : (targetRepairs T label F tb gb q x).card ≤
      ∑ v ∈ S, if p v then a else b := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro v hv
    have hta := tolerant_target_weak_false T label F hF ta tb ga gb ht hg x hq
      (by decide) hx hv
    by_cases hp : p v
    · simpa only [if_pos hp, childFlipsTo_card] using ha _ hp hta
    · have hfalse : F gb (recursiveChild x v (tw v)) = false := by
        simpa only [p, Bool.not_eq_true] using hp
      simpa only [if_neg hp, childFlipsTo_card] using hb _ hfalse
  rw [sum_binary_weights] at hsum
  exact hsum



theorem positiveTargets_empty_of_gate_eq (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (heq : gb = ta)
    (qa q : ℕ) (hq : q ≤ qa)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    positiveTargets T label F tb gb q x (by decide) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hT,htrue⟩ := Finset.mem_filter.mp hv
  have hfalse := tolerant_target_weak_false T label F hF ta tb ga gb ht hg x hq
    (by decide) hx hT
  rw [heq,hfalse] at htrue
  contradiction

end ZT
end
end z33

section z34

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









@[simp] theorem mem_guardArcs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (e : Fin k × Fin k) :
    e ∈ guardArcs T label F t g q x ↔
      e.1 ∈ tolerantGuards T label F t g q x ∧ e.2 ∈ failedGuards T label F g x e.1 := by
  simp [guardArcs]

theorem guardArcs_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (externalGuardArcs T label F t g q x).card =
      (tolerantGuards T label F t g q x).card*(q+1)-
        (tolerantGuards T label F t g q x).card.choose 2 ∧
    (internalGuardArcs T label F t g q x).card =
      (tolerantGuards T label F t g q x).card.choose 2 := by
  let R := tolerantGuards T label F t g q x
  let B := failedGuards T label F g x
  have he : (externalGuardArcs T label F t g q x).card =
      ∑ v ∈ R, ∑ w ∈ B v, if w ∈ R then 0 else 1 := by
    simp only [externalGuardArcs,guardArcs,Finset.card_eq_sum_ones,
      Finset.sum_filter,Finset.sum_product,Finset.sum_const_zero]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hr : w ∈ R <;> simp [R,B,hr]
  have hi : (internalGuardArcs T label F t g q x).card =
      ∑ v ∈ R, ∑ w ∈ B v, if w ∈ R then 1 else 0 := by
    simp only [internalGuardArcs,guardArcs,Finset.card_eq_sum_ones,
      Finset.sum_filter,Finset.sum_product,Finset.sum_const_zero]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hr : w ∈ R <;> simp [R,B,hr]
  constructor
  · rw [he]
    simpa using guard_charge T label F hF t g hgt q x 1 0
  · rw [hi]
    simpa using guard_charge T label F hF t g hgt q x 0 1

theorem guardRepairs_subset_coordinates (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    guardRepairs T label F t g q x ⊆
      ((externalGuardArcs T label F t g q x).image (arcCoordinate label)).biUnion
        (fun z => childFlipsTo F g false x z.1 z.2) ∪
      ((internalGuardArcs T label F t g q x).image (arcCoordinate label)).biUnion
        (fun z => childFlipsTo F g false x z.1 z.2) := by
  intro p hp
  obtain ⟨v,hv,hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨w,hw,hp⟩ := Finset.mem_biUnion.mp hp
  have harc : (v,w) ∈ guardArcs T label F t g q x := (mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hv,hw⟩
  by_cases hin : w ∈ tolerantGuards T label F t g q x
  · apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨(w,label v w),Finset.mem_image.mpr
      ⟨(v,w),Finset.mem_filter.mpr ⟨harc,hin⟩,rfl⟩,hp⟩
  · apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨(w,label v w),Finset.mem_image.mpr
      ⟨(v,w),Finset.mem_filter.mpr ⟨harc,hin⟩,rfl⟩,hp⟩

theorem filter_image_card_le {A B : Type} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → B) (p : B → Prop) [DecidablePred p] :
    ((S.image f).filter p).card ≤ (S.filter fun a => p (f a)).card := by
  have hsub : (S.image f).filter p ⊆ (S.filter fun a => p (f a)).image f := by
    intro b hb
    obtain ⟨hb,hp⟩ := Finset.mem_filter.mp hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩,rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

theorem positive_costly_coordinates_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (Z : Finset (Fin k × Fin 2)) :
    (Z.filter fun z => z.1 ∈ positiveTargets T label F t g q x (by decide) ∧
      F t (recursiveChild x z.1 z.2) = false).card ≤
      (positiveTargets T label F t g q x (by decide)).card := by
  let S := Z.filter fun z => z.1 ∈ positiveTargets T label F t g q x (by decide) ∧
    F t (recursiveChild x z.1 z.2) = false
  have hinj : Set.InjOn Prod.fst (↑S : Set (Fin k × Fin 2)) := by
    intro z hz w hw he
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hzt := (Finset.mem_filter.mp hz'.1).1
    have hwt := (Finset.mem_filter.mp hw'.1).1
    have hzc := missingWitness_unique F t x (by decide) z.1
      (Finset.mem_filter.mp hzt).2.1 z.2 hz'.2
    have hwc := missingWitness_unique F t x (by decide) w.1
      (Finset.mem_filter.mp hwt).2.1 w.2 hw'.2
    apply Prod.ext he
    rw [hzc,hwc,he]
  have hcard : (S.image Prod.fst).card = S.card := Finset.card_image_iff.mpr hinj
  have hsub : S.image Prod.fst ⊆ positiveTargets T label F t g q x (by decide) := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hz).2.1
  change S.card ≤ _
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem positive_coordinates_card (P : Finset (Fin k)) (Z : Finset (Fin k × Fin 2)) :
    (Z.filter fun z => z.1 ∈ P).card ≤ 2*P.card := by
  have hs : Z.filter (fun z => z.1 ∈ P) ⊆ P ×ˢ Finset.univ := by
    intro z hz
    exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hz).2,Finset.mem_univ _⟩
  simpa [Nat.mul_comm] using Finset.card_le_card hs

end ZT
end
end z34

section z35

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
namespace ZT

theorem binary_capacity_charge (n z N J s j : ℕ)
    (hjs : j ≤ s) (hnz : n ≤ z) (hnN : n ≤ N) (hz : z ≤ N+J) :
    n*s+(z-n)*j ≤ N*s+J*j := by
  have hn : n+(N-n)=N := Nat.add_sub_of_le hnN
  have hzn : n+(z-n)=z := Nat.add_sub_of_le hnz
  have hm := Nat.mul_le_mul_left (N-n) hjs
  have htail := Nat.mul_le_mul_right j (show z-n ≤ (N-n)+J by omega)
  nlinarith

theorem positive_capacity_charge (n z E W L u δ s j : ℕ)
    (hjs : j ≤ s) (hnz : n ≤ z)
    (hnE : n+δ ≤ E) (hnW : n+δ ≤ W+u)
    (hzE : z ≤ E) (hzW : z ≤ W+2*u)
    (hWL : W+L ≤ E) (hδW : δ ≤ W) :
    n*s+(z-n)*j ≤
      (E-(L-u)-δ)*s+(min u (L-u)+δ)*j := by
  apply binary_capacity_charge _ _ _ _ _ _ hjs hnz
  · omega
  · omega

theorem positive_union_charge {V α : Type} [DecidableEq V] [DecidableEq α]
    (Z : Finset V) (inside costly : V → Prop)
    [DecidablePred inside] [DecidablePred costly]
    (D : V → Finset α) (E W L u δ s j : ℕ)
    (hjs : j ≤ s)
    (hZ : Z.card ≤ E) (hW : (Z.filter (fun v => ¬ inside v)).card ≤ W)
    (hL : W+L ≤ E)
    (hin : (Z.filter inside).card ≤ 2*u)
    (hcost : (Z.filter fun v => inside v ∧ costly v).card ≤ u)
    (hcheap : δ ≤ (Z.filter fun v => ¬ inside v ∧ ¬ costly v).card)
    (hD : ∀ v ∈ Z, (D v).card ≤ if costly v then s else j) :
    (Z.biUnion D).card ≤ (E-(L-u)-δ)*s+(min u (L-u)+δ)*j := by
  let n := (Z.filter costly).card
  let z := Z.card
  let ni := (Z.filter fun v => inside v ∧ costly v).card
  let no := (Z.filter fun v => ¬ inside v ∧ costly v).card
  let co := (Z.filter fun v => ¬ inside v ∧ ¬ costly v).card
  let out := (Z.filter fun v => ¬ inside v).card
  have hnz : n ≤ z := Finset.card_filter_le _ _
  have hout : no+co=out := by
    simpa only [no,co,out,Finset.filter_filter,and_assoc] using
      (Finset.card_filter_add_card_filter_not (s := Z.filter fun v => ¬inside v) costly)
  have hn : ni+no=n := by
    simpa only [ni,no,n,Finset.filter_filter,and_comm] using
      (Finset.card_filter_add_card_filter_not (s := Z.filter costly) inside)
  have hsplit : (Z.filter inside).card+out=z := by
    exact Finset.card_filter_add_card_filter_not (s := Z) inside
  have hδW : δ ≤ W := by
    have hco : co ≤ out := by omega
    exact hcheap.trans (hco.trans hW)
  have hnW : n+δ ≤ W+u := by
    change ni ≤ u at hcost
    change δ ≤ co at hcheap
    change out ≤ W at hW
    omega
  have hzW : z ≤ W+2*u := by
    change out ≤ W at hW
    omega
  have hnE : n+δ ≤ E := by
    have hdis : Disjoint (Z.filter costly)
        (Z.filter fun v => ¬inside v ∧ ¬costly v) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact (Finset.mem_filter.mp hw).2.2 (Finset.mem_filter.mp hv).2
    have hcard : n+co ≤ z := by
      rw [← Finset.card_union_of_disjoint hdis]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    change δ ≤ co at hcheap
    omega
  have hbound : (Z.biUnion D).card ≤ n*s+(z-n)*j := by
    apply Finset.card_biUnion_le.trans
    apply (Finset.sum_le_sum hD).trans_eq
    exact sum_binary_weights Z costly s j
  exact hbound.trans (positive_capacity_charge n z E W L u δ s j hjs hnz hnE hnW hZ hzW hL hδW)

theorem by_head_child_card {H α : Type} [DecidableEq H] [DecidableEq α]
    (S : Finset H) (Z : Finset (H × Fin 2)) (D : H × Fin 2 → Finset α) (j : ℕ)
    (hZS : ∀ z ∈ Z, z.1 ∈ S) (hD : ∀ z ∈ Z, (D z).card ≤ j) :
    (Z.biUnion D).card ≤ (2*S.card)*j := by
  have hcard : Z.card ≤ 2*S.card := by
    have hsub : Z ⊆ S ×ˢ Finset.univ := by
      intro z hz
      exact Finset.mem_product.mpr ⟨hZS z hz,Finset.mem_univ _⟩
    simpa [Nat.mul_comm] using Finset.card_le_card hsub
  calc
    (Z.biUnion D).card ≤ ∑ z ∈ Z, (D z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ Z, j := Finset.sum_le_sum hD
    _ = Z.card*j := by simp
    _ ≤ (2*S.card)*j := Nat.mul_le_mul_right j hcard

end ZT
end
end z35

section z36
set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace SensitivityOrdinaryGuard
theorem tournament_outside_budget {k : ℕ} (T : Tournament k)
    (P R : Finset (Fin k)) (B O : Fin k → Finset (Fin k)) (q : ℕ)
    (hdis : Disjoint P R)
    (hinside : ∀ i, (P ∪ R).filter (T.Adj i) ⊆ B i)
    (hP : ∀ i ∈ P, (B i).card ≤ q)
    (hR : ∀ i ∈ R, (B i).card = q+1)
    (hOB : ∀ i, O i ⊆ B i)
    (hOR : ∀ i, ∀ j ∈ O i, j ∉ R) :
    (∑ i ∈ R, ((O i).filter fun j => j ∉ P).card)+
      (P.card+R.card).choose 2 ≤ q*P.card+(q+1)*R.card := by
  let S := P ∪ R
  let W := ∑ i ∈ R, ((O i).filter fun j => j ∉ P).card
  have hlocalP : ∀ i ∈ P, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    exact (Finset.card_le_card (hinside i)).trans (hP i hi)
  have hlocalR : ∀ i ∈ R,
      ((O i).filter fun j => j ∉ P).card+
        (S.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have hd : Disjoint ((O i).filter fun j => j ∉ P) (S.filter (T.Adj i)) := by
      apply Finset.disjoint_left.mpr
      intro j hjO hjS
      obtain ⟨hjO, hjnotP⟩ := Finset.mem_filter.mp hjO
      obtain ⟨hjS, _⟩ := Finset.mem_filter.mp hjS
      rcases Finset.mem_union.mp hjS with hjP | hjR
      · exact hjnotP hjP
      · exact hOR i j hjO hjR
    calc
      _ = (((O i).filter fun j => j ∉ P) ∪ S.filter (T.Adj i)).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ (B i).card := Finset.card_le_card (Finset.union_subset
        ((Finset.filter_subset _ _).trans (hOB i)) (hinside i))
      _ = q+1 := hR i hi
  have hs : (P.card+R.card).choose 2 =
      (∑ i ∈ P, (S.filter (T.Adj i)).card)+
        ∑ i ∈ R, (S.filter (T.Adj i)).card := by
    calc
      _ = S.card.choose 2 := by
        rw [show S.card = P.card+R.card from Finset.card_union_of_disjoint hdis]
      _ = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
        rw [T.sum_outdegree_eq, T.card_internalEdges]
      _ = _ := Finset.sum_union hdis
  have hp : (∑ i ∈ P, (S.filter (T.Adj i)).card) ≤ P.card*q := by
    simpa using Finset.sum_le_sum hlocalP
  have hr : W+(∑ i ∈ R, (S.filter (T.Adj i)).card) ≤ R.card*(q+1) := by
    calc
      _ = ∑ i ∈ R, (((O i).filter fun j => j ∉ P).card+
          (S.filter (T.Adj i)).card) := by rw [Finset.sum_add_distrib]
      _ ≤ ∑ _i ∈ R, (q+1) := Finset.sum_le_sum hlocalR
      _ = _ := by simp
  change W+(P.card+R.card).choose 2 ≤ _
  rw [hs]
  have hh := Nat.add_le_add hp hr
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_comm] using hh

theorem positive_guards_disjoint {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (A G : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    Disjoint (positiveTargets T label F A G q x hr)
      (tolerantGuards T label F A G q x) := by
  apply Finset.disjoint_left.mpr
  intro i hiP hiR
  have hone : (missingTargets F A x i).card = 1 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hiP).1).2.1
  have hempty : missingTargets F A x i = ∅ :=
    (Finset.mem_filter.mp hiR).2.1
  simp only [hempty, Finset.card_empty] at hone
  omega

theorem positive_gate_true {n k r : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (A G : Fin n) (hGA : G ≤ A) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r)
    (j : Fin k) (hj : j ∈ positiveTargets T label F A G q x hr)
    (c : Fin r) : F G (recursiveChild x j c) = true := by
  obtain ⟨hjT, hpass⟩ := Finset.mem_filter.mp hj
  by_cases hc : c = missingWitness F A x hr j
  · simpa only [hc] using hpass
  · exact hF.accepts_of_le hGA
      (missingWitness_other_true F A x hr j (Finset.mem_filter.mp hjT).2.1 c hc)

theorem choose_add_two (u m : ℕ) :
    (u+m).choose 2 = u.choose 2+m.choose 2+u*m := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [show u+1+m=(u+m)+1 by omega, Nat.choose_succ_succ, ih,
      Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    ring

theorem positive_lower_budget (q u m W : ℕ)
    (hW : W ≤ m*(q+1)-m.choose 2)
    (hbudget : W+(u+m).choose 2 ≤ q*u+(q+1)*m) :
    W+((u*m+u.choose 2)-q*u) ≤ m*(q+1)-m.choose 2 := by
  rw [choose_add_two] at hbudget
  have hbudget' : W+(u.choose 2+m.choose 2+u*m) ≤ q*u+m*(q+1) := by
    simpa only [Nat.mul_comm] using hbudget
  omega

end SensitivityOrdinaryGuard
end
end z36

section z37

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem ordinary_failed_target_true (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (z : Fin k × Fin 2)
    (hz : z ∈ externalGuardCoordinates T label F t g q x)
    (hT : z.1 ∈ tolerantTargets T label F t g q x)
    (hU : z.1 ∉ positiveTargets T label F t g q x (by decide)) :
    F t (recursiveChild x z.1 z.2) = true := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
  have harc := (mem_guardArcs T label F t g q x e).mp (Finset.mem_filter.mp he).1
  have hgate := ((mem_failedGuards T label F g x e.1 e.2).mp harc.2).2
  cases ht : F t (recursiveChild x e.2 (label e.1 e.2))
  · have hsel := missingWitness_unique F t x (by decide) e.2
      (Finset.mem_filter.mp hT).2.1 (label e.1 e.2) ht
    apply False.elim
    apply hU
    apply Finset.mem_filter.mpr
    refine ⟨hT,?_⟩
    simpa only [arcCoordinate,←hsel] using hgate
  · exact ht

theorem crossedTargetHeads_cheap_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (crossedTargetHeads T label F t g q x).card ≤
      ((externalGuardCoordinates T label F t g q x).filter fun z =>
        z.1 ∉ positiveTargets T label F t g q x (by decide) ∧
          ¬ F t (recursiveChild x z.1 z.2) = false).card := by
  apply Finset.card_image_le.trans
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hz,hT,hU⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨hz,hU,?_⟩
  have hon := ordinary_failed_target_true T label F t g q x z hz hT hU
  simp [hon]

theorem selected_guard_weak_true (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga q x = false)
    (e : Fin k × Fin k) (he : e ∈ guardArcs T label F tb gb q x) :
    F ga (recursiveChild x e.2 (label e.1 e.2)) = true := by
  have he' := (mem_guardArcs T label F tb gb q x e).mp he
  have hh := tolerant_guard_sets_eq T label F hF ta tb ga gb ht hg x q hx he'.1
  have hmem : e.2 ∈ failedGuards T label F ga x e.1 := by rw [hh]; exact he'.2
  exact ((mem_failedGuards T label F ga x e.1 e.2).mp hmem).2

theorem internal_guard_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ) (j : ℕ) (hj : BBound F g t j)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (((internalGuardArcs T label F t g q x).image (arcCoordinate label)).biUnion
      (fun z => childFlipsTo F g false x z.1 z.2)).card ≤
      min ((tolerantGuards T label F t g q x).card.choose 2)
        (2*(tolerantGuards T label F t g q x).card)*j := by
  let R := tolerantGuards T label F t g q x
  let S := internalGuardArcs T label F t g q x
  let Z := S.image (arcCoordinate label)
  let D := fun z : Fin k × Fin 2 => childFlipsTo F g false x z.1 z.2
  have hhead : ∀ z ∈ Z, z.1 ∈ R := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp he).2
  have hD : ∀ z ∈ Z, (D z).card ≤ j := by
    intro z hz
    have hon := (missingTargets_empty F t x z.1).mp (Finset.mem_filter.mp (hhead z hz)).2.1 z.2
    simpa only [D,childFlipsTo_card] using hj _ hon
  have hbyarc : (Z.biUnion D).card ≤ R.card.choose 2*j := by
    calc
      (Z.biUnion D).card ≤ ∑ z ∈ Z, (D z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ Z, j := Finset.sum_le_sum hD
      _ = Z.card*j := by simp
      _ ≤ S.card*j := Nat.mul_le_mul_right j Finset.card_image_le
      _ = R.card.choose 2*j := by rw [(guardArcs_card T label F hF t g hgt q x).2]
  have hbyhead : (Z.biUnion D).card ≤ (2*R.card)*j :=
    by_head_child_card R Z D j hhead hD
  rw [min_mul]
  exact le_min hbyarc hbyhead

theorem external_guard_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hgbtb : gb ≤ tb)
    (q s j L : ℕ) (hjs : j ≤ s) (hs : BBound F gb ga s) (hj : BBound F gb tb j)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga q x = false)
    (hL : ((externalGuardArcs T label F tb gb q x).filter fun e =>
        e.2 ∉ positiveTargets T label F tb gb q x (by decide)).card+L ≤
      (externalGuardArcs T label F tb gb q x).card) :
    ((externalGuardCoordinates T label F tb gb q x).biUnion
      (fun z => childFlipsTo F gb false x z.1 z.2)).card ≤
      ((externalGuardArcs T label F tb gb q x).card-
        (L-(positiveTargets T label F tb gb q x (by decide)).card)-
        (crossedTargetHeads T label F tb gb q x).card)*s+
      (min (positiveTargets T label F tb gb q x (by decide)).card
        (L-(positiveTargets T label F tb gb q x (by decide)).card)+
        (crossedTargetHeads T label F tb gb q x).card)*j := by
  let Z := externalGuardCoordinates T label F tb gb q x
  let S := externalGuardArcs T label F tb gb q x
  let P := positiveTargets T label F tb gb q x (by decide)
  let D := fun z : Fin k × Fin 2 => childFlipsTo F gb false x z.1 z.2
  apply positive_union_charge Z (fun z => z.1 ∈ P)
    (fun z => F tb (recursiveChild x z.1 z.2) = false) D
    S.card ((S.filter fun e => e.2 ∉ P).card) L P.card
    (crossedTargetHeads T label F tb gb q x).card s j hjs
  · exact Finset.card_image_le
  · exact filter_image_card_le S (arcCoordinate label) (fun z => z.1 ∉ P)
  · exact hL
  · exact positive_coordinates_card P Z
  · exact positive_costly_coordinates_card T label F tb gb q x Z
  · exact crossedTargetHeads_cheap_card T label F tb gb q x
  · intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    have hweak := selected_guard_weak_true T label F hF ta tb ga gb ht hg q x hx e
      (Finset.mem_filter.mp he).1
    by_cases hc : F tb (recursiveChild x e.2 (label e.1 e.2)) = false
    · simpa [D,arcCoordinate,hc] using hs _ hweak
    · have hon : F tb (recursiveChild x e.2 (label e.1 e.2)) = true := by
        simpa only [Bool.not_eq_false] using hc
      simpa [D,arcCoordinate,hc] using hj _ hon

end ZT
end
end z37

section z40

set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

end ZT
end
end z40

section z41

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem crossedTargetHeads_subset (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    crossedTargetHeads T label F t g q x ⊆
      tolerantTargets T label F t g q x \ positiveTargets T label F t g q x (by decide) := by
  intro v hv
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_sdiff.mpr (Finset.mem_filter.mp hz).2

theorem crossedTargetHeads_of_failed (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (v w : Fin k)
    (hv : v ∈ tolerantGuards T label F t g q x)
    (hw : w ∈ tolerantTargets T label F t g q x)
    (hP : w ∉ positiveTargets T label F t g q x (by decide))
    (hfailed : w ∈ failedGuards T label F g x v) :
    w ∈ crossedTargetHeads T label F t g q x := by
  have hwG : w ∉ tolerantGuards T label F t g q x := by
    exact Finset.disjoint_left.mp (target_guard_disjoint T label F t g q x) hw
  have hext : (v,w) ∈ externalGuardArcs T label F t g q x :=
    Finset.mem_filter.mpr ⟨(mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hv,hfailed⟩,hwG⟩
  exact Finset.mem_image.mpr ⟨(w,label v w),Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(v,w),hext,rfl⟩,hw,hP⟩,rfl⟩

theorem remaining_targets_subset (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    remainingOrdinaryTargets T label F t g q x ⊆ tolerantTargets T label F t g q x := by
  intro v hv
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).1

theorem remaining_targets_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (remainingOrdinaryTargets T label F t g q x).card+
      (crossedTargetHeads T label F t g q x).card+
      (positiveTargets T label F t g q x (by decide)).card =
      (tolerantTargets T label F t g q x).card := by
  have hC := Finset.card_sdiff_add_card_eq_card (crossedTargetHeads_subset T label F t g q x)
  have hP := Finset.card_sdiff_add_card_eq_card
    (show positiveTargets T label F t g q x (by decide) ⊆ tolerantTargets T label F t g q x from
      Finset.filter_subset _ _)
  change (remainingOrdinaryTargets T label F t g q x).card+_=_ at hC
  omega

theorem remaining_targets_guard_mismatch_empty (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : v ∈ tolerantGuards T label F t g q x) :
    ZL.mismatch T.Adj (fun e => label e.1 e.2)
      (remainingOrdinaryTargets T label F t g q x) (missingWitness F t x (by decide)) v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hfailed := target_mismatch_failed T label F hF t g hgt q x
    (remainingOrdinaryTargets T label F t g q x) (remaining_targets_subset T label F t g q x) v hw
  have hrem := (Finset.mem_filter.mp hw).1
  obtain ⟨hord,hnotC⟩ := Finset.mem_sdiff.mp hrem
  obtain ⟨hT,hnotP⟩ := Finset.mem_sdiff.mp hord
  exact hnotC (crossedTargetHeads_of_failed T label F t g q x v w hv hT hnotP hfailed)

theorem remaining_targets_marked_zero (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (M : Finset (Fin k))
    (hM : M ⊆ tolerantGuards T label F t g q x) :
    ZL.MarkedGood T.Adj (fun e => label e.1 e.2)
      (remainingOrdinaryTargets T label F t g q x) M ∅ q 0
      (missingWitness F t x (by decide)) := by
  apply candidates_markedGood T label F hF t g hgt q 0 x
    (remainingOrdinaryTargets T label F t g q x) M ∅
    (remaining_targets_subset T label F t g q x)
    (fun v hv => Finset.mem_union_right _ (hM hv)) (Finset.empty_subset _)
  · apply (target_guard_disjoint T label F t g q x).mono
      (remaining_targets_subset T label F t g q x) hM
  · have he : (∑ v ∈ M, (ZL.mismatch T.Adj (fun e => label e.1 e.2)
        (remainingOrdinaryTargets T label F t g q x) (missingWitness F t x (by decide)) v).card) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [remaining_targets_guard_mismatch_empty T label F hF t g hgt q x v (hM hv)]
      rfl
    exact he.le



end ZT
end
end z41

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]













theorem remaining_card_guard_marked (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q r w : ℕ)
    (hcap : MarkedCardBound T label q r 0 0 w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hr : r ≤ (tolerantGuards T label F t g q x).card) :
    (remainingOrdinaryTargets T label F t g q x).card < w := by
  obtain ⟨M,hM,hcard⟩ := Finset.exists_subset_card_eq hr
  have hdis := (target_guard_disjoint T label F t g q x).mono
    (remaining_targets_subset T label F t g q x) hM
  exact hcap _ M ∅ _ hdis (Finset.empty_subset _) hcard rfl
    (remaining_targets_marked_zero T label F hF t g hgt q x M hM)





end ZT
end
end z43

section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]







theorem markedDeletionCap_bound (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hCaps : LabelCaps T label) (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ) (hq8 : q ≤ 8)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card-
      (positiveTargets T label F t g q x (by decide)).card ≤
      markedCap q (tolerantGuards T label F t g q x).card+
        (crossedTargetHeads T label F t g q x).card := by
  let C := tolerantTargets T label F t g q x
  let G := tolerantGuards T label F t g q x
  let P := positiveTargets T label F t g q x (by decide)
  let A := remainingOrdinaryTargets T label F t g q x
  let δ := (crossedTargetHeads T label F t g q x).card
  have hpart : A.card+δ+P.card=C.card := remaining_targets_card T label F t g q x
  have hrem : A.card ≤ markedCap q G.card := by
    unfold markedCap
    split_ifs with h1 h2 h3 h4 h5 h6
    · obtain ⟨rfl,hm⟩ := h1
      have hh := remaining_card_guard_marked T label F hF t g hgt 1 3 24 hCaps.zero_one_three x (by simpa [G] using hm.ge)
      change A.card < 24 at hh
      omega
    · obtain ⟨rfl,hm⟩ := h2
      have hh := remaining_card_guard_marked T label F hF t g hgt 2 4 28 hCaps.zero_two_four x (by simpa [G] using hm.ge)
      change A.card < 28 at hh
      omega
    · obtain ⟨rfl,hm⟩ := h3
      have hh := remaining_card_guard_marked T label F hF t g hgt 3 5 31 hCaps.zero_three_five x (by simpa [G] using hm.ge)
      change A.card < 31 at hh
      omega
    · obtain ⟨rfl,hm⟩ := h4
      have hh := remaining_card_guard_marked T label F hF t g hgt 3 6 29 hCaps.zero_three_six x (by simpa [G] using hm.ge)
      change A.card < 29 at hh
      omega
    · obtain ⟨rfl,hm⟩ := h5
      have hh := remaining_card_guard_marked T label F hF t g hgt 4 6 34 hCaps.zero_four_six x (by simpa [G] using hm.ge)
      change A.card < 34 at hh
      omega
    · obtain ⟨rfl,hm⟩ := h6
      have hh := remaining_card_guard_marked T label F hF t g hgt 3 7 27 hCaps.zero_three_seven x (by simpa [G] using hm.ge)
      change A.card < 27 at hh
      omega
    · have hc := targets_card_of_exclusion T label F hF t g hgt q (cutoff q) (hCaps.ordinary q hq8) x
      change C.card < cutoff q at hc
      have hn : cutoff q ≤ 74 := by interval_cases q <;> decide
      omega
  change C.card-P.card ≤ markedCap q G.card+δ
  omega

end ZT
end
end z45

section z58

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ SensitivityOrdinaryGuard
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem external_outside_positive_budget (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    let G := tolerantGuards T label F t g q x
    let P := positiveTargets T label F t g q x (by decide)
    let S := externalGuardArcs T label F t g q x
    ((S.filter fun e => e.2 ∉ P).card)+
      ((P.card*G.card+P.card.choose 2)-q*P.card) ≤ S.card := by
  let G := tolerantGuards T label F t g q x
  let P := positiveTargets T label F t g q x (by decide)
  let B := failedGuards T label F g x
  let O := fun v => (B v).filter fun w => w ∉ G
  let S := externalGuardArcs T label F t g q x
  let W := (S.filter fun e => e.2 ∉ P).card
  have hWcount : W = ∑ v ∈ G, ((O v).filter fun w => w ∉ P).card := by
    simp only [W,S,externalGuardArcs,guardArcs,Finset.card_eq_sum_ones,
      Finset.sum_filter,Finset.sum_product,O]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hg : w ∈ G <;> by_cases hp : w ∈ P <;> simp [G,hg,hp]
  have hinside : ∀ v, (P ∪ G).filter (T.Adj v) ⊆ B v := by
    intro v w hw
    obtain ⟨hw,hadj⟩ := Finset.mem_filter.mp hw
    apply (mem_failedGuards T label F g x v w).mpr
    refine ⟨hadj,?_⟩
    rcases Finset.mem_union.mp hw with hw | hw
    · exact positive_gate_true T label F hF t g hgt q x (by decide) w hw _
    · exact hF.accepts_of_le hgt
        ((missingTargets_empty F t x w).mp (Finset.mem_filter.mp hw).2.1 _)
  have hP : ∀ v ∈ P, (B v).card ≤ q := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2.2
  have hG : ∀ v ∈ G, (B v).card = q+1 := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2.2
  have hbudget := tournament_outside_budget T P G B O q
    (positive_guards_disjoint T label F t g q x (by decide)) hinside hP hG
    (fun _ => Finset.filter_subset _ _) (by
      intro v w hw
      exact (Finset.mem_filter.mp hw).2)
  rw [←hWcount] at hbudget
  have hS : S.card = G.card*(q+1)-G.card.choose 2 :=
    (guardArcs_card T label F hF t g hgt q x).1
  have hW : W ≤ G.card*(q+1)-G.card.choose 2 := by
    rw [←hS]
    exact Finset.card_filter_le _ _
  change W+((P.card*G.card+P.card.choose 2)-q*P.card) ≤ S.card
  rw [hS]
  exact positive_lower_budget q P.card G.card W hW hbudget

end ZT
end
end z58

section z59

set_option maxHeartbeats 5000000
namespace ZT



theorem deletion_affine_endpoints (K ext intr e δ B S J : ℕ)
    (hδ : δ ≤ e) (he : e ≤ ext) :
    (K+δ)*B+(ext-δ)*S+(intr+δ)*J ≤
      max (K*B+ext*S+intr*J) ((K+e)*B+(ext-e)*S+(intr+e)*J) := by
  have hδext : δ ≤ ext := hδ.trans he
  have hδsum : (ext-δ)+δ=ext := Nat.sub_add_cancel hδext
  by_cases hc : B+J ≤ S
  · apply le_trans _ (le_max_left _ _)
    have hm := Nat.mul_le_mul_left δ hc
    nlinarith
  · apply le_trans _ (le_max_right _ _)
    have hcs : S ≤ B+J := by omega
    have hm := Nat.mul_le_mul_left (e-δ) hcs
    have hesum : (ext-e)+e=ext := Nat.sub_add_cancel he
    have hsub : (e-δ)+δ=e := Nat.sub_add_cancel hδ
    nlinarith

theorem deletion_cost_dominate (n K ext intr δ δ' B S J : ℕ)
    (hJS : J ≤ S) (hδ' : δ' ≤ δ) (hδ : δ ≤ ext) (hn : n ≤ K+δ') :
    n*B+(ext-δ)*S+(intr+δ)*J ≤
      (K+δ')*B+(ext-δ')*S+(intr+δ')*J := by
  have hb := Nat.mul_le_mul_right B hn
  have hm := Nat.mul_le_mul_left (δ-δ') hJS
  have hsub : (δ-δ')+δ'=δ := Nat.sub_add_cancel hδ'
  have he : (ext-δ)+δ=ext := Nat.sub_add_cancel hδ
  have he' : (ext-δ')+δ'=ext := Nat.sub_add_cancel (hδ'.trans hδ)
  nlinarith

theorem deletion_cost_bound (n K t ext intr budget δ B S J : ℕ)
    (hJS : J ≤ S) (hn : n ≤ t) (hnK : n ≤ K+δ)
    (hδ : δ ≤ budget) (hbudget : budget ≤ ext) :
    n*B+(ext-δ)*S+(intr+δ)*J ≤ deletionCost K t ext intr budget B S J := by
  let k := min K t
  let e := min t (k+budget)-k
  let δ' := min δ e
  have hk : k ≤ t := min_le_right _ _
  have he : e ≤ budget := by dsimp [e]; omega
  have hδe : δ' ≤ e := min_le_right _ _
  have hδδ : δ' ≤ δ := min_le_left _ _
  have hn' : n ≤ k+δ' := by dsimp [δ',e,k]; omega
  have hcost := deletion_cost_dominate n k ext intr δ δ' B S J hJS hδδ
    (hδ.trans hbudget) hn'
  exact hcost.trans (deletion_affine_endpoints k ext intr e δ' B S J hδe (he.trans hbudget))

end ZT
end z59

section z60

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem crossedTargetHeads_budget (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    let G := tolerantGuards T label F t g q x
    let P := positiveTargets T label F t g q x (by decide)
    (crossedTargetHeads T label F t g q x).card+
      ((P.card*G.card+P.card.choose 2)-q*P.card) ≤
      G.card*(q+1)-G.card.choose 2 := by
  let G := tolerantGuards T label F t g q x
  let P := positiveTargets T label F t g q x (by decide)
  let S := externalGuardArcs T label F t g q x
  let Z := externalGuardCoordinates T label F t g q x
  have hcheap := crossedTargetHeads_cheap_card T label F t g q x
  have hout : (Z.filter fun z => z.1 ∉ P ∧ ¬ F t (recursiveChild x z.1 z.2) = false).card ≤
      (S.filter fun e => e.2 ∉ P).card := by
    apply (Finset.card_le_card ?_).trans
      (filter_image_card_le S (arcCoordinate label) (fun z => z.1 ∉ P))
    intro z hz
    obtain ⟨hz,hp,_⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz,hp⟩
  have hδ := hcheap.trans hout
  have hL := external_outside_positive_budget T label F hF t g hgt q x
  have hc := (guardArcs_card T label F hF t g hgt q x).1
  change S.card = G.card*(q+1)-G.card.choose 2 at hc
  change (S.filter fun e => e.2 ∉ P).card+
    ((P.card*G.card+P.card.choose 2)-q*P.card) ≤ S.card at hL
  change (crossedTargetHeads T label F t g q x).card+
    ((P.card*G.card+P.card.choose 2)-q*P.card) ≤ G.card*(q+1)-G.card.choose 2
  rw [←hc]
  exact (Nat.add_le_add_right hδ _).trans hL

theorem ordinary_zero_candidate_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (q a b s j : ℕ) (hjs : j ≤ s)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga q x = false) :
    (flipsTo (tolerantFamily T label F tb gb q) true x).card ≤
      candidateCost q (tolerantTargets T label F tb gb q x).card
        (positiveTargets T label F tb gb q x (by decide)).card
        (tolerantGuards T label F tb gb q x).card
        (crossedTargetHeads T label F tb gb q x).card a b s j := by
  let TC := tolerantTargets T label F tb gb q x
  let P := positiveTargets T label F tb gb q x (by decide)
  let G := tolerantGuards T label F tb gb q x
  let δ := (crossedTargetHeads T label F tb gb q x).card
  let E := G.card*(q+1)-G.card.choose 2
  let L := (P.card*G.card+P.card.choose 2)-q*P.card
  let intr := min (G.card.choose 2) (2*G.card)
  let X := (externalGuardCoordinates T label F tb gb q x).biUnion
    (fun z => childFlipsTo F gb false x z.1 z.2)
  let Y := ((internalGuardArcs T label F tb gb q x).image (arcCoordinate label)).biUnion
    (fun z => childFlipsTo F gb false x z.1 z.2)
  have hgt : gb ≤ tb := hg.trans (hga.trans ht)
  have hX : X.card ≤ (E-(L-P.card)-δ)*s+(min P.card (L-P.card)+δ)*j := by
    have hh := external_guard_cost T label F hF ta tb ga gb ht hg hgt q s j L
      hjs hs hj x hx (external_outside_positive_budget T label F hF tb gb hgt q x)
    rw [(guardArcs_card T label F hF tb gb hgt q x).1] at hh
    exact hh
  have hY : Y.card ≤ intr*j := internal_guard_cost T label F hF tb gb hgt q j hj x
  have hG : (guardRepairs T label F tb gb q x).card ≤
      (E-(L-P.card)-δ)*s+(intr+min P.card (L-P.card)+δ)*j := by
    have hh := (Finset.card_le_card (guardRepairs_subset_coordinates T label F tb gb q x)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hX hY))
    simpa only [Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
  have hT := targetRepairs_card T label F hF ta tb ga gb ht hg q q (le_refl q) a b ha hb x hx
  have hoff : tolerantFamily T label F tb gb q x = false := by
    cases hh : tolerantFamily T label F tb gb q x
    · rfl
    · have hw := family_nested T label F hF ht hg (le_refl q) x hh
      simp [hx] at hw
  have hh := (Finset.card_le_card (up_subset_repairs T label F tb gb q x hoff)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hT hG))
  simpa only [candidateCost,Nat.add_assoc] using hh



theorem candidateCost_le_deletionCost (q t u m δ a b s j K tt : ℕ)
    (hjs : j ≤ s) (ht : t ≤ tt) (hK : t-u ≤ K+δ)
    (hδ : δ+((u*m+u.choose 2)-q*u) ≤ m*(q+1)-m.choose 2) :
    candidateCost q t u m δ a b s j ≤
      u*a+deletionCost K (tt-u)
        ((m*(q+1)-m.choose 2)-(((u*m+u.choose 2)-q*u)-u))
        (min (m.choose 2) (2*m)+min u (((u*m+u.choose 2)-q*u)-u))
        ((m*(q+1)-m.choose 2)-((u*m+u.choose 2)-q*u)) b s j := by
  let E := m*(q+1)-m.choose 2
  let L := (u*m+u.choose 2)-q*u
  let save := L-u
  let intr := min (m.choose 2) (2*m)
  have hδ' : δ ≤ E-L := by change δ+L ≤ E at hδ; omega
  have hbudget : E-L ≤ E-save := by dsimp [save]; omega
  have hh := deletion_cost_bound (t-u) K (tt-u) (E-save) (intr+min u save)
    (E-L) δ b s j hjs (Nat.sub_le_sub_right ht u) hK hδ' hbudget
  have hh' := Nat.add_le_add_left hh (u*a)
  simpa only [candidateCost,Nat.add_assoc] using hh'

end ZT
end
end z60

section z61

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]











theorem _root_.ThreeBoundOrdinaryArchive.Paley11987Verified.CompactBooleanTransfer.ordinary_positive_of_cases (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hCaps : LabelCaps T label) (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (qa q : ℕ) (hq : q ≤ qa) (hpos : 0 < q) (hq8 : q ≤ 8)
    (a b s j z : ℕ) (hjs : j ≤ s)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j)
    (hcases : ∀ m u, m ≤ (if qa=q then 2*q+3 else 0) → u ≤ 2*q+1 →
      (u+m).choose 2 ≤ q*u+(q+1)*m → u ≤ candidateTotalCap q m u →
      (0 < u → gb ≠ ta) → positiveCaseCost q m u a b s j ≤ z)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    (flipsTo (tolerantFamily T label F tb gb q) true x).card ≤ z := by
  let C := tolerantTargets T label F tb gb q x
  let G := tolerantGuards T label F tb gb q x
  let P := positiveTargets T label F tb gb q x (by decide)
  let δ := (crossedTargetHeads T label F tb gb q x).card
  have hgt : gb ≤ tb := hg.trans (hga.trans ht)
  have hxq : tolerantFamily T label F ta ga q x = false := by
    cases hh : tolerantFamily T label F ta ga q x
    · rfl
    · have hw := family_nested T label F hF (le_refl ta) (le_refl ga) hq x hh
      simp [hx] at hw
  have hm : G.card ≤ if qa=q then 2*q+3 else 0 := by
    split_ifs with he
    · exact guards_card T label F hF tb gb hgt q x
    · have hstrict : q < qa := by omega
      have hempty : G=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact no_guard_candidate_of_strict T label F hF ta tb ga gb ht hg x hstrict hx hv
      simp [hempty]
  have hu : P.card ≤ 2*q+1 := positiveTargets_card T label F hF tb gb hgt q x (by decide)
  have hc : (P.card+G.card).choose 2 ≤ q*P.card+(q+1)*G.card :=
    positiveTargets_guards_coupling T label F hF tb gb hgt q x (by decide)
  have htt : C.card ≤ candidateTotalCap q G.card P.card :=
    _root_.ThreeBoundOrdinaryArchive.Paley11987Verified.CompactBooleanTransfer.candidateTotalCap_bound T label hCaps F hF tb gb hgt q hpos hq8 x
  have huC : P.card ≤ C.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hskip : 0 < P.card → gb ≠ ta := by
    intro hn he
    have hempty := positiveTargets_empty_of_gate_eq T label F hF ta tb ga gb ht hg he qa q hq x hx
    have hh : P.card=0 := by simp only [P,hempty,Finset.card_empty]
    omega
  have hK := markedDeletionCap_bound T label hCaps F hF tb gb hgt q hq8 x
  have hδ := crossedTargetHeads_budget T label F hF tb gb hgt q x
  have hraw := ordinary_zero_candidate_cost T label F hF ta tb ga gb ht hg hga q a b s j
    hjs ha hb hs hj x hxq
  have hcost := candidateCost_le_deletionCost q C.card P.card G.card δ a b s j
    (markedCap q G.card) (candidateTotalCap q G.card P.card) hjs htt hK hδ
  exact hraw.trans (hcost.trans (hcases G.card P.card hm hu hc (huC.trans htt) hskip))

end ZT
end
end z61

end ThreeBoundOrdinaryArchive


