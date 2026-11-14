-- Prove2me | solution 1 for APFPaper5.K1.sharedCost_channel_no_joint
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:44:02.675782+00:00
-- url     : https://prove2.me/submissions/68fb2aba-0e14-42c7-80f9-0c39bcc653a7

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_shared_cost
title: The shared cost is symmetric, equals a family's own cost on the diagonal, and counts shared channels less joint channels
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K1_SharedCost. The channel identity is the codebank's check_T_delta_JR_derived, with
 its two named clauses as hypotheses: CH1 (a join activates at least both activation sets) and CH2 (cost is the
 floor times the number of activated channels).
consumes_inputs: none. Ordinary mathematics on a cost function of families.
statement: (sharedCost_symm) the shared cost of S and T is that of T and S. (sharedCost_self) a family's shared
 cost with itself is its cost. (sharedCost_eq_discount) it equals T's cost less what T adds to S.
 (sharedCost_le_left, sharedCost_le_right) if adding a family never lowers cost, the shared cost is at most
 each family's own cost. (sharedCost_nonneg_iff) it is nonnegative exactly when together costs no more than
 apart. (sharedCost_channel_ledger) under CH1 and CH2 it is the floor times (shared channels less joint
 channels). (sharedCost_channel_no_joint) with no joint channel it is the floor times the shared channels.
 (sharedCost_channel_le) it never exceeds the floor times the shared channels.
 (sharedCost_channel_disjoint) with no joint channel and no shared channel, cost adds.
 (cost_is_count_times_floor) the codebank's characterization: a cost that depends only on the count, adds
 across disjoint counts and is eps on one channel is the count times eps. So CH2 reduces to those two clauses.
not_claimed: CH1 or CH2 for the ledger's familyCost; any sign of the shared cost in general; that this number
 is the K layer's score.
-/
import Definitions.Def_APFPaper5_K1_SharedCost
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1

universe u v
variable {D : Type u} [DecidableEq D]

theorem sharedCost_symm (cost : Finset D → ℝ) (S T : Finset D) :
    sharedCost cost S T = sharedCost cost T S := by
  unfold sharedCost
  rw [Finset.union_comm S T]
  ring

theorem sharedCost_self (cost : Finset D → ℝ) (S : Finset D) : sharedCost cost S S = cost S := by
  unfold sharedCost
  rw [Finset.union_self]
  ring

theorem sharedCost_eq_discount (cost : Finset D → ℝ) (S T : Finset D) :
    sharedCost cost S T = cost T - (cost (S ∪ T) - cost S) := by
  unfold sharedCost
  ring

theorem sharedCost_le_right (cost : Finset D → ℝ) (S T : Finset D)
    (h : cost S ≤ cost (S ∪ T)) : sharedCost cost S T ≤ cost T := by
  unfold sharedCost
  linarith

theorem sharedCost_le_left (cost : Finset D → ℝ) (S T : Finset D)
    (h : cost T ≤ cost (S ∪ T)) : sharedCost cost S T ≤ cost S := by
  unfold sharedCost
  linarith

theorem sharedCost_nonneg_iff (cost : Finset D → ℝ) (S T : Finset D) :
    0 ≤ sharedCost cost S T ↔ cost (S ∪ T) ≤ cost S + cost T := by
  unfold sharedCost
  constructor <;> intro h <;> linarith

theorem sharedCost_channel_ledger {Ch : Type v} [DecidableEq Ch] (chan : Finset D → Finset Ch)
    (eps : ℝ) (S T : Finset D) (hCH1 : chan S ∪ chan T ⊆ chan (S ∪ T)) :
    sharedCost (fun X => eps * ((chan X).card : ℝ)) S T =
      eps * (((chan S ∩ chan T).card : ℝ) -
        ((chan (S ∪ T) \ (chan S ∪ chan T)).card : ℝ)) := by
  have h1 := Finset.card_union_add_card_inter (chan S) (chan T)
  have h2 := Finset.card_sdiff_add_card_eq_card hCH1
  have h1' : ((chan S ∪ chan T).card : ℝ) + ((chan S ∩ chan T).card : ℝ) =
      ((chan S).card : ℝ) + ((chan T).card : ℝ) := by exact_mod_cast h1
  have h2' : ((chan (S ∪ T) \ (chan S ∪ chan T)).card : ℝ) + ((chan S ∪ chan T).card : ℝ) =
      ((chan (S ∪ T)).card : ℝ) := by exact_mod_cast h2
  have key : ((chan S).card : ℝ) + ((chan T).card : ℝ) - ((chan (S ∪ T)).card : ℝ) =
      ((chan S ∩ chan T).card : ℝ) - ((chan (S ∪ T) \ (chan S ∪ chan T)).card : ℝ) := by
    linarith
  simp only [sharedCost]
  rw [← key]
  ring

theorem sharedCost_channel_no_joint {Ch : Type v} [DecidableEq Ch] (chan : Finset D → Finset Ch)
    (eps : ℝ) (S T : Finset D) (hJ : chan (S ∪ T) = chan S ∪ chan T) :
    sharedCost (fun X => eps * ((chan X).card : ℝ)) S T =
      eps * ((chan S ∩ chan T).card : ℝ) := by
  rw [sharedCost_channel_ledger chan eps S T (Finset.subset_of_eq hJ.symm), hJ, Finset.sdiff_self,
    Finset.card_empty, Nat.cast_zero, sub_zero]

theorem sharedCost_channel_le {Ch : Type v} [DecidableEq Ch] (chan : Finset D → Finset Ch)
    (eps : ℝ) (heps : 0 ≤ eps) (S T : Finset D) (hCH1 : chan S ∪ chan T ⊆ chan (S ∪ T)) :
    sharedCost (fun X => eps * ((chan X).card : ℝ)) S T ≤
      eps * ((chan S ∩ chan T).card : ℝ) := by
  rw [sharedCost_channel_ledger chan eps S T hCH1]
  have hJ : (0 : ℝ) ≤ ((chan (S ∪ T) \ (chan S ∪ chan T)).card : ℝ) := Nat.cast_nonneg _
  have hprod := mul_nonneg heps hJ
  linarith

theorem sharedCost_channel_disjoint {Ch : Type v} [DecidableEq Ch] (chan : Finset D → Finset Ch)
    (eps : ℝ) (S T : Finset D) (hJ : chan (S ∪ T) = chan S ∪ chan T)
    (hdisj : chan S ∩ chan T = ∅) :
    eps * ((chan (S ∪ T)).card : ℝ) =
      eps * ((chan S).card : ℝ) + eps * ((chan T).card : ℝ) := by
  have h := sharedCost_channel_no_joint chan eps S T hJ
  rw [hdisj, Finset.card_empty, Nat.cast_zero, mul_zero] at h
  simp only [sharedCost] at h
  linarith

omit [DecidableEq D] in
theorem cost_is_count_times_floor (f : ℕ → ℝ) (eps : ℝ)
    (hadd : ∀ m n : ℕ, f (m + n) = f m + f n) (h1 : f 1 = eps) :
    ∀ n : ℕ, f n = (n : ℝ) * eps := by
  have h0 : f 0 = 0 := by
    have h := hadd 0 0
    rw [Nat.add_zero] at h
    linarith
  intro n
  induction n with
  | zero => rw [h0, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [hadd k 1, ih, h1, Nat.cast_succ]
    ring

end APFPaper5.K1


universe apfNative_u apfNative_v
theorem solution :
∀ {D : Type apfNative_u} [inst : DecidableEq.{apfNative_u + 1} D] {Ch : Type apfNative_v}
  [inst_1 : DecidableEq.{apfNative_v + 1} Ch] (chan : Finset.{apfNative_u} D → Finset.{apfNative_v} Ch) (eps : Real)
  (S T : Finset.{apfNative_u} D)
  (hJ :
    @Eq.{apfNative_v + 1} (Finset.{apfNative_v} Ch)
      (chan (@Union.union.{apfNative_u} (Finset.{apfNative_u} D) (@Finset.instUnion.{apfNative_u} D inst) S T))
      (@Union.union.{apfNative_v} (Finset.{apfNative_v} Ch) (@Finset.instUnion.{apfNative_v} Ch inst_1) (chan S)
        (chan T))),
  @Eq.{1} Real
    (@APFPaper5.K1.sharedCost.{apfNative_u} D inst
      (fun (X : Finset.{apfNative_u} D) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) eps
          (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{apfNative_v} Ch (chan X))))
      S T)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) eps
      (@Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{apfNative_v} Ch
          (@Inter.inter.{apfNative_v} (Finset.{apfNative_v} Ch) (@Finset.instInter.{apfNative_v} Ch inst_1) (chan S)
            (chan T))))) := by
  exact @APFPaper5.K1.sharedCost_channel_no_joint
