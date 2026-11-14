-- Prove2me | Definitions.Def_KMedian195_ClientConstraints
-- name    : KMedian195_ClientConstraints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:33.661271+00:00
-- url     : https://prove2.me/theorems/1e25429a-fb4c-42c6-8da0-e112c0d72799
-- title:
--   KMedian195.ClientConstraints
-- statement:
--   This is module `KMedian195.ClientConstraints` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 32 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_ClientConstraints`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/ClientConstraints.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/ClientConstraints.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`).
-/
module

public import Definitions.Def_KMedian195_CreditLemmas

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.ClientConstraints` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

noncomputable section

variable {n : ℕ} [NeZero n]

namespace DualProgram

omit [NeZero n] in
theorem bid_le_one (P : DualProgram n) (i j : Idx n) : P.bid i j ≤ 1 := by
  by_cases h : P.bidding i j
  · simp [DualProgram.bid, BiddingMatrix.coeff, h]
  · simp [DualProgram.bid, BiddingMatrix.coeff, h]

end DualProgram

namespace ProcedureInput

theorem bid_eq_one_at_firstBidTime (I : ProcedureInput n) (j : Idx n) :
    I.program.bid (I.firstBidTime j) j = 1 := by
  simpa [DualProgram.bid] using
    I.program.bidding.coeff_eq_one (I.firstBidTime_isOne j)

theorem bid_eq_zero_of_lt_firstBidTime
    (I : ProcedureInput n) {j i : Idx n} (hji : j ≤ i) (hif : i < I.firstBidTime j) :
    I.program.bid i j = 0 := by
  by_cases hbid : I.program.bidding i j = true
  · have hmem : i ∈ I.activeTimes j := by
      exact mem_activeTimes.mpr ⟨hji, hbid⟩
    have hmin : I.firstBidTime j ≤ i := Finset.min'_le _ _ hmem
    exact (not_le_of_gt hif hmin).elim
  · simp [DualProgram.bid, BiddingMatrix.coeff, hbid]

theorem sum_halfOpen_bid_eq_zero_of_le_firstBidTime
    (I : ProcedureInput n) {j i : Idx n} (_hji : j ≤ i) (hif : i ≤ I.firstBidTime j) :
    Finset.sum (halfOpenIntervalRange j i) (fun p => I.program.bid p j) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hpj : j ≤ p := (mem_halfOpenIntervalRange.mp hp).1
  have hpf : p < I.firstBidTime j :=
    lt_of_lt_of_le (mem_halfOpenIntervalRange.mp hp).2 hif
  exact I.bid_eq_zero_of_lt_firstBidTime hpj hpf

theorem sum_halfOpen_bid_ge_one_of_firstBidTime_lt
    (I : ProcedureInput n) {j i : Idx n} (hif : I.firstBidTime j < i) :
    1 ≤ Finset.sum (halfOpenIntervalRange j i) (fun p => I.program.bid p j) := by
  have hmem : I.firstBidTime j ∈ halfOpenIntervalRange j i := by
    simp [I.le_firstBidTime j, hif]
  calc
    1 = I.program.bid (I.firstBidTime j) j := by
      symm
      exact I.bid_eq_one_at_firstBidTime j
    _ ≤ Finset.sum (halfOpenIntervalRange j i) (fun p => I.program.bid p j) := by
      exact Finset.single_le_sum
        (fun p hp => by
          simpa [DualProgram.bid] using I.program.bidding.coeff_nonneg p j)
        hmem

theorem clientConstraintRhs_eq_zero_of_lt_firstBidTime
    (I : ProcedureInput n) {j i : Idx n} (hji : j ≤ i) (hif : i < I.firstBidTime j) :
    I.program.bid i j -
        I.program.Mcoeffmone *
          Finset.sum (halfOpenIntervalRange j i) (fun p => I.program.bid p j) = 0 := by
  rw [I.bid_eq_zero_of_lt_firstBidTime hji hif,
    I.sum_halfOpen_bid_eq_zero_of_le_firstBidTime hji (le_of_lt hif)]
  ring

theorem clientConstraintRhs_eq_one_of_eq_firstBidTime
    (I : ProcedureInput n) {j : Idx n} :
    I.program.bid (I.firstBidTime j) j -
        I.program.Mcoeffmone *
          Finset.sum (halfOpenIntervalRange j (I.firstBidTime j))
            (fun p => I.program.bid p j) = 1 := by
  rw [I.bid_eq_one_at_firstBidTime j,
    I.sum_halfOpen_bid_eq_zero_of_le_firstBidTime (I.le_firstBidTime j) le_rfl]
  ring

theorem clientConstraintRhs_le_one_sub_epsilon_of_firstBidTime_lt
    (I : ProcedureInput n) (hγlo : 1 ≤ I.program.Mcoeff)
    {j i : Idx n} (_hji : j ≤ i) (hif : I.firstBidTime j < i) :
    I.program.bid i j -
        I.program.Mcoeffmone *
          Finset.sum (halfOpenIntervalRange j i) (fun p => I.program.bid p j) ≤
      1 - I.program.epsilon := by
  have hsum : 1 ≤ Finset.sum (halfOpenIntervalRange j i) (fun p => I.program.bid p j) :=
    I.sum_halfOpen_bid_ge_one_of_firstBidTime_lt hif
  have hbid : I.program.bid i j ≤ 1 := I.program.bid_le_one i j
  have hε : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  change I.program.bid i j -
      I.program.epsilon *
        Finset.sum (halfOpenIntervalRange j i) (fun p => I.program.bid p j) ≤
      1 - I.program.epsilon
  nlinarith

end ProcedureInput

namespace ProfileData

variable {I : ProcedureInput n} {Γ : Advice I}

def creditAfterA (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  1 - Finset.sum (intervalRange j i) (fun p => AUX.delta p j)

def creditAfterB (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  1 - (if I.firstBidTime j < i then I.program.epsilon else 0)

def creditAfterC (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  1 - (if I.firstBidTime j < i then I.program.epsilon else 0)

def creditAfterD (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (_i _j : Idx n) : ℝ :=
  1

def creditBeforeA (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) +
    Finset.sum (intervalRange j i) (fun p => AUX.sigma p j)

def creditBeforeB (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (_i j : Idx n) : ℝ :=
  I.program.tau + min (beforeBudget C.hatG j) I.program.barTau

def creditBeforeC (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (_i j : Idx n) : ℝ :=
  I.program.tau + beforeBudget C.hatG j

def creditBeforeD (C : ProfileData I Γ) (_AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  beforeBudget C.hatG j - tailBudget C.hatG i

def weightedCreditAfter (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  (C.memberships).muA j * C.creditAfterA AUX i j +
    (C.memberships).muB j * C.creditAfterB AUX i j +
    (C.memberships).muC j * C.creditAfterC AUX i j +
    (C.memberships).muD j * C.creditAfterD AUX i j

def weightedCreditBefore (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (i j : Idx n) : ℝ :=
  (C.memberships).muA j * C.creditBeforeA AUX i j +
    (C.memberships).muB j * C.creditBeforeB AUX i j +
    (C.memberships).muC j * C.creditBeforeC AUX i j +
    (C.memberships).muD j * C.creditBeforeD AUX i j

theorem hatG_eq_zero_of_t3_lt
    (C : ProfileData I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (hi : Γ.t3Star < i) :
    C.hatG i = 0 := by
  have ht1i : C.t1 < i := lt_of_le_of_lt (C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos) hi
  rw [C.copied_above_t1 ht1i, C.phaseTwo.zero_above_t3 hi]

theorem delta_eq_zero_of_t3_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i j : Idx n} (hj : 0 < (C.memberships).muA j) (hi : Γ.t3Star < i) :
    AUX.delta i j = 0 := by
  have hhat : C.hatG i = 0 := C.hatG_eq_zero_of_t3_lt hγlo hγhi hθpos hi
  have hδnonneg : 0 ≤ AUX.delta i j := AUX.delta_nonneg i j hj
  have hδle : AUX.delta i j ≤ C.hatG i := AUX.delta_le_hatG i j hj
  linarith

theorem muD_mul_one_sub_tail_eq_of_firstBid_le
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hif : I.firstBidTime j ≤ i) :
    (C.memberships).muD j * (1 - tailBudget C.hatG i) =
      (C.memberships).muD j * 1 := by
  by_cases hμ0 : Γ.muD j = 0
  · rw [C.memberships_muD, hμ0]
    ring
  · have hμnonneg : 0 ≤ Γ.muD j := Advice.muD_nonneg_of_admissible Γ hΓ j
    have hμpos : 0 < Γ.muD j := lt_of_le_of_ne hμnonneg (Ne.symm hμ0)
    have ht3le : Γ.t3Star ≤ i := le_trans (t3_le_firstBidTime_of_muD_pos Γ hμpos) hif
    rw [C.memberships_muD, C.tailBudget_eq_zero_of_t3_le hγlo hγhi hθpos ht3le]
    ring

theorem sum_interval_delta_eq_zero_at_firstBidTime
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    {j : Idx n} (hj : 0 < (C.memberships).muA j) :
    Finset.sum (intervalRange j (I.firstBidTime j)) (fun p => AUX.delta p j) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  exact AUX.delta_eq_zero p j hj (mem_intervalRange.mp hp).2

theorem sum_interval_delta_le_deltaRange
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hj : 0 < (C.memberships).muA j) :
    Finset.sum (intervalRange j i) (fun p => AUX.delta p j) ≤
      Finset.sum (deltaRange I Γ j) (fun p => AUX.delta p j) := by
  let s :=
    (intervalRange j i).filter fun p => I.firstBidTime j < p ∧ p ≤ Γ.t3Star
  have hs_subset : s ⊆ intervalRange j i := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hsum_eq :
      Finset.sum (intervalRange j i) (fun p => AUX.delta p j) =
        Finset.sum s (fun p => AUX.delta p j) := by
    symm
    apply Finset.sum_subset hs_subset
    intro p hpInt hpNot
    have hzero : AUX.delta p j = 0 := by
      by_cases hp_le : p ≤ I.firstBidTime j
      · exact AUX.delta_eq_zero p j hj hp_le
      · have hp_gt : I.firstBidTime j < p := lt_of_not_ge hp_le
        have hp_not_t3 : ¬ p ≤ Γ.t3Star := by
          intro hp_t3
          exact hpNot (Finset.mem_filter.mpr ⟨hpInt, ⟨hp_gt, hp_t3⟩⟩)
        exact C.delta_eq_zero_of_t3_lt AUX hγlo hγhi hθpos hj (lt_of_not_ge hp_not_t3)
    simp [hzero]
  have hs_delta : s ⊆ deltaRange I Γ j := by
    intro p hp
    exact mem_deltaRange.mpr (Finset.mem_filter.mp hp).2
  calc
    Finset.sum (intervalRange j i) (fun p => AUX.delta p j)
      = Finset.sum s (fun p => AUX.delta p j) := hsum_eq
    _ ≤ Finset.sum (deltaRange I Γ j) (fun p => AUX.delta p j) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hs_delta
        (fun p hp hpnot => AUX.delta_nonneg p j hj)

theorem sum_interval_delta_le_epsilon_of_muA_pos
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hj : 0 < (C.memberships).muA j) :
    Finset.sum (intervalRange j i) (fun p => AUX.delta p j) ≤ I.program.epsilon := by
  have hle :=
    C.sum_interval_delta_le_deltaRange AUX hγlo hγhi hθpos hj (j := j) (i := i)
  have hfactor_nonneg :
      0 ≤ posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) / I.program.theta := by
    exact div_nonneg (posPart_nonneg _ ) (le_of_lt hθpos)
  have hfactor_le :
      1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
          I.program.theta ≤ 1 := by
    linarith
  calc
    Finset.sum (intervalRange j i) (fun p => AUX.delta p j)
      ≤ Finset.sum (deltaRange I Γ j) (fun p => AUX.delta p j) := hle
    _ = I.program.epsilon *
        (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
          I.program.theta) := by
          rw [AUX.delta_sum_eq j hj]
    _ ≤ I.program.epsilon * 1 := by
          exact mul_le_mul_of_nonneg_left hfactor_le
            (I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo)
    _ = I.program.epsilon := by ring

theorem creditAfterA_ge_one_sub_epsilon_of_muA_pos
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hj : 0 < (C.memberships).muA j) :
    1 - I.program.epsilon ≤ C.creditAfterA AUX i j := by
  unfold creditAfterA
  have hle := C.sum_interval_delta_le_epsilon_of_muA_pos AUX hγlo hγhi hθpos hj (j := j) (i := i)
  linarith

theorem creditValue_after_eq_weighted
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hji : j ≤ i) (hif : I.firstBidTime j ≤ i) :
    C.creditValue AUX i j = C.weightedCreditAfter AUX i j := by
  by_cases hjt1 : j < C.t1
  · calc
      C.creditValue AUX i j
        = (C.memberships).muA j *
            (1 - Finset.sum (intervalRange j i) (fun p => AUX.delta p j)) +
          (C.memberships).muD j * (1 - tailBudget C.hatG i) := by
              simpa using
                C.creditValue_after_eq_weighted_AD_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjt1 hji hif
      _ = C.weightedCreditAfter AUX i j := by
            unfold weightedCreditAfter creditAfterA creditAfterB creditAfterC creditAfterD
            rw [C.memberships_muB_eq_zero_of_lt_t1 hjt1, C.memberships_muC_eq_zero_of_lt_t1 hjt1,
              C.muD_mul_one_sub_tail_eq_of_firstBid_le hΓ hγlo hγhi hθpos hif]
            ring
  · by_cases hjeq : j = C.t1
    · subst hjeq
      calc
        C.creditValue AUX i C.t1
          = (C.memberships).muA C.t1 *
              (1 - Finset.sum (intervalRange C.t1 i) (fun p => AUX.delta p C.t1)) +
            (C.memberships).muB C.t1 *
              (1 - (if I.firstBidTime C.t1 < i then I.program.epsilon else 0)) +
            (C.memberships).muD C.t1 * 1 := by
                simpa using
                  C.creditValue_after_eq_weighted_ABD_at_t1 AUX hΓ hγlo hγhi hθpos hji hif
        _ = C.weightedCreditAfter AUX i C.t1 := by
              unfold weightedCreditAfter creditAfterA creditAfterB creditAfterC creditAfterD
              rw [C.memberships_muC_eq_zero_at_t1]
              ring
    · by_cases hjt2 : j ≤ C.t2
      · have ht1j : C.t1 < j := lt_of_le_of_ne (not_lt.mp hjt1) (Ne.symm hjeq)
        calc
          C.creditValue AUX i j
            = (C.memberships).muB j *
                (1 - (if I.firstBidTime j < i then I.program.epsilon else 0)) +
              (C.memberships).muD j * (1 - tailBudget C.hatG i) := by
                  simpa using
                    C.creditValue_after_eq_weighted_BD_of_between_t1_t2 AUX hΓ ht1j hjt2 hji hif
          _ = C.weightedCreditAfter AUX i j := by
                unfold weightedCreditAfter creditAfterA creditAfterB creditAfterC creditAfterD
                rw [C.memberships_muA_eq_zero_of_between_t1_t2 ht1j hjt2,
                  C.memberships_muC_eq_zero_of_between_t1_t2 ht1j hjt2,
                  C.muD_mul_one_sub_tail_eq_of_firstBid_le hΓ hγlo hγhi hθpos hif]
                ring
      · by_cases hjt3 : j ≤ Γ.t3Star
        · have ht2j : C.t2 < j := lt_of_not_ge hjt2
          calc
            C.creditValue AUX i j
              = (C.memberships).muC j *
                  (1 - (if I.firstBidTime j < i then I.program.epsilon else 0)) +
                (C.memberships).muD j * (1 - tailBudget C.hatG i) := by
                    simpa using
                      C.creditValue_after_eq_weighted_CD_of_between_t2_t3 AUX hΓ ht2j hjt3 hji hif
            _ = C.weightedCreditAfter AUX i j := by
                  unfold weightedCreditAfter creditAfterA creditAfterB creditAfterC creditAfterD
                  rw [C.memberships_muA_eq_zero_of_between_t2_t3 ht2j hjt3,
                    C.memberships_muB_eq_zero_of_between_t2_t3 ht2j hjt3,
                    C.muD_mul_one_sub_tail_eq_of_firstBid_le hΓ hγlo hγhi hθpos hif]
                  ring
        · have hgt3 : Γ.t3Star < j := lt_of_not_ge hjt3
          have hμ : Γ.muD j = 1 := by
            exact Advice.muD_eq_one Γ (lt_of_lt_of_le hgt3 (I.le_firstBidTime j))
          calc
            C.creditValue AUX i j = 1 := by
              simpa using
                C.creditValue_D_after_eq_of_integralD AUX hΓ hγlo hγhi hθpos hμ hji hif
            _ = C.weightedCreditAfter AUX i j := by
              unfold weightedCreditAfter creditAfterA creditAfterB creditAfterC creditAfterD
              rw [C.memberships_muA_eq_zero_of_muD_eq_one hΓ hμ,
                C.memberships_muB_eq_zero_of_muD_eq_one hΓ hμ,
                C.memberships_muC_eq_zero_of_muD_eq_one hΓ hμ,
                C.memberships_muD, hμ]
              ring

theorem creditValue_before_eq_weighted
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hji : j ≤ i) (hif : i < I.firstBidTime j) :
    C.creditValue AUX i j = C.weightedCreditBefore AUX i j := by
  by_cases hjt1 : j < C.t1
  · calc
      C.creditValue AUX i j
        = (C.memberships).muA j *
            (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) +
              Finset.sum (intervalRange j i) (fun p => AUX.sigma p j)) +
          (C.memberships).muD j * (beforeBudget C.hatG j - tailBudget C.hatG i) := by
              simpa using
                C.creditValue_before_eq_weighted_AD_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjt1 hji hif
      _ = C.weightedCreditBefore AUX i j := by
            unfold weightedCreditBefore creditBeforeA creditBeforeB creditBeforeC creditBeforeD
            rw [C.memberships_muB_eq_zero_of_lt_t1 hjt1, C.memberships_muC_eq_zero_of_lt_t1 hjt1]
            ring
  · by_cases hjeq : j = C.t1
    · subst hjeq
      calc
        C.creditValue AUX i C.t1
          = (C.memberships).muA C.t1 *
              (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime C.t1)) +
                Finset.sum (intervalRange C.t1 i) (fun p => AUX.sigma p C.t1)) +
            (C.memberships).muB C.t1 * 1 +
            (C.memberships).muD C.t1 * (beforeBudget C.hatG C.t1 - tailBudget C.hatG i) := by
                simpa using
                  C.creditValue_before_eq_weighted_ABD_at_t1 AUX hΓ hγlo hγhi hθpos hji hif
        _ = C.weightedCreditBefore AUX i C.t1 := by
              unfold weightedCreditBefore creditBeforeA creditBeforeB creditBeforeC creditBeforeD
              rw [C.memberships_muC_eq_zero_at_t1,
                min_eq_right (C.beforeBudget_t1_ge_barTau hΓ hγlo hγhi)]
              simp [DualProgram.barTau]
    · by_cases hjt2 : j ≤ C.t2
      · have ht1j : C.t1 < j := lt_of_le_of_ne (not_lt.mp hjt1) (Ne.symm hjeq)
        calc
          C.creditValue AUX i j
            = (C.memberships).muB j * (I.program.tau + beforeBudget C.hatG j) +
              (C.memberships).muD j * (beforeBudget C.hatG j - tailBudget C.hatG i) := by
                  simpa using
                    C.creditValue_before_eq_weighted_BD_of_between_t1_t2 AUX hΓ ht1j hjt2 hji hif
          _ = C.weightedCreditBefore AUX i j := by
                unfold weightedCreditBefore creditBeforeA creditBeforeB creditBeforeC creditBeforeD
                rw [C.memberships_muA_eq_zero_of_between_t1_t2 ht1j hjt2,
                  C.memberships_muC_eq_zero_of_between_t1_t2 ht1j hjt2,
                  min_eq_left (le_of_lt (C.beforeBudget_lt_barTau_of_lt_t1 ht1j))]
                ring
      · by_cases hjt3 : j ≤ Γ.t3Star
        · have ht2j : C.t2 < j := lt_of_not_ge hjt2
          calc
            C.creditValue AUX i j
              = (C.memberships).muC j * (I.program.tau + beforeBudget C.hatG j) +
                (C.memberships).muD j * (beforeBudget C.hatG j - tailBudget C.hatG i) := by
                    simpa using
                      C.creditValue_before_eq_weighted_CD_of_between_t2_t3 AUX hΓ ht2j hjt3 hji hif
            _ = C.weightedCreditBefore AUX i j := by
                  unfold weightedCreditBefore creditBeforeA creditBeforeB
                    creditBeforeC creditBeforeD
                  rw [C.memberships_muA_eq_zero_of_between_t2_t3 ht2j hjt3,
                    C.memberships_muB_eq_zero_of_between_t2_t3 ht2j hjt3]
                  ring
        · have hgt3 : Γ.t3Star < j := lt_of_not_ge hjt3
          have hμ : Γ.muD j = 1 := by
            exact Advice.muD_eq_one Γ (lt_of_lt_of_le hgt3 (I.le_firstBidTime j))
          calc
            C.creditValue AUX i j = beforeBudget C.hatG j - tailBudget C.hatG i := by
              simpa using
                C.creditValue_D_before_eq_of_integralD AUX hΓ hγlo hγhi hθpos hμ hji hif
            _ = C.weightedCreditBefore AUX i j := by
              unfold weightedCreditBefore creditBeforeA creditBeforeB creditBeforeC creditBeforeD
              rw [C.memberships_muA_eq_zero_of_muD_eq_one hΓ hμ,
                C.memberships_muB_eq_zero_of_muD_eq_one hΓ hμ,
                C.memberships_muC_eq_zero_of_muD_eq_one hΓ hμ,
                C.memberships_muD, hμ]
              ring

theorem creditValue_nonneg_of_lt_firstBidTime
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hji : j ≤ i) (hif : i < I.firstBidTime j) :
    0 ≤ C.creditValue AUX i j := by
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have hhatG : ∀ k, 0 ≤ C.hatG k :=
    C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  rw [C.creditValue_before_eq_weighted AUX hΓ hγlo hγhi hθpos hji hif]
  have hA :
      0 ≤ (C.memberships).muA j * C.creditBeforeA AUX i j := by
    by_cases hμA0 : (C.memberships).muA j = 0
    · simp [hμA0]
    · have hμApos : 0 < (C.memberships).muA j := lt_of_le_of_ne (hμnonneg.1 j) (Ne.symm hμA0)
      have htail : 0 ≤ tailBudget C.hatG (I.firstBidTime j) :=
        tailBudget_nonneg_of_nonneg hhatG (I.firstBidTime j)
      have hθnonneg : 0 ≤ I.program.theta := I.program.theta_nonneg_of_one_le_Mcoeff hγlo
      have hθle1 : I.program.theta ≤ 1 := I.program.theta_le_one_of_le_153_div_125 hγlo hγhi
      have hbase :
          0 ≤ 1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) := by
        exact one_sub_posPart_sub_nonneg htail hθnonneg hθle1
      have hsigma :
          0 ≤ Finset.sum (intervalRange j i) (fun p => AUX.sigma p j) := by
        exact Finset.sum_nonneg (fun p hp => AUX.sigma_nonneg p j hμApos)
      have hcredit : 0 ≤ C.creditBeforeA AUX i j := by
        unfold creditBeforeA
        linarith
      exact mul_nonneg (hμnonneg.1 j) hcredit
  have hB :
      0 ≤ (C.memberships).muB j * C.creditBeforeB AUX i j := by
    have hbefore : 0 ≤ beforeBudget C.hatG j := beforeBudget_nonneg_of_nonneg hhatG j
    have hbar : 0 ≤ I.program.barTau := I.program.barTau_nonneg_of_le_153_div_125 hγlo hγhi
    have hcredit : 0 ≤ C.creditBeforeB AUX i j := by
      unfold creditBeforeB
      exact add_nonneg (I.program.tau_nonneg_of_one_le_Mcoeff hγlo) (le_min hbefore hbar)
    exact mul_nonneg (hμnonneg.2.1 j) hcredit
  have hC :
      0 ≤ (C.memberships).muC j * C.creditBeforeC AUX i j := by
    have hcredit : 0 ≤ C.creditBeforeC AUX i j := by
      unfold creditBeforeC
      exact add_nonneg (I.program.tau_nonneg_of_one_le_Mcoeff hγlo)
        (beforeBudget_nonneg_of_nonneg hhatG j)
    exact mul_nonneg (hμnonneg.2.2.1 j) hcredit
  have hD :
      0 ≤ (C.memberships).muD j * C.creditBeforeD AUX i j := by
    have hcredit : 0 ≤ C.creditBeforeD AUX i j := by
      unfold creditBeforeD
      rw [← C.sum_interval_hatG_eq_before_sub_tail hji]
      exact Finset.sum_nonneg (fun p hp => hhatG p)
    exact mul_nonneg (hμnonneg.2.2.2 j) hcredit
  unfold weightedCreditBefore
  nlinarith

theorem creditValue_eq_one_of_eq_firstBidTime
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hji : j ≤ i) (hif : i = I.firstBidTime j) :
    C.creditValue AUX i j = 1 := by
  subst i
  rw [C.creditValue_after_eq_weighted AUX hΓ hγlo hγhi hθpos hji le_rfl]
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have hA :
      (C.memberships).muA j * C.creditAfterA AUX (I.firstBidTime j) j =
        (C.memberships).muA j := by
    by_cases hμA0 : (C.memberships).muA j = 0
    · simp [hμA0, creditAfterA]
    · have hμApos : 0 < (C.memberships).muA j := lt_of_le_of_ne (hμnonneg.1 j) (Ne.symm hμA0)
      rw [show C.creditAfterA AUX (I.firstBidTime j) j =
          1 - Finset.sum (intervalRange j (I.firstBidTime j)) (fun p => AUX.delta p j) by rfl,
        C.sum_interval_delta_eq_zero_at_firstBidTime AUX hμApos]
      ring
  unfold weightedCreditAfter
  rw [hA]
  unfold creditAfterB creditAfterC creditAfterD
  calc
    (C.memberships).muA j +
        (C.memberships).muB j *
          (1 - if I.firstBidTime j < I.firstBidTime j then I.program.epsilon else 0) +
        (C.memberships).muC j *
          (1 - if I.firstBidTime j < I.firstBidTime j then I.program.epsilon else 0) +
        (C.memberships).muD j * 1
      = (C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j +
          (C.memberships).muD j := by simp
    _ = 1 := by
      simpa [MembershipWeights.total] using C.memberships_total j

theorem creditValue_ge_one_sub_epsilon_of_firstBidTime_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hji : j ≤ i) (hif : I.firstBidTime j < i) :
    1 - I.program.epsilon ≤ C.creditValue AUX i j := by
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  rw [C.creditValue_after_eq_weighted AUX hΓ hγlo hγhi hθpos hji (le_of_lt hif)]
  have hA :
      (C.memberships).muA j * (1 - I.program.epsilon) ≤
        (C.memberships).muA j * C.creditAfterA AUX i j := by
    by_cases hμA0 : (C.memberships).muA j = 0
    · simp [hμA0]
    · have hμApos : 0 < (C.memberships).muA j := lt_of_le_of_ne (hμnonneg.1 j) (Ne.symm hμA0)
      exact mul_le_mul_of_nonneg_left
        (C.creditAfterA_ge_one_sub_epsilon_of_muA_pos AUX hγlo hγhi hθpos hμApos)
        (hμnonneg.1 j)
  have hB :
      (C.memberships).muB j * (1 - I.program.epsilon) =
        (C.memberships).muB j * C.creditAfterB AUX i j := by
    unfold creditAfterB
    simp [hif]
  have hC :
      (C.memberships).muC j * (1 - I.program.epsilon) =
        (C.memberships).muC j * C.creditAfterC AUX i j := by
    unfold creditAfterC
    simp [hif]
  have hD :
      (C.memberships).muD j * (1 - I.program.epsilon) ≤
        (C.memberships).muD j * C.creditAfterD AUX i j := by
    unfold creditAfterD
    have hε : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
    have hone : 1 - I.program.epsilon ≤ 1 := by linarith
    exact mul_le_mul_of_nonneg_left hone (hμnonneg.2.2.2 j)
  have htotal :
      (C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j +
          (C.memberships).muD j = 1 := by
    simpa [MembershipWeights.total] using C.memberships_total j
  unfold weightedCreditAfter
  calc
    1 - I.program.epsilon
      = (C.memberships).muA j * (1 - I.program.epsilon) +
          (C.memberships).muB j * (1 - I.program.epsilon) +
          (C.memberships).muC j * (1 - I.program.epsilon) +
          (C.memberships).muD j * (1 - I.program.epsilon) := by
            calc
              1 - I.program.epsilon
                = ((C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j +
                    (C.memberships).muD j) * (1 - I.program.epsilon) := by
                      rw [htotal]
                      ring
              _ = (C.memberships).muA j * (1 - I.program.epsilon) +
                    (C.memberships).muB j * (1 - I.program.epsilon) +
                    (C.memberships).muC j * (1 - I.program.epsilon) +
                    (C.memberships).muD j * (1 - I.program.epsilon) := by
                      ring
    _ ≤ (C.memberships).muA j * C.creditAfterA AUX i j +
          (C.memberships).muB j * C.creditAfterB AUX i j +
          (C.memberships).muC j * C.creditAfterC AUX i j +
          (C.memberships).muD j * C.creditAfterD AUX i j := by
            nlinarith [hA, hB, hC, hD]
    _ = C.weightedCreditAfter AUX i j := by rfl

theorem constructedDualSolution_clientCredit_ge_creditValue
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i j : Idx n} (hji : j ≤ i) :
    C.creditValue AUX i j ≤ DualSolution.clientCredit (C.constructedDualSolution AUX) i j := by
  rcases lt_or_eq_of_le hji with hlt | rfl
  · have hstrict :
        ∀ p,
          DualSolution.strictS (C.constructedDualSolution AUX) p j = C.shiftedSValue AUX p j := by
      intro p
      by_cases hjp : j < p <;> simp [DualSolution.strictS, ProfileData.shiftedSValue, hjp]
    have hs₁ :
        Finset.sum (intervalRange j i)
            (fun p => DualSolution.strictS (C.constructedDualSolution AUX) p j) =
          Finset.sum (intervalRange j i) (fun p => C.shiftedSValue AUX p j) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hstrict p
    have hs₂ :
        Finset.sum (intervalRange j i) (fun p => C.shiftedSValue AUX p j) =
          Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j) := by
      exact C.sum_interval_shiftedSValue_eq_of_lt AUX hlt
    have hs :
        Finset.sum (intervalRange j i)
            (fun p => DualSolution.strictS (C.constructedDualSolution AUX) p j) =
          Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j) := by
      exact hs₁.trans hs₂
    unfold DualSolution.clientCredit ProfileData.creditValue ProfileData.integralClientCredit
    simp only
      [Finset.sum_sub_distrib, constructedDualSolution_g, constructedDualSolution_t,
        add_le_add_iff_left, tsub_le_iff_right, ge_iff_le]
    rw [hs]
    ring_nf
    exact le_rfl
  · let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
    have hsdiag : 0 ≤ C.sValue AUX j j := C.sValue_nonneg H AUX j j
    have hsingle : intervalRange j j = ({j} : Finset (Idx n)) := by
      ext x
      constructor
      · intro hx
        rcases mem_intervalRange.mp hx with ⟨hjx, hxj⟩
        simp [le_antisymm hxj hjx]
      · intro hx
        have hx' : x = j := by simpa using hx
        subst x
        exact mem_intervalRange.mpr ⟨le_rfl, le_rfl⟩
    have hraw :
        C.creditValue AUX j j =
          Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) +
            (C.gValue AUX j j + C.tValue AUX j j - C.sValue AUX j j) := by
      unfold ProfileData.creditValue ProfileData.integralClientCredit
      rw [hsingle]
      simp
    have hnew :
        DualSolution.clientCredit (C.constructedDualSolution AUX) j j =
          Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) +
            (C.gValue AUX j j + C.tValue AUX j j) := by
      unfold DualSolution.clientCredit DualSolution.strictS
      rw [hsingle]
      simp [constructedDualSolution_g, constructedDualSolution_t, ProfileData.shiftedSValue]
    rw [hraw, hnew]
    linarith

theorem constructedDualSolution_satisfiesClientConstraints
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    DualSolution.SatisfiesClientConstraints (C.constructedDualSolution AUX) I.program := by
  intro j i hji
  have hcredit_ge :
      C.creditValue AUX i j ≤ DualSolution.clientCredit (C.constructedDualSolution AUX) i j :=
    C.constructedDualSolution_clientCredit_ge_creditValue AUX hΓ hγlo hγhi hji
  by_cases hlt : i < I.firstBidTime j
  · rw [I.clientConstraintRhs_eq_zero_of_lt_firstBidTime hji hlt]
    have hcredit_nonneg :
        0 ≤ C.creditValue AUX i j :=
      C.creditValue_nonneg_of_lt_firstBidTime AUX hΓ hγlo hγhi hθpos hji hlt
    linarith
  · by_cases heq : i = I.firstBidTime j
    · rw [heq, I.clientConstraintRhs_eq_one_of_eq_firstBidTime]
      have hcredit_eq : C.creditValue AUX (I.firstBidTime j) j = 1 := by
        simpa [heq] using
          C.creditValue_eq_one_of_eq_firstBidTime AUX hΓ hγlo hγhi hθpos hji heq
      have hcredit_ge' :
          C.creditValue AUX (I.firstBidTime j) j ≤
            DualSolution.clientCredit (C.constructedDualSolution AUX) (I.firstBidTime j) j := by
        simpa [heq] using hcredit_ge
      linarith
    · have hgt : I.firstBidTime j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm heq)
      have hcredit :
          1 - I.program.epsilon ≤ C.creditValue AUX i j :=
        C.creditValue_ge_one_sub_epsilon_of_firstBidTime_lt AUX hΓ hγlo hγhi hθpos hji hgt
      have hrhs :
          I.program.bid i j -
              I.program.Mcoeffmone *
                Finset.sum (halfOpenIntervalRange j i) (fun p => I.program.bid p j) ≤
            1 - I.program.epsilon :=
        I.clientConstraintRhs_le_one_sub_epsilon_of_firstBidTime_lt hγlo hji hgt
      linarith

end ProfileData

end

end KMedian195


