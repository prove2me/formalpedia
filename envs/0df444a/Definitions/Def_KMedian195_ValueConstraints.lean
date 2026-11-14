-- Prove2me | Definitions.Def_KMedian195_ValueConstraints
-- name    : KMedian195_ValueConstraints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:46.079692+00:00
-- url     : https://prove2.me/theorems/2bbe2021-b6fa-48d3-afff-e19f75c25085
-- title:
--   KMedian195.ValueConstraints
-- statement:
--   This is module `KMedian195.ValueConstraints` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 35 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_ValueConstraints`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/ValueConstraints.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/ValueConstraints.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`), and:
* `if_pos`, `if_neg`, `dif_pos`, `dif_neg` (deprecated) are `if_pos`, `if_neg`,
  `dif_pos`, `dif_neg`.
-/
module

public import Definitions.Def_KMedian195_ClientConstraints

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.ValueConstraints` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

noncomputable section

variable {n : ℕ} [NeZero n]

namespace DualProgram

omit [NeZero n] in
theorem epsilon_add_barTau_eq_oneMinusTheta (P : DualProgram n) :
    P.epsilon + P.barTau = P.oneMinusTheta := by
  dsimp [epsilon, barTau, oneMinusTheta, tau, theta, DualProgram.Mcoeffmone]
  ring

omit [NeZero n] in
theorem gamma_add_oneMinusTheta_eq_rho (P : DualProgram n) :
    P.Mcoeff + P.oneMinusTheta = P.rhoBound := by
  calc
    P.Mcoeff + P.oneMinusTheta = P.Mcoeff + 1 - P.theta := by
      simp [oneMinusTheta]
      ring
    _ = P.rhoBound := P.gamma_add_one_sub_theta_eq_rho

omit [NeZero n] in
theorem frac_mul_tau_eq_epsilon_of_theta_pos
    (P : DualProgram n) (hγlo : 1 ≤ P.Mcoeff) (hθpos : 0 < P.theta) :
    P.frac * P.tau = P.epsilon := by
  have hτpos : 0 < P.tau := by
    rw [← P.epsilon_add_theta_eq_tau]
    linarith [P.epsilon_nonneg_of_one_le_Mcoeff hγlo]
  unfold DualProgram.frac
  field_simp [ne_of_gt hτpos]

end DualProgram

theorem suffixRange_eq_interval_last (j : Idx n) :
    suffixRange j = intervalRange j (lastIdx n) := by
  ext i
  simp [le_lastIdx]

omit [NeZero n] in
theorem sum_univ_eq_filter_lt_add_self_add_strictSuffix
    (f : Idx n → ℝ) (k : Idx n) :
    Finset.sum Finset.univ f =
      Finset.sum (Finset.univ.filter fun i : Idx n => i < k) f +
        f k + Finset.sum (strictSuffixRange k) f := by
  classical
  let ltRange : Finset (Idx n) := Finset.univ.filter fun i : Idx n => i < k
  have hrest :
      Finset.univ.filter (fun i : Idx n => ¬ i < k) = insert k (strictSuffixRange k) := by
    ext i
    constructor
    · intro hi
      by_cases hik : i = k
      · simp [hik]
      · have hlt_or_gt : i < k ∨ k < i := lt_or_gt_of_ne hik
        rcases hlt_or_gt with hlt | hgt
        · exact False.elim ((Finset.mem_filter.mp hi).2 hlt)
        · simp [hik, mem_strictSuffixRange.mpr hgt]
    · intro hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · simp
      · have hgt : k < i := mem_strictSuffixRange.mp hi'
        exact Finset.mem_filter.mpr ⟨by simp, not_lt.mpr (le_of_lt hgt)⟩
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun i : Idx n => i < k) f
  rw [hrest, Finset.sum_insert] at hsplit
  · simpa [ltRange, add_assoc, add_left_comm, add_comm] using hsplit.symm
  · simp

namespace ProfileData

variable {I : ProcedureInput n} {Γ : Advice I}

def groupColumnA (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) : ℝ :=
  I.program.Mcoeff * Finset.sum Finset.univ (fun i => C.gA AUX i j) +
    Finset.sum (suffixRange j) (fun i => C.sA AUX i j + C.tA AUX i j)

def groupColumnB (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) : ℝ :=
  I.program.Mcoeff * Finset.sum Finset.univ (fun i => C.gB AUX i j) +
    Finset.sum (suffixRange j) (fun i => C.sB AUX i j + C.tB AUX i j)

def groupColumnC (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) : ℝ :=
  I.program.Mcoeff * Finset.sum Finset.univ (fun i => C.gC AUX i j) +
    Finset.sum (suffixRange j) (fun i => C.sC AUX i j + C.tC AUX i j)

def groupColumnD (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) : ℝ :=
  I.program.Mcoeff * Finset.sum Finset.univ (fun i => C.gD AUX i j) +
    Finset.sum (suffixRange j) (fun i => C.sD AUX i j + C.tD AUX i j)

theorem sum_univ_gValue_eq_membership_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum Finset.univ (fun i => C.gValue AUX i j) =
      (C.memberships).muA j * Finset.sum Finset.univ (fun i => C.gA AUX i j) +
      (C.memberships).muB j * Finset.sum Finset.univ (fun i => C.gB AUX i j) +
      (C.memberships).muC j * Finset.sum Finset.univ (fun i => C.gC AUX i j) +
      (C.memberships).muD j * Finset.sum Finset.univ (fun i => C.gD AUX i j) := by
  calc
    Finset.sum Finset.univ (fun i => C.gValue AUX i j)
      = Finset.sum Finset.univ (fun i =>
          (C.memberships).muA j * C.gA AUX i j +
          (C.memberships).muB j * C.gB AUX i j +
          (C.memberships).muC j * C.gC AUX i j +
          (C.memberships).muD j * C.gD AUX i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [ProfileData.gValue]
    _ = (C.memberships).muA j * Finset.sum Finset.univ (fun i => C.gA AUX i j) +
          (C.memberships).muB j * Finset.sum Finset.univ (fun i => C.gB AUX i j) +
          (C.memberships).muC j * Finset.sum Finset.univ (fun i => C.gC AUX i j) +
          (C.memberships).muD j * Finset.sum Finset.univ (fun i => C.gD AUX i j) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

theorem sum_suffix_sValue_eq_membership_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum (suffixRange j) (fun i => C.sValue AUX i j) =
      (C.memberships).muA j * Finset.sum (suffixRange j) (fun i => C.sA AUX i j) +
      (C.memberships).muB j * Finset.sum (suffixRange j) (fun i => C.sB AUX i j) +
      (C.memberships).muC j * Finset.sum (suffixRange j) (fun i => C.sC AUX i j) +
      (C.memberships).muD j * Finset.sum (suffixRange j) (fun i => C.sD AUX i j) := by
  calc
    Finset.sum (suffixRange j) (fun i => C.sValue AUX i j)
      = Finset.sum (suffixRange j) (fun i =>
          (C.memberships).muA j * C.sA AUX i j +
          (C.memberships).muB j * C.sB AUX i j +
          (C.memberships).muC j * C.sC AUX i j +
          (C.memberships).muD j * C.sD AUX i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [ProfileData.sValue]
    _ = (C.memberships).muA j * Finset.sum (suffixRange j) (fun i => C.sA AUX i j) +
          (C.memberships).muB j * Finset.sum (suffixRange j) (fun i => C.sB AUX i j) +
          (C.memberships).muC j * Finset.sum (suffixRange j) (fun i => C.sC AUX i j) +
          (C.memberships).muD j * Finset.sum (suffixRange j) (fun i => C.sD AUX i j) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

theorem sum_suffix_tValue_eq_membership_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum (suffixRange j) (fun i => C.tValue AUX i j) =
      (C.memberships).muA j * Finset.sum (suffixRange j) (fun i => C.tA AUX i j) +
      (C.memberships).muB j * Finset.sum (suffixRange j) (fun i => C.tB AUX i j) +
      (C.memberships).muC j * Finset.sum (suffixRange j) (fun i => C.tC AUX i j) +
      (C.memberships).muD j * Finset.sum (suffixRange j) (fun i => C.tD AUX i j) := by
  calc
    Finset.sum (suffixRange j) (fun i => C.tValue AUX i j)
      = Finset.sum (suffixRange j) (fun i =>
          (C.memberships).muA j * C.tA AUX i j +
          (C.memberships).muB j * C.tB AUX i j +
          (C.memberships).muC j * C.tC AUX i j +
          (C.memberships).muD j * C.tD AUX i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [ProfileData.tValue]
    _ = (C.memberships).muA j * Finset.sum (suffixRange j) (fun i => C.tA AUX i j) +
          (C.memberships).muB j * Finset.sum (suffixRange j) (fun i => C.tB AUX i j) +
          (C.memberships).muC j * Finset.sum (suffixRange j) (fun i => C.tC AUX i j) +
          (C.memberships).muD j * Finset.sum (suffixRange j) (fun i => C.tD AUX i j) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

theorem sum_suffix_stValue_eq_membership_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum (suffixRange j) (fun i => C.sValue AUX i j + C.tValue AUX i j) =
      (C.memberships).muA j * Finset.sum (suffixRange j) (fun i => C.sA AUX i j + C.tA AUX i j) +
      (C.memberships).muB j * Finset.sum (suffixRange j) (fun i => C.sB AUX i j + C.tB AUX i j) +
      (C.memberships).muC j * Finset.sum (suffixRange j) (fun i => C.sC AUX i j + C.tC AUX i j) +
      (C.memberships).muD j *
        Finset.sum (suffixRange j) (fun i => C.sD AUX i j + C.tD AUX i j) := by
  have hA :
      Finset.sum (suffixRange j) (fun i => C.sA AUX i j + C.tA AUX i j) =
        Finset.sum (suffixRange j) (fun i => C.sA AUX i j) +
          Finset.sum (suffixRange j) (fun i => C.tA AUX i j) := by
    rw [Finset.sum_add_distrib]
  have hB :
      Finset.sum (suffixRange j) (fun i => C.sB AUX i j + C.tB AUX i j) =
        Finset.sum (suffixRange j) (fun i => C.sB AUX i j) +
          Finset.sum (suffixRange j) (fun i => C.tB AUX i j) := by
    rw [Finset.sum_add_distrib]
  have hC :
      Finset.sum (suffixRange j) (fun i => C.sC AUX i j + C.tC AUX i j) =
        Finset.sum (suffixRange j) (fun i => C.sC AUX i j) +
          Finset.sum (suffixRange j) (fun i => C.tC AUX i j) := by
    rw [Finset.sum_add_distrib]
  have hD :
      Finset.sum (suffixRange j) (fun i => C.sD AUX i j + C.tD AUX i j) =
        Finset.sum (suffixRange j) (fun i => C.sD AUX i j) +
          Finset.sum (suffixRange j) (fun i => C.tD AUX i j) := by
    rw [Finset.sum_add_distrib]
  rw [show (fun i => C.sValue AUX i j + C.tValue AUX i j) =
      (fun i => (C.sValue AUX i j) + C.tValue AUX i j) by
        funext i
        ring,
    Finset.sum_add_distrib, C.sum_suffix_sValue_eq_membership_combo AUX,
    C.sum_suffix_tValue_eq_membership_combo AUX, hA, hB, hC, hD]
  ring

theorem sum_univ_gA_eq_of_muA_pos
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hj : 0 < (C.memberships).muA j) :
    Finset.sum Finset.univ (fun i => C.gA AUX i j) =
      1 - I.program.epsilon *
        (1 -
          posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) / I.program.theta) := by
  have hdelta_support :
      Finset.sum Finset.univ (fun i => AUX.delta i j) =
        Finset.sum (deltaRange I Γ j) (fun i => AUX.delta i j) := by
    let s := deltaRange I Γ j
    have hs_subset : s ⊆ Finset.univ := by intro i hi; simp
    symm
    apply Finset.sum_subset hs_subset
    intro i hiUniv hiNot
    have hiNotMem : i ∉ deltaRange I Γ j := hiNot
    have hzero : AUX.delta i j = 0 := by
      by_cases hle : i ≤ I.firstBidTime j
      · exact AUX.delta_eq_zero i j hj hle
      · have hgt : I.firstBidTime j < i := lt_of_not_ge hle
        have hnotT3 : ¬ i ≤ Γ.t3Star := by
          intro hiT3
          exact hiNotMem (mem_deltaRange.mpr ⟨hgt, hiT3⟩)
        exact C.delta_eq_zero_of_t3_lt AUX hγlo hγhi hθpos hj (lt_of_not_ge hnotT3)
    simp [hzero]
  calc
    Finset.sum Finset.univ (fun i => C.gA AUX i j)
      = Finset.sum Finset.univ (fun i => C.hatG i - AUX.delta i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [ProfileData.gA]
    _ = Finset.sum Finset.univ C.hatG - Finset.sum Finset.univ (fun i => AUX.delta i j) := by
          rw [Finset.sum_sub_distrib]
    _ = totalBudget C.hatG - Finset.sum Finset.univ (fun i => AUX.delta i j) := by
          simp [totalBudget]
    _ = 1 - Finset.sum (deltaRange I Γ j) (fun i => AUX.delta i j) := by
          rw [C.total_eq_one, hdelta_support]
    _ = 1 - I.program.epsilon *
          (1 -
            posPart
                (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) / I.program.theta) := by
          rw [AUX.delta_sum_eq j hj]

theorem sum_univ_gB_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum Finset.univ (fun i => C.gB AUX i j) = 1 := by
  simpa [ProfileData.gB, totalBudget] using C.total_eq_one

theorem sum_univ_gC_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum Finset.univ (fun i => C.gC AUX i j) = 1 := by
  simpa [ProfileData.gC, totalBudget] using C.total_eq_one

theorem tailBudget_last (hatG : Idx n → ℝ) :
    tailBudget hatG (lastIdx n) = 0 := by
  unfold tailBudget
  apply Finset.sum_eq_zero
  intro i hi
  exact False.elim ((not_lt_of_ge (le_lastIdx i)) (mem_strictSuffixRange.mp hi))

theorem tailBudget_le_barTau_of_muB_pos
    (C : ProfileData I Γ) (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {j : Idx n} (hj : 0 < (C.memberships).muB j) :
    tailBudget C.hatG j ≤ I.program.barTau := by
  by_cases hjeq : j = C.t1
  · subst hjeq
    by_cases ht1 : C.t1 = lastIdx n
    · have hbar : 0 ≤ I.program.barTau := I.program.barTau_nonneg_of_le_153_div_125 hγlo hγhi
      simpa [ht1, tailBudget_last] using hbar
    · rw [C.tailBudget_eq_phaseTwo_afterBudget_at_t1]
      linarith [C.phaseTwo_afterBudget_t1_lt_barTau ht1]
  · by_cases hcond : C.t1 < j ∧ j ≤ C.t2
    · have ht1j : C.t1 < j := hcond.1
      rw [C.tailBudget_eq_phaseTwo_afterBudget_of_lt_t1 ht1j]
      have hafter_le_before : C.phaseTwo.afterBudget j ≤ C.phaseTwo.beforeBudget j := by
        have hbefore := C.phaseTwo.beforeBudget_eq_self_add_afterBudget j
        linarith [C.phaseTwo.hatG2_nonneg j]
      exact le_trans hafter_le_before (le_of_lt (C.phaseTwo_beforeBudget_lt_barTau_above_t1 ht1j))
    · have hzero : (C.memberships).muB j = 0 := by
        simp [ProfileData.memberships, hjeq, hcond]
      linarith

theorem sum_univ_gD_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (j : Idx n) :
    Finset.sum Finset.univ (fun i => C.gD AUX i j) = 1 - I.program.epsilon * C.chi j := by
  by_cases ht1 : C.t1 = lastIdx n
  · have ht2 : C.t2 = lastIdx n := by
      apply le_antisymm (le_lastIdx _)
      simpa [ht1] using C.t1_le_t2
    have hjt2 : j ≤ C.t2 := by
      simp [ht2]
    have hjt1 : j ≤ C.t1 := by
      simp [ht1]
    have hchi : C.chi j = 0 := C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos hjt2
    calc
      Finset.sum Finset.univ (fun i => C.gD AUX i j)
        = Finset.sum Finset.univ C.hatG := by
            apply Finset.sum_congr rfl
            intro i hi
            exact C.gD_eq_hatG_of_col_le_t1_of_chi_zero AUX hjt1 hchi
      _ = 1 := by simpa [totalBudget] using C.total_eq_one
      _ = 1 - I.program.epsilon * C.chi j := by simp [hchi]
  · let prefixRangeT1 : Finset (Idx n) := Finset.univ.filter fun i : Idx n => i < C.t1
    have hprefix_g :
        Finset.sum prefixRangeT1 (fun i => C.gD AUX i j) =
          Finset.sum prefixRangeT1 C.hatG -
            C.chi j * I.program.frac * Finset.sum prefixRangeT1 C.hatG := by
      calc
        Finset.sum prefixRangeT1 (fun i => C.gD AUX i j)
          = Finset.sum prefixRangeT1
              (fun i => C.hatG i - C.chi j * I.program.frac * C.hatG i) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hit1 : i < C.t1 := (Finset.mem_filter.mp hi).2
                simp [ProfileData.gD, hit1]
        _ = Finset.sum prefixRangeT1 C.hatG -
              Finset.sum prefixRangeT1 (fun i => C.chi j * I.program.frac * C.hatG i) := by
                rw [Finset.sum_sub_distrib]
        _ = Finset.sum prefixRangeT1 C.hatG -
              C.chi j * I.program.frac * Finset.sum prefixRangeT1 C.hatG := by
                rw [← Finset.mul_sum]
    have hstrict_g :
        Finset.sum (strictSuffixRange C.t1) (fun i => C.gD AUX i j) =
          tailBudget C.hatG C.t1 := by
      calc
        Finset.sum (strictSuffixRange C.t1) (fun i => C.gD AUX i j)
          = Finset.sum (strictSuffixRange C.t1) C.hatG := by
              apply Finset.sum_congr rfl
              intro i hi
              have ht1i : C.t1 < i := mem_strictSuffixRange.mp hi
              have hnot : ¬ i < C.t1 := not_lt.mpr (le_of_lt ht1i)
              simp [ProfileData.gD, hnot, ne_of_gt ht1i]
        _ = tailBudget C.hatG C.t1 := rfl
    have hprefix :
        Finset.sum prefixRangeT1 C.hatG = 1 - C.hatG C.t1 - tailBudget C.hatG C.t1 := by
      have hsplit := sum_univ_eq_filter_lt_add_self_add_strictSuffix (f := C.hatG) C.t1
      have htotal : Finset.sum Finset.univ C.hatG = 1 := by
        simpa [totalBudget] using C.total_eq_one
      have htail : Finset.sum (strictSuffixRange C.t1) C.hatG = tailBudget C.hatG C.t1 := rfl
      rw [htotal, htail] at hsplit
      linarith
    have hprefix_tau :
        Finset.sum prefixRangeT1 C.hatG + C.boundaryHatGA = I.program.tau := by
      have htail :
          tailBudget C.hatG C.t1 + I.program.tau + C.boundaryHatGB = 1 :=
        C.tailBudget_add_tau_add_boundaryHatGB_eq_one_of_ne_last ht1
      have hbound : C.hatG C.t1 = C.boundaryHatGA + C.boundaryHatGB := C.boundary_eq
      linarith [hprefix, htail, hbound]
    have hboundary :
        C.gD AUX C.t1 j = C.hatG C.t1 - C.chi j * I.program.frac * C.boundaryHatGA := by
      simp [ProfileData.gD]
    calc
      Finset.sum Finset.univ (fun i => C.gD AUX i j)
        = Finset.sum prefixRangeT1 (fun i => C.gD AUX i j) +
            C.gD AUX C.t1 j + Finset.sum (strictSuffixRange C.t1) (fun i => C.gD AUX i j) := by
              simpa [prefixRangeT1] using
                (sum_univ_eq_filter_lt_add_self_add_strictSuffix
                  (f := fun i => C.gD AUX i j) C.t1)
      _ = (Finset.sum prefixRangeT1 C.hatG -
              C.chi j * I.program.frac * Finset.sum prefixRangeT1 C.hatG) +
            (C.hatG C.t1 - C.chi j * I.program.frac * C.boundaryHatGA) +
            tailBudget C.hatG C.t1 := by
              rw [hprefix_g, hboundary, hstrict_g]
      _ = 1 - C.chi j * I.program.frac *
            (Finset.sum prefixRangeT1 C.hatG + C.boundaryHatGA) := by
              rw [C.boundary_eq, hprefix]
              nlinarith [C.boundary_eq]
      _ = 1 - C.chi j * I.program.frac * I.program.tau := by rw [hprefix_tau]
      _ = 1 - I.program.epsilon * C.chi j := by
            rw [mul_assoc, I.program.frac_mul_tau_eq_epsilon_of_theta_pos hγlo hθpos]
            ring

theorem sum_suffix_sA_add_tA_eq_of_muA_pos
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j : Idx n}
    (hj : 0 < (C.memberships).muA j) :
    Finset.sum (suffixRange j) (fun i => C.sA AUX i j + C.tA AUX i j) =
      beforeBudget C.hatG j -
        posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) := by
  have hji : j ≤ lastIdx n := le_lastIdx j
  have hif : I.firstBidTime j ≤ lastIdx n := le_lastIdx (I.firstBidTime j)
  rw [suffixRange_eq_interval_last]
  rw [show (fun i => C.sA AUX i j + C.tA AUX i j) = (fun i => C.sA AUX i j) by
        funext i
        simp [ProfileData.tA]]
  rw [C.sum_interval_sA_eq_after_firstBid AUX hj hji hif, tailBudget_last]
  ring

theorem sum_suffix_sB_add_tB_le_oneMinusTheta_of_muB_pos
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {j : Idx n} (hj : 0 < (C.memberships).muB j) :
    Finset.sum (suffixRange j) (fun i => C.sB AUX i j + C.tB AUX i j) ≤
      I.program.oneMinusTheta := by
  have hji : j ≤ lastIdx n := le_lastIdx j
  have hif : I.firstBidTime j ≤ lastIdx n := le_lastIdx (I.firstBidTime j)
  have htail_le : tailBudget C.hatG j ≤ I.program.barTau :=
    C.tailBudget_le_barTau_of_muB_pos hγlo hγhi hj
  have hεnonneg : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hhatnonneg := C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hind_le :
      (if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) ≤ I.program.epsilon := by
    by_cases hlt : I.firstBidTime j < lastIdx n
    · simp [hlt]
    · simp [hlt, hεnonneg]
  rw [suffixRange_eq_interval_last, Finset.sum_add_distrib,
    C.sum_interval_sB_eq AUX hji, C.sum_interval_tB_eq AUX, if_pos hif, tailBudget_last]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  have hone :
      I.program.epsilon + I.program.barTau = I.program.oneMinusTheta :=
    I.program.epsilon_add_barTau_eq_oneMinusTheta
  have hbar :
      1 - beforeBudget C.hatG j - I.program.tau =
        I.program.barTau - beforeBudget C.hatG j := by
    rw [DualProgram.barTau]
    ring
  rw [hbar, hbefore]
  by_cases hpos : 0 ≤ I.program.barTau - beforeBudget C.hatG j
  · have hpos' : 0 ≤ I.program.barTau - (C.hatG j + tailBudget C.hatG j) := by
      simpa [hbefore] using hpos
    rw [posPart_of_nonneg hpos']
    have hEq :
        (tailBudget C.hatG j - 0 + if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) +
            (I.program.barTau - (C.hatG j + tailBudget C.hatG j)) =
          (if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) +
            I.program.barTau - C.hatG j := by
              ring
    rw [hEq]
    linarith [hind_le, hone, hhatnonneg j]
  · have hnonpos' : I.program.barTau - (C.hatG j + tailBudget C.hatG j) ≤ 0 := by
      simpa [hbefore] using (le_of_not_ge hpos)
    rw [posPart_of_nonpos hnonpos']
    have hEq :
        (tailBudget C.hatG j - 0 + if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) +
            0 =
          tailBudget C.hatG j +
            (if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) := by
              ring
    rw [hEq]
    linarith [hind_le, hone, htail_le]

theorem sum_suffix_sC_add_tC_le_oneMinusTheta
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (j : Idx n) :
    Finset.sum (suffixRange j) (fun i => C.sC AUX i j + C.tC AUX i j) ≤
      I.program.oneMinusTheta := by
  have hji : j ≤ lastIdx n := le_lastIdx j
  have hif : I.firstBidTime j ≤ lastIdx n := le_lastIdx (I.firstBidTime j)
  have hεnonneg : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hind_le :
      (if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) ≤ I.program.epsilon := by
    by_cases hlt : I.firstBidTime j < lastIdx n
    · simp [hlt]
    · simp [hlt, hεnonneg]
  have hhatnonneg := C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  rw [suffixRange_eq_interval_last, Finset.sum_add_distrib,
    C.sum_interval_sC_eq AUX hji, C.sum_interval_tC_eq AUX, if_pos hif, tailBudget_last]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  have hone :
      I.program.epsilon + (1 - I.program.tau) = I.program.oneMinusTheta := by
    simpa [DualProgram.barTau] using I.program.epsilon_add_barTau_eq_oneMinusTheta
  rw [hbefore]
  have hEq :
      (tailBudget C.hatG j - 0 + if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) +
          (1 - (C.hatG j + tailBudget C.hatG j) - I.program.tau) =
        (if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) +
          (1 - I.program.tau) - C.hatG j := by
            ring
  rw [hEq]
  linarith [hind_le, hone, hhatnonneg j]

theorem sum_suffix_sD_add_tD_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum (suffixRange j) (fun i => C.sD AUX i j + C.tD AUX i j) =
      1 - beforeBudget C.hatG j := by
  have hji : j ≤ lastIdx n := le_lastIdx j
  have hif : I.firstBidTime j ≤ lastIdx n := le_lastIdx (I.firstBidTime j)
  rw [suffixRange_eq_interval_last, Finset.sum_add_distrib,
    C.sum_interval_sD_eq AUX, C.sum_interval_tD_eq AUX, if_pos hif]
  simp

theorem theta_le_before_add_theta_mul_chi
    (C : ProfileData I Γ) (hθpos : 0 < I.program.theta) (j : Idx n) :
    I.program.theta ≤ beforeBudget C.hatG j + I.program.theta * C.chi j := by
  by_cases hinner : 1 - beforeBudget C.hatG j / I.program.theta ≤ 0
  · have hchi : C.chi j = 0 := by
      simp [ProfileData.chi, hinner]
    have hbefore_ge : I.program.theta ≤ beforeBudget C.hatG j := by
      have hdiv : beforeBudget C.hatG j / I.program.theta ≥ 1 := by linarith
      have hmult := (le_div_iff₀ hθpos).mp hdiv
      simpa using hmult
    simpa [hchi] using hbefore_ge
  · have hpos : 0 ≤ 1 - beforeBudget C.hatG j / I.program.theta := by linarith
    have hchi : C.chi j = 1 - beforeBudget C.hatG j / I.program.theta := by
      simp [ProfileData.chi, hpos]
    have hEq :
        beforeBudget C.hatG j + I.program.theta * C.chi j = I.program.theta := by
      rw [hchi]
      field_simp [ne_of_gt hθpos]
      ring
    rw [hEq]

theorem groupColumnA_le_rho_of_muA_pos
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hj : 0 < (C.memberships).muA j) :
    C.groupColumnA AUX j ≤ I.program.rhoBound := by
  unfold ProfileData.groupColumnA
  rw [C.sum_univ_gA_eq_of_muA_pos AUX hγlo hγhi hθpos hj,
    C.sum_suffix_sA_add_tA_eq_of_muA_pos AUX hj]
  let p : ℝ := posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j))
  have hp :
      I.program.Mcoeff * (I.program.epsilon * (1 - p / I.program.theta)) =
        I.program.theta - p := by
    calc
      I.program.Mcoeff * (I.program.epsilon * (1 - p / I.program.theta))
        = (I.program.Mcoeff * I.program.epsilon) * (1 - p / I.program.theta) := by ring
      _ = I.program.theta * (1 - p / I.program.theta) := by
            rw [I.program.gamma_mul_epsilon_eq_theta]
      _ = I.program.theta - p := by
            field_simp [ne_of_gt hθpos]
            
  have hhatnonneg := C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hbefore_le : beforeBudget C.hatG j ≤ 1 :=
    beforeBudget_le_one_of_nonneg_of_total_eq_one hhatnonneg C.total_eq_one j
  have hrho : I.program.Mcoeff + 1 - I.program.theta = I.program.rhoBound :=
    I.program.gamma_add_one_sub_theta_eq_rho
  rw [show posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) = p by rfl]
  linarith

theorem groupColumnB_le_rho_of_muB_pos
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {j : Idx n} (hj : 0 < (C.memberships).muB j) :
    C.groupColumnB AUX j ≤ I.program.rhoBound := by
  unfold ProfileData.groupColumnB
  rw [C.sum_univ_gB_eq AUX j]
  have htran := C.sum_suffix_sB_add_tB_le_oneMinusTheta_of_muB_pos AUX hΓ hγlo hγhi hj
  have hrho : I.program.Mcoeff + I.program.oneMinusTheta = I.program.rhoBound :=
    I.program.gamma_add_oneMinusTheta_eq_rho
  linarith

theorem groupColumnC_le_rho
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (j : Idx n) :
    C.groupColumnC AUX j ≤ I.program.rhoBound := by
  unfold ProfileData.groupColumnC
  rw [C.sum_univ_gC_eq AUX j]
  have htran := C.sum_suffix_sC_add_tC_le_oneMinusTheta AUX hΓ hγlo hγhi j
  have hrho : I.program.Mcoeff + I.program.oneMinusTheta = I.program.rhoBound :=
    I.program.gamma_add_oneMinusTheta_eq_rho
  linarith

theorem groupColumnD_le_rho
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (j : Idx n) :
    C.groupColumnD AUX j ≤ I.program.rhoBound := by
  unfold ProfileData.groupColumnD
  rw [C.sum_univ_gD_eq AUX hΓ hγlo hγhi hθpos j, C.sum_suffix_sD_add_tD_eq AUX j]
  have hmain := C.theta_le_before_add_theta_mul_chi hθpos j
  have hrho : I.program.Mcoeff + 1 - I.program.theta = I.program.rhoBound :=
    I.program.gamma_add_one_sub_theta_eq_rho
  calc
    I.program.Mcoeff * (1 - I.program.epsilon * C.chi j) + (1 - beforeBudget C.hatG j)
      = I.program.Mcoeff + 1 -
          (beforeBudget C.hatG j + (I.program.Mcoeff * I.program.epsilon) * C.chi j) := by
            ring
    _ = I.program.Mcoeff + 1 -
          (beforeBudget C.hatG j + I.program.theta * C.chi j) := by
            rw [I.program.gamma_mul_epsilon_eq_theta]
    _ ≤ I.program.Mcoeff + 1 - I.program.theta := by
          linarith
    _ = I.program.rhoBound := hrho

theorem constructedDualSolution_columnValue_le_membership_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (j : Idx n) :
    DualSolution.columnValue (C.constructedDualSolution AUX) I.program j ≤
      (C.memberships).muA j * C.groupColumnA AUX j +
      (C.memberships).muB j * C.groupColumnB AUX j +
      (C.memberships).muC j * C.groupColumnC AUX j +
      (C.memberships).muD j * C.groupColumnD AUX j := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  have hs :
      Finset.sum (strictSuffixRange j) (fun i => C.shiftedSValue AUX i j) ≤
        Finset.sum (suffixRange j) (fun i => C.sValue AUX i j) :=
    C.sum_strictSuffix_shiftedSValue_le H AUX j
  simp only [DualSolution.columnValue, constructedDualSolution_g, constructedDualSolution_s,
    constructedDualSolution_t, memberships_muD]
  calc
    I.program.Mcoeff * ∑ x, C.gValue AUX x j +
        ∑ x ∈ strictSuffixRange j, C.shiftedSValue AUX x j +
        ∑ x ∈ suffixRange j, C.tValue AUX x j
      ≤ I.program.Mcoeff * ∑ x, C.gValue AUX x j + ∑ x ∈ suffixRange j, C.sValue AUX x j +
          ∑ x ∈ suffixRange j, C.tValue AUX x j := by
            linarith
    _ = I.program.Mcoeff * ∑ x, C.gValue AUX x j +
          ∑ x ∈ suffixRange j, (C.sValue AUX x j + C.tValue AUX x j) := by
            rw [Finset.sum_add_distrib]
            ring
    _ = (C.memberships).muA j * C.groupColumnA AUX j +
          (C.memberships).muB j * C.groupColumnB AUX j +
          (C.memberships).muC j * C.groupColumnC AUX j +
          (C.memberships).muD j * C.groupColumnD AUX j := by
            rw [C.sum_univ_gValue_eq_membership_combo AUX j,
              C.sum_suffix_stValue_eq_membership_combo AUX j]
            unfold ProfileData.groupColumnA ProfileData.groupColumnB
              ProfileData.groupColumnC ProfileData.groupColumnD
            ring

theorem weighted_groupColumnA_le_rho
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (j : Idx n) :
    (C.memberships).muA j * C.groupColumnA AUX j ≤
      (C.memberships).muA j * I.program.rhoBound := by
  have hnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  by_cases hμ : 0 < (C.memberships).muA j
  · exact mul_le_mul_of_nonneg_left
      (C.groupColumnA_le_rho_of_muA_pos AUX hΓ hγlo hγhi hθpos hμ) (hnonneg.1 j)
  · have hμzero : (C.memberships).muA j = 0 := by
      linarith [hnonneg.1 j]
    simp [hμzero]

theorem weighted_groupColumnB_le_rho
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (j : Idx n) :
    (C.memberships).muB j * C.groupColumnB AUX j ≤
      (C.memberships).muB j * I.program.rhoBound := by
  have hnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  by_cases hμ : 0 < (C.memberships).muB j
  · exact mul_le_mul_of_nonneg_left
      (C.groupColumnB_le_rho_of_muB_pos AUX hΓ hγlo hγhi hμ) (hnonneg.2.1 j)
  · have hμzero : (C.memberships).muB j = 0 := by
      linarith [hnonneg.2.1 j]
    simp [hμzero]

theorem weighted_groupColumnC_le_rho
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (j : Idx n) :
    (C.memberships).muC j * C.groupColumnC AUX j ≤
      (C.memberships).muC j * I.program.rhoBound := by
  have hnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  exact mul_le_mul_of_nonneg_left
    (C.groupColumnC_le_rho AUX hΓ hγlo hγhi j) (hnonneg.2.2.1 j)

theorem weighted_groupColumnD_le_rho
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (j : Idx n) :
    (C.memberships).muD j * C.groupColumnD AUX j ≤
      (C.memberships).muD j * I.program.rhoBound := by
  have hnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  exact mul_le_mul_of_nonneg_left
    (C.groupColumnD_le_rho AUX hΓ hγlo hγhi hθpos j) (hnonneg.2.2.2 j)

theorem constructedDualSolution_columnValue_le_groupColumn_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (j : Idx n) :
    DualSolution.columnValue (C.constructedDualSolution AUX) I.program j ≤
      (C.memberships).muA j * C.groupColumnA AUX j +
      (C.memberships).muB j * C.groupColumnB AUX j +
      (C.memberships).muC j * C.groupColumnC AUX j +
      (C.memberships).muD j * C.groupColumnD AUX j :=
  C.constructedDualSolution_columnValue_le_membership_combo AUX hΓ hγlo hγhi j

theorem constructedDualSolution_satisfiesValueConstraints
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    DualSolution.SatisfiesValueConstraints (C.constructedDualSolution AUX) I.program := by
  intro j
  rw [C.constructedDualSolution_rho AUX]
  have hcol :
      DualSolution.columnValue (C.constructedDualSolution AUX) I.program j ≤
        (C.memberships).muA j * C.groupColumnA AUX j +
          (C.memberships).muB j * C.groupColumnB AUX j +
          (C.memberships).muC j * C.groupColumnC AUX j +
          (C.memberships).muD j * C.groupColumnD AUX j :=
    C.constructedDualSolution_columnValue_le_groupColumn_combo AUX hΓ hγlo hγhi j
  have hA := C.weighted_groupColumnA_le_rho AUX hΓ hγlo hγhi hθpos j
  have hB := C.weighted_groupColumnB_le_rho AUX hΓ hγlo hγhi j
  have hC := C.weighted_groupColumnC_le_rho AUX hΓ hγlo hγhi j
  have hD := C.weighted_groupColumnD_le_rho AUX hΓ hγlo hγhi hθpos j
  have htot : (C.memberships).total j = 1 := C.memberships_total j
  unfold MembershipWeights.total at htot
  have hrho_combo :
      (C.memberships).muA j * I.program.rhoBound +
        (C.memberships).muB j * I.program.rhoBound +
        (C.memberships).muC j * I.program.rhoBound +
        (C.memberships).muD j * I.program.rhoBound = I.program.rhoBound := by
    calc
      (C.memberships).muA j * I.program.rhoBound +
          (C.memberships).muB j * I.program.rhoBound +
          (C.memberships).muC j * I.program.rhoBound +
          (C.memberships).muD j * I.program.rhoBound
        = ((C.memberships).muA j + (C.memberships).muB j +
            (C.memberships).muC j + (C.memberships).muD j) * I.program.rhoBound := by
              ring
      _ = 1 * I.program.rhoBound := by rw [htot]
      _ = I.program.rhoBound := by ring
  calc
    I.program.rhoBound =
        (C.memberships).muA j * I.program.rhoBound +
          (C.memberships).muB j * I.program.rhoBound +
          (C.memberships).muC j * I.program.rhoBound +
          (C.memberships).muD j * I.program.rhoBound := by
            symm
            exact hrho_combo
    _ ≥ (C.memberships).muA j * C.groupColumnA AUX j +
          (C.memberships).muB j * C.groupColumnB AUX j +
          (C.memberships).muC j * C.groupColumnC AUX j +
          (C.memberships).muD j * C.groupColumnD AUX j := by
            linarith
    _ ≥ DualSolution.columnValue (C.constructedDualSolution AUX) I.program j := by
            linarith

end ProfileData

end

end KMedian195


