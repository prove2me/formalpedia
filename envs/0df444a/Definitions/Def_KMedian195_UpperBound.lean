-- Prove2me | Definitions.Def_KMedian195_UpperBound
-- name    : KMedian195_UpperBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:17.438217+00:00
-- url     : https://prove2.me/theorems/eab13934-0fc3-4489-bd3b-db754f7222ba
-- title:
--   KMedian195.UpperBound
-- statement:
--   This is module `KMedian195.UpperBound` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 51 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_UpperBound`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/UpperBound.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/UpperBound.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`), and:
* In `auxiliaryCorrections_nonempty`, two `simpa [_, hj] using e` are
  `simp only [hj, ↓reduceDIte]; exact e`: our `simp` also rewrites inside the `Classical.choose`
  in the type of `e`, after which the two no longer match.
* In `trivialSingletonSolution_feasible`, `Finset.filter_singleton` is added to a `simpa`.
* In `familyUpperBound_of_restrictedSuccessfulFamilyFromTwo`, `let` instead of `letI` for a
  `NeZero` instance (linter).
-/
module

public import Definitions.Def_KMedian195_Feasibility
public import Definitions.Def_KMedian195_GoodAdvice

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.UpperBound` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

noncomputable section

variable {n : ℕ}

namespace BiddingMatrix

theorem coeff_le_one (b : BiddingMatrix n) (i j : Idx n) : b.coeff i j ≤ 1 := by
  by_cases h : b i j = true
  · simp [BiddingMatrix.coeff, h]
  · simp [BiddingMatrix.coeff, h]

variable [NeZero n]

/-- Strengthen a bidding pattern by forcing the last row to be all ones. -/
def forceFinalRowOne (b : BiddingMatrix n) : BiddingMatrix n where
  toFun i j := if i = lastIdx n then true else b i j
  upper_zero := by
    intro i j hij
    by_cases hi : i = lastIdx n
    · exfalso
      exact (not_lt_of_ge (le_lastIdx j)) (by simpa [hi] using hij)
    · simp [hi, b.upper_zero hij]

@[simp] theorem forceFinalRowOne_apply_lastIdx (b : BiddingMatrix n) (j : Idx n) :
    b.forceFinalRowOne (lastIdx n) j = true := by
  simp [BiddingMatrix.forceFinalRowOne]

@[simp] theorem forceFinalRowOne_apply_of_ne_last (b : BiddingMatrix n)
    {i j : Idx n} (hi : i ≠ lastIdx n) :
    b.forceFinalRowOne i j = b i j := by
  simp [BiddingMatrix.forceFinalRowOne, hi]

end BiddingMatrix

namespace DualProgram

variable [NeZero n]

/-- The inner program with the last bidding row strengthened to all ones. -/
def forceFinalRowOne (P : DualProgram n) : DualProgram n where
  Mcoeff := P.Mcoeff
  bidding := P.bidding.forceFinalRowOne

@[simp] theorem forceFinalRowOne_bid_lastIdx (P : DualProgram n) (j : Idx n) :
    (P.forceFinalRowOne).bid (lastIdx n) j = 1 := by
  simp [DualProgram.forceFinalRowOne, DualProgram.bid, BiddingMatrix.coeff]

@[simp] theorem forceFinalRowOne_bid_of_ne_last (P : DualProgram n)
    {i j : Idx n} (hi : i ≠ lastIdx n) :
    (P.forceFinalRowOne).bid i j = P.bid i j := by
  simp [DualProgram.forceFinalRowOne, DualProgram.bid, BiddingMatrix.coeff, hi]

theorem bid_le_forceFinalRowOne_bid (P : DualProgram n) (i j : Idx n) :
    P.bid i j ≤ (P.forceFinalRowOne).bid i j := by
  by_cases hi : i = lastIdx n
  · subst hi
    calc
      P.bid (lastIdx n) j ≤ 1 := P.bid_le_one _ _
      _ = (P.forceFinalRowOne).bid (lastIdx n) j := by
        rw [P.forceFinalRowOne_bid_lastIdx]
  · simp [P.forceFinalRowOne_bid_of_ne_last hi]

theorem sum_halfOpen_bids_forceFinalRowOne_eq
    (P : DualProgram n) (j i : Idx n) :
    Finset.sum (halfOpenIntervalRange j i) (fun p => (P.forceFinalRowOne).bid p j) =
      Finset.sum (halfOpenIntervalRange j i) (fun p => P.bid p j) := by
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpi : p < i := (mem_halfOpenIntervalRange.mp hp).2
  have hpne : p ≠ lastIdx n := by
    intro hpLast
    exact (not_lt_of_ge (le_lastIdx i)) (by simpa [hpLast] using hpi)
  simp [P.forceFinalRowOne_bid_of_ne_last hpne]

omit [NeZero n] in
theorem theta_pos_of_one_lt_Mcoeff (P : DualProgram n) (hγ : 1 < P.Mcoeff) :
    0 < P.theta := by
  dsimp [DualProgram.theta, DualProgram.epsilon, DualProgram.Mcoeffmone]
  nlinarith

end DualProgram

namespace ProcedureInput

variable [NeZero n]

/-- The restricted input used in the paper after forcing `b_{n,j} = 1`. -/
def forced (Mcoeff : ℝ) (bidding : BiddingMatrix n) : ProcedureInput n where
  program := ({ Mcoeff := Mcoeff, bidding := bidding } : DualProgram n).forceFinalRowOne
  final_bid_one := by
    intro j
    simp [DualProgram.forceFinalRowOne]

end ProcedureInput

section MassDistribution

variable {α : Type*}

theorem exists_bounded_sum_eq_of_nonneg_of_le_sum
    (s : Finset α) (cap : α → ℝ) (hcap_nonneg : ∀ a, 0 ≤ cap a)
    {target : ℝ} (htarget_nonneg : 0 ≤ target) (htarget_le : target ≤ Finset.sum s cap) :
    ∃ dist : α → ℝ,
      (∀ a, 0 ≤ dist a) ∧
      (∀ a, dist a ≤ cap a) ∧
      (∀ a, a ∉ s → dist a = 0) ∧
      Finset.sum s dist = target := by
  classical
  induction s using Finset.induction_on generalizing target with
  | empty =>
      have htarget_zero : target = 0 := by
        simpa using le_antisymm htarget_le htarget_nonneg
      refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
      · intro a
        simp
      · intro a
        simpa [htarget_zero] using hcap_nonneg a
      · intro a _
        simp
      · simp [htarget_zero]
  | @insert a s ha ih =>
      have hcapa : 0 ≤ cap a := hcap_nonneg a
      rw [Finset.sum_insert ha] at htarget_le
      by_cases htarget_a : target ≤ cap a
      · refine ⟨fun x => if x = a then target else 0, ?_, ?_, ?_, ?_⟩
        · intro x
          by_cases hx : x = a
          · simpa [hx] using htarget_nonneg
          · simp [hx]
        · intro x
          by_cases hx : x = a
          · simpa [hx] using htarget_a
          · simpa [hx] using hcap_nonneg x
        · intro x hx
          by_cases hx' : x = a
          · subst hx'
            exact False.elim (hx (by simp))
          · simp [hx']
        · rw [Finset.sum_insert ha]
          simp [ha]
      · have hcapa_lt : cap a < target := lt_of_not_ge htarget_a
        have hrest_nonneg : 0 ≤ target - cap a := by
          linarith
        have hrest_le : target - cap a ≤ Finset.sum s cap := by
          linarith
        obtain ⟨dist, hdist_nonneg, hdist_le, hdist_out, hdist_sum⟩ :=
          ih hrest_nonneg hrest_le
        refine ⟨fun x => if x = a then cap a else dist x, ?_, ?_, ?_, ?_⟩
        · intro x
          by_cases hx : x = a
          · simpa [hx] using hcapa
          · simpa [hx] using hdist_nonneg x
        · intro x
          by_cases hx : x = a
          · simp [hx]
          · simpa [hx] using hdist_le x
        · intro x hx
          by_cases hx' : x = a
          · subst hx'
            exact False.elim (hx (by simp))
          · simpa [hx'] using hdist_out x (by simpa [Finset.mem_insert, hx'] using hx)
        · rw [Finset.sum_insert ha]
          have hsum_eq :
              ∑ x ∈ s, (if x = a then cap a else dist x) = ∑ x ∈ s, dist x := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxa : x ≠ a := by
              intro hxa
              subst hxa
              exact ha hx
            simp [hxa]
          rw [hsum_eq, hdist_sum]
          simp

end MassDistribution

section Successful

/--
A successful advice choice for the specification-level construction:
an admissible advice together with witnesses for the profile and the auxiliary corrections.
-/
structure SuccessfulAdvice {n : ℕ} [NeZero n] (I : ProcedureInput n) (Γ : Advice I) where
  admissible : Γ.Admissible
  profile : ProfileData I Γ
  corrections : AuxiliaryCorrections profile

def SuccessfulInput {n : ℕ} [NeZero n] (I : ProcedureInput n) : Prop :=
  ∃ Γ, Nonempty (SuccessfulAdvice I Γ)

namespace SuccessfulAdvice

theorem hasValueAtMost {n : ℕ} [NeZero n] {I : ProcedureInput n} {Γ : Advice I}
    (h : SuccessfulAdvice I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    DualSolution.HasValueAtMost I.program I.program.rhoBound := by
  exact h.profile.constructedDualSolution_hasValueAtMost
    h.corrections h.admissible hγlo hγhi hθpos

end SuccessfulAdvice

theorem hasValueAtMost_of_successfulInput
    {n : ℕ} [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (hI : SuccessfulInput I) :
    DualSolution.HasValueAtMost I.program I.program.rhoBound := by
  rcases hI with ⟨Γ, ⟨hΓ⟩⟩
  exact SuccessfulAdvice.hasValueAtMost hΓ hγlo hγhi hθpos

end Successful

namespace ProfileData

variable {n : ℕ} [NeZero n] {I : ProcedureInput n} {Γ : Advice I}

def deltaTarget (C : ProfileData I Γ) (j : Idx n) : ℝ :=
  I.program.epsilon *
    (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) / I.program.theta)

def sigmaTarget (C : ProfileData I Γ) (j : Idx n) : ℝ :=
  posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j))

theorem muA_pos_le_t1
    (C : ProfileData I Γ) {j : Idx n} (hj : 0 < (C.memberships).muA j) :
    j ≤ C.t1 := by
  by_cases hjlt : j < C.t1
  · exact le_of_lt hjlt
  · by_cases hjeq : j = C.t1
    · exact le_of_eq hjeq
    · have hzero : (C.memberships).muA j = 0 := by
        simp [ProfileData.memberships, hjlt, hjeq]
      linarith

theorem firstBidTime_le_t3_of_muA_pos
    (C : ProfileData I Γ) {j : Idx n} (hj : 0 < (C.memberships).muA j) :
    I.firstBidTime j ≤ Γ.t3Star := by
  by_cases hfj : Γ.t3Star < I.firstBidTime j
  · have hmuD : Γ.muD j = 1 := Advice.muD_eq_one Γ hfj
    by_cases hjlt : j < C.t1
    · rw [C.memberships_muA_eq_of_lt_t1 hjlt, hmuD] at hj
      norm_num at hj
    · by_cases hjeq : j = C.t1
      · subst hjeq
        rw [C.memberships_muA_eq_at_t1, hmuD] at hj
        simp at hj
      · have hzero : (C.memberships).muA j = 0 := by
          simp [ProfileData.memberships, hjlt, hjeq]
        linarith
  · exact not_lt.mp hfj

theorem sum_deltaRange_hatG_eq_tailBudget_of_muA_pos
    (C : ProfileData I Γ) (_ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (_ : 0 < (C.memberships).muA j) :
    Finset.sum (deltaRange I Γ j) C.hatG = tailBudget C.hatG (I.firstBidTime j) := by
  have hsubset : deltaRange I Γ j ⊆ strictSuffixRange (I.firstBidTime j) := by
    intro i hi
    exact mem_strictSuffixRange.mpr (mem_deltaRange.mp hi).1
  have hsum :
      Finset.sum (strictSuffixRange (I.firstBidTime j)) C.hatG =
        Finset.sum (deltaRange I Γ j) C.hatG := by
    symm
    apply Finset.sum_subset hsubset
    intro i hiStrict hiNot
    have hit3 : Γ.t3Star < i := by
      by_cases hiT3 : i ≤ Γ.t3Star
      · exact False.elim (hiNot (mem_deltaRange.mpr ⟨mem_strictSuffixRange.mp hiStrict, hiT3⟩))
      · exact lt_of_not_ge hiT3
    exact C.hatG_eq_zero_of_t3_lt hγlo hγhi hθpos hit3
  simpa [tailBudget] using hsum.symm

theorem deltaTarget_nonneg
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    (j : Idx n) :
    0 ≤ C.deltaTarget j := by
  unfold ProfileData.deltaTarget
  let hhatG : ∀ i, 0 ≤ C.hatG i :=
    C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hε : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have htail : 0 ≤ tailBudget C.hatG (I.firstBidTime j) := tailBudget_nonneg_of_nonneg hhatG _
  have hquot_nonneg :
      0 ≤ posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) / I.program.theta := by
    exact div_nonneg (posPart_nonneg _) (le_of_lt hθpos)
  have hquot_le :
      posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) / I.program.theta ≤ 1 := by
    have hθ : 0 ≤ I.program.theta := I.program.theta_nonneg_of_one_le_Mcoeff hγlo
    have hposle :
        posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) ≤ I.program.theta :=
      posPart_sub_le_left htail hθ
    exact (div_le_iff₀ hθpos).2 (by simpa using hposle)
  have hfactor : 0 ≤ 1 -
      posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) / I.program.theta := by
    linarith
  exact mul_nonneg hε hfactor

theorem deltaTarget_le_tailBudget
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} :
    C.deltaTarget j ≤ tailBudget C.hatG (I.firstBidTime j) := by
  unfold ProfileData.deltaTarget
  let r := tailBudget C.hatG (I.firstBidTime j)
  have hε : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hεleθ : I.program.epsilon ≤ I.program.theta :=
    I.program.epsilon_le_theta_of_one_le_Mcoeff hγlo
  let hhatG : ∀ i, 0 ≤ C.hatG i :=
    C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hrnonneg : 0 ≤ r := by
    simpa [r] using tailBudget_nonneg_of_nonneg hhatG (I.firstBidTime j)
  by_cases hθr : I.program.theta ≤ r
  · have hpos : I.program.theta - r ≤ 0 := by
      linarith
    rw [posPart_of_nonpos hpos]
    have hεr : I.program.epsilon ≤ r := le_trans hεleθ hθr
    simpa [hθpos.ne'] using hεr
  · have hlt : r < I.program.theta := lt_of_not_ge hθr
    have hpos : 0 ≤ I.program.theta - r := by
      linarith
    have hθne : I.program.theta ≠ 0 := ne_of_gt hθpos
    rw [posPart_of_nonneg hpos]
    have hrewrite :
        1 - (I.program.theta - r) / I.program.theta = r / I.program.theta := by
      rw [sub_div]
      rw [div_self hθne]
      ring
    calc
      I.program.epsilon * (1 - (I.program.theta - r) / I.program.theta)
          = I.program.epsilon * (r / I.program.theta) := by rw [hrewrite]
      _ = (I.program.epsilon / I.program.theta) * r := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      _ ≤ 1 * r := by
            have hratio : I.program.epsilon / I.program.theta ≤ 1 := by
              exact (div_le_iff₀ hθpos).2 (by simpa using hεleθ)
            exact mul_le_mul_of_nonneg_right hratio hrnonneg
      _ = r := by ring

theorem deltaTarget_le_sum_deltaRange_hatG_of_muA_pos
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hj : 0 < (C.memberships).muA j) :
    C.deltaTarget j ≤ Finset.sum (deltaRange I Γ j) C.hatG := by
  rw [C.sum_deltaRange_hatG_eq_tailBudget_of_muA_pos hΓ hγlo hγhi hθpos hj]
  exact C.deltaTarget_le_tailBudget hΓ hγlo hγhi hθpos

theorem sigmaTarget_nonneg
    (C : ProfileData I Γ) (j : Idx n) :
    0 ≤ C.sigmaTarget j := by
  unfold ProfileData.sigmaTarget
  exact posPart_nonneg _

theorem beforeBudget_ge_theta_of_muA_pos
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {j : Idx n} (hj : 0 < (C.memberships).muA j) :
    I.program.theta ≤ beforeBudget C.hatG j := by
  let hhatG : ∀ i, 0 ≤ C.hatG i :=
    C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hjt1 : j ≤ C.t1 := C.muA_pos_le_t1 hj
  have hbar_t1 : I.program.barTau ≤ beforeBudget C.hatG C.t1 :=
    C.beforeBudget_t1_ge_barTau hΓ hγlo hγhi
  have hbar_j : I.program.barTau ≤ beforeBudget C.hatG j := by
    exact le_trans hbar_t1 (beforeBudget_antitone_of_nonneg hhatG hjt1)
  have hθbar : I.program.theta ≤ I.program.barTau :=
    I.program.theta_le_barTau_of_le_153_div_125 hγlo hγhi
  exact le_trans hθbar hbar_j

theorem sigmaTarget_le_sum_interval_hatG_of_muA_pos
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {j : Idx n} (hj : 0 < (C.memberships).muA j) :
    C.sigmaTarget j ≤ Finset.sum (intervalRange j (I.firstBidTime j)) C.hatG := by
  have hhatG : ∀ i, 0 ≤ C.hatG i :=
    C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hsum :
      Finset.sum (intervalRange j (I.firstBidTime j)) C.hatG =
        beforeBudget C.hatG j - tailBudget C.hatG (I.firstBidTime j) := by
    simpa using C.sum_interval_hatG_eq_before_sub_tail (I.le_firstBidTime j)
  have hcap_nonneg :
      0 ≤ beforeBudget C.hatG j - tailBudget C.hatG (I.firstBidTime j) := by
    rw [← hsum]
    exact Finset.sum_nonneg (fun i _ => hhatG i)
  have hbefore : I.program.theta ≤ beforeBudget C.hatG j :=
    C.beforeBudget_ge_theta_of_muA_pos hΓ hγlo hγhi hj
  have htail : 0 ≤ tailBudget C.hatG (I.firstBidTime j) :=
    tailBudget_nonneg_of_nonneg hhatG _
  unfold ProfileData.sigmaTarget
  by_cases hpos : 0 ≤ I.program.theta - tailBudget C.hatG (I.firstBidTime j)
  · rw [posPart_of_nonneg hpos]
    rw [hsum]
    linarith
  · rw [posPart_of_nonpos (le_of_not_ge hpos)]
    rw [hsum]
    exact hcap_nonneg

theorem auxiliaryCorrections_nonempty
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    Nonempty (AuxiliaryCorrections C) := by
  classical
  let hhatG : ∀ i, 0 ≤ C.hatG i :=
    C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hdelta_exists :
      ∀ j, 0 < (C.memberships).muA j →
        ∃ δj : Idx n → ℝ,
          (∀ i, 0 ≤ δj i) ∧
          (∀ i, δj i ≤ C.hatG i) ∧
          (∀ i, i ∉ deltaRange I Γ j → δj i = 0) ∧
          Finset.sum (deltaRange I Γ j) δj = C.deltaTarget j := by
    intro j hj
    exact exists_bounded_sum_eq_of_nonneg_of_le_sum
      (deltaRange I Γ j) C.hatG hhatG
      (C.deltaTarget_nonneg hΓ hγlo hγhi hθpos j)
      (C.deltaTarget_le_sum_deltaRange_hatG_of_muA_pos hΓ hγlo hγhi hθpos hj)
  have hsigma_exists :
      ∀ j, 0 < (C.memberships).muA j →
        ∃ σj : Idx n → ℝ,
          (∀ i, 0 ≤ σj i) ∧
          (∀ i, σj i ≤ C.hatG i) ∧
          (∀ i, i ∉ intervalRange j (I.firstBidTime j) → σj i = 0) ∧
          Finset.sum (intervalRange j (I.firstBidTime j)) σj = C.sigmaTarget j := by
    intro j hj
    exact exists_bounded_sum_eq_of_nonneg_of_le_sum
      (intervalRange j (I.firstBidTime j)) C.hatG hhatG
      (C.sigmaTarget_nonneg j)
      (C.sigmaTarget_le_sum_interval_hatG_of_muA_pos hΓ hγlo hγhi hj)
  refine ⟨{
    delta := fun i j =>
      if hj : 0 < (C.memberships).muA j then Classical.choose (hdelta_exists j hj) i else 0
    sigma := fun i j =>
      if hj : 0 < (C.memberships).muA j then Classical.choose (hsigma_exists j hj) i else 0
    delta_nonneg := ?_
    delta_le_hatG := ?_
    delta_eq_zero := ?_
    delta_sum_eq := ?_
    sigma_nonneg := ?_
    sigma_le_hatG := ?_
    sigma_eq_zero := ?_
    sigma_sum_eq := ?_
  }⟩
  · intro i j hj
    simpa [hj] using (Classical.choose_spec (hdelta_exists j hj)).1 i
  · intro i j hj
    simpa [hj] using (Classical.choose_spec (hdelta_exists j hj)).2.1 i
  · intro i j hj hij
    have hiNot : i ∉ deltaRange I Γ j := by
      intro hi
      exact (not_lt_of_ge hij) (mem_deltaRange.mp hi).1
    simpa [hj] using (Classical.choose_spec (hdelta_exists j hj)).2.2.1 i hiNot
  · intro j hj
    simp only [hj, ↓reduceDIte]
    exact (Classical.choose_spec (hdelta_exists j hj)).2.2.2
  · intro i j hj
    simpa [hj] using (Classical.choose_spec (hsigma_exists j hj)).1 i
  · intro i j hj
    simpa [hj] using (Classical.choose_spec (hsigma_exists j hj)).2.1 i
  · intro i j hj hij
    have hiNot : i ∉ intervalRange j (I.firstBidTime j) := by
      intro hi
      rcases mem_intervalRange.mp hi with ⟨hji, hif⟩
      cases hij with
      | inl hijlt =>
          exact (not_lt_of_ge hji hijlt).elim
      | inr hgt =>
          exact (not_lt_of_ge hif hgt).elim
    simpa [hj] using (Classical.choose_spec (hsigma_exists j hj)).2.2.1 i hiNot
  · intro j hj
    simp only [hj, ↓reduceDIte]
    exact (Classical.choose_spec (hsigma_exists j hj)).2.2.2

end ProfileData

theorem successfulInput_of_admissible_profile
    {n : ℕ} [NeZero n] {I : ProcedureInput n} {Γ : Advice I}
    (hΓ : Γ.Admissible) (C : ProfileData I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    SuccessfulInput I := by
  refine ⟨Γ, ⟨{
    admissible := hΓ
    profile := C
    corrections := Classical.choice (C.auxiliaryCorrections_nonempty hΓ hγlo hγhi hθpos)
  }⟩⟩

def RestrictedProfileFamilyFromTwo (Mcoeff : ℝ) : Prop :=
  ∀ n, ∀ _ : NeZero n, n ≠ 1 → ∀ bidding : BiddingMatrix n,
    ∃ Γ : Advice (ProcedureInput.forced Mcoeff bidding),
      Γ.Admissible ∧ Nonempty (ProfileData (ProcedureInput.forced Mcoeff bidding) Γ)

def RestrictedGoodAdvicePointwiseContinuityFamilyFromTwo (Mcoeff : ℝ) : Prop :=
  ∀ n, ∀ _ : NeZero n, n ≠ 1 → ∀ bidding : BiddingMatrix n,
    let I : ProcedureInput n := ProcedureInput.forced Mcoeff bidding
    ∃ P : SectionRawOutputPath n I,
      P.EndpointCompatible ∧
      (∀ ℓ, ∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 →
        ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam) ∧
      P.firstOutput.R0 ≤ 1 ∧
      1 ≤ P.lastOutput.R0

namespace DualSolution

theorem hasValueAtMost_mono
    {P : DualProgram n} {bound₁ bound₂ : ℝ}
    (h : HasValueAtMost P bound₁) (hbound : bound₁ ≤ bound₂) :
    HasValueAtMost P bound₂ := by
  rcases h with ⟨x, hx, hρ⟩
  exact ⟨x, hx, le_trans hρ hbound⟩

variable [NeZero n]

theorem satisfiesClientConstraints_of_forceFinalRowOne
    {x : DualSolution n} {P : DualProgram n}
    (hx : x.SatisfiesClientConstraints P.forceFinalRowOne) :
    x.SatisfiesClientConstraints P := by
  intro j i hji
  have hxji := hx hji
  rw [P.sum_halfOpen_bids_forceFinalRowOne_eq j i] at hxji
  have hxji' :
      x.clientCredit i j ≥
        (P.forceFinalRowOne).bid i j -
          P.Mcoeffmone * Finset.sum (halfOpenIntervalRange j i) (fun p => P.bid p j) := by
    simpa [DualProgram.forceFinalRowOne, DualProgram.Mcoeffmone] using hxji
  have hrhs :
      (P.forceFinalRowOne).bid i j -
          P.Mcoeffmone * Finset.sum (halfOpenIntervalRange j i) (fun p => P.bid p j) ≥
        P.bid i j -
          P.Mcoeffmone * Finset.sum (halfOpenIntervalRange j i) (fun p => P.bid p j) := by
    have hbid : P.bid i j ≤ (P.forceFinalRowOne).bid i j := P.bid_le_forceFinalRowOne_bid i j
    linarith
  exact ge_trans hxji' hrhs

theorem satisfiesValueConstraints_of_forceFinalRowOne
    {x : DualSolution n} {P : DualProgram n}
    (hx : x.SatisfiesValueConstraints P.forceFinalRowOne) :
    x.SatisfiesValueConstraints P := by
  intro j
  simpa [DualSolution.columnValue, DualProgram.forceFinalRowOne] using hx j

theorem feasible_of_forceFinalRowOne
    {x : DualSolution n} {P : DualProgram n}
    (hx : x.Feasible P.forceFinalRowOne) :
    x.Feasible P := by
  rcases hx with ⟨hHat, hDom, hClient, hPool, hValue, hNonneg⟩
  exact ⟨hHat, hDom, x.satisfiesClientConstraints_of_forceFinalRowOne hClient,
    hPool, x.satisfiesValueConstraints_of_forceFinalRowOne hValue, hNonneg⟩

theorem hasValueAtMost_of_forceFinalRowOne
    {P : DualProgram n} {bound : ℝ}
    (h : HasValueAtMost P.forceFinalRowOne bound) :
    HasValueAtMost P bound := by
  rcases h with ⟨x, hx, hρ⟩
  exact ⟨x, x.feasible_of_forceFinalRowOne hx, hρ⟩

end DualSolution

def trivialSingletonSolution (Mcoeff : ℝ) : DualSolution 1 where
  rho := Mcoeff
  hatG := fun _ => 1
  g := fun _ _ => 1
  s := fun _ _ => 0
  t := fun _ _ => 0

theorem trivialSingletonSolution_feasible (P : DualProgram 1) :
    (trivialSingletonSolution P.Mcoeff).Feasible P := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [DualSolution.BoundedHatG, DualSolution.totalHatG, trivialSingletonSolution]
  · intro i j
    fin_cases i
    fin_cases j
    simp [trivialSingletonSolution]
  · intro j i hji
    fin_cases j
    fin_cases i
    simpa [DualSolution.clientCredit, DualSolution.strictS, strictSuffixRange, intervalRange,
      halfOpenIntervalRange, trivialSingletonSolution, DualProgram.Mcoeffmone, ge_iff_le,
      Finset.filter_singleton] using
      P.bid_le_one 0 0
  · intro i
    fin_cases i
    simp [DualSolution.poolCredit, DualSolution.strictS, trivialSingletonSolution]
  · intro j
    fin_cases j
    simp [DualSolution.columnValue, trivialSingletonSolution]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      simp [trivialSingletonSolution]
    · intro i j
      fin_cases i
      fin_cases j
      simp [trivialSingletonSolution]
    · intro i j
      fin_cases i
      fin_cases j
      simp [trivialSingletonSolution]
    · intro i j
      fin_cases i
      fin_cases j
      simp [trivialSingletonSolution]

theorem hasValueAtMost_singleton
    (P : DualProgram 1) {bound : ℝ} (hbound : P.Mcoeff ≤ bound) :
    DualSolution.HasValueAtMost P bound := by
  exact ⟨trivialSingletonSolution P.Mcoeff, trivialSingletonSolution_feasible P, hbound⟩

/--
Successful-advice existence for the restricted family of inputs used in the paper:
all inner programs after forcing `b_{n,j} = 1`, and only for sizes `n ≥ 2`.
-/
def RestrictedSuccessfulFamilyFromTwo (Mcoeff : ℝ) : Prop :=
  ∀ n, ∀ _ : NeZero n, n ≠ 1 → ∀ bidding : BiddingMatrix n,
    SuccessfulInput (ProcedureInput.forced Mcoeff bidding)

theorem familyUpperBound_of_restrictedSuccessfulFamilyFromTwo
    {Mcoeff bound : ℝ}
    (hγlo : 1 < Mcoeff)
    (hγhi : Mcoeff ≤ (153 : ℝ) / 125)
    (hMbound : Mcoeff ≤ bound)
    (hρbound : 2 - (Mcoeff - 1) ^ 2 ≤ bound)
    (hsuccess : RestrictedSuccessfulFamilyFromTwo Mcoeff) :
    FamilyUpperBound Mcoeff bound := by
  intro n hn bidding
  by_cases h1 : n = 1
  · subst h1
    simpa using hasValueAtMost_singleton
      ({ Mcoeff := Mcoeff, bidding := bidding } : DualProgram 1) hMbound
  · let : NeZero n := ⟨hn⟩
    let P : DualProgram n := { Mcoeff := Mcoeff, bidding := bidding }
    let I : ProcedureInput n := ProcedureInput.forced Mcoeff bidding
    have hI : SuccessfulInput I := hsuccess n inferInstance h1 bidding
    have hγlo' : 1 ≤ I.program.Mcoeff := by
      simp [I, ProcedureInput.forced, DualProgram.forceFinalRowOne, le_of_lt hγlo]
    have hγhi' : I.program.Mcoeff ≤ (153 : ℝ) / 125 := by
      simp [I, ProcedureInput.forced, DualProgram.forceFinalRowOne, hγhi]
    have hθpos : 0 < I.program.theta := by
      simpa [I, ProcedureInput.forced, DualProgram.forceFinalRowOne] using
        DualProgram.theta_pos_of_one_lt_Mcoeff I.program
          (by simp [I, ProcedureInput.forced, DualProgram.forceFinalRowOne, hγlo])
    have hforcedRho :
        DualSolution.HasValueAtMost I.program I.program.rhoBound :=
      hasValueAtMost_of_successfulInput hγlo' hγhi' hθpos hI
    have hrho_le : I.program.rhoBound ≤ bound := by
      simpa [I, ProcedureInput.forced, DualProgram.forceFinalRowOne,
        DualProgram.rhoBound, DualProgram.epsilon, DualProgram.Mcoeffmone] using hρbound
    have hforced :
        DualSolution.HasValueAtMost I.program bound :=
      DualSolution.hasValueAtMost_mono hforcedRho hrho_le
    have horig :
        DualSolution.HasValueAtMost P bound := by
      apply DualSolution.hasValueAtMost_of_forceFinalRowOne (P := P)
      simpa [P, I, ProcedureInput.forced, DualProgram.forceFinalRowOne] using hforced
    simpa [P] using horig

theorem familyUpperBound_195_of_restrictedSuccessfulFamilyFromTwo
    (hsuccess : RestrictedSuccessfulFamilyFromTwo ((153 : ℝ) / 125)) :
    FamilyUpperBound ((153 : ℝ) / 125) ((39 : ℝ) / 20) := by
  refine familyUpperBound_of_restrictedSuccessfulFamilyFromTwo ?_ ?_ ?_ ?_ hsuccess
  · nlinarith
  · linarith
  · nlinarith
  · nlinarith

theorem restrictedSuccessfulFamilyFromTwo_of_restrictedProfileFamilyFromTwo
    {Mcoeff : ℝ}
    (hγlo : 1 < Mcoeff) (hγhi : Mcoeff ≤ (153 : ℝ) / 125)
    (hprof : RestrictedProfileFamilyFromTwo Mcoeff) :
    RestrictedSuccessfulFamilyFromTwo Mcoeff := by
  intro n _ hn1 bidding
  rcases hprof n inferInstance hn1 bidding with ⟨Γ, hΓ, ⟨C⟩⟩
  let I : ProcedureInput n := ProcedureInput.forced Mcoeff bidding
  have hγlo' : 1 ≤ I.program.Mcoeff := by
    simp [I, ProcedureInput.forced, DualProgram.forceFinalRowOne, le_of_lt hγlo]
  have hγhi' : I.program.Mcoeff ≤ (153 : ℝ) / 125 := by
    simp [I, ProcedureInput.forced, DualProgram.forceFinalRowOne, hγhi]
  have hθpos : 0 < I.program.theta := by
    simpa [I, ProcedureInput.forced, DualProgram.forceFinalRowOne] using
      DualProgram.theta_pos_of_one_lt_Mcoeff I.program
        (by simp [I, ProcedureInput.forced, DualProgram.forceFinalRowOne, hγlo])
  exact successfulInput_of_admissible_profile hΓ C hγlo' hγhi' hθpos

theorem familyUpperBound_195_of_restrictedProfileFamilyFromTwo
    (hprof : RestrictedProfileFamilyFromTwo ((153 : ℝ) / 125)) :
    FamilyUpperBound ((153 : ℝ) / 125) ((39 : ℝ) / 20) := by
  apply familyUpperBound_195_of_restrictedSuccessfulFamilyFromTwo
  exact restrictedSuccessfulFamilyFromTwo_of_restrictedProfileFamilyFromTwo
    (by nlinarith) (by linarith) hprof

theorem restrictedProfileFamilyFromTwo_of_restrictedGoodAdvicePointwiseContinuityFamilyFromTwo
    {Mcoeff : ℝ}
    (hγlo : 1 < Mcoeff)
    (hpoint : RestrictedGoodAdvicePointwiseContinuityFamilyFromTwo Mcoeff) :
    RestrictedProfileFamilyFromTwo Mcoeff := by
  intro n _ hn1 bidding
  let I : ProcedureInput n := ProcedureInput.forced Mcoeff bidding
  rcases hpoint n inferInstance hn1 bidding with ⟨P, hcompat, hcont, hleft, hright⟩
  rcases P.exists_profileData_of_compatible_pointwise
      (I := I)
      (hγ := by simpa [I, ProcedureInput.forced, DualProgram.forceFinalRowOne] using hγlo)
      hcont hcompat hleft hright with
    ⟨Γ, hΓ, hprof⟩
  exact ⟨Γ, hΓ, hprof⟩

theorem familyUpperBound_195_of_restrictedGoodAdvicePointwiseContinuityFamilyFromTwo
    (hpoint : RestrictedGoodAdvicePointwiseContinuityFamilyFromTwo ((153 : ℝ) / 125)) :
    FamilyUpperBound ((153 : ℝ) / 125) ((39 : ℝ) / 20) := by
  apply familyUpperBound_195_of_restrictedProfileFamilyFromTwo
  exact restrictedProfileFamilyFromTwo_of_restrictedGoodAdvicePointwiseContinuityFamilyFromTwo
    (by nlinarith) hpoint

theorem restrictedGoodAdvicePointwiseContinuityFamilyFromTwo_of_one_lt
    {Mcoeff : ℝ} (hγlo : 1 < Mcoeff) (hγhi : Mcoeff ≤ (153 : ℝ) / 125) :
    RestrictedGoodAdvicePointwiseContinuityFamilyFromTwo Mcoeff := by
  intro n _ hn1 bidding
  let I : ProcedureInput n := ProcedureInput.forced Mcoeff bidding
  have hγ : 1 < I.program.Mcoeff := by
    simpa [I, ProcedureInput.forced, DualProgram.forceFinalRowOne] using hγlo
  have hγhi' : I.program.Mcoeff ≤ (153 : ℝ) / 125 := by
    simpa [I, ProcedureInput.forced, DualProgram.forceFinalRowOne] using hγhi
  refine ⟨canonicalPath I (le_of_lt hγ) hγhi', ?_, ?_, ?_, ?_⟩
  · exact canonicalPath_compatible (I := I) (le_of_lt hγ) hγhi'
  · intro ℓ lam hlam
    exact canonicalPath_continuousWithinAt (I := I) hγ hγhi' hlam
  · exact canonicalPath_firstOutput_R0_le_one (I := I) hγ hγhi'
  · exact canonicalPath_lastOutput_R0_ge_one (I := I) (le_of_lt hγ) hγhi'

theorem restrictedGoodAdvicePointwiseContinuityFamilyFromTwo_153_div_125 :
    RestrictedGoodAdvicePointwiseContinuityFamilyFromTwo ((153 : ℝ) / 125) := by
  exact restrictedGoodAdvicePointwiseContinuityFamilyFromTwo_of_one_lt (by norm_num) le_rfl

/-- The generic construction bounds every dual family for `1 < γ ≤ 1.224`. -/
theorem familyUpperBound_exact_of_one_lt
    {Mcoeff : ℝ} (hγlo : 1 < Mcoeff) (hγhi : Mcoeff ≤ (153 : ℝ) / 125) :
    FamilyUpperBound Mcoeff (2 - (Mcoeff - 1) ^ 2) := by
  refine familyUpperBound_of_restrictedSuccessfulFamilyFromTwo hγlo hγhi ?_ le_rfl ?_
  · nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hγlo)) (sub_nonneg.mpr hγhi)]
  · exact
      restrictedSuccessfulFamilyFromTwo_of_restrictedProfileFamilyFromTwo hγlo hγhi
        (restrictedProfileFamilyFromTwo_of_restrictedGoodAdvicePointwiseContinuityFamilyFromTwo
          hγlo (restrictedGoodAdvicePointwiseContinuityFamilyFromTwo_of_one_lt hγlo hγhi))

theorem familyUpperBound_153_div_125_exact :
    FamilyUpperBound ((153 : ℝ) / 125)
      (2 - (((153 : ℝ) / 125) - 1) ^ 2) := by
  exact familyUpperBound_exact_of_one_lt (by norm_num) le_rfl

theorem familyUpperBound_195 :
    FamilyUpperBound ((153 : ℝ) / 125) ((39 : ℝ) / 20) := by
  intro n hn bidding
  rcases familyUpperBound_153_div_125_exact n hn bidding with ⟨x, hx, hρx⟩
  refine ⟨x, hx, ?_⟩
  have hbound : 2 - (((153 : ℝ) / 125) - 1) ^ 2 ≤ (39 : ℝ) / 20 := by
    norm_num
  exact le_trans hρx hbound

end

end KMedian195


