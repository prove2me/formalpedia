-- Prove2me | Definitions.Def_KMedian195_PoolConstraints
-- name    : KMedian195_PoolConstraints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:34.325314+00:00
-- url     : https://prove2.me/theorems/de315cc5-ebad-4d2a-a6d5-262a35871931
-- title:
--   KMedian195.PoolConstraints
-- statement:
--   This is module `KMedian195.PoolConstraints` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 151 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_PoolConstraints`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/PoolConstraints.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/PoolConstraints.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`), and:
* `if_pos`, `if_neg`, `dif_pos`, `dif_neg` (deprecated) are `if_pos`, `if_neg`,
  `dif_pos`, `dif_neg`.
-/
module

public import Definitions.Def_KMedian195_ValueConstraints

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.PoolConstraints` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

noncomputable section

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem sum_prefixTriangle_eq_sumByColumn
    (f : Idx n → Idx n → ℝ) (i : Idx n) :
    Finset.sum (prefixRange i) (fun p => Finset.sum (prefixRange p) (fun j => f p j)) =
      Finset.sum (prefixRange i) (fun j => Finset.sum (intervalRange j i) (fun p => f p j)) := by
  classical
  have hleft :
      Finset.sum (prefixRange i) (fun p => Finset.sum (prefixRange p) (fun j => f p j)) =
        Finset.sum (prefixRange i)
          (fun p => Finset.sum (prefixRange i) (fun j => if j ≤ p then f p j else 0)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpi : p ≤ i := mem_prefixRange.mp hp
    have hset : prefixRange p = (prefixRange i).filter (fun j => j ≤ p) := by
      ext j
      constructor
      · intro hj
        exact Finset.mem_filter.mpr
          ⟨mem_prefixRange.mpr (le_trans (mem_prefixRange.mp hj) hpi), mem_prefixRange.mp hj⟩
      · intro hj
        exact mem_prefixRange.mpr (Finset.mem_filter.mp hj).2
    rw [hset, Finset.sum_filter]
  have hright :
      Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => f p j)) =
        Finset.sum (prefixRange i)
          (fun j => Finset.sum (prefixRange i) (fun p => if j ≤ p then f p j else 0)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≤ i := mem_prefixRange.mp hj
    have hset : intervalRange j i = (prefixRange i).filter (fun p => j ≤ p) := by
      ext p
      constructor
      · intro hp
        rcases mem_intervalRange.mp hp with ⟨hjp, hpi⟩
        exact Finset.mem_filter.mpr ⟨mem_prefixRange.mpr hpi, hjp⟩
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hpi, hjp⟩
        exact mem_intervalRange.mpr ⟨hjp, mem_prefixRange.mp hpi⟩
    rw [hset, Finset.sum_filter]
  rw [hleft, hright, Finset.sum_comm]

namespace ProfileData

variable {I : ProcedureInput n} {Γ : Advice I}

def muBC (C : ProfileData I Γ) (j : Idx n) : ℝ :=
  (C.memberships).muB j + (C.memberships).muC j

def poolValue (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) : ℝ :=
  Finset.sum (prefixRange i) fun p =>
    Finset.sum (prefixRange p) fun j => C.sValue AUX p j - C.tValue AUX p j

def shiftedPoolValue (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) : ℝ :=
  Finset.sum (prefixRange i) fun p =>
    Finset.sum (prefixRange p) fun j => C.shiftedSValue AUX p j - C.tValue AUX p j

@[simp] theorem constructedDualSolution_poolCredit_eq_shiftedPoolValue
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) :
    DualSolution.poolCredit (C.constructedDualSolution AUX) i = C.shiftedPoolValue AUX i := by
  unfold DualSolution.poolCredit ProfileData.shiftedPoolValue DualSolution.strictS
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjp : j < p
  · simp [ProfileData.shiftedSValue, hjp]
  · simp [ProfileData.shiftedSValue, hjp]

theorem poolValue_eq_sumByColumn
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) :
    C.poolValue AUX i =
      Finset.sum (prefixRange i)
        (fun j =>
          Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j - C.tValue AUX p j)) := by
  unfold ProfileData.poolValue
  exact sum_prefixTriangle_eq_sumByColumn (f := fun p j => C.sValue AUX p j - C.tValue AUX p j) i

theorem shiftedPoolValue_eq_sumByColumn
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) :
    C.shiftedPoolValue AUX i =
      Finset.sum (prefixRange i)
        (fun j =>
          Finset.sum
            (intervalRange j i)
            (fun p => C.shiftedSValue AUX p j - C.tValue AUX p j)) := by
  unfold ProfileData.shiftedPoolValue
  exact
    sum_prefixTriangle_eq_sumByColumn
      (f := fun p j => C.shiftedSValue AUX p j - C.tValue AUX p j) i

theorem shiftedPoolValue_eq_poolValue_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (_hΓ : Γ.Admissible)
    (_hγlo : 1 ≤ I.program.Mcoeff) (_hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (ht1i : C.t1 < i) :
    C.shiftedPoolValue AUX i = C.poolValue AUX i := by
  rw [C.shiftedPoolValue_eq_sumByColumn AUX i, C.poolValue_eq_sumByColumn AUX i]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≤ i := mem_prefixRange.mp hj
  have hs :
      Finset.sum (intervalRange j i) (fun p => C.shiftedSValue AUX p j) =
        Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j) := by
    rcases lt_or_eq_of_le hji with hjlt | rfl
    · exact C.sum_interval_shiftedSValue_eq_of_lt AUX hjlt
    · have hsdiag0 : C.sValue AUX j j = 0 := C.sValue_diag_eq_zero_of_t1_lt AUX ht1i
      have hsingle : intervalRange j j = ({j} : Finset (Idx n)) := by
        ext p
        constructor
        · intro hp
          exact Finset.mem_singleton.mpr <|
            le_antisymm (mem_intervalRange.mp hp).2 (mem_intervalRange.mp hp).1
        · intro hp
          rw [Finset.mem_singleton.mp hp]
          exact mem_intervalRange.mpr ⟨le_rfl, le_rfl⟩
      rw [hsingle]
      simp [ProfileData.shiftedSValue, hsdiag0]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hs]

theorem sValue_diag_eq_zero_of_t1_eq_last
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (ht1 : C.t1 = lastIdx n) :
    C.sValue AUX (lastIdx n) (lastIdx n) = 0 := by
  have hmuA0 : (C.memberships).muA (lastIdx n) = 0 := by
    rw [← ht1, C.memberships_muA_eq_at_t1, C.alpha_eq, if_pos ht1]
    ring
  have hnotNext : ¬ IsNextIndex (lastIdx n) (I.firstBidTime (lastIdx n)) := by
    intro hnext
    unfold IsNextIndex at hnext
    have hlt : I.firstBidTime (lastIdx n) < lastIdx n := Fin.lt_def.mpr (by omega)
    exact (not_lt_of_ge (I.le_firstBidTime (lastIdx n))) hlt
  simp [ProfileData.sValue, ProfileData.sA, ProfileData.sB, ProfileData.sC, ProfileData.sD,
    hmuA0, hnotNext]

theorem shiftedPoolValue_eq_poolValue_at_last
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (_hΓ : Γ.Admissible)
    (_hγlo : 1 ≤ I.program.Mcoeff) (_hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    C.shiftedPoolValue AUX (lastIdx n) = C.poolValue AUX (lastIdx n) := by
  rw [C.shiftedPoolValue_eq_sumByColumn AUX (lastIdx n), C.poolValue_eq_sumByColumn AUX (lastIdx n)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlast : j ≤ lastIdx n := le_lastIdx j
  have hs :
      Finset.sum (intervalRange j (lastIdx n)) (fun p => C.shiftedSValue AUX p j) =
        Finset.sum (intervalRange j (lastIdx n)) (fun p => C.sValue AUX p j) := by
    rcases lt_or_eq_of_le hjlast with hjlt | hjeq
    · exact C.sum_interval_shiftedSValue_eq_of_lt AUX hjlt
    · subst hjeq
      have hsdiag0 : C.sValue AUX (lastIdx n) (lastIdx n) = 0 := by
        by_cases ht1 : C.t1 < lastIdx n
        · exact C.sValue_diag_eq_zero_of_t1_lt AUX ht1
        · have ht1eq : C.t1 = lastIdx n := le_antisymm (le_lastIdx _) (not_lt.mp ht1)
          exact C.sValue_diag_eq_zero_of_t1_eq_last AUX ht1eq
      have hsingle :
          intervalRange (lastIdx n) (lastIdx n) = ({lastIdx n} : Finset (Idx n)) := by
        ext p
        constructor
        · intro hp
          exact Finset.mem_singleton.mpr <|
            le_antisymm (le_lastIdx p) (mem_intervalRange.mp hp).1
        · intro hp
          rw [Finset.mem_singleton.mp hp]
          exact mem_intervalRange.mpr ⟨le_rfl, le_rfl⟩
      rw [hsingle]
      simp [ProfileData.shiftedSValue, hsdiag0]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hs]

theorem sum_interval_tValue_eq_if_firstBid
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j i : Idx n) :
    Finset.sum (intervalRange j i) (fun p => C.tValue AUX p j) =
      if I.firstBidTime j ≤ i then
        C.tValue AUX (I.firstBidTime j) j
      else
        0 := by
  by_cases hfi : I.firstBidTime j ≤ i
  · rw [C.sum_interval_tValue_eq_membership_combo AUX, if_pos hfi, C.sum_interval_tA_eq AUX,
      C.sum_interval_tB_eq AUX, C.sum_interval_tC_eq AUX, C.sum_interval_tD_eq AUX]
    simp [ProfileData.tValue, ProfileData.tA, ProfileData.tB, ProfileData.tC, ProfileData.tD, hfi]
  · rw [C.sum_interval_tValue_eq_membership_combo AUX, if_neg hfi, C.sum_interval_tA_eq AUX,
      C.sum_interval_tB_eq AUX, C.sum_interval_tC_eq AUX, C.sum_interval_tD_eq AUX]
    simp [hfi]

theorem poolValue_eq_rewrite
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) :
    C.poolValue AUX i =
      Finset.sum (prefixRange i)
        (fun j => Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j)) -
      Finset.sum (prefixRange i)
        (fun j =>
          if I.firstBidTime j ≤ i then
            C.tValue AUX (I.firstBidTime j) j
          else
            0) := by
  calc
    C.poolValue AUX i
      = Finset.sum (prefixRange i)
          (fun j =>
            Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j) -
              Finset.sum (intervalRange j i) (fun p => C.tValue AUX p j)) := by
          rw [C.poolValue_eq_sumByColumn AUX i]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_sub_distrib]
    _ = Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j)) -
        Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.tValue AUX p j)) := by
          rw [Finset.sum_sub_distrib]
    _ = Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j)) -
        Finset.sum (prefixRange i)
          (fun j =>
            if I.firstBidTime j ≤ i then
              C.tValue AUX (I.firstBidTime j) j
            else
              0) := by
          congr
          ext j
          rw [C.sum_interval_tValue_eq_if_firstBid AUX j i]

theorem shiftedPoolValue_eq_rewrite
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) :
    C.shiftedPoolValue AUX i =
      Finset.sum (prefixRange i)
        (fun j => Finset.sum (intervalRange j i) (fun p => C.shiftedSValue AUX p j)) -
      Finset.sum (prefixRange i)
        (fun j =>
          if I.firstBidTime j ≤ i then
            C.tValue AUX (I.firstBidTime j) j
          else
            0) := by
  calc
    C.shiftedPoolValue AUX i
      = Finset.sum (prefixRange i)
          (fun j =>
            Finset.sum (intervalRange j i) (fun p => C.shiftedSValue AUX p j) -
              Finset.sum (intervalRange j i) (fun p => C.tValue AUX p j)) := by
          rw [C.shiftedPoolValue_eq_sumByColumn AUX i]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_sub_distrib]
    _ = Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.shiftedSValue AUX p j)) -
        Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.tValue AUX p j)) := by
          rw [Finset.sum_sub_distrib]
    _ = Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.shiftedSValue AUX p j)) -
        Finset.sum (prefixRange i)
          (fun j =>
            if I.firstBidTime j ≤ i then
              C.tValue AUX (I.firstBidTime j) j
            else
              0) := by
          congr
          ext j
          rw [C.sum_interval_tValue_eq_if_firstBid AUX j i]

theorem tValue_eq_zero_of_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {p j : Idx n} (hjt1 : j < C.t1) (hpt1 : p < C.t1) :
    C.tValue AUX p j = 0 := by
  have hB0 : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_lt_t1 hjt1
  have hC0 : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_lt_t1 hjt1
  by_cases hμ : 0 < Γ.muD j
  · have ht1le : C.t1 ≤ Γ.t3Star := C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos
    have ht3le : Γ.t3Star ≤ I.firstBidTime j := t3_le_firstBidTime_of_muD_pos Γ hμ
    have hpne : p ≠ I.firstBidTime j := by
      intro hpeq
      have hle : C.t1 ≤ p := hpeq ▸ le_trans ht1le ht3le
      exact (not_le_of_gt hpt1) hle
    simp [ProfileData.tValue, ProfileData.tA, ProfileData.tB, ProfileData.tC, ProfileData.tD,
      hB0, hC0, hpne]
  · have hμ0 : Γ.muD j = 0 := by
      have hμnonneg : 0 ≤ Γ.muD j := Advice.muD_nonneg_of_admissible Γ hΓ j
      linarith
    simp [ProfileData.tValue, ProfileData.tA, ProfileData.tB, ProfileData.tC, ProfileData.tD,
      hB0, hC0, hμ0]

theorem sum_interval_tValue_eq_zero_of_le_t1_of_t1_lt_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {j : Idx n} (hjt1 : j ≤ C.t1) (ht1t3 : C.t1 < Γ.t3Star) :
    Finset.sum (intervalRange j C.t1) (fun p => C.tValue AUX p j) = 0 := by
  rw [C.sum_interval_tValue_eq_if_firstBid AUX j C.t1]
  by_cases hfi : I.firstBidTime j ≤ C.t1
  · rw [if_pos hfi]
    have hfjlt3 : I.firstBidTime j < Γ.t3Star := lt_of_le_of_lt hfi ht1t3
    have hμD0 : Γ.muD j = 0 := Advice.muD_eq_zero Γ hfjlt3
    rcases lt_or_eq_of_le hjt1 with hjlt1 | rfl
    · have hB0 : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_lt_t1 hjlt1
      have hC0 : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_lt_t1 hjlt1
      simp [ProfileData.tValue, ProfileData.tA, ProfileData.tB, ProfileData.tC, ProfileData.tD,
        hB0, hC0, hμD0]
    · have hC0 : (C.memberships).muC C.t1 = 0 := C.memberships_muC_eq_zero_at_t1
      have hBterm0 : posPart (1 - beforeBudget C.hatG C.t1 - I.program.tau) = 0 := by
        have hbar : I.program.barTau ≤ beforeBudget C.hatG C.t1 :=
          C.beforeBudget_t1_ge_barTau hΓ hγlo hγhi
        have hbar' : 1 - I.program.tau ≤ beforeBudget C.hatG C.t1 := by
          simpa [DualProgram.barTau] using hbar
        have hnonpos : 1 - beforeBudget C.hatG C.t1 - I.program.tau ≤ 0 := by
          linarith
        simp [posPart_of_nonpos hnonpos]
      simp [ProfileData.tValue, ProfileData.tA, ProfileData.tB, ProfileData.tC, ProfileData.tD,
        hμD0, hC0, hBterm0]
  · simp [hfi]

theorem poolValue_nonneg_of_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (hit1 : i < C.t1) :
    0 ≤ C.poolValue AUX i := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  rw [C.poolValue_eq_sumByColumn AUX i]
  apply Finset.sum_nonneg
  intro j hj
  have hji : j ≤ i := mem_prefixRange.mp hj
  have hjt1 : j < C.t1 := lt_of_le_of_lt hji hit1
  apply Finset.sum_nonneg
  intro p hp
  have hpi : p ≤ i := (mem_intervalRange.mp hp).2
  have hpt1 : p < C.t1 := lt_of_le_of_lt hpi hit1
  have hs : 0 ≤ C.sValue AUX p j := by
    simpa using C.sValue_nonneg H AUX p j
  have ht : C.tValue AUX p j = 0 :=
    C.tValue_eq_zero_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjt1 hpt1
  simpa [ht] using hs

theorem constructedDualSolution_poolCredit_nonneg_of_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (hit1 : i < C.t1) :
    0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) i := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  rw [C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX i,
    C.shiftedPoolValue_eq_sumByColumn AUX i]
  apply Finset.sum_nonneg
  intro j hj
  have hji : j ≤ i := mem_prefixRange.mp hj
  have hjt1 : j < C.t1 := lt_of_le_of_lt hji hit1
  apply Finset.sum_nonneg
  intro p hp
  have hpi : p ≤ i := (mem_intervalRange.mp hp).2
  have hpt1 : p < C.t1 := lt_of_le_of_lt hpi hit1
  have hs : 0 ≤ C.shiftedSValue AUX p j := by
    simpa using C.shiftedSValue_nonneg H AUX p j
  have ht : C.tValue AUX p j = 0 :=
    C.tValue_eq_zero_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjt1 hpt1
  simpa [ht] using hs

theorem poolValue_nonneg_at_t1_of_lt_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ht1t3 : C.t1 < Γ.t3Star) :
    0 ≤ C.poolValue AUX C.t1 := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  rw [C.poolValue_eq_rewrite AUX C.t1]
  have htZero :
      Finset.sum (prefixRange C.t1)
        (fun j =>
          if I.firstBidTime j ≤ C.t1 then
            C.tValue AUX (I.firstBidTime j) j
          else
            0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjt1 : j ≤ C.t1 := mem_prefixRange.mp hj
        have hzero :=
          C.sum_interval_tValue_eq_zero_of_le_t1_of_t1_lt_t3 AUX hΓ hγlo hγhi hjt1 ht1t3
        rw [C.sum_interval_tValue_eq_if_firstBid AUX j C.t1] at hzero
        exact hzero
  rw [htZero, sub_zero]
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro p hp
  simpa using C.sValue_nonneg H AUX p j

theorem constructedDualSolution_poolCredit_nonneg_at_t1_of_lt_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ht1t3 : C.t1 < Γ.t3Star) :
    0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) C.t1 := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  rw [C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX C.t1,
    C.shiftedPoolValue_eq_rewrite AUX C.t1]
  have htZero :
      Finset.sum (prefixRange C.t1)
        (fun j =>
          if I.firstBidTime j ≤ C.t1 then
            C.tValue AUX (I.firstBidTime j) j
          else
            0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjt1 : j ≤ C.t1 := mem_prefixRange.mp hj
        have hzero :=
          C.sum_interval_tValue_eq_zero_of_le_t1_of_t1_lt_t3 AUX hΓ hγlo hγhi hjt1 ht1t3
        rw [C.sum_interval_tValue_eq_if_firstBid AUX j C.t1] at hzero
        exact hzero
  rw [htZero, sub_zero]
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro p hp
  simpa using C.shiftedSValue_nonneg H AUX p j

theorem muBC_nonneg
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) (j : Idx n) :
    0 ≤ C.muBC j := by
  have hμ := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  exact add_nonneg (hμ.2.1 j) (hμ.2.2.1 j)

theorem muBC_eq_muB_add_muC
    (C : ProfileData I Γ) (j : Idx n) :
    C.muBC j = (C.memberships).muB j + (C.memberships).muC j := rfl

theorem muBC_eq_of_between_t1_t2
    (C : ProfileData I Γ) {j : Idx n} (ht1j : C.t1 < j) (hjt2 : j ≤ C.t2) :
    C.muBC j = 1 - Γ.muD j := by
  rw [ProfileData.muBC, C.memberships_muB_eq_of_between_t1_t2 ht1j hjt2,
    C.memberships_muC_eq_zero_of_between_t1_t2 ht1j hjt2]
  ring

theorem muBC_eq_at_t1
    (C : ProfileData I Γ) :
    C.muBC C.t1 = (C.memberships).muB C.t1 := by
  rw [ProfileData.muBC, C.memberships_muC_eq_zero_at_t1, add_zero]

theorem muBC_eq_of_between_t2_t3
    (C : ProfileData I Γ) {j : Idx n} (ht2j : C.t2 < j) (hjt3 : j ≤ Γ.t3Star) :
    C.muBC j = 1 - Γ.muD j := by
  rw [ProfileData.muBC, C.memberships_muB_eq_zero_of_between_t2_t3 ht2j hjt3,
    zero_add, C.memberships_muC_eq_of_between_t2_t3 ht2j hjt3]

omit [NeZero n] in
theorem tailBudget_antitone_of_nonneg {hatG : Idx n → ℝ}
    (hhatG : ∀ i, 0 ≤ hatG i) {i j : Idx n} (hij : i ≤ j) :
    tailBudget hatG j ≤ tailBudget hatG i := by
  unfold tailBudget
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro k hk
    exact mem_strictSuffixRange.mpr (lt_of_le_of_lt hij (mem_strictSuffixRange.mp hk))
  · intro k hki hknj
    exact hhatG k

omit [NeZero n] in
theorem sum_halfOpen_eq_before_sub_before (hatG : Idx n → ℝ) {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (halfOpenIntervalRange j i) hatG =
      beforeBudget hatG j - beforeBudget hatG i := by
  have hleft : (suffixRange j).filter (fun p => p < i) = halfOpenIntervalRange j i := by
    ext p
    simp [suffixRange, halfOpenIntervalRange]
  have hright : (suffixRange j).filter (fun p => ¬ p < i) = suffixRange i := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨-, hpnot⟩
      exact mem_suffixRange.mpr (not_lt.mp hpnot)
    · intro hp
      exact Finset.mem_filter.mpr ⟨mem_suffixRange.mpr (le_trans hji (mem_suffixRange.mp hp)),
        not_lt.mpr (mem_suffixRange.mp hp)⟩
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := suffixRange j) (p := fun p => p < i) hatG
  rw [hleft, hright] at hsplit
  have hsplit' :
      Finset.sum (halfOpenIntervalRange j i) hatG + beforeBudget hatG i = beforeBudget hatG j := by
    simpa [beforeBudget] using hsplit
  linarith

def predIdx {i : Idx n} (hi : 0 < i.1) : Idx n :=
  ⟨i.1 - 1, by omega⟩

omit [NeZero n] in
theorem predIdx_lt {i : Idx n} (hi : 0 < i.1) :
    predIdx hi < i := by
  exact Fin.lt_def.mpr (by
    dsimp [ProfileData.predIdx]
    omega)

omit [NeZero n] in
theorem tailBudget_predIdx_eq_beforeBudget
    (hatG : Idx n → ℝ) {i : Idx n} (hi : 0 < i.1) :
    tailBudget hatG (predIdx hi) = beforeBudget hatG i := by
  unfold tailBudget beforeBudget strictSuffixRange suffixRange
  congr
  ext k
  constructor
  · intro hk
    have hk' : predIdx hi < k := hk
    exact Fin.le_def.mpr <| by
      have hvals : (predIdx hi).1 < k.1 := Fin.lt_def.mp hk'
      change (i.1 - 1) < k.1 at hvals
      omega
  · intro hk
    have hk' : i ≤ k := hk
    exact show predIdx hi < k by
      exact Fin.lt_def.mpr <| by
        have hvals : i.1 ≤ k.1 := Fin.le_def.mp hk'
        change i.1 - 1 < k.1
        omega

omit [NeZero n] in
theorem futureCount_predIdx {i : Idx n} (hi : 0 < i.1) :
    futureCount (predIdx hi) = futureCount i + 1 := by
  change (((n - (predIdx hi).1.succ : ℕ) : ℝ) = ((n - i.1.succ : ℕ) : ℝ) + 1)
  have hpred : (predIdx hi).1.succ = i.1 := by
    change (i.1 - 1).succ = i.1
    exact Nat.succ_pred_eq_of_pos hi
  rw [hpred]
  have hnat : n - i.1 = (n - i.1.succ) + 1 := by
    have hle : i.1.succ ≤ n := Nat.succ_le_of_lt i.is_lt
    omega
  exact_mod_cast hnat

/-- The paper's phase-2 profile `\hat g'`, obtained by replacing the boundary mass at `t₁`
by its `B`-part. -/
def hatGPrime (C : ProfileData I Γ) (i : Idx n) : ℝ :=
  if i = C.t1 then
    C.boundaryHatGB
  else
    C.hatG i

def tailBudgetPrime (C : ProfileData I Γ) (i : Idx n) : ℝ :=
  tailBudget C.hatGPrime i

def beforeBudgetPrime (C : ProfileData I Γ) (i : Idx n) : ℝ :=
  beforeBudget C.hatGPrime i

@[simp] theorem hatGPrime_at_t1
    (C : ProfileData I Γ) :
    C.hatGPrime C.t1 = C.boundaryHatGB := by
  simp [ProfileData.hatGPrime]

theorem hatGPrime_eq_hatG_of_ne_t1
    (C : ProfileData I Γ) {i : Idx n} (hi : i ≠ C.t1) :
    C.hatGPrime i = C.hatG i := by
  simp [ProfileData.hatGPrime, hi]

theorem tailBudgetPrime_eq_tailBudget_of_t1_le
    (C : ProfileData I Γ) {i : Idx n} (ht1i : C.t1 ≤ i) :
    C.tailBudgetPrime i = tailBudget C.hatG i := by
  unfold ProfileData.tailBudgetPrime tailBudget ProfileData.hatGPrime
  apply Finset.sum_congr rfl
  intro k hk
  have hik : i < k := mem_strictSuffixRange.mp hk
  have ht1k : C.t1 < k := lt_of_le_of_lt ht1i hik
  simp [ne_of_gt ht1k]

theorem beforeBudgetPrime_eq_beforeBudget_of_t1_lt
    (C : ProfileData I Γ) {j : Idx n} (ht1j : C.t1 < j) :
    C.beforeBudgetPrime j = beforeBudget C.hatG j := by
  unfold ProfileData.beforeBudgetPrime beforeBudget ProfileData.hatGPrime
  apply Finset.sum_congr rfl
  intro k hk
  have hjk : j ≤ k := mem_suffixRange.mp hk
  have ht1k : C.t1 < k := lt_of_lt_of_le ht1j hjk
  simp [ne_of_gt ht1k]

theorem beforeBudgetPrime_t1_eq_barTau_of_ne_last
    (C : ProfileData I Γ) (ht1 : C.t1 ≠ lastIdx n) :
    C.beforeBudgetPrime C.t1 = I.program.barTau := by
  calc
    C.beforeBudgetPrime C.t1 = C.hatGPrime C.t1 + C.tailBudgetPrime C.t1 := by
      exact beforeBudget_eq_self_add_tail C.hatGPrime C.t1
    _ = C.boundaryHatGB + tailBudget C.hatG C.t1 := by
      rw [C.hatGPrime_at_t1, C.tailBudgetPrime_eq_tailBudget_of_t1_le le_rfl]
    _ = I.program.barTau := by
      have htail : tailBudget C.hatG C.t1 + I.program.tau + C.boundaryHatGB = 1 :=
        C.tailBudget_add_tau_add_boundaryHatGB_eq_one_of_ne_last ht1
      rw [DualProgram.barTau]
      linarith

theorem futureCount_mul_hatGPrime_eq_muB_mul_tailBudgetPrime_add_tau_at_t1_of_ne_last
    (C : ProfileData I Γ) (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) (hθpos : 0 < I.program.theta)
    (ht1 : C.t1 ≠ lastIdx n) :
    futureCount C.t1 * C.hatGPrime C.t1 =
      (C.memberships).muB C.t1 * (C.tailBudgetPrime C.t1 + I.program.tau) := by
  rw [C.hatGPrime_at_t1, C.tailBudgetPrime_eq_tailBudget_of_t1_le le_rfl]
  exact C.futureCount_mul_boundaryHatGB_eq_muB_mul_tailBudget_add_tau_of_ne_last
    hγlo hγhi hθpos ht1

theorem futureCount_mul_hatGPrime_eq_muB_mul_tailBudgetPrime_add_tau_of_between_t1_t2
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) {j : Idx n}
    (ht1j : C.t1 < j) (hjt2 : j ≤ C.t2) :
    futureCount j * C.hatGPrime j =
      (C.memberships).muB j * (C.tailBudgetPrime j + I.program.tau) := by
  rw [C.hatGPrime_eq_hatG_of_ne_t1 (ne_of_gt ht1j),
    C.tailBudgetPrime_eq_tailBudget_of_t1_le (le_of_lt ht1j)]
  exact C.futureCount_mul_hatG_eq_one_sub_muD_mul_tailBudget_add_tau_of_t1_lt hΓ ht1j |>.trans
    (by rw [C.memberships_muB_eq_of_between_t1_t2 ht1j hjt2])

theorem futureCount_mul_hatGPrime_eq_muC_mul_tailBudgetPrime_add_tau_of_between_t2_t3
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) {j : Idx n}
    (ht2j : C.t2 < j) (hjt3 : j ≤ Γ.t3Star) :
    futureCount j * C.hatGPrime j =
      (C.memberships).muC j * (C.tailBudgetPrime j + I.program.tau) := by
  have ht1j : C.t1 < j := lt_of_le_of_lt C.t1_le_t2 ht2j
  rw [C.hatGPrime_eq_hatG_of_ne_t1 (ne_of_gt ht1j),
    C.tailBudgetPrime_eq_tailBudget_of_t1_le (le_of_lt ht1j)]
  exact C.futureCount_mul_hatG_eq_one_sub_muD_mul_tailBudget_add_tau_of_t1_lt hΓ ht1j |>.trans
    (by rw [C.memberships_muC_eq_of_between_t2_t3 ht2j hjt3])

theorem futureCount_mul_hatGPrime_eq_muBC_mul_tailBudgetPrime_add_tau
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (ht1j : C.t1 ≤ j) (hjt3 : j ≤ Γ.t3Star) (hjlast : j ≠ lastIdx n) :
    futureCount j * C.hatGPrime j = C.muBC j * (C.tailBudgetPrime j + I.program.tau) := by
  rcases lt_or_eq_of_le ht1j with ht1j' | rfl
  · by_cases hjt2 : j ≤ C.t2
    · rw [ProfileData.muBC, C.memberships_muC_eq_zero_of_between_t1_t2 ht1j' hjt2, add_zero]
      exact C.futureCount_mul_hatGPrime_eq_muB_mul_tailBudgetPrime_add_tau_of_between_t1_t2
        hΓ ht1j' hjt2
    · have ht2j : C.t2 < j := lt_of_not_ge hjt2
      rw [ProfileData.muBC, C.memberships_muB_eq_zero_of_between_t2_t3 ht2j hjt3, zero_add]
      exact C.futureCount_mul_hatGPrime_eq_muC_mul_tailBudgetPrime_add_tau_of_between_t2_t3
        hΓ ht2j hjt3
  · rw [C.muBC_eq_at_t1]
    exact C.futureCount_mul_hatGPrime_eq_muB_mul_tailBudgetPrime_add_tau_at_t1_of_ne_last
      hγlo hγhi hθpos hjlast

omit [NeZero n] in
theorem tau_pos_of_theta_pos (P : DualProgram n)
    (hγlo : 1 ≤ P.Mcoeff) (hθpos : 0 < P.theta) :
    0 < P.tau := by
  rw [← P.epsilon_add_theta_eq_tau]
  linarith [P.epsilon_nonneg_of_one_le_Mcoeff hγlo]

omit [NeZero n] in
theorem epsilon_le_28_div_125_of_le_153_div_125 (P : DualProgram n)
    (hγhi : P.Mcoeff ≤ (153 : ℝ) / 125) :
    P.epsilon ≤ (28 : ℝ) / 125 := by
  dsimp [DualProgram.epsilon, DualProgram.Mcoeffmone]
  linarith

omit [NeZero n] in
theorem tau_le_barTau_of_le_153_div_125 (P : DualProgram n)
    (hγlo : 1 ≤ P.Mcoeff) (hγhi : P.Mcoeff ≤ (153 : ℝ) / 125) :
    P.tau ≤ P.barTau := by
  have hεnonneg : 0 ≤ P.epsilon := P.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hεle : P.epsilon ≤ (28 : ℝ) / 125 := epsilon_le_28_div_125_of_le_153_div_125 P hγhi
  dsimp [DualProgram.tau, DualProgram.barTau]
  nlinarith

omit [NeZero n] in
theorem tau_lt_barTau_of_le_153_div_125 (P : DualProgram n)
    (hγlo : 1 ≤ P.Mcoeff) (hγhi : P.Mcoeff ≤ (153 : ℝ) / 125) :
    P.tau < P.barTau := by
  have hεnonneg : 0 ≤ P.epsilon := P.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hεle : P.epsilon ≤ (28 : ℝ) / 125 := epsilon_le_28_div_125_of_le_153_div_125 P hγhi
  dsimp [DualProgram.tau, DualProgram.barTau]
  nlinarith

omit [NeZero n] in
theorem function_tau_bound (P : DualProgram n)
    (hγlo : 1 ≤ P.Mcoeff) (hγhi : P.Mcoeff ≤ (153 : ℝ) / 125) (hθpos : 0 < P.theta)
    {x : ℝ} (hx_nonneg : 0 ≤ x) (hx_le_barTau : x ≤ P.barTau) :
    posPart (1 - x / P.theta) ≤ (P.barTau - x) / (x + P.tau) := by
  have hεnonneg : 0 ≤ P.epsilon := P.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hεle : P.epsilon ≤ (28 : ℝ) / 125 := epsilon_le_28_div_125_of_le_153_div_125 P hγhi
  have hτpos : 0 < P.tau := tau_pos_of_theta_pos P hγlo hθpos
  have hdenpos : 0 < x + P.tau := by
    linarith
  by_cases hxθ : P.theta ≤ x
  · have hlhs : posPart (1 - x / P.theta) = 0 := by
      apply posPart_of_nonpos
      have hdiv : 1 ≤ x / P.theta := (one_le_div hθpos).2 hxθ
      linarith
    have hrhs_nonneg : 0 ≤ (P.barTau - x) / (x + P.tau) := by
      exact div_nonneg (sub_nonneg.mpr hx_le_barTau) (le_of_lt hdenpos)
    rw [hlhs]
    linarith
  · have hxθ' : x < P.theta := lt_of_not_ge hxθ
    have hlhs :
        posPart (1 - x / P.theta) = 1 - x / P.theta := by
      apply posPart_of_nonneg
      have hdiv : x / P.theta < 1 := (div_lt_one hθpos).2 hxθ'
      linarith
    rw [hlhs]
    have hθne : P.theta ≠ 0 := ne_of_gt hθpos
    have hquad : -(P.epsilon ^ 4) / 4 ≤ x ^ 2 - P.epsilon ^ 2 * x := by
      have hsq : 0 ≤ (2 * x - P.epsilon ^ 2) ^ 2 := by positivity
      nlinarith
    have hpoly :
        0 ≤ P.epsilon - 3 * P.epsilon ^ 2 - 6 * P.epsilon ^ 3 -
          ((9 : ℝ) / 4) * P.epsilon ^ 4 := by
      have hg_le :
          9 * P.epsilon ^ 3 + 24 * P.epsilon ^ 2 + 12 * P.epsilon - 4 ≤
            9 * ((28 : ℝ) / 125) ^ 3 + 24 * ((28 : ℝ) / 125) ^ 2 +
              12 * ((28 : ℝ) / 125) - 4 := by
        nlinarith
      have hg_nonpos : 9 * P.epsilon ^ 3 + 24 * P.epsilon ^ 2 + 12 * P.epsilon - 4 ≤ 0 := by
        norm_num at hg_le ⊢
        linarith
      nlinarith [hεnonneg, hg_nonpos]
    have hcross :
        (P.theta - x) * (x + P.tau) ≤ (P.barTau - x) * P.theta := by
      have hmain :
          0 ≤ x ^ 2 - P.epsilon ^ 2 * x - 2 * P.epsilon ^ 4 - 6 * P.epsilon ^ 3 -
              3 * P.epsilon ^ 2 + P.epsilon := by
        linarith
      have hmain' := hmain
      dsimp [DualProgram.theta, DualProgram.tau, DualProgram.barTau] at hmain' ⊢
      nlinarith
    have hrew : 1 - x / P.theta = (P.theta - x) / P.theta := by
      field_simp [hθne]
    rw [hrew]
    field_simp [hθne]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

theorem phaseTwo_beforeBudget_t3Star_lt_barTau_of_lt_last
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ht3last : Γ.t3Star < lastIdx n) :
    C.phaseTwo.beforeBudget Γ.t3Star < I.program.barTau := by
  have hspecial : ¬ (Γ.t3Star = lastIdx n ∧ Γ.t3Star = lastIdx n) := by
    intro h
    exact (ne_of_lt ht3last) h.1
  have hafter0 : C.phaseTwo.afterBudget Γ.t3Star = 0 := by
    unfold PhaseTwoData.afterBudget tailBudget
    apply Finset.sum_eq_zero
    intro i hi
    exact C.phaseTwo.zero_above_t3 (mem_strictSuffixRange.mp hi)
  have htail0 : tailBudget C.phaseTwo.hatG2 Γ.t3Star = 0 := by
    simpa [PhaseTwoData.afterBudget] using hafter0
  have ht3ne : Γ.t3Star ≠ lastIdx n := ne_of_lt ht3last
  have hstep := C.phaseTwo.step_eq Γ.t3Star le_rfl
  have hhat :
      C.phaseTwo.hatG2 Γ.t3Star =
        (1 - Γ.muD Γ.t3Star) * I.program.tau / futureCount Γ.t3Star := by
    have hstep' :
        C.phaseTwo.hatG2 Γ.t3Star =
          (1 - Γ.muD Γ.t3Star) *
              (tailBudget C.phaseTwo.hatG2 Γ.t3Star + I.program.tau) / futureCount Γ.t3Star := by
      simpa [ht3ne, hspecial] using hstep
    simpa [htail0] using hstep'
  have hμle : Γ.muD Γ.t3Star ≤ 1 := Advice.muD_le_one_of_admissible Γ hΓ Γ.t3Star
  have hτnonneg : 0 ≤ I.program.tau := I.program.tau_nonneg_of_one_le_Mcoeff hγlo
  have hnum_nonneg : 0 ≤ (1 - Γ.muD Γ.t3Star) * I.program.tau := by
    have h1μ : 0 ≤ 1 - Γ.muD Γ.t3Star := sub_nonneg.mpr hμle
    exact mul_nonneg h1μ hτnonneg
  have hnat : 0 < futureCountNat Γ.t3Star := by
    have ht3val : Γ.t3Star.1 < Nat.pred n := Fin.lt_def.mp ht3last
    have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
    have hsucc : Γ.t3Star.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt ht3val) hpredlt
    exact Nat.sub_pos_of_lt hsucc
  have hfcge1 : (1 : ℝ) ≤ futureCount Γ.t3Star := by
    change (1 : ℝ) ≤ (futureCountNat Γ.t3Star : ℝ)
    exact_mod_cast Nat.succ_le_of_lt hnat
  have hhat_le_tau : C.phaseTwo.hatG2 Γ.t3Star ≤ I.program.tau := by
    rw [hhat]
    have hdivle :
        ((1 - Γ.muD Γ.t3Star) * I.program.tau) / futureCount Γ.t3Star ≤
          (1 - Γ.muD Γ.t3Star) * I.program.tau := by
      exact div_le_self hnum_nonneg hfcge1
    have hnum_le_tau : (1 - Γ.muD Γ.t3Star) * I.program.tau ≤ I.program.tau := by
      have hμnonneg : 0 ≤ Γ.muD Γ.t3Star := Advice.muD_nonneg_of_admissible Γ hΓ Γ.t3Star
      have h1μle1 : 1 - Γ.muD Γ.t3Star ≤ 1 := by linarith
      simpa using mul_le_mul_of_nonneg_right h1μle1 hτnonneg
    exact le_trans hdivle hnum_le_tau
  have htau_bar : I.program.tau < I.program.barTau :=
    tau_lt_barTau_of_le_153_div_125 I.program hγlo hγhi
  rw [C.phaseTwo.beforeBudget_eq_self_add_afterBudget Γ.t3Star, hafter0]
  linarith

theorem t1_lt_t3Star_of_t3_lt_last
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht3last : Γ.t3Star < lastIdx n) :
    C.t1 < Γ.t3Star := by
  have ht1le : C.t1 ≤ Γ.t3Star := C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos
  by_contra ht1t3
  have ht3le : Γ.t3Star ≤ C.t1 := not_lt.mp ht1t3
  have ht1eq : C.t1 = Γ.t3Star := le_antisymm ht1le ht3le
  have hbar : I.program.barTau ≤ C.phaseTwo.beforeBudget C.t1 := C.t1_beforeBudget_ge_barTau
  have hlt :
      C.phaseTwo.beforeBudget Γ.t3Star < I.program.barTau :=
    C.phaseTwo_beforeBudget_t3Star_lt_barTau_of_lt_last hΓ hγlo hγhi ht3last
  exact (not_lt_of_ge hbar) (ht1eq ▸ hlt)

theorem shiftedPoolValue_eq_poolValue_at_t3Star
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    C.shiftedPoolValue AUX Γ.t3Star = C.poolValue AUX Γ.t3Star := by
  by_cases ht3last : Γ.t3Star < lastIdx n
  · have ht1t3 : C.t1 < Γ.t3Star :=
      C.t1_lt_t3Star_of_t3_lt_last hΓ hγlo hγhi hθpos ht3last
    exact C.shiftedPoolValue_eq_poolValue_of_t1_lt AUX hΓ hγlo hγhi ht1t3
  · have ht3eq : Γ.t3Star = lastIdx n := le_antisymm (le_lastIdx _) (not_lt.mp ht3last)
    simpa [ht3eq] using C.shiftedPoolValue_eq_poolValue_at_last AUX hΓ hγlo hγhi

def phaseTwoWeight (C : ProfileData I Γ) (j l : Idx n) : ℝ :=
  if j < l then
    Γ.muD l * (tailBudget C.hatG j + I.program.tau) / (beforeBudget C.hatG l + I.program.tau)
  else
    0

theorem beforeBudget_eq_step_of_t1_lt
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hθpos : 0 < I.program.theta)
    {i : Idx n} (ht1i : C.t1 < i) (hilast : i ≠ lastIdx n) :
    beforeBudget C.hatG i + I.program.tau =
      (tailBudget C.hatG i + I.program.tau) * ((futureCount i + 1 - Γ.muD i) / futureCount i) := by
  have _ := hγlo
  have _ := hθpos
  have hfcpos : 0 < futureCount i := futureCount_pos_of_ne_last i hilast
  have hfcne : futureCount i ≠ 0 := ne_of_gt hfcpos
  have hhat :
      C.hatG i =
        ((1 - Γ.muD i) * (tailBudget C.hatG i + I.program.tau)) / futureCount i := by
    apply (eq_div_iff hfcne).2
    rw [mul_comm]
    exact C.futureCount_mul_hatG_eq_one_sub_muD_mul_tailBudget_add_tau_of_t1_lt hΓ ht1i
  calc
    beforeBudget C.hatG i + I.program.tau
      = C.hatG i + (tailBudget C.hatG i + I.program.tau) := by
          rw [beforeBudget_eq_self_add_tail]
          ring
    _ =
        (((1 - Γ.muD i) * (tailBudget C.hatG i + I.program.tau)) / futureCount i) +
          (tailBudget C.hatG i + I.program.tau) := by
            rw [hhat]
    _ =
        (tailBudget C.hatG i + I.program.tau) *
          ((futureCount i + 1 - Γ.muD i) / futureCount i) := by
          field_simp [hfcne]
          ring

theorem tailBudget_predIdx_eq_step_of_t1_lt
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hθpos : 0 < I.program.theta)
    {i : Idx n} (ht1i : C.t1 < i) (hi0 : 0 < i.1) (hilast : i ≠ lastIdx n) :
    tailBudget C.hatG (predIdx hi0) + I.program.tau =
      (tailBudget C.hatG i + I.program.tau) *
        ((futureCount (predIdx hi0) - Γ.muD i) / futureCount i) := by
  rw [tailBudget_predIdx_eq_beforeBudget C.hatG hi0, futureCount_predIdx hi0]
  exact C.beforeBudget_eq_step_of_t1_lt hΓ hγlo hθpos ht1i hilast

omit [NeZero n] in
theorem intervalRange_eq_insert_pred
    {j i : Idx n} (hji : j < i) (hi0 : 0 < i.1) :
    intervalRange j i = insert i (intervalRange j (predIdx hi0)) := by
  ext p
  constructor
  · intro hp
    rcases mem_intervalRange.mp hp with ⟨hjp, hpi⟩
    by_cases hpeq : p = i
    · simp [hpeq]
    · have hplt : p < i := lt_of_le_of_ne hpi hpeq
      have hppred : p ≤ predIdx hi0 := by
        exact Fin.le_def.mpr (by
          have hpvals := Fin.lt_def.mp hplt
          change p.1 ≤ i.1 - 1
          omega)
      simp [hpeq, mem_intervalRange.mpr ⟨hjp, hppred⟩]
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp'
    · exact mem_intervalRange.mpr ⟨le_of_lt hji, le_rfl⟩
    · rcases mem_intervalRange.mp hp' with ⟨hjp, hppred⟩
      exact mem_intervalRange.mpr ⟨hjp, le_trans hppred (le_of_lt (predIdx_lt hi0))⟩

theorem tailBudget_eq_phaseTwo_product
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hθpos : 0 < I.program.theta)
    {j i : Idx n} (ht1j : C.t1 ≤ j) (hji : j ≤ i)
    (hit3 : i ≤ Γ.t3Star) (hilast : i < lastIdx n) :
    tailBudget C.hatG j + I.program.tau =
      (tailBudget C.hatG i + I.program.tau) *
        ((futureCount j -
            Finset.sum (intervalRange j i) (fun l => C.phaseTwoWeight j l)) / futureCount i) := by
  let P : ℕ → Prop := fun d =>
    ∀ {j i : Idx n},
      C.t1 ≤ j → j ≤ i → i ≤ Γ.t3Star → i < lastIdx n → i.1 - j.1 = d →
        tailBudget C.hatG j + I.program.tau =
          (tailBudget C.hatG i + I.program.tau) *
            ((futureCount j -
                Finset.sum (intervalRange j i) (fun l => C.phaseTwoWeight j l)) / futureCount i)
  have hP : ∀ d, P d := by
    intro d
    induction d with
    | zero =>
        intro j i ht1j hji hit3 hilast hdiff
        have hij : j = i := by
          apply Fin.ext
          have hji' : j.1 ≤ i.1 := Fin.le_def.mp hji
          omega
        subst i
        have hfcne : futureCount j ≠ 0 := by
          exact ne_of_gt (futureCount_pos_of_ne_last j (ne_of_lt hilast))
        have hsum :
            Finset.sum (intervalRange j j) (fun l => C.phaseTwoWeight j l) = 0 := by
          have hset : intervalRange j j = {j} := by
            ext l
            constructor
            · intro hl
              rcases mem_intervalRange.mp hl with ⟨hjl, hlj⟩
              exact Finset.mem_singleton.mpr (le_antisymm hlj hjl)
            · intro hl
              rw [Finset.mem_singleton.mp hl]
              exact mem_intervalRange.mpr ⟨le_rfl, le_rfl⟩
          rw [hset]
          simp [ProfileData.phaseTwoWeight]
        rw [hsum]
        have hdiv : (futureCount j - 0) / futureCount j = (1 : ℝ) := by
          rw [sub_zero, div_self hfcne]
        rw [hdiv, mul_one]
    | succ d ih =>
        intro j i ht1j hji hit3 hilast hdiff
        have hjlti : j < i := by
          apply Fin.lt_def.mpr
          omega
        have hi0 : 0 < i.1 := by
          omega
        let im1 : Idx n := predIdx hi0
        have him1_lt_i : im1 < i := predIdx_lt hi0
        have hjim1 : j ≤ im1 := by
          exact Fin.le_def.mpr (by
            have hvals : j.1 < i.1 := Fin.lt_def.mp hjlti
            change j.1 ≤ i.1 - 1
            omega)
        have him1t3 : im1 ≤ Γ.t3Star := le_trans (le_of_lt him1_lt_i) hit3
        have him1last : im1 < lastIdx n := lt_of_le_of_lt (le_of_lt him1_lt_i) hilast
        have hdiff' : im1.1 - j.1 = d := by
          change (i.1 - 1) - j.1 = d
          omega
        have hprev :=
          ih ht1j hjim1 him1t3 him1last hdiff'
        have hstep :=
          C.tailBudget_predIdx_eq_step_of_t1_lt hΓ hγlo hθpos
            (lt_of_le_of_lt ht1j hjlti) hi0 (ne_of_lt hilast)
        let zeta : ℝ :=
          futureCount j -
            Finset.sum (intervalRange j im1) (fun l => C.phaseTwoWeight j l)
        have hi_not_mem : i ∉ intervalRange j im1 := by
          intro hi_mem
          rcases mem_intervalRange.mp hi_mem with ⟨_, hile⟩
          exact (not_le_of_gt him1_lt_i) hile
        have hsum :
            Finset.sum (intervalRange j i) (fun l => C.phaseTwoWeight j l) =
              Finset.sum (intervalRange j im1) (fun l => C.phaseTwoWeight j l) +
                C.phaseTwoWeight j i := by
          have hset : intervalRange j i = insert i (intervalRange j im1) :=
            intervalRange_eq_insert_pred hjlti hi0
          rw [hset, Finset.sum_insert hi_not_mem]
          ring
        have hweighti :
            C.phaseTwoWeight j i =
              Γ.muD i * (tailBudget C.hatG j + I.program.tau) /
                (beforeBudget C.hatG i + I.program.tau) := by
          simp [ProfileData.phaseTwoWeight, hjlti]
        have hfcipred_pos : 0 < futureCount im1 :=
          futureCount_pos_of_ne_last im1 (ne_of_lt him1last)
        have hfcipred_ne : futureCount im1 ≠ 0 := ne_of_gt hfcipred_pos
        have hfcine : futureCount i ≠ 0 := by
          exact ne_of_gt (futureCount_pos_of_ne_last i (ne_of_lt hilast))
        have hτpos : 0 < I.program.tau := tau_pos_of_theta_pos I.program hγlo hθpos
        have htail_nonneg : 0 ≤ tailBudget C.hatG im1 :=
          C.tailBudget_nonneg_of_t1_le (le_trans ht1j hjim1)
        have hBne : tailBudget C.hatG im1 + I.program.tau ≠ 0 := by
          linarith
        have hbefore :
            beforeBudget C.hatG i + I.program.tau =
              tailBudget C.hatG im1 + I.program.tau := by
          dsimp [im1]
          rw [tailBudget_predIdx_eq_beforeBudget C.hatG hi0]
        have hbefore_ne : beforeBudget C.hatG i + I.program.tau ≠ 0 := by
          rw [hbefore]
          exact hBne
        have htaili_nonneg : 0 ≤ tailBudget C.hatG i := by
          exact C.tailBudget_nonneg_of_t1_le (le_trans ht1j hji)
        have hBi_ne : tailBudget C.hatG i + I.program.tau ≠ 0 := by
          linarith
        have hratio :
            (tailBudget C.hatG j + I.program.tau) / (tailBudget C.hatG im1 + I.program.tau) =
              zeta / futureCount im1 := by
          rw [hprev]
          simpa [zeta] using (by
            field_simp [hBne, hfcipred_ne])
        have hstep' :
            tailBudget C.hatG im1 + I.program.tau =
              (tailBudget C.hatG i + I.program.tau) *
                ((futureCount im1 - Γ.muD i) / futureCount i) := by
          simpa [im1] using hstep
        calc
          tailBudget C.hatG j + I.program.tau
            = (tailBudget C.hatG im1 + I.program.tau) * (zeta / futureCount im1) := by
                simpa [zeta] using hprev
          _ = (tailBudget C.hatG i + I.program.tau) *
                (((futureCount im1 - Γ.muD i) / futureCount i) * (zeta / futureCount im1)) := by
                  rw [hstep']
                  ring
          _ = (tailBudget C.hatG i + I.program.tau) *
                ((zeta - Γ.muD i * (zeta / futureCount im1)) / futureCount i) := by
                  field_simp [hfcine, hfcipred_ne]
          _ = (tailBudget C.hatG i + I.program.tau) *
                ((zeta - Γ.muD i * ((tailBudget C.hatG j + I.program.tau) /
                    (tailBudget C.hatG im1 + I.program.tau))) / futureCount i) := by
                  rw [← hratio]
          _ = (tailBudget C.hatG i + I.program.tau) *
                ((zeta - Γ.muD i * ((tailBudget C.hatG j + I.program.tau) /
                    (beforeBudget C.hatG i + I.program.tau))) / futureCount i) := by
                  rw [← hbefore]
          _ = (tailBudget C.hatG i + I.program.tau) *
                ((futureCount j -
                    Finset.sum (intervalRange j i) (fun l => C.phaseTwoWeight j l)) /
                  futureCount i) := by
                  rw [mul_eq_mul_left_iff]
                  left
                  simp [zeta, hsum, hweighti]
                  ring_nf
  exact hP (i.1 - j.1) ht1j hji hit3 hilast rfl

theorem muBC_add_muD_eq_one_of_t1_lt_of_le_t3
    (C : ProfileData I Γ) {j : Idx n} (ht1j : C.t1 < j) (hjt3 : j ≤ Γ.t3Star) :
    C.muBC j + Γ.muD j = 1 := by
  by_cases hjt2 : j ≤ C.t2
  · rw [C.muBC_eq_of_between_t1_t2 ht1j hjt2]
    ring
  · have ht2j : C.t2 < j := lt_of_not_ge hjt2
    rw [C.muBC_eq_of_between_t2_t3 ht2j hjt3]
    ring

omit [NeZero n] in
theorem sum_interval_strict_one_eq_futureCount_sub {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => if j < p then (1 : ℝ) else 0) =
      futureCount j - futureCount i := by
  rw [← Finset.sum_filter]
  have hset : (intervalRange j i).filter (fun p => j < p) = prefixRange i \ prefixRange j := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpInt, hjp⟩
      rcases mem_intervalRange.mp hpInt with ⟨hjp', hpi⟩
      exact Finset.mem_sdiff.mpr
        ⟨mem_prefixRange.mpr hpi,
          fun hpj => (not_lt_of_ge (mem_prefixRange.mp hpj)) hjp⟩
    · intro hp
      rcases Finset.mem_sdiff.mp hp with ⟨hpi, hpj⟩
      have hnpj : ¬ p ≤ j := by
        intro hpj'
        exact hpj (mem_prefixRange.mpr hpj')
      exact Finset.mem_filter.mpr ⟨mem_intervalRange.mpr
        ⟨le_of_lt (lt_of_not_ge hnpj), mem_prefixRange.mp hpi⟩, lt_of_not_ge hnpj⟩
  have hsubset : prefixRange j ⊆ prefixRange i := by
    intro p hp
    exact mem_prefixRange.mpr (le_trans (mem_prefixRange.mp hp) hji)
  rw [hset, Finset.sum_const, nsmul_eq_mul]
  simp only [mul_one]
  rw [Finset.card_sdiff]
  have hinter : prefixRange j ∩ prefixRange i = prefixRange j := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_inter.mp hp).1
    · intro hp
      exact Finset.mem_inter.mpr ⟨hp, hsubset hp⟩
  rw [hinter, card_prefixRange, card_prefixRange]
  have hnat : i.1.succ - j.1.succ = futureCountNat j - futureCountNat i := by
    unfold futureCountNat
    omega
  have hfcji : futureCountNat i ≤ futureCountNat j := by
    have hji' : j.1 ≤ i.1 := Fin.le_def.mp hji
    unfold futureCountNat
    omega
  rw [futureCount, futureCount, ← Nat.cast_sub hfcji]
  exact_mod_cast hnat

theorem sum_interval_strict_muBC_add_muD_eq_futureCount_sub
    (C : ProfileData I Γ) {j i : Idx n}
    (ht1j : C.t1 ≤ j) (hji : j ≤ i) (hit3 : i ≤ Γ.t3Star) :
    Finset.sum (intervalRange j i) (fun p => if j < p then (C.muBC p + Γ.muD p) else 0) =
      futureCount j - futureCount i := by
  calc
    Finset.sum (intervalRange j i) (fun p => if j < p then (C.muBC p + Γ.muD p) else 0)
      = Finset.sum (intervalRange j i) (fun p => if j < p then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hjp : j < p
          · have ht1p : C.t1 < p := lt_of_le_of_lt ht1j hjp
            have hpt3 : p ≤ Γ.t3Star := le_trans (mem_intervalRange.mp hp).2 hit3
            rw [if_pos hjp, if_pos hjp, C.muBC_add_muD_eq_one_of_t1_lt_of_le_t3 ht1p hpt3]
          · simp [hjp]
    _ = futureCount j - futureCount i := sum_interval_strict_one_eq_futureCount_sub hji

theorem sum_interval_strict_muBC_eq_futureCount_sub_muD
    (C : ProfileData I Γ) {j i : Idx n}
    (ht1j : C.t1 ≤ j) (hji : j ≤ i) (hit3 : i ≤ Γ.t3Star) :
    Finset.sum (intervalRange j i) (fun p => if j < p then C.muBC p else 0) =
      futureCount j - futureCount i -
        Finset.sum (intervalRange j i) (fun p => if j < p then Γ.muD p else 0) := by
  have hsum := C.sum_interval_strict_muBC_add_muD_eq_futureCount_sub ht1j hji hit3
  have hsplit :
      Finset.sum (intervalRange j i) (fun p => if j < p then (C.muBC p + Γ.muD p) else 0) =
        Finset.sum (intervalRange j i) (fun p => if j < p then C.muBC p else 0) +
          Finset.sum (intervalRange j i) (fun p => if j < p then Γ.muD p else 0) := by
    calc
      Finset.sum (intervalRange j i) (fun p => if j < p then (C.muBC p + Γ.muD p) else 0)
        = Finset.sum (intervalRange j i)
            (fun p => (if j < p then C.muBC p else 0) + (if j < p then Γ.muD p else 0)) := by
              apply Finset.sum_congr rfl
              intro p hp
              by_cases hjp : j < p <;> simp [hjp]
      _ =
          Finset.sum (intervalRange j i) (fun p => if j < p then C.muBC p else 0) +
            Finset.sum (intervalRange j i) (fun p => if j < p then Γ.muD p else 0) := by
              rw [Finset.sum_add_distrib]
  rw [hsplit] at hsum
  linarith

theorem tailBudget_add_tau_le_phaseTwo_target
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (ht1j : C.t1 ≤ j) (hji : j ≤ i)
    (hit3 : i ≤ Γ.t3Star) (hilast : i < lastIdx n) :
    tailBudget C.hatG i + I.program.tau ≤
      (tailBudget C.hatG j + I.program.tau) *
        ((futureCount j -
            Finset.sum (intervalRange j i) (fun p => if j < p then C.muBC p else 0)) /
          futureCount j) := by
  have hhatnonneg := C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hτpos : 0 < I.program.tau := tau_pos_of_theta_pos I.program hγlo hθpos
  have hfcipos : 0 < futureCount i := futureCount_pos_of_ne_last i (ne_of_lt hilast)
  have hfcine : futureCount i ≠ 0 := ne_of_gt hfcipos
  have hjlast : j < lastIdx n := lt_of_le_of_lt hji hilast
  have hfcjpos : 0 < futureCount j := futureCount_pos_of_ne_last j (ne_of_lt hjlast)
  have hfcjne : futureCount j ≠ 0 := ne_of_gt hfcjpos
  have hBi_nonneg : 0 ≤ tailBudget C.hatG i + I.program.tau := by
    have htaili : 0 ≤ tailBudget C.hatG i := C.tailBudget_nonneg_of_t1_le (le_trans ht1j hji)
    linarith
  have hBj_nonneg : 0 ≤ tailBudget C.hatG j + I.program.tau := by
    have htailj : 0 ≤ tailBudget C.hatG j := C.tailBudget_nonneg_of_t1_le ht1j
    linarith
  have hprod := C.tailBudget_eq_phaseTwo_product hΓ hγlo hθpos ht1j hji hit3 hilast
  have hprod_mul := hprod
  field_simp [hfcine] at hprod_mul
  have hweight_bound :
      ∀ l ∈ intervalRange j i,
        (tailBudget C.hatG i + I.program.tau) * C.phaseTwoWeight j l ≤
          (tailBudget C.hatG j + I.program.tau) * (if j < l then Γ.muD l else 0) := by
    intro l hl
    by_cases hjl : j < l
    · have hli : l ≤ i := (mem_intervalRange.mp hl).2
      have ht1l : C.t1 < l := lt_of_le_of_lt ht1j hjl
      have hbefore_nonneg : 0 ≤ beforeBudget C.hatG l := by
        rw [C.beforeBudget_eq_phaseTwo_beforeBudget_of_lt_t1 ht1l]
        exact C.phaseTwo.beforeBudget_nonneg l
      have hdenpos : 0 < beforeBudget C.hatG l + I.program.tau := by
        linarith
      have htail_le : tailBudget C.hatG i ≤ tailBudget C.hatG l :=
        tailBudget_antitone_of_nonneg hhatnonneg hli
      have hBi_le_den :
          tailBudget C.hatG i + I.program.tau ≤ beforeBudget C.hatG l + I.program.tau := by
        have htail_le_before : tailBudget C.hatG l ≤ beforeBudget C.hatG l := by
          rw [beforeBudget_eq_self_add_tail]
          have hhatl : 0 ≤ C.hatG l := hhatnonneg l
          linarith
        linarith
      have hμBj_nonneg : 0 ≤ Γ.muD l * (tailBudget C.hatG j + I.program.tau) := by
        exact mul_nonneg (Advice.muD_nonneg_of_admissible Γ hΓ l) hBj_nonneg
      have hfrac_le_one :
          (tailBudget C.hatG i + I.program.tau) /
              (beforeBudget C.hatG l + I.program.tau) ≤ 1 := by
        exact (div_le_one hdenpos).2 hBi_le_den
      calc
        (tailBudget C.hatG i + I.program.tau) * C.phaseTwoWeight j l
          = ((tailBudget C.hatG i + I.program.tau) / (beforeBudget C.hatG l + I.program.tau)) *
              (Γ.muD l * (tailBudget C.hatG j + I.program.tau)) := by
                simp [ProfileData.phaseTwoWeight, hjl]
                ring
        _ ≤ 1 * (Γ.muD l * (tailBudget C.hatG j + I.program.tau)) := by
              exact mul_le_mul_of_nonneg_right hfrac_le_one hμBj_nonneg
        _ = (tailBudget C.hatG j + I.program.tau) * (if j < l then Γ.muD l else 0) := by
              simp [hjl]
              ring
    · simp [ProfileData.phaseTwoWeight, hjl]
  have hsum_bound :
      (tailBudget C.hatG i + I.program.tau) *
          Finset.sum (intervalRange j i) (fun l => C.phaseTwoWeight j l)
        ≤
      (tailBudget C.hatG j + I.program.tau) *
          Finset.sum (intervalRange j i) (fun l => if j < l then Γ.muD l else 0) := by
    calc
      (tailBudget C.hatG i + I.program.tau) *
          Finset.sum (intervalRange j i) (fun l => C.phaseTwoWeight j l)
        = Finset.sum (intervalRange j i)
            (fun l => (tailBudget C.hatG i + I.program.tau) * C.phaseTwoWeight j l) := by
              rw [Finset.mul_sum]
      _ ≤ Finset.sum (intervalRange j i)
            (fun l => (tailBudget C.hatG j + I.program.tau) * (if j < l then Γ.muD l else 0)) := by
              apply Finset.sum_le_sum
              intro l hl
              exact hweight_bound l hl
      _ =
          (tailBudget C.hatG j + I.program.tau) *
            Finset.sum (intervalRange j i) (fun l => if j < l then Γ.muD l else 0) := by
              rw [Finset.mul_sum]
  have hmain :
      (tailBudget C.hatG i + I.program.tau) * futureCount j ≤
        (tailBudget C.hatG j + I.program.tau) *
          (futureCount i +
            Finset.sum (intervalRange j i) (fun l => if j < l then Γ.muD l else 0)) := by
    have hcalc :
        (tailBudget C.hatG i + I.program.tau) * futureCount j =
          (tailBudget C.hatG j + I.program.tau) * futureCount i +
            (tailBudget C.hatG i + I.program.tau) *
              Finset.sum (intervalRange j i) (fun l => C.phaseTwoWeight j l) := by
      linarith
    calc
      (tailBudget C.hatG i + I.program.tau) * futureCount j
        = (tailBudget C.hatG j + I.program.tau) * futureCount i +
            (tailBudget C.hatG i + I.program.tau) *
              Finset.sum (intervalRange j i) (fun l => C.phaseTwoWeight j l) := hcalc
      _ ≤ (tailBudget C.hatG j + I.program.tau) * futureCount i +
            (tailBudget C.hatG j + I.program.tau) *
              Finset.sum (intervalRange j i) (fun l => if j < l then Γ.muD l else 0) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hsum_bound ((tailBudget C.hatG j + I.program.tau) * futureCount i)
      _ = (tailBudget C.hatG j + I.program.tau) *
            (futureCount i +
              Finset.sum (intervalRange j i) (fun l => if j < l then Γ.muD l else 0)) := by
              ring
  have hrewrite :
      futureCount i + Finset.sum (intervalRange j i) (fun l => if j < l then Γ.muD l else 0) =
        futureCount j -
          Finset.sum (intervalRange j i) (fun l => if j < l then C.muBC l else 0) := by
    have hsum := C.sum_interval_strict_muBC_eq_futureCount_sub_muD ht1j hji hit3
    linarith
  rw [show
      (tailBudget C.hatG j + I.program.tau) *
          ((futureCount j -
              Finset.sum (intervalRange j i) (fun p => if j < p then C.muBC p else 0)) /
            futureCount j) =
        ((tailBudget C.hatG j + I.program.tau) *
            (futureCount j -
              Finset.sum (intervalRange j i) (fun p => if j < p then C.muBC p else 0))) /
          futureCount j by ring]
  exact (le_div_iff₀ hfcjpos).2 (by simpa [hrewrite] using hmain)

theorem phaseTwoTerm_nonneg
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (ht1j : C.t1 ≤ j) (hji : j ≤ i) (hit3 : i ≤ Γ.t3Star)
    (hilast : i < lastIdx n) :
    0 ≤
      C.muBC j * (tailBudget C.hatG j - tailBudget C.hatG i) -
        C.hatGPrime j *
          Finset.sum (intervalRange j i) (fun p => if j < p then C.muBC p else 0) := by
  let S : ℝ := Finset.sum (intervalRange j i) (fun p => if j < p then C.muBC p else 0)
  have hμnonneg : 0 ≤ C.muBC j := C.muBC_nonneg hΓ j
  have hjlast : j < lastIdx n := lt_of_le_of_lt hji hilast
  have hfcjpos : 0 < futureCount j := futureCount_pos_of_ne_last j (ne_of_lt hjlast)
  have hfcjne : futureCount j ≠ 0 := ne_of_gt hfcjpos
  have hphase :=
    C.tailBudget_add_tau_le_phaseTwo_target hΓ hγlo hγhi hθpos ht1j hji hit3 hilast
  have hmul :
      C.muBC j * (tailBudget C.hatG i + I.program.tau) ≤
        C.muBC j *
          ((tailBudget C.hatG j + I.program.tau) * ((futureCount j - S) / futureCount j)) := by
    exact mul_le_mul_of_nonneg_left hphase hμnonneg
  have hhatprime :
      futureCount j * C.hatGPrime j =
        C.muBC j * (tailBudget C.hatG j + I.program.tau) := by
    have hjt3 : j ≤ Γ.t3Star := le_trans hji hit3
    simpa [C.tailBudgetPrime_eq_tailBudget_of_t1_le ht1j] using
      C.futureCount_mul_hatGPrime_eq_muBC_mul_tailBudgetPrime_add_tau
        hΓ hγlo hγhi hθpos ht1j hjt3 (ne_of_lt hjlast)
  have hrewrite_rhs :
      C.muBC j *
          ((tailBudget C.hatG j + I.program.tau) * ((futureCount j - S) / futureCount j)) =
        C.hatGPrime j * (futureCount j - S) := by
    calc
      C.muBC j *
          ((tailBudget C.hatG j + I.program.tau) * ((futureCount j - S) / futureCount j))
        =
            (C.muBC j * (tailBudget C.hatG j + I.program.tau)) *
              ((futureCount j - S) / futureCount j) := by
            ring
      _ = (futureCount j * C.hatGPrime j) * ((futureCount j - S) / futureCount j) := by
            rw [← hhatprime]
      _ = C.hatGPrime j * (futureCount j - S) := by
            field_simp [hfcjne]
  have hmul' :
      C.muBC j * (tailBudget C.hatG i + I.program.tau) ≤
        C.hatGPrime j * (futureCount j - S) := by
    calc
      C.muBC j * (tailBudget C.hatG i + I.program.tau)
        ≤ C.muBC j *
            ((tailBudget C.hatG j + I.program.tau) * ((futureCount j - S) / futureCount j)) := hmul
      _ = C.hatGPrime j * (futureCount j - S) := hrewrite_rhs
  have hrewrite_target :
      C.hatGPrime j * (futureCount j - S) =
        C.muBC j * (tailBudget C.hatG j + I.program.tau) - C.hatGPrime j * S := by
    calc
      C.hatGPrime j * (futureCount j - S)
        = C.hatGPrime j * futureCount j - C.hatGPrime j * S := by ring
      _ = C.muBC j * (tailBudget C.hatG j + I.program.tau) - C.hatGPrime j * S := by
            rw [mul_comm, hhatprime]
  have hfinal :
      C.muBC j * (tailBudget C.hatG i + I.program.tau) ≤
        C.muBC j * (tailBudget C.hatG j + I.program.tau) - C.hatGPrime j * S := by
    rw [← hrewrite_target]
    exact hmul'
  dsimp [S] at hfinal ⊢
  linarith

theorem hatGPrime_nonneg
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (j : Idx n) :
    0 ≤ C.hatGPrime j := by
  by_cases hj : j = C.t1
  · simp [ProfileData.hatGPrime, hj, C.boundaryHatGB_nonneg]
  · simp [ProfileData.hatGPrime, hj,
      C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi j]

theorem sum_interval_sValue_ge_muBC_tail
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {j i : Idx n} (hji : j ≤ i) :
    C.muBC j * (tailBudget C.hatG j - tailBudget C.hatG i) ≤
      Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j) := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have hA :
      0 ≤
        (C.memberships).muA j *
          Finset.sum (intervalRange j i) (fun p => C.sA AUX p j) := by
    have hA' :
        0 ≤
          Finset.sum (intervalRange j i) (fun p => (C.memberships).muA j * C.sA AUX p j) := by
      apply Finset.sum_nonneg
      intro p hp
      simpa using C.weighted_sA_nonneg H AUX p j
    simpa [Finset.mul_sum] using hA'
  have hD :
      0 ≤
        (C.memberships).muD j *
          Finset.sum (intervalRange j i) (fun p => C.sD AUX p j) := by
    rw [C.sum_interval_sD_eq AUX]
    simp
  have hεnonneg : 0 ≤ if I.firstBidTime j < i then I.program.epsilon else 0 := by
    split_ifs with hif
    · exact I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
    · simp
  have hBextra :
      0 ≤ (C.memberships).muB j * (if I.firstBidTime j < i then I.program.epsilon else 0) := by
    exact mul_nonneg (hμnonneg.2.1 j) hεnonneg
  have hCextra :
      0 ≤ (C.memberships).muC j * (if I.firstBidTime j < i then I.program.epsilon else 0) := by
    exact mul_nonneg (hμnonneg.2.2.1 j) hεnonneg
  rw [C.sum_interval_sValue_eq_membership_combo AUX, C.sum_interval_sB_eq AUX hji,
    C.sum_interval_sC_eq AUX hji, C.sum_interval_sD_eq AUX]
  dsimp [ProfileData.muBC]
  linarith

theorem sum_halfOpen_hatGPrime_eq_gap_of_t1_lt
    (C : ProfileData I Γ) {j : Idx n} (ht1j : C.t1 < j) :
    Finset.sum (halfOpenIntervalRange C.t1 j) C.hatGPrime =
      1 - beforeBudget C.hatG j - I.program.tau := by
  have ht1ne : C.t1 ≠ lastIdx n := by
    intro ht1eq
    exact (not_lt_of_ge (ht1eq ▸ le_lastIdx j)) ht1j
  calc
    Finset.sum (halfOpenIntervalRange C.t1 j) C.hatGPrime
      = C.beforeBudgetPrime C.t1 - C.beforeBudgetPrime j := by
          exact sum_halfOpen_eq_before_sub_before (hatG := C.hatGPrime) (hji := le_of_lt ht1j)
    _ = I.program.barTau - beforeBudget C.hatG j := by
          rw [C.beforeBudgetPrime_t1_eq_barTau_of_ne_last ht1ne,
            C.beforeBudgetPrime_eq_beforeBudget_of_t1_lt ht1j]
    _ = 1 - beforeBudget C.hatG j - I.program.tau := by
          simp [DualProgram.barTau]
          ring

theorem tValue_if_firstBid_eq_zero_of_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j i : Idx n} (hjt1 : j < C.t1) (hit3 : i < Γ.t3Star) :
    (if I.firstBidTime j ≤ i then C.tValue AUX (I.firstBidTime j) j else 0) = 0 := by
  have _ := hΓ
  by_cases hfi : I.firstBidTime j ≤ i
  · have hfj : I.firstBidTime j < Γ.t3Star := lt_of_le_of_lt hfi hit3
    have hμD0 : Γ.muD j = 0 := Advice.muD_eq_zero Γ hfj
    have hB0 : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_lt_t1 hjt1
    have hC0 : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_lt_t1 hjt1
    simp [hfi, ProfileData.tValue, ProfileData.tA, ProfileData.tB, ProfileData.tC,
      ProfileData.tD, hB0, hC0, hμD0]
  · simp [hfi]

theorem tValue_if_firstBid_eq_zero_at_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (hit3 : i < Γ.t3Star) :
    (if I.firstBidTime C.t1 ≤ i then C.tValue AUX (I.firstBidTime C.t1) C.t1 else 0) = 0 := by
  by_cases hfi : I.firstBidTime C.t1 ≤ i
  · have hfj : I.firstBidTime C.t1 < Γ.t3Star := lt_of_le_of_lt hfi hit3
    have hμD0 : Γ.muD C.t1 = 0 := Advice.muD_eq_zero Γ hfj
    have hC0 : (C.memberships).muC C.t1 = 0 := C.memberships_muC_eq_zero_at_t1
    have htB0 : posPart (1 - beforeBudget C.hatG C.t1 - I.program.tau) = 0 := by
      have hnonpos : 1 - beforeBudget C.hatG C.t1 - I.program.tau ≤ 0 := by
        have hbar : I.program.barTau ≤ beforeBudget C.hatG C.t1 :=
          C.beforeBudget_t1_ge_barTau hΓ hγlo hγhi
        have hbar' : 1 - I.program.tau ≤ beforeBudget C.hatG C.t1 := by
          simpa [DualProgram.barTau] using hbar
        linarith
      simp [posPart_of_nonpos hnonpos]
    simp [hfi, ProfileData.tValue, ProfileData.tA, ProfileData.tB, ProfileData.tC,
      ProfileData.tD, hC0, hμD0, htB0]
  · simp [hfi]

theorem tValue_if_firstBid_eq_muBC_gap_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j i : Idx n} (ht1j : C.t1 < j) (hji : j ≤ i) (hit3 : i < Γ.t3Star) :
    (if I.firstBidTime j ≤ i then C.tValue AUX (I.firstBidTime j) j else 0) =
      if I.firstBidTime j ≤ i then
        C.muBC j * (1 - beforeBudget C.hatG j - I.program.tau)
      else
        0 := by
  have _ := hΓ
  by_cases hfi : I.firstBidTime j ≤ i
  · have hfj : I.firstBidTime j < Γ.t3Star := lt_of_le_of_lt hfi hit3
    have hμD0 : Γ.muD j = 0 := Advice.muD_eq_zero Γ hfj
    have hgap_pos : 0 < 1 - beforeBudget C.hatG j - I.program.tau := by
      have hbar : beforeBudget C.hatG j < I.program.barTau :=
        C.beforeBudget_lt_barTau_of_lt_t1 ht1j
      have hbar' : beforeBudget C.hatG j < 1 - I.program.tau := by
        simpa [DualProgram.barTau] using hbar
      linarith
    have hgap_nonneg : 0 ≤ 1 - beforeBudget C.hatG j - I.program.tau := le_of_lt hgap_pos
    have htB :
        posPart (1 - beforeBudget C.hatG j - I.program.tau) =
          1 - beforeBudget C.hatG j - I.program.tau := by
      simp [posPart_of_nonneg hgap_nonneg]
    by_cases hjt2 : j ≤ C.t2
    · have hA0 : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_between_t1_t2 ht1j hjt2
      have hC0 : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_between_t1_t2 ht1j hjt2
      have hB1 : (C.memberships).muB j = 1 := by
        rw [C.memberships_muB_eq_of_between_t1_t2 ht1j hjt2, hμD0]
        norm_num
      rw [if_pos hfi, if_pos hfi, C.muBC_eq_of_between_t1_t2 ht1j hjt2]
      simp [ProfileData.tValue, ProfileData.tA, ProfileData.tB, ProfileData.tC,
        ProfileData.tD, hA0, hB1, hC0, hμD0, htB]
    · have ht2j : C.t2 < j := lt_of_not_ge hjt2
      have hA0 : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_between_t2_t3 ht2j
        (le_trans hji (le_of_lt hit3))
      have hB0 : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_between_t2_t3 ht2j
        (le_trans hji (le_of_lt hit3))
      have hC1 : (C.memberships).muC j = 1 := by
        rw [C.memberships_muC_eq_of_between_t2_t3 ht2j (le_trans hji (le_of_lt hit3)), hμD0]
        norm_num
      rw [if_pos hfi, if_pos hfi, C.muBC_eq_of_between_t2_t3 ht2j (le_trans hji (le_of_lt hit3))]
      simp [ProfileData.tValue, ProfileData.tA, ProfileData.tB, ProfileData.tC,
        ProfileData.tD, hA0, hB0, hC1, hμD0, htB]
  · simp [hfi]

theorem tValue_if_firstBid_le_halfOpenPrime
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {j i : Idx n} (ht1j : C.t1 ≤ j) (hji : j ≤ i) (hit3 : i < Γ.t3Star) :
    (if I.firstBidTime j ≤ i then C.tValue AUX (I.firstBidTime j) j else 0) ≤
      C.muBC j * Finset.sum (halfOpenIntervalRange C.t1 j) C.hatGPrime := by
  rcases lt_or_eq_of_le ht1j with ht1j' | rfl
  · rw [C.tValue_if_firstBid_eq_muBC_gap_of_t1_lt AUX hΓ ht1j' hji hit3]
    by_cases hfi : I.firstBidTime j ≤ i
    · rw [if_pos hfi, C.sum_halfOpen_hatGPrime_eq_gap_of_t1_lt ht1j']
    · have hμnonneg : 0 ≤ C.muBC j := C.muBC_nonneg hΓ j
      have hhatprime_nonneg : 0 ≤ Finset.sum (halfOpenIntervalRange C.t1 j) C.hatGPrime := by
        apply Finset.sum_nonneg
        intro p hp
        exact C.hatGPrime_nonneg hΓ hγlo hγhi p
      rw [if_neg hfi]
      exact mul_nonneg hμnonneg hhatprime_nonneg
  · rw [C.tValue_if_firstBid_eq_zero_at_t1 AUX hΓ hγlo hγhi hit3]
    have hempty : halfOpenIntervalRange C.t1 C.t1 = ∅ := by
      ext p
      simp [halfOpenIntervalRange]
    have hsum0 : Finset.sum (halfOpenIntervalRange C.t1 C.t1) C.hatGPrime = 0 := by
      rw [hempty]
      simp
    rw [hsum0]
    simp

omit [NeZero n] in
theorem sum_halfOpenTriangle_eq_sumByColumnFrom
    (f : Idx n → Idx n → ℝ) (j0 i : Idx n) :
    Finset.sum (intervalRange j0 i)
        (fun j => Finset.sum (halfOpenIntervalRange j0 j) (fun p => f p j)) =
      Finset.sum (intervalRange j0 i)
        (fun p => Finset.sum (intervalRange p i) (fun j => if p < j then f p j else 0)) := by
  classical
  calc
    Finset.sum (intervalRange j0 i)
        (fun j => Finset.sum (halfOpenIntervalRange j0 j) (fun p => f p j))
      = Finset.sum (intervalRange j0 i)
          (fun j => Finset.sum (intervalRange j0 i) (fun p => if p < j then f p j else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hji : j ≤ i := (mem_intervalRange.mp hj).2
            have hset :
                halfOpenIntervalRange j0 j = (intervalRange j0 i).filter (fun p => p < j) := by
              ext p
              constructor
              · intro hp
                rcases mem_halfOpenIntervalRange.mp hp with ⟨hj0p, hpj⟩
                exact Finset.mem_filter.mpr
                  ⟨mem_intervalRange.mpr ⟨hj0p, le_trans (le_of_lt hpj) hji⟩, hpj⟩
              · intro hp
                rcases Finset.mem_filter.mp hp with ⟨hpInt, hpj⟩
                exact mem_halfOpenIntervalRange.mpr ⟨(mem_intervalRange.mp hpInt).1, hpj⟩
            rw [hset, Finset.sum_filter]
    _ = Finset.sum (intervalRange j0 i)
          (fun p => Finset.sum (intervalRange j0 i) (fun j => if p < j then f p j else 0)) := by
            rw [Finset.sum_comm]
    _ = Finset.sum (intervalRange j0 i)
          (fun p => Finset.sum (intervalRange p i) (fun j => if p < j then f p j else 0)) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hj0p : j0 ≤ p := (mem_intervalRange.mp hp).1
            have hset : intervalRange p i = (intervalRange j0 i).filter (fun j => p ≤ j) := by
              ext j
              constructor
              · intro hj
                rcases mem_intervalRange.mp hj with ⟨hpj, hji⟩
                exact
                  Finset.mem_filter.mpr
                    ⟨mem_intervalRange.mpr ⟨le_trans hj0p hpj, hji⟩, hpj⟩
              · intro hj
                rcases Finset.mem_filter.mp hj with ⟨hjInt, hpj⟩
                exact mem_intervalRange.mpr ⟨hpj, (mem_intervalRange.mp hjInt).2⟩
            rw [hset, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hpj : p < j
            · simp [hpj, le_of_lt hpj]
            · by_cases hple : p ≤ j
              · have hEq : p = j := le_antisymm hple (not_lt.mp hpj)
                simp [hEq]
              · simp [hpj, hple]

theorem phaseTwo_s_lower_bound
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (ht1i : C.t1 ≤ i) :
    Finset.sum (intervalRange C.t1 i)
        (fun j => C.muBC j * (tailBudget C.hatG j - tailBudget C.hatG i)) ≤
      Finset.sum (intervalRange C.t1 i)
        (fun j => Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j)) := by
  have _ := ht1i
  apply Finset.sum_le_sum
  intro j hj
  exact C.sum_interval_sValue_ge_muBC_tail AUX hΓ hγlo hγhi (hji := (mem_intervalRange.mp hj).2)

theorem phaseTwo_t_upper_bound
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (ht1i : C.t1 ≤ i) (hit3 : i < Γ.t3Star) :
    Finset.sum (intervalRange C.t1 i)
        (fun j =>
          if I.firstBidTime j ≤ i then
            C.tValue AUX (I.firstBidTime j) j
          else
            0) ≤
      Finset.sum (intervalRange C.t1 i)
        (fun p =>
          C.hatGPrime p *
            Finset.sum (intervalRange p i) (fun j => if p < j then C.muBC j else 0)) := by
  have _ := ht1i
  have hpoint :
      Finset.sum (intervalRange C.t1 i)
          (fun j =>
            if I.firstBidTime j ≤ i then
              C.tValue AUX (I.firstBidTime j) j
            else
              0) ≤
        Finset.sum (intervalRange C.t1 i)
          (fun j => C.muBC j * Finset.sum (halfOpenIntervalRange C.t1 j) C.hatGPrime) := by
    apply Finset.sum_le_sum
    intro j hj
    exact C.tValue_if_firstBid_le_halfOpenPrime AUX hΓ hγlo hγhi
      (ht1j := (mem_intervalRange.mp hj).1) (hji := (mem_intervalRange.mp hj).2) hit3
  calc
    Finset.sum (intervalRange C.t1 i)
        (fun j =>
          if I.firstBidTime j ≤ i then
            C.tValue AUX (I.firstBidTime j) j
          else
            0)
      ≤ Finset.sum (intervalRange C.t1 i)
          (fun j => C.muBC j * Finset.sum (halfOpenIntervalRange C.t1 j) C.hatGPrime) := hpoint
    _ = Finset.sum (intervalRange C.t1 i)
          (fun j =>
            Finset.sum (halfOpenIntervalRange C.t1 j) (fun p => C.hatGPrime p * C.muBC j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            calc
              C.muBC j * Finset.sum (halfOpenIntervalRange C.t1 j) C.hatGPrime
                = Finset.sum (halfOpenIntervalRange C.t1 j) C.hatGPrime * C.muBC j := by ring
              _ =
                  Finset.sum (halfOpenIntervalRange C.t1 j)
                    (fun p => C.hatGPrime p * C.muBC j) := by
                    rw [Finset.sum_mul]
    _ = Finset.sum (intervalRange C.t1 i)
          (fun p =>
            Finset.sum (intervalRange p i)
              (fun j => if p < j then C.hatGPrime p * C.muBC j else 0)) := by
            exact
              sum_halfOpenTriangle_eq_sumByColumnFrom
                (f := fun p j => C.hatGPrime p * C.muBC j) C.t1 i
    _ = Finset.sum (intervalRange C.t1 i)
          (fun p =>
            C.hatGPrime p *
              Finset.sum (intervalRange p i) (fun j => if p < j then C.muBC j else 0)) := by
            apply Finset.sum_congr rfl
            intro p hp
            calc
              Finset.sum (intervalRange p i)
                  (fun j => if p < j then C.hatGPrime p * C.muBC j else 0)
                = Finset.sum (intervalRange p i)
                    (fun j => C.hatGPrime p * (if p < j then C.muBC j else 0)) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      by_cases hpj : p < j <;> simp [hpj]
              _ =
                  C.hatGPrime p *
                    Finset.sum (intervalRange p i) (fun j => if p < j then C.muBC j else 0) := by
                    rw [Finset.mul_sum]

theorem phaseTwo_kernel_sum_nonneg
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (ht1i : C.t1 ≤ i) (hit3 : i < Γ.t3Star) :
    0 ≤
      Finset.sum (intervalRange C.t1 i)
        (fun j =>
          C.muBC j * (tailBudget C.hatG j - tailBudget C.hatG i) -
            C.hatGPrime j *
              Finset.sum (intervalRange j i) (fun p => if j < p then C.muBC p else 0)) := by
  have _ := ht1i
  have hilast : i < lastIdx n := lt_of_lt_of_le hit3 (le_lastIdx _)
  apply Finset.sum_nonneg
  intro j hj
  exact C.phaseTwoTerm_nonneg hΓ hγlo hγhi hθpos
    (ht1j := (mem_intervalRange.mp hj).1) (hji := (mem_intervalRange.mp hj).2)
    (hit3 := le_of_lt hit3) hilast

theorem sPrefix_ge_phaseTwoColumns
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (ht1i : C.t1 ≤ i) :
    Finset.sum (intervalRange C.t1 i)
        (fun j => Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j)) ≤
      Finset.sum (prefixRange i)
        (fun j => Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j)) := by
  have _ := ht1i
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  let T : Idx n → ℝ := fun j => Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j)
  have hset : (prefixRange i).filter (fun j => C.t1 ≤ j) = intervalRange C.t1 i := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hpi, ht1j⟩
      exact mem_intervalRange.mpr ⟨ht1j, mem_prefixRange.mp hpi⟩
    · intro hj
      rcases mem_intervalRange.mp hj with ⟨ht1j, hji⟩
      exact Finset.mem_filter.mpr ⟨mem_prefixRange.mpr hji, ht1j⟩
  have hnonneg :
      0 ≤ Finset.sum ((prefixRange i).filter (fun j => ¬ C.t1 ≤ j)) T := by
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro p hp
    simpa using C.sValue_nonneg H AUX p j
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := prefixRange i) (p := fun j => C.t1 ≤ j) T
  rw [hset] at hsplit
  linarith

theorem tPrefix_eq_phaseTwoColumns
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (ht1i : C.t1 ≤ i) (hit3 : i < Γ.t3Star) :
    Finset.sum (prefixRange i)
        (fun j =>
          if I.firstBidTime j ≤ i then
            C.tValue AUX (I.firstBidTime j) j
          else
            0) =
      Finset.sum (intervalRange C.t1 i)
        (fun j =>
          if I.firstBidTime j ≤ i then
            C.tValue AUX (I.firstBidTime j) j
          else
            0) := by
  have _ := hγlo
  have _ := hγhi
  have _ := ht1i
  let T : Idx n → ℝ := fun j =>
    if I.firstBidTime j ≤ i then
      C.tValue AUX (I.firstBidTime j) j
    else
      0
  have hset : (prefixRange i).filter (fun j => C.t1 ≤ j) = intervalRange C.t1 i := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hpi, ht1j⟩
      exact mem_intervalRange.mpr ⟨ht1j, mem_prefixRange.mp hpi⟩
    · intro hj
      rcases mem_intervalRange.mp hj with ⟨ht1j, hji⟩
      exact Finset.mem_filter.mpr ⟨mem_prefixRange.mpr hji, ht1j⟩
  have hzero :
      Finset.sum ((prefixRange i).filter (fun j => ¬ C.t1 ≤ j)) T = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjt1 : j < C.t1 := lt_of_not_ge (Finset.mem_filter.mp hj).2
    exact C.tValue_if_firstBid_eq_zero_of_lt_t1 AUX hΓ hjt1 hit3
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := prefixRange i) (p := fun j => C.t1 ≤ j) T
  rw [hset, hzero, add_zero] at hsplit
  simpa [T] using hsplit.symm

theorem poolValue_nonneg_of_between_t1_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (ht1i : C.t1 < i) (hit3 : i < Γ.t3Star) :
    0 ≤ C.poolValue AUX i := by
  rw [C.poolValue_eq_rewrite AUX i]
  have hsLow := C.phaseTwo_s_lower_bound AUX hΓ hγlo hγhi (ht1i := le_of_lt ht1i)
  have htUp := C.phaseTwo_t_upper_bound AUX hΓ hγlo hγhi (ht1i := le_of_lt ht1i) hit3
  have hKernel := C.phaseTwo_kernel_sum_nonneg hΓ hγlo hγhi hθpos (ht1i := le_of_lt ht1i) hit3
  have hsPrefix :=
    C.sPrefix_ge_phaseTwoColumns AUX hΓ hγlo hγhi (ht1i := le_of_lt ht1i)
  have htPrefix :=
    C.tPrefix_eq_phaseTwoColumns AUX hΓ hγlo hγhi (ht1i := le_of_lt ht1i) hit3
  have hPhase :
      Finset.sum (intervalRange C.t1 i)
          (fun p =>
            C.hatGPrime p *
              Finset.sum (intervalRange p i) (fun j => if p < j then C.muBC j else 0)) ≤
        Finset.sum (intervalRange C.t1 i)
          (fun j => C.muBC j * (tailBudget C.hatG j - tailBudget C.hatG i)) := by
    have hKernel' := hKernel
    rw [Finset.sum_sub_distrib] at hKernel'
    linarith
  apply sub_nonneg.mpr
  rw [htPrefix]
  exact le_trans htUp (le_trans hPhase (le_trans hsLow hsPrefix))

theorem constructedDualSolution_poolCredit_nonneg_of_between_t1_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (ht1i : C.t1 < i) (hit3 : i < Γ.t3Star) :
    0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) i := by
  rw [C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX i,
    C.shiftedPoolValue_eq_poolValue_of_t1_lt AUX hΓ hγlo hγhi ht1i]
  exact C.poolValue_nonneg_of_between_t1_t3 AUX hΓ hγlo hγhi hθpos ht1i hit3

omit [NeZero n] in
theorem sum_univ_eq_prefix_add_strictSuffix
    (f : Idx n → ℝ) (k : Idx n) :
    Finset.sum Finset.univ f =
      Finset.sum (prefixRange k) f + Finset.sum (strictSuffixRange k) f := by
  classical
  have hprefix :
      prefixRange k = insert k (Finset.univ.filter fun i : Idx n => i < k) := by
    ext i
    constructor
    · intro hi
      by_cases hik : i = k
      · simp [hik]
      · have hlt_or_gt : i < k ∨ k < i := lt_or_gt_of_ne hik
        rcases hlt_or_gt with hlt | hgt
        · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨by simp, hlt⟩
        · exact False.elim ((not_le_of_gt hgt) (mem_prefixRange.mp hi))
    · intro hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact mem_prefixRange.mpr le_rfl
      · exact mem_prefixRange.mpr (le_of_lt (Finset.mem_filter.mp hi').2)
  have hsum := sum_univ_eq_filter_lt_add_self_add_strictSuffix (f := f) k
  have hprefixsum :
      Finset.sum (prefixRange k) f =
        Finset.sum (Finset.univ.filter fun i : Idx n => i < k) f + f k := by
    rw [hprefix, Finset.sum_insert]
    · ring
    · simp
  calc
    Finset.sum Finset.univ f
      = Finset.sum (Finset.univ.filter fun i : Idx n => i < k) f +
          f k + Finset.sum (strictSuffixRange k) f := hsum
    _ = Finset.sum (prefixRange k) f + Finset.sum (strictSuffixRange k) f := by
          rw [hprefixsum]

def generatedMassPrefix
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) : ℝ :=
  Finset.sum (prefixRange i) (fun p => Finset.sum Finset.univ (fun j => C.gValue AUX p j))

def totalGeneratedMass
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) : ℝ :=
  Finset.sum Finset.univ (fun p => Finset.sum Finset.univ (fun j => C.gValue AUX p j))

def generatedColumnValue
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) : ℝ :=
  Finset.sum Finset.univ (fun i => C.gValue AUX i j)

def case4BCLift
    (C : ProfileData I Γ) (j : Idx n) : ℝ :=
  if I.firstBidTime j < Γ.t3Star then
    I.program.epsilon * C.muBC j
  else
    0

def case4FrontierDeficit
    (C : ProfileData I Γ) (j : Idx n) : ℝ :=
  if I.firstBidTime j = Γ.t3Star then
    I.program.epsilon * (C.memberships).muD j * C.chi j
  else
    0

def frontierPositive
    (_C : ProfileData I Γ) : Finset (Idx n) :=
  (I.frontier Γ.t3Star).filter fun j => 0 < Γ.muD j

@[simp] theorem mem_frontierPositive
    (C : ProfileData I Γ) {j : Idx n} :
    j ∈ C.frontierPositive ↔ I.firstBidTime j = Γ.t3Star ∧ 0 < Γ.muD j := by
  simp [ProfileData.frontierPositive]

noncomputable def pStar
    (C : ProfileData I Γ) (hpos : C.frontierPositive.Nonempty) : Idx n :=
  C.frontierPositive.max' hpos

theorem pStar_mem
    (C : ProfileData I Γ) (hpos : C.frontierPositive.Nonempty) :
    C.pStar hpos ∈ C.frontierPositive := by
  exact Finset.max'_mem _ _

theorem pStar_onFrontier
    (C : ProfileData I Γ) (hpos : C.frontierPositive.Nonempty) :
    I.firstBidTime (C.pStar hpos) = Γ.t3Star := by
  exact (C.mem_frontierPositive.mp (C.pStar_mem hpos)).1

theorem pStar_muD_pos
    (C : ProfileData I Γ) (hpos : C.frontierPositive.Nonempty) :
    0 < Γ.muD (C.pStar hpos) := by
  exact (C.mem_frontierPositive.mp (C.pStar_mem hpos)).2

theorem pStar_le_t3Star
    (C : ProfileData I Γ) (hpos : C.frontierPositive.Nonempty) :
    C.pStar hpos ≤ Γ.t3Star := by
  exact I.frontier_client_le (by
    simpa [ProcedureInput.mem_frontier] using C.pStar_onFrontier hpos)

omit [NeZero n] in
theorem sum_interval_one_eq_futureCount_add_one_sub {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) (fun _ => (1 : ℝ)) = futureCount j + 1 - futureCount i := by
  have hstrict := sum_interval_strict_one_eq_futureCount_sub hji
  have hone :
      Finset.sum (intervalRange j i) (fun p => if j < p then (1 : ℝ) else 0) =
        futureCount j - futureCount i := hstrict
  have hsplit :
      Finset.sum (intervalRange j i) (fun _ => (1 : ℝ)) =
        Finset.sum (intervalRange j i) (fun p => if p = j then (1 : ℝ) else 0) +
          Finset.sum (intervalRange j i) (fun p => if j < p then (1 : ℝ) else 0) := by
    calc
      Finset.sum (intervalRange j i) (fun _ => (1 : ℝ))
        =
          Finset.sum (intervalRange j i)
            (fun p => (if p = j then (1 : ℝ) else 0) + (if j < p then (1 : ℝ) else 0)) := by
              apply Finset.sum_congr rfl
              intro p hp
              rcases mem_intervalRange.mp hp with ⟨hjp, _⟩
              by_cases hpj : p = j
              · simp [hpj]
              · have hjp' : j < p := lt_of_le_of_ne hjp (Ne.symm hpj)
                simp [hpj, hjp']
      _ =
          Finset.sum (intervalRange j i) (fun p => if p = j then (1 : ℝ) else 0) +
            Finset.sum (intervalRange j i) (fun p => if j < p then (1 : ℝ) else 0) := by
              rw [Finset.sum_add_distrib]
  have honept :
      Finset.sum (intervalRange j i) (fun p => if p = j then (1 : ℝ) else 0) = 1 := by
    have hjmem : j ∈ intervalRange j i := mem_intervalRange.mpr ⟨le_rfl, hji⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro p hp hpne
      simp [hpne]
    · intro hjnot
      exact False.elim (hjnot hjmem)
  rw [hsplit, honept, hone]
  ring

theorem tailBudget_t1_add_tau_mul_boundaryFactor_eq_one
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht1ne : C.t1 ≠ lastIdx n) :
    (tailBudget C.hatG C.t1 + I.program.tau) *
      ((futureCount C.t1 + C.muBC C.t1) / futureCount C.t1) = 1 := by
  have hfcpos : 0 < futureCount C.t1 := futureCount_pos_of_ne_last C.t1 ht1ne
  have hfcne : futureCount C.t1 ≠ 0 := ne_of_gt hfcpos
  calc
    (tailBudget C.hatG C.t1 + I.program.tau) *
        ((futureCount C.t1 + C.muBC C.t1) / futureCount C.t1)
      =
        (tailBudget C.hatG C.t1 + I.program.tau) +
          (tailBudget C.hatG C.t1 + I.program.tau) *
            (C.muBC C.t1 / futureCount C.t1) := by
              field_simp [hfcne]
    _ =
        (tailBudget C.hatG C.t1 + I.program.tau) + C.hatGPrime C.t1 := by
          congr 1
          have hhat :
              futureCount C.t1 * C.hatGPrime C.t1 =
                C.muBC C.t1 * (C.tailBudgetPrime C.t1 + I.program.tau) := by
            simpa [C.tailBudgetPrime_eq_tailBudget_of_t1_le le_rfl] using
              C.futureCount_mul_hatGPrime_eq_muBC_mul_tailBudgetPrime_add_tau
                hΓ hγlo hγhi hθpos le_rfl (C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos) ht1ne
          have hhat' :
              C.hatGPrime C.t1 =
                (tailBudget C.hatG C.t1 + I.program.tau) *
                  (C.muBC C.t1 / futureCount C.t1) := by
            have hhat'' :
                C.hatGPrime C.t1 =
                  ((tailBudget C.hatG C.t1 + I.program.tau) * C.muBC C.t1) /
                    futureCount C.t1 := by
              rw [eq_div_iff hfcne]
              rw [mul_comm, hhat, C.tailBudgetPrime_eq_tailBudget_of_t1_le le_rfl]
              ring
            simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hhat''
          simpa [mul_comm] using hhat'.symm
    _ = C.beforeBudgetPrime C.t1 + I.program.tau := by
          unfold ProfileData.beforeBudgetPrime
          have htail' : tailBudget C.hatGPrime C.t1 = tailBudget C.hatG C.t1 := by
            exact C.tailBudgetPrime_eq_tailBudget_of_t1_le le_rfl
          rw [beforeBudget_eq_self_add_tail, C.hatGPrime_at_t1, htail']
          ring
    _ = 1 := by
          rw [C.beforeBudgetPrime_t1_eq_barTau_of_ne_last ht1ne, DualProgram.barTau]
          ring

theorem futureCount_t1_div_tailBudget_t1_add_tau_eq
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht1ne : C.t1 ≠ lastIdx n) :
    futureCount C.t1 / (tailBudget C.hatG C.t1 + I.program.tau) =
      futureCount C.t1 + C.muBC C.t1 := by
  have hfcpos : 0 < futureCount C.t1 := futureCount_pos_of_ne_last C.t1 ht1ne
  have hfcne : futureCount C.t1 ≠ 0 := ne_of_gt hfcpos
  have hτpos : 0 < I.program.tau := tau_pos_of_theta_pos I.program hγlo hθpos
  have htailnonneg : 0 ≤ tailBudget C.hatG C.t1 := C.tailBudget_nonneg_of_t1_le le_rfl
  have hBpos : 0 < tailBudget C.hatG C.t1 + I.program.tau := by linarith
  have hunit := C.tailBudget_t1_add_tau_mul_boundaryFactor_eq_one hΓ hγlo hγhi hθpos ht1ne
  rw [div_eq_iff hBpos.ne']
  have hunit' := hunit
  field_simp [hfcne] at hunit'
  linarith

theorem futureCount_div_tailBudget_eq_t1_mass_sub_weightQuotient
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (ht1i : C.t1 ≤ i) (hit3 : i ≤ Γ.t3Star) (hilast : i < lastIdx n) :
    futureCount i / (tailBudget C.hatG i + I.program.tau) =
      futureCount C.t1 + C.muBC C.t1 -
        Finset.sum (intervalRange C.t1 i)
          (fun l => C.phaseTwoWeight C.t1 l / (tailBudget C.hatG C.t1 + I.program.tau)) := by
  have ht1ne : C.t1 ≠ lastIdx n := ne_of_lt (lt_of_le_of_lt ht1i hilast)
  have hτpos : 0 < I.program.tau := tau_pos_of_theta_pos I.program hγlo hθpos
  have htailt1_nonneg : 0 ≤ tailBudget C.hatG C.t1 := C.tailBudget_nonneg_of_t1_le le_rfl
  have htaili_nonneg : 0 ≤ tailBudget C.hatG i := C.tailBudget_nonneg_of_t1_le ht1i
  have hBt1_pos : 0 < tailBudget C.hatG C.t1 + I.program.tau := by linarith
  have hBi_pos : 0 < tailBudget C.hatG i + I.program.tau := by linarith
  have hfcine : futureCount i ≠ 0 := ne_of_gt (futureCount_pos_of_ne_last i (ne_of_lt hilast))
  have hprod :=
    C.tailBudget_eq_phaseTwo_product hΓ hγlo hθpos (ht1j := le_rfl) ht1i hit3 hilast
  have hprod' :
      futureCount i / (tailBudget C.hatG i + I.program.tau) =
        (futureCount C.t1 -
            Finset.sum (intervalRange C.t1 i) (fun l => C.phaseTwoWeight C.t1 l)) /
          (tailBudget C.hatG C.t1 + I.program.tau) := by
    apply (div_eq_div_iff hBi_pos.ne' hBt1_pos.ne').2
    have hprodmul := hprod
    field_simp [hfcine] at hprodmul
    linarith
  rw [hprod']
  have hrewrite_sum :
      (futureCount C.t1 -
          Finset.sum (intervalRange C.t1 i) (fun l => C.phaseTwoWeight C.t1 l)) /
        (tailBudget C.hatG C.t1 + I.program.tau)
        =
      futureCount C.t1 / (tailBudget C.hatG C.t1 + I.program.tau) -
        Finset.sum (intervalRange C.t1 i)
          (fun l => C.phaseTwoWeight C.t1 l / (tailBudget C.hatG C.t1 + I.program.tau)) := by
    rw [sub_div]
    rw [Finset.sum_div]
  rw [hrewrite_sum, C.futureCount_t1_div_tailBudget_t1_add_tau_eq hΓ hγlo hγhi hθpos ht1ne]

theorem phaseTwoWeight_t1_div_boundary_of_lt
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hθpos : 0 < I.program.theta)
    {l : Idx n} (ht1l : C.t1 < l) :
    C.phaseTwoWeight C.t1 l / (tailBudget C.hatG C.t1 + I.program.tau) =
      Γ.muD l / (beforeBudget C.hatG l + I.program.tau) := by
  have _ := hΓ
  have hτpos : 0 < I.program.tau := tau_pos_of_theta_pos I.program hγlo hθpos
  have htail_nonneg : 0 ≤ tailBudget C.hatG C.t1 := C.tailBudget_nonneg_of_t1_le le_rfl
  have hBpos : 0 < tailBudget C.hatG C.t1 + I.program.tau := by linarith
  rw [ProfileData.phaseTwoWeight, if_pos ht1l]
  field_simp [hBpos.ne']

theorem le_pStar_of_mem_frontierPositive
    (C : ProfileData I Γ) (hpos : C.frontierPositive.Nonempty)
    {j : Idx n} (hj : j ∈ C.frontierPositive) :
    j ≤ C.pStar hpos := by
  exact Finset.le_max' _ _ hj

theorem muD_antitone_on_frontier
    (Γ : Advice I) (hΓ : Γ.Admissible) {j₁ j₂ : Idx n}
    (hj : j₁ ≤ j₂) (h₁ : Γ.OnFrontier j₁) (h₂ : Γ.OnFrontier j₂) :
    Γ.muD j₂ ≤ Γ.muD j₁ := by
  rcases hΓ with ⟨_, hmono, _, _⟩
  rw [Advice.muD_eq_muStar Γ h₂, Advice.muD_eq_muStar Γ h₁]
  exact hmono hj h₁ h₂

theorem muD_eq_zero_of_onFrontier_of_pStar_lt
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) (hpos : C.frontierPositive.Nonempty)
    {j : Idx n} (hjfront : Γ.OnFrontier j) (hpj : C.pStar hpos < j) :
    Γ.muD j = 0 := by
  have hnonneg : 0 ≤ Γ.muD j := Advice.muD_nonneg_of_admissible Γ hΓ j
  by_contra hμ
  have hμpos : 0 < Γ.muD j := lt_of_le_of_ne hnonneg (Ne.symm hμ)
  have hjmem : j ∈ C.frontierPositive := by
    simpa [Advice.OnFrontier] using (C.mem_frontierPositive.mpr ⟨hjfront, hμpos⟩)
  have hle : j ≤ C.pStar hpos := C.le_pStar_of_mem_frontierPositive hpos hjmem
  exact (not_le_of_gt hpj) hle

theorem muD_eq_one_of_onFrontier_of_lt_pStar
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) (hpos : C.frontierPositive.Nonempty)
    {j : Idx n} (hjfront : Γ.OnFrontier j) (hjp : j < C.pStar hpos) :
    Γ.muD j = 1 := by
  have hpfront : Γ.OnFrontier (C.pStar hpos) := C.pStar_onFrontier hpos
  have hμj_nonneg : 0 ≤ Γ.muD j := Advice.muD_nonneg_of_admissible Γ hΓ j
  have hμj_le : Γ.muD j ≤ 1 := Advice.muD_le_one_of_admissible Γ hΓ j
  have hμp_le_j : Γ.muD (C.pStar hpos) ≤ Γ.muD j :=
    muD_antitone_on_frontier (Γ := Γ) hΓ (le_of_lt hjp) hjfront hpfront
  have hμj_pos : 0 < Γ.muD j := lt_of_lt_of_le (C.pStar_muD_pos hpos) hμp_le_j
  by_cases hfracp : IsFractional (Γ.muD (C.pStar hpos))
  · have hfracj_or_one : ¬ IsFractional (Γ.muD j) := by
      intro hfracj
      rcases hΓ with ⟨_, _, hatmost, _⟩
      have hneq : j ≠ C.pStar hpos := ne_of_lt hjp
      have hfracj' : IsFractional (Γ.muStar j) := by
        simpa [Advice.OnFrontier, Advice.muD_eq_muStar Γ hjfront] using hfracj
      have hfracp' : IsFractional (Γ.muStar (C.pStar hpos)) := by
        simpa [Advice.OnFrontier, Advice.muD_eq_muStar Γ hpfront] using hfracp
      exact hneq (hatmost hjfront hpfront hfracj' hfracp')
    have hnotlt : ¬ Γ.muD j < 1 := by
      intro hlt
      exact hfracj_or_one ⟨hμj_pos, hlt⟩
    exact le_antisymm hμj_le (le_of_not_gt hnotlt)
  · have hμp_eq_one : Γ.muD (C.pStar hpos) = 1 := by
      have hμp_le : Γ.muD (C.pStar hpos) ≤ 1 := by
        exact Advice.muD_le_one_of_admissible Γ hΓ (C.pStar hpos)
      have hnotlt : ¬ Γ.muD (C.pStar hpos) < 1 := by
        intro hlt
        exact hfracp ⟨C.pStar_muD_pos hpos, hlt⟩
      exact le_antisymm hμp_le (le_of_not_gt hnotlt)
    have h1le : 1 ≤ Γ.muD j := by
      linarith
    exact le_antisymm hμj_le h1le

theorem muBC_eq_zero_of_muD_eq_one
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) {j : Idx n} (hμ : Γ.muD j = 1) :
    C.muBC j = 0 := by
  rw [C.muBC_eq_muB_add_muC]
  simp [C.memberships_muB_eq_zero_of_muD_eq_one hΓ hμ,
    C.memberships_muC_eq_zero_of_muD_eq_one hΓ hμ]

theorem beforeBudget_lt_barTau_of_t1_lt
    (C : ProfileData I Γ) {j : Idx n} (ht1j : C.t1 < j) :
    beforeBudget C.hatG j < I.program.barTau := by
  rw [C.beforeBudget_eq_phaseTwo_beforeBudget_of_lt_t1 ht1j]
  exact C.phaseTwo_beforeBudget_lt_barTau_above_t1 ht1j

theorem case4Gap_ge_chi_of_t1_lt
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (ht1j : C.t1 < j) :
    C.chi j ≤
      (I.program.barTau - beforeBudget C.hatG j) / (beforeBudget C.hatG j + I.program.tau) := by
  have hhatnonneg := C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hbefore_nonneg : 0 ≤ beforeBudget C.hatG j := beforeBudget_nonneg_of_nonneg hhatnonneg j
  have hbefore_le : beforeBudget C.hatG j ≤ I.program.barTau := by
    linarith [C.beforeBudget_lt_barTau_of_t1_lt ht1j]
  simpa [ProfileData.chi] using
    function_tau_bound I.program hγlo hγhi hθpos hbefore_nonneg hbefore_le

theorem generatedColumnValue_nonneg
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (j : Idx n) :
    0 ≤ C.generatedColumnValue AUX j := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  unfold ProfileData.generatedColumnValue
  apply Finset.sum_nonneg
  intro i hi
  simpa using C.gValue_nonneg H AUX i j

theorem sum_interval_muBC_ge_case4_chi_core
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (hi0 : 0 < i.1) (ht1i : C.t1 < i) (hit3 : i ≤ Γ.t3Star) :
    Finset.sum (intervalRange C.t1 (predIdx hi0)) C.muBC ≥
      C.chi i +
        Finset.sum (intervalRange C.t1 (predIdx hi0))
          (fun l => if C.t1 < l then Γ.muD l * C.chi l else 0) := by
  let im1 : Idx n := predIdx hi0
  let gap : Idx n → ℝ := fun l =>
    (I.program.barTau - beforeBudget C.hatG l) / (beforeBudget C.hatG l + I.program.tau)
  have hhatnonneg := C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hτpos : 0 < I.program.tau := tau_pos_of_theta_pos I.program hγlo hθpos
  have ht1im1 : C.t1 ≤ im1 := by
    dsimp [im1]
    exact Fin.le_def.mpr (by
      have hvals : C.t1.1 < i.1 := Fin.lt_def.mp ht1i
      change C.t1.1 ≤ i.1 - 1
      omega)
  have him1t3 : im1 ≤ Γ.t3Star := by
    dsimp [im1]
    exact le_trans (le_of_lt (predIdx_lt hi0)) hit3
  have him1last : im1 < lastIdx n := by
    dsimp [im1]
    exact lt_of_lt_of_le (predIdx_lt hi0) (le_trans hit3 (le_lastIdx _))
  have hquot :=
    C.futureCount_div_tailBudget_eq_t1_mass_sub_weightQuotient
      hΓ hγlo hγhi hθpos (ht1i := ht1im1) (hit3 := him1t3) him1last
  have hweights :
      Finset.sum (intervalRange C.t1 im1)
          (fun l => C.phaseTwoWeight C.t1 l / (tailBudget C.hatG C.t1 + I.program.tau)) =
        Finset.sum (intervalRange C.t1 im1)
          (fun l =>
            if C.t1 < l then Γ.muD l / (beforeBudget C.hatG l + I.program.tau) else 0) := by
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlt : C.t1 < l
    · rw [if_pos hlt, C.phaseTwoWeight_t1_div_boundary_of_lt hΓ hγlo hθpos hlt]
    · have hEq : l = C.t1 := le_antisymm (not_lt.mp hlt) (mem_intervalRange.mp hl).1
      subst l
      simp [ProfileData.phaseTwoWeight]
  have hmuSplit :
      Finset.sum (intervalRange C.t1 im1) C.muBC =
        C.muBC C.t1 +
          Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then C.muBC l else 0) := by
    have hmem : C.t1 ∈ intervalRange C.t1 im1 := mem_intervalRange.mpr ⟨le_rfl, ht1im1⟩
    calc
      Finset.sum (intervalRange C.t1 im1) C.muBC
        = Finset.sum (intervalRange C.t1 im1)
            (fun l =>
              (if l = C.t1 then C.muBC C.t1 else 0) +
                (if C.t1 < l then C.muBC l else 0)) := by
            apply Finset.sum_congr rfl
            intro l hl
            by_cases hEq : l = C.t1
            · subst l
              simp
            · have hlt : C.t1 < l := by
                have hne : C.t1 ≠ l := by
                  intro h'
                  exact hEq h'.symm
                exact lt_of_le_of_ne (mem_intervalRange.mp hl).1 hne
              simp [hEq, hlt]
      _ =
          Finset.sum (intervalRange C.t1 im1) (fun l => if l = C.t1 then C.muBC C.t1 else 0) +
            Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then C.muBC l else 0) := by
              rw [Finset.sum_add_distrib]
      _ = C.muBC C.t1 +
            Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then C.muBC l else 0) := by
              rw [Finset.sum_eq_single C.t1]
              · simp
              · intro l hl hne
                simp [hne]
              · intro hnot
                exact False.elim (hnot hmem)
  have hstrict :=
    C.sum_interval_strict_muBC_add_muD_eq_futureCount_sub
      (ht1j := le_rfl) (hji := ht1im1) (hit3 := him1t3)
  have hstrictSplit :
      Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then (C.muBC l + Γ.muD l) else 0) =
        Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then C.muBC l else 0) +
          Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l else 0) := by
    calc
      Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then (C.muBC l + Γ.muD l) else 0)
        = Finset.sum (intervalRange C.t1 im1)
            (fun l => (if C.t1 < l then C.muBC l else 0) + (if C.t1 < l then Γ.muD l else 0)) := by
              apply Finset.sum_congr rfl
              intro l hl
              by_cases hlt : C.t1 < l <;> simp [hlt]
      _ =
          Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then C.muBC l else 0) +
            Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l else 0) := by
              rw [Finset.sum_add_distrib]
  have hcount :
      Finset.sum (intervalRange C.t1 im1) C.muBC +
          Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l else 0) =
        futureCount C.t1 + C.muBC C.t1 - futureCount im1 := by
    have haux :
        Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then C.muBC l else 0) +
            Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l else 0) =
          futureCount C.t1 - futureCount im1 := by
      rw [← hstrictSplit, hstrict]
    calc
      Finset.sum (intervalRange C.t1 im1) C.muBC +
          Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l else 0)
        = C.muBC C.t1 +
            (Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then C.muBC l else 0) +
              Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l else 0)) := by
              rw [hmuSplit]
              ring
      _ = C.muBC C.t1 + (futureCount C.t1 - futureCount im1) := by rw [haux]
      _ = futureCount C.t1 + C.muBC C.t1 - futureCount im1 := by ring
  have hquot' :
      futureCount im1 / (beforeBudget C.hatG i + I.program.tau) +
          Finset.sum (intervalRange C.t1 im1)
            (fun l => if C.t1 < l then Γ.muD l / (beforeBudget C.hatG l + I.program.tau) else 0) =
        futureCount C.t1 + C.muBC C.t1 := by
    rw [tailBudget_predIdx_eq_beforeBudget C.hatG hi0, hweights] at hquot
    linarith
  have hcore :
      Finset.sum (intervalRange C.t1 im1) C.muBC =
        (futureCount im1 / (beforeBudget C.hatG i + I.program.tau) - futureCount im1) +
          (Finset.sum (intervalRange C.t1 im1)
              (fun l =>
                if C.t1 < l then Γ.muD l / (beforeBudget C.hatG l + I.program.tau) else 0) -
            Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l else 0)) := by
    linarith
  have hbefore_i_nonneg : 0 ≤ beforeBudget C.hatG i := beforeBudget_nonneg_of_nonneg hhatnonneg i
  have hden_i_pos : 0 < beforeBudget C.hatG i + I.program.tau := by
    linarith
  have hboundary :
      futureCount im1 / (beforeBudget C.hatG i + I.program.tau) - futureCount im1 =
        futureCount im1 * gap i := by
    unfold gap
    field_simp [hden_i_pos.ne']
    rw [DualProgram.barTau]
    ring
  have hgapSum :
      Finset.sum (intervalRange C.t1 im1)
          (fun l => if C.t1 < l then Γ.muD l / (beforeBudget C.hatG l + I.program.tau) else 0) -
        Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l else 0) =
      Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l * gap l else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlt : C.t1 < l
    · have hbefore_l_nonneg : 0 ≤ beforeBudget C.hatG l := by
        exact beforeBudget_nonneg_of_nonneg hhatnonneg l
      have hden_l_pos : 0 < beforeBudget C.hatG l + I.program.tau := by
        linarith
      rw [if_pos hlt, if_pos hlt, if_pos hlt]
      unfold gap
      field_simp [hden_l_pos.ne']
      rw [DualProgram.barTau]
      ring
    · simp [hlt]
  have heq :
      Finset.sum (intervalRange C.t1 im1) C.muBC =
        futureCount im1 * gap i +
          Finset.sum (intervalRange C.t1 im1)
            (fun l => if C.t1 < l then Γ.muD l * gap l else 0) := by
    rw [hcore, hboundary, hgapSum]
  have hgap_i_nonneg : 0 ≤ gap i := by
    unfold gap
    exact div_nonneg
      (sub_nonneg.mpr (le_of_lt (C.beforeBudget_lt_barTau_of_t1_lt ht1i)))
      (le_of_lt hden_i_pos)
  have hgap_i_chi : C.chi i ≤ gap i :=
    C.case4Gap_ge_chi_of_t1_lt hΓ hγlo hγhi hθpos ht1i
  have hfuture_ge_one : 1 ≤ futureCount im1 := by
    dsimp [im1]
    rw [futureCount_predIdx hi0]
    linarith [futureCount_nonneg i]
  have hfirstTerm :
      C.chi i ≤ futureCount im1 * gap i := by
    calc
      C.chi i ≤ 1 * gap i := by simpa using hgap_i_chi
      _ ≤ futureCount im1 * gap i := by
            exact mul_le_mul_of_nonneg_right hfuture_ge_one hgap_i_nonneg
  have hsumTerm :
      Finset.sum (intervalRange C.t1 im1) (fun l => if C.t1 < l then Γ.muD l * C.chi l else 0) ≤
        Finset.sum
          (intervalRange C.t1 im1)
          (fun l => if C.t1 < l then Γ.muD l * gap l else 0) := by
    apply Finset.sum_le_sum
    intro l hl
    by_cases hlt : C.t1 < l
    · rw [if_pos hlt, if_pos hlt]
      exact mul_le_mul_of_nonneg_left
        (C.case4Gap_ge_chi_of_t1_lt hΓ hγlo hγhi hθpos hlt)
        (Advice.muD_nonneg_of_admissible Γ hΓ l)
    · simp [hlt]
  linarith [heq, hfirstTerm, hsumTerm]

theorem totalGeneratedMass_eq_sum_generatedColumnValue
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) :
    C.totalGeneratedMass AUX =
      Finset.sum Finset.univ (fun j => C.generatedColumnValue AUX j) := by
  unfold ProfileData.totalGeneratedMass ProfileData.generatedColumnValue
  rw [Finset.sum_comm]

theorem weighted_sum_univ_gA_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (j : Idx n) :
    (C.memberships).muA j * Finset.sum Finset.univ (fun i => C.gA AUX i j) =
      (C.memberships).muA j *
        (1 - I.program.epsilon *
          (1 -
            posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
              I.program.theta)) := by
  by_cases hμA0 : (C.memberships).muA j = 0
  · simp [hμA0]
  · have hμAnonneg := (C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds).1 j
    have hμApos : 0 < (C.memberships).muA j :=
      lt_of_le_of_ne hμAnonneg (Ne.symm hμA0)
    rw [C.sum_univ_gA_eq_of_muA_pos AUX hγlo hγhi hθpos hμApos]

theorem generatedColumnValue_eq_one_sub_epsilon_mul
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (j : Idx n) :
    C.generatedColumnValue AUX j =
      1 -
        I.program.epsilon *
          ((C.memberships).muA j *
              (1 -
                posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
                  I.program.theta) +
            (C.memberships).muD j * C.chi j) := by
  have hA := C.weighted_sum_univ_gA_eq AUX hΓ hγlo hγhi hθpos j
  rw [ProfileData.generatedColumnValue, C.sum_univ_gValue_eq_membership_combo AUX j, hA,
    C.sum_univ_gB_eq AUX j, C.sum_univ_gC_eq AUX j, C.sum_univ_gD_eq AUX hΓ hγlo hγhi hθpos j]
  have htotal : (C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j +
      (C.memberships).muD j = 1 := by
    simpa [MembershipWeights.total] using C.memberships_total j
  ring_nf
  linarith

theorem sum_interval_delta_eq_deltaRange_at_t3Star
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    {j : Idx n} (hj : 0 < (C.memberships).muA j) (hfj : I.firstBidTime j < Γ.t3Star) :
    Finset.sum (intervalRange j Γ.t3Star) (fun p => AUX.delta p j) =
      Finset.sum (deltaRange I Γ j) (fun p => AUX.delta p j) := by
  have _ := hfj
  let s := deltaRange I Γ j
  have hs_subset : s ⊆ intervalRange j Γ.t3Star := by
    intro p hp
    rcases mem_deltaRange.mp hp with ⟨hfp, hpt3⟩
    exact mem_intervalRange.mpr ⟨le_trans (I.le_firstBidTime j) (le_of_lt hfp), hpt3⟩
  symm
  apply Finset.sum_subset hs_subset
  intro p hpInt hpNot
  have hp_le : p ≤ I.firstBidTime j := by
    by_cases hfp : I.firstBidTime j < p
    · have hpt3 : p ≤ Γ.t3Star := (mem_intervalRange.mp hpInt).2
      exact False.elim (hpNot (mem_deltaRange.mpr ⟨hfp, hpt3⟩))
    · exact not_lt.mp hfp
  exact AUX.delta_eq_zero p j hj hp_le

theorem creditAfterA_at_t3Star_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hj : 0 < (C.memberships).muA j) (hfj : I.firstBidTime j < Γ.t3Star) :
    C.creditAfterA AUX Γ.t3Star j =
      1 - I.program.epsilon *
        (1 -
          posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
            I.program.theta) := by
  have _ := hγlo
  have _ := hγhi
  have _ := hθpos
  unfold ProfileData.creditAfterA
  rw [C.sum_interval_delta_eq_deltaRange_at_t3Star AUX hj hfj, AUX.delta_sum_eq j hj]

theorem beforeBudget_le_one_sub_epsilon_mul_chi
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (j : Idx n) :
    beforeBudget C.hatG j ≤ 1 - I.program.epsilon * C.chi j := by
  have hhatnonneg := C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hbefore_le : beforeBudget C.hatG j ≤ 1 :=
    beforeBudget_le_one_of_nonneg_of_total_eq_one hhatnonneg C.total_eq_one j
  have hεnonneg : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hεleθ : I.program.epsilon ≤ I.program.theta := by
    rw [← I.program.gamma_mul_epsilon_eq_theta]
    have hM : 1 ≤ I.program.Mcoeff := hγlo
    nlinarith
  have hθle1 : I.program.theta ≤ 1 := I.program.theta_le_one_of_le_153_div_125 hγlo hγhi
  by_cases hinner : 1 - beforeBudget C.hatG j / I.program.theta ≤ 0
  · have hchi : C.chi j = 0 := by
      simp [ProfileData.chi, hinner]
    simpa [hchi] using hbefore_le
  · have hpos : 0 ≤ 1 - beforeBudget C.hatG j / I.program.theta := by
      linarith
    have hchi : C.chi j = 1 - beforeBudget C.hatG j / I.program.theta := by
      simp [ProfileData.chi, hpos]
    have hmul :
        I.program.epsilon * C.chi j ≤ I.program.theta * C.chi j := by
      exact mul_le_mul_of_nonneg_right hεleθ (C.chi_nonneg j)
    have htheta :
        beforeBudget C.hatG j + I.program.theta * C.chi j = I.program.theta := by
      rw [hchi]
      field_simp [ne_of_gt hθpos]
      ring
    have hmain :
        beforeBudget C.hatG j + I.program.epsilon * C.chi j ≤ 1 := by
      calc
        beforeBudget C.hatG j + I.program.epsilon * C.chi j
          ≤ beforeBudget C.hatG j + I.program.theta * C.chi j := by
              linarith
        _ = I.program.theta := htheta
        _ ≤ 1 := hθle1
    linarith

theorem chi_eq_one_of_t3_lt
    (C : ProfileData I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (ht3j : Γ.t3Star < j) :
    C.chi j = 1 := by
  have hhat0 : C.hatG j = 0 := C.hatG_eq_zero_of_t3_lt hγlo hγhi hθpos ht3j
  have htail0 : tailBudget C.hatG j = 0 :=
    C.tailBudget_eq_zero_of_t3_le hγlo hγhi hθpos (le_of_lt ht3j)
  have hbefore0 : beforeBudget C.hatG j = 0 := by
    rw [beforeBudget_eq_self_add_tail, hhat0, htail0]
    ring
  rw [ProfileData.chi, hbefore0]
  simp

theorem generatedMassPrefix_eq_rowSuffix_add_triangle
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) :
    C.generatedMassPrefix AUX i =
      Finset.sum (prefixRange i)
          (fun j => Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q)) +
        Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.gValue AUX p j)) := by
  unfold ProfileData.generatedMassPrefix
  calc
    Finset.sum (prefixRange i) (fun p => Finset.sum Finset.univ (fun j => C.gValue AUX p j))
      = Finset.sum (prefixRange i)
          (fun p =>
            Finset.sum (prefixRange p) (fun j => C.gValue AUX p j) +
              Finset.sum (strictSuffixRange p) (fun j => C.gValue AUX p j)) := by
                apply Finset.sum_congr rfl
                intro p hp
                rw [sum_univ_eq_prefix_add_strictSuffix (f := fun j => C.gValue AUX p j) p]
    _ = Finset.sum (prefixRange i)
          (fun p => Finset.sum (prefixRange p) (fun j => C.gValue AUX p j)) +
        Finset.sum (prefixRange i)
          (fun p => Finset.sum (strictSuffixRange p) (fun j => C.gValue AUX p j)) := by
          rw [Finset.sum_add_distrib]
    _ = Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.gValue AUX p j)) +
        Finset.sum (prefixRange i)
          (fun p => Finset.sum (strictSuffixRange p) (fun j => C.gValue AUX p j)) := by
          rw [sum_prefixTriangle_eq_sumByColumn (f := fun p j => C.gValue AUX p j) i]
    _ = Finset.sum (prefixRange i)
          (fun j => Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q)) +
        Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.gValue AUX p j)) := by
          rw [add_comm]

theorem sum_prefix_creditValue_add_poolValue_eq_generatedMassPrefix
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) :
    Finset.sum (prefixRange i) (fun j => C.creditValue AUX i j) + C.poolValue AUX i =
      C.generatedMassPrefix AUX i := by
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.poolValue_eq_sumByColumn AUX i, C.generatedMassPrefix_eq_rowSuffix_add_triangle AUX i]
  calc
    Finset.sum (prefixRange i)
        (fun j =>
          Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) +
            Finset.sum (intervalRange j i)
              (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j)) +
        Finset.sum (prefixRange i)
          (fun j => Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j - C.tValue AUX p j))
      = Finset.sum (prefixRange i)
          (fun j =>
            (Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) +
              Finset.sum (intervalRange j i)
                (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j)) +
              Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j - C.tValue AUX p j)) := by
              rw [← Finset.sum_add_distrib]
    _ = Finset.sum (prefixRange i)
          (fun j =>
            Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) +
              Finset.sum (intervalRange j i) (fun p => C.gValue AUX p j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              calc
                (Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) +
                    Finset.sum (intervalRange j i)
                      (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j)) +
                    Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j - C.tValue AUX p j)
                  =
                    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) +
                      (Finset.sum (intervalRange j i)
                        (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j) +
                        Finset.sum (intervalRange j i)
                          (fun p => C.sValue AUX p j - C.tValue AUX p j)) := by
                            ring
                _ =
                    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) +
                      Finset.sum (intervalRange j i)
                        (fun p =>
                          (C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j) +
                            (C.sValue AUX p j - C.tValue AUX p j)) := by
                              rw [← Finset.sum_add_distrib]
                _ =
                    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) +
                      Finset.sum (intervalRange j i) (fun p => C.gValue AUX p j) := by
                              congr 1
                              apply Finset.sum_congr rfl
                              intro p hp
                              ring
    _ = Finset.sum (prefixRange i)
          (fun j => Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q)) +
            Finset.sum (prefixRange i)
              (fun j => Finset.sum (intervalRange j i) (fun p => C.gValue AUX p j)) := by
            rw [Finset.sum_add_distrib]

theorem poolValue_eq_generatedMassPrefix_sub_creditSum
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i : Idx n) :
    C.poolValue AUX i =
      C.generatedMassPrefix AUX i -
        Finset.sum (prefixRange i) (fun j => C.creditValue AUX i j) := by
  have h := C.sum_prefix_creditValue_add_poolValue_eq_generatedMassPrefix AUX i
  linarith

theorem hatG_eq_zero_of_t3_lt_local
    (C : ProfileData I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (hi : Γ.t3Star < i) :
    C.hatG i = 0 := by
  have ht1i : C.t1 < i := lt_of_le_of_lt (C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos) hi
  rw [C.copied_above_t1 ht1i, C.phaseTwo.zero_above_t3 hi]

theorem gValue_eq_zero_of_t3_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i j : Idx n} (hi : Γ.t3Star < i) :
    C.gValue AUX i j = 0 := by
  have hhat0 : C.hatG i = 0 := C.hatG_eq_zero_of_t3_lt_local hγlo hγhi hθpos hi
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have ht1i : C.t1 < i := lt_of_le_of_lt (C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos) hi
  have hA :
      (C.memberships).muA j * C.gA AUX i j = 0 := by
    by_cases hμA0 : (C.memberships).muA j = 0
    · simp [hμA0]
    · have hμApos : 0 < (C.memberships).muA j := lt_of_le_of_ne (hμnonneg.1 j) (Ne.symm hμA0)
      have hδnonneg : 0 ≤ AUX.delta i j := AUX.delta_nonneg i j hμApos
      have hδle : AUX.delta i j ≤ C.hatG i := AUX.delta_le_hatG i j hμApos
      have hδ0 : AUX.delta i j = 0 := by
        linarith
      simp [ProfileData.gA, hδ0, hhat0]
  have hD : C.gD AUX i j = 0 := by
    have hnot : ¬ i < C.t1 := not_lt.mpr (le_of_lt ht1i)
    have hneq : i ≠ C.t1 := ne_of_gt ht1i
    simp [ProfileData.gD, hnot, hneq, hhat0]
  simp [ProfileData.gValue, hA, ProfileData.gB, ProfileData.gC, hD, hhat0]

theorem sValue_eq_zero_of_after_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i p j : Idx n} (hi : Γ.t3Star < i) (hip : i < p) :
    C.sValue AUX p j = 0 := by
  have hhat0 : C.hatG p = 0 :=
    C.hatG_eq_zero_of_t3_lt_local hγlo hγhi hθpos (lt_trans hi hip)
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have hA :
      (C.memberships).muA j * C.sA AUX p j = 0 := by
    by_cases hμA0 : (C.memberships).muA j = 0
    · simp [hμA0]
    · have hμApos : 0 < (C.memberships).muA j :=
        lt_of_le_of_ne (hμnonneg.1 j) (Ne.symm hμA0)
      have hσnonneg : 0 ≤ AUX.sigma p j := AUX.sigma_nonneg p j hμApos
      have hσle : AUX.sigma p j ≤ C.hatG p := AUX.sigma_le_hatG p j hμApos
      have hσ0 : AUX.sigma p j = 0 := by
        linarith
      by_cases hjp : j ≤ p
      · simp [ProfileData.sA, hjp, hσ0, hhat0]
      · simp [ProfileData.sA, hjp]
  have hB :
      (C.memberships).muB j * C.sB AUX p j = 0 := by
    by_cases hgt3 : Γ.t3Star < I.firstBidTime j
    · have hμ : Γ.muD j = 1 := Advice.muD_eq_one Γ hgt3
      rw [C.memberships_muB_eq_zero_of_muD_eq_one hΓ hμ]
      ring
    · have hfjle : I.firstBidTime j ≤ Γ.t3Star := not_lt.mp hgt3
      have hjp : j < p := by
        exact lt_of_le_of_lt (le_trans (I.le_firstBidTime j) hfjle) (lt_trans hi hip)
      have hnotNext : ¬ IsNextIndex p (I.firstBidTime j) := by
        unfold IsNextIndex
        intro hnext
        have hfi : (I.firstBidTime j).1 ≤ Γ.t3Star.1 := Fin.le_def.mp hfjle
        have hpgt : Γ.t3Star.1 + 1 < p.1 := by
          have hi' : Γ.t3Star.1 < i.1 := Fin.lt_def.mp hi
          have hip' : i.1 < p.1 := Fin.lt_def.mp hip
          omega
        have hple : p.1 ≤ Γ.t3Star.1 + 1 := by
          omega
        exact (not_le_of_gt hpgt) hple
      simp [ProfileData.sB, hnotNext, hjp, hhat0]
  have hC :
      (C.memberships).muC j * C.sC AUX p j = 0 := by
    by_cases hgt3 : Γ.t3Star < I.firstBidTime j
    · have hμ : Γ.muD j = 1 := Advice.muD_eq_one Γ hgt3
      rw [C.memberships_muC_eq_zero_of_muD_eq_one hΓ hμ]
      ring
    · have hfjle : I.firstBidTime j ≤ Γ.t3Star := not_lt.mp hgt3
      have hjp : j < p := by
        exact lt_of_le_of_lt (le_trans (I.le_firstBidTime j) hfjle) (lt_trans hi hip)
      have hnotNext : ¬ IsNextIndex p (I.firstBidTime j) := by
        unfold IsNextIndex
        intro hnext
        have hfi : (I.firstBidTime j).1 ≤ Γ.t3Star.1 := Fin.le_def.mp hfjle
        have hpgt : Γ.t3Star.1 + 1 < p.1 := by
          have hi' : Γ.t3Star.1 < i.1 := Fin.lt_def.mp hi
          have hip' : i.1 < p.1 := Fin.lt_def.mp hip
          omega
        have hple : p.1 ≤ Γ.t3Star.1 + 1 := by
          omega
        exact (not_le_of_gt hpgt) hple
      simp [ProfileData.sC, hnotNext, hjp, hhat0]
  have hD : (C.memberships).muD j * C.sD AUX p j = 0 := by
    simp [ProfileData.sD]
  simp [ProfileData.sValue, ProfileData.sD, hA, hB, hC]

theorem rowContribution_nonpos_of_after_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i p : Idx n} (hi : Γ.t3Star < i) (hip : i < p) :
    Finset.sum (prefixRange p) (fun j => C.sValue AUX p j - C.tValue AUX p j) ≤ 0 := by
  let H : NonnegHypotheses C := NonnegHypotheses.of_profile_construction C hΓ hγlo hγhi
  calc
    Finset.sum (prefixRange p) (fun j => C.sValue AUX p j - C.tValue AUX p j)
      = Finset.sum (prefixRange p) (fun j => -C.tValue AUX p j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [C.sValue_eq_zero_of_after_t3 AUX hΓ hγlo hγhi hθpos hi hip, zero_sub]
    _ = -Finset.sum (prefixRange p) (fun j => C.tValue AUX p j) := by
          rw [Finset.sum_neg_distrib]
    _ ≤ 0 := by
          have htNonneg : 0 ≤ Finset.sum (prefixRange p) (fun j => C.tValue AUX p j) := by
            apply Finset.sum_nonneg
            intro j hj
            simpa using C.tValue_nonneg H AUX p j
          linarith

theorem poolValue_antitone_after_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i k : Idx n} (hi : Γ.t3Star < i) (hik : i ≤ k) :
    C.poolValue AUX k ≤ C.poolValue AUX i := by
  let row : Idx n → ℝ := fun p =>
    Finset.sum (prefixRange p) (fun j => C.sValue AUX p j - C.tValue AUX p j)
  unfold ProfileData.poolValue
  have hset : (prefixRange k).filter (fun p => p ≤ i) = prefixRange i := by
    ext p
    constructor
    · intro hp
      exact mem_prefixRange.mpr (Finset.mem_filter.mp hp).2
    · intro hp
      exact Finset.mem_filter.mpr
        ⟨mem_prefixRange.mpr (le_trans (mem_prefixRange.mp hp) hik), mem_prefixRange.mp hp⟩
  have htail :
      Finset.sum ((prefixRange k).filter (fun p => ¬ p ≤ i)) row ≤ 0 := by
    have hnonneg :
        0 ≤ Finset.sum ((prefixRange k).filter (fun p => ¬ p ≤ i)) (fun p => -row p) := by
      apply Finset.sum_nonneg
      intro p hp
      have hip : i < p := lt_of_not_ge (Finset.mem_filter.mp hp).2
      have hrow : row p ≤ 0 := by
        dsimp [row]
        exact C.rowContribution_nonpos_of_after_t3 AUX hΓ hγlo hγhi hθpos hi hip
      linarith
    have hneg :
        Finset.sum ((prefixRange k).filter (fun p => ¬ p ≤ i)) (fun p => -row p) =
          -Finset.sum ((prefixRange k).filter (fun p => ¬ p ≤ i)) row := by
      rw [Finset.sum_neg_distrib]
    linarith
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := prefixRange k) (p := fun p => p ≤ i) row
  rw [hset] at hsplit
  have hk :
      Finset.sum (prefixRange k) row =
        Finset.sum (prefixRange i) row +
          Finset.sum ((prefixRange k).filter (fun p => ¬ p ≤ i)) row := by
    simpa using hsplit.symm
  linarith

theorem constructedDualSolution_poolCredit_antitone_after_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i k : Idx n} (hi : Γ.t3Star < i) (hik : i ≤ k) :
    DualSolution.poolCredit (C.constructedDualSolution AUX) k ≤
      DualSolution.poolCredit (C.constructedDualSolution AUX) i := by
  have ht1i : C.t1 < i := lt_of_le_of_lt (C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos) hi
  have ht1k : C.t1 < k := lt_of_lt_of_le ht1i hik
  rw [C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX k,
    C.shiftedPoolValue_eq_poolValue_of_t1_lt AUX hΓ hγlo hγhi ht1k,
    C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX i,
    C.shiftedPoolValue_eq_poolValue_of_t1_lt AUX hΓ hγlo hγhi ht1i]
  exact C.poolValue_antitone_after_t3 AUX hΓ hγlo hγhi hθpos hi hik

theorem poolValue_nonneg_of_after_t3_of_last_nonneg
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (hi : Γ.t3Star < i) (hlast : 0 ≤ C.poolValue AUX (lastIdx n)) :
    0 ≤ C.poolValue AUX i := by
  have hmono := C.poolValue_antitone_after_t3 AUX hΓ hγlo hγhi hθpos hi (le_lastIdx _)
  linarith

theorem constructedDualSolution_poolCredit_nonneg_of_after_t3_of_last_nonneg
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (hi : Γ.t3Star < i)
    (hlast : 0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) (lastIdx n)) :
    0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) i := by
  have ht1i : C.t1 < i := lt_of_le_of_lt (C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos) hi
  rw [C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX (lastIdx n),
    C.shiftedPoolValue_eq_poolValue_at_last AUX hΓ hγlo hγhi] at hlast
  rw [C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX i,
    C.shiftedPoolValue_eq_poolValue_of_t1_lt AUX hΓ hγlo hγhi ht1i]
  exact C.poolValue_nonneg_of_after_t3_of_last_nonneg AUX hΓ hγlo hγhi hθpos hi hlast

theorem prefixRange_lastIdx_eq_univ :
    prefixRange (lastIdx n) = (Finset.univ : Finset (Idx n)) := by
  ext j
  simp [prefixRange, le_lastIdx]

theorem generatedMassPrefix_eq_totalGeneratedMass_at_last
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) :
    C.generatedMassPrefix AUX (lastIdx n) = C.totalGeneratedMass AUX := by
  simp [ProfileData.generatedMassPrefix, ProfileData.totalGeneratedMass,
    prefixRange_lastIdx_eq_univ]

theorem poolValue_eq_totalGeneratedMass_sub_creditSum_at_last
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) :
    C.poolValue AUX (lastIdx n) =
      C.totalGeneratedMass AUX -
        Finset.sum Finset.univ (fun j => C.creditValue AUX (lastIdx n) j) := by
  rw [C.poolValue_eq_generatedMassPrefix_sub_creditSum AUX (lastIdx n),
    C.generatedMassPrefix_eq_totalGeneratedMass_at_last AUX, prefixRange_lastIdx_eq_univ]

theorem muBC_eq_zero_of_t3_lt_firstBid
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) {j : Idx n}
    (hfj : Γ.t3Star < I.firstBidTime j) :
    C.muBC j = 0 := by
  have hμ : Γ.muD j = 1 := Advice.muD_eq_one Γ hfj
  exact C.muBC_eq_zero_of_muD_eq_one hΓ hμ

theorem creditAfterA_at_last_eq_of_muA_pos
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (_ht3last : Γ.t3Star < lastIdx n)
    {j : Idx n} (hj : 0 < (C.memberships).muA j) :
    C.creditAfterA AUX (lastIdx n) j =
      1 - I.program.epsilon *
        (1 -
          posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
            I.program.theta) := by
  by_cases hfj : I.firstBidTime j < Γ.t3Star
  · have hA3 := C.creditAfterA_at_t3Star_eq AUX hγlo hγhi hθpos hj hfj
    have hs_subset : intervalRange j Γ.t3Star ⊆ intervalRange j (lastIdx n) := by
      intro p hp
      rcases mem_intervalRange.mp hp with ⟨hjp, hp3⟩
      exact mem_intervalRange.mpr ⟨hjp, le_trans hp3 (le_lastIdx _)⟩
    have hsum :
        Finset.sum (intervalRange j Γ.t3Star) (fun p => AUX.delta p j) =
          Finset.sum (intervalRange j (lastIdx n)) (fun p => AUX.delta p j) := by
      apply Finset.sum_subset hs_subset
      intro p hpBig hpNot
      have hgt3 : Γ.t3Star < p := by
        have hpNotLe : ¬ p ≤ Γ.t3Star := by
          intro hp3
          exact hpNot (mem_intervalRange.mpr ⟨(mem_intervalRange.mp hpBig).1, hp3⟩)
        exact lt_of_not_ge hpNotLe
      exact C.delta_eq_zero_of_t3_lt AUX hγlo hγhi hθpos hj hgt3
    calc
      C.creditAfterA AUX (lastIdx n) j
        = 1 - Finset.sum (intervalRange j (lastIdx n)) (fun p => AUX.delta p j) := by rfl
      _ = 1 - Finset.sum (intervalRange j Γ.t3Star) (fun p => AUX.delta p j) := by
            rw [hsum]
      _ = 1 - I.program.epsilon *
            (1 -
              posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
                I.program.theta) := by
                  simpa [ProfileData.creditAfterA] using hA3
  · have hfjle : I.firstBidTime j ≤ Γ.t3Star := by
      by_contra hgt
      have hμ : Γ.muD j = 1 := Advice.muD_eq_one Γ (lt_of_not_ge hgt)
      have hA0 : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_muD_eq_one hΓ hμ
      exact (lt_irrefl (0 : ℝ)) (hA0 ▸ hj)
    have hEq : I.firstBidTime j = Γ.t3Star := le_antisymm hfjle (not_lt.mp hfj)
    unfold ProfileData.creditAfterA
    have hsum0 :
        Finset.sum (intervalRange j (lastIdx n)) (fun p => AUX.delta p j) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        by_cases hp3 : p ≤ Γ.t3Star
        · have hple : p ≤ I.firstBidTime j := by simpa [hEq] using hp3
          exact AUX.delta_eq_zero p j hj hple
        · exact C.delta_eq_zero_of_t3_lt AUX hγlo hγhi hθpos hj (lt_of_not_ge hp3)
    calc
      C.creditAfterA AUX (lastIdx n) j
        = 1 - Finset.sum (intervalRange j (lastIdx n)) (fun p => AUX.delta p j) := by rfl
      _ = 1 := by rw [hsum0]; ring
      _ = 1 - I.program.epsilon *
            (1 -
              posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
                I.program.theta) := by
                  rw [hEq, C.tailBudget_eq_zero_of_t3_le hγlo hγhi hθpos le_rfl, sub_zero]
                  have htheta :
                      posPart I.program.theta / I.program.theta = 1 := by
                    rw [posPart_of_nonneg (le_of_lt hθpos)]
                    field_simp [ne_of_gt hθpos]
                  rw [htheta]
                  ring

theorem creditValue_at_last_eq_one_sub_epsilon_mul
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht3last : Γ.t3Star < lastIdx n) (j : Idx n) :
    C.creditValue AUX (lastIdx n) j =
      1 -
        I.program.epsilon *
          ((C.memberships).muA j *
              (1 -
                posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
                  I.program.theta) +
            C.muBC j) := by
  by_cases hlt : I.firstBidTime j < lastIdx n
  · have hcredit :=
      C.creditValue_after_eq_weighted AUX hΓ hγlo hγhi hθpos (le_lastIdx j) (le_lastIdx _)
    let gap :=
      1 -
        posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
          I.program.theta
    have hAterm :
        (C.memberships).muA j * C.creditAfterA AUX (lastIdx n) j =
          (C.memberships).muA j *
            (1 - I.program.epsilon * gap) := by
      by_cases hμA0 : (C.memberships).muA j = 0
      · simp [hμA0]
      · have hμApos : 0 < (C.memberships).muA j :=
          lt_of_le_of_ne
            ((C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds).1 j)
            (Ne.symm hμA0)
        have hAeq :=
          C.creditAfterA_at_last_eq_of_muA_pos AUX hΓ hγlo hγhi hθpos ht3last hμApos
        rw [hAeq]
    have htotal : (C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j +
        (C.memberships).muD j = 1 := by
      simpa [MembershipWeights.total] using C.memberships_total j
    rw [hcredit, weightedCreditAfter, hAterm, creditAfterB, creditAfterC, creditAfterD]
    calc
      (C.memberships).muA j * (1 - I.program.epsilon * gap) +
          (C.memberships).muB j *
            (1 - if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) +
          (C.memberships).muC j *
            (1 - if I.firstBidTime j < lastIdx n then I.program.epsilon else 0) +
          (C.memberships).muD j * 1
        = (C.memberships).muA j * (1 - I.program.epsilon * gap) +
            (C.memberships).muB j * (1 - I.program.epsilon) +
            (C.memberships).muC j * (1 - I.program.epsilon) +
            (C.memberships).muD j * 1 := by
              simp [hlt]
      (C.memberships).muA j * (1 - I.program.epsilon * gap) +
          (C.memberships).muB j * (1 - I.program.epsilon) +
          (C.memberships).muC j * (1 - I.program.epsilon) +
          (C.memberships).muD j * 1
        = ((C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j +
              (C.memberships).muD j) -
            I.program.epsilon * ((C.memberships).muA j * gap + C.muBC j) := by
              simp [gap, C.muBC_eq_muB_add_muC]
              ring
      _ = 1 - I.program.epsilon * ((C.memberships).muA j * gap + C.muBC j) := by
            rw [htotal]
  · have hEq : I.firstBidTime j = lastIdx n := le_antisymm (le_lastIdx _) (not_lt.mp hlt)
    have hμ : Γ.muD j = 1 := Advice.muD_eq_one Γ (hEq ▸ ht3last)
    have hcredit : C.creditValue AUX (lastIdx n) j = 1 := by
      simpa [hEq] using
        C.creditValue_eq_one_of_eq_firstBidTime AUX hΓ hγlo hγhi hθpos (le_lastIdx j) hEq.symm
    have hA0 : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_muD_eq_one hΓ hμ
    have hBC0 : C.muBC j = 0 := C.muBC_eq_zero_of_muD_eq_one hΓ hμ
    rw [hcredit, hA0, hBC0]
    ring

theorem generatedColumn_sub_credit_at_last_eq_case5_term
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht3last : Γ.t3Star < lastIdx n) (j : Idx n) :
    C.generatedColumnValue AUX j - C.creditValue AUX (lastIdx n) j =
      I.program.epsilon * (C.muBC j - (C.memberships).muD j * C.chi j) := by
  rw [C.generatedColumnValue_eq_one_sub_epsilon_mul AUX hΓ hγlo hγhi hθpos j,
    C.creditValue_at_last_eq_one_sub_epsilon_mul AUX hΓ hγlo hγhi hθpos ht3last j]
  ring

theorem sum_univ_muBC_eq_sum_interval_t1_t3
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) :
    Finset.sum Finset.univ C.muBC =
      Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC := by
  have hsplit1 :=
    sum_univ_eq_prefix_add_strictSuffix (f := C.muBC) Γ.t3Star
  have hsuffix0 :
      Finset.sum (strictSuffixRange Γ.t3Star) C.muBC = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact C.muBC_eq_zero_of_t3_lt_firstBid hΓ
      (lt_of_lt_of_le (mem_strictSuffixRange.mp hj) (I.le_firstBidTime j))
  rw [hsuffix0, add_zero] at hsplit1
  have hsplit2 :=
    Finset.sum_filter_add_sum_filter_not
      (s := prefixRange Γ.t3Star) (p := fun j => C.t1 ≤ j) C.muBC
  have hset :
      (prefixRange Γ.t3Star).filter (fun j => C.t1 ≤ j) = intervalRange C.t1 Γ.t3Star := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hpre, ht1j⟩
      exact mem_intervalRange.mpr ⟨ht1j, mem_prefixRange.mp hpre⟩
    · intro hj
      rcases mem_intervalRange.mp hj with ⟨ht1j, hjt3⟩
      exact Finset.mem_filter.mpr ⟨mem_prefixRange.mpr hjt3, ht1j⟩
  have hzero :
      Finset.sum ((prefixRange Γ.t3Star).filter fun j => ¬ C.t1 ≤ j) C.muBC = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [C.muBC_eq_muB_add_muC,
      C.memberships_muB_eq_zero_of_lt_t1 (lt_of_not_ge (Finset.mem_filter.mp hj).2),
      C.memberships_muC_eq_zero_of_lt_t1 (lt_of_not_ge (Finset.mem_filter.mp hj).2)]
    ring
  rw [hset, hzero, add_zero] at hsplit2
  simpa [prefixRange_lastIdx_eq_univ] using hsplit1.trans hsplit2.symm

theorem poolValue_at_last_eq_case5_gap
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht3last : Γ.t3Star < lastIdx n) :
    C.poolValue AUX (lastIdx n) =
      I.program.epsilon *
        (Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC -
          Finset.sum Finset.univ (fun j => (C.memberships).muD j * C.chi j)) := by
  rw [C.poolValue_eq_totalGeneratedMass_sub_creditSum_at_last AUX,
    C.totalGeneratedMass_eq_sum_generatedColumnValue AUX]
  calc
    Finset.sum Finset.univ (fun j => C.generatedColumnValue AUX j) -
        Finset.sum Finset.univ (fun j => C.creditValue AUX (lastIdx n) j)
      = Finset.sum Finset.univ
          (fun j => C.generatedColumnValue AUX j - C.creditValue AUX (lastIdx n) j) := by
            rw [← Finset.sum_sub_distrib]
    _ = Finset.sum Finset.univ
          (fun j => I.program.epsilon * (C.muBC j - (C.memberships).muD j * C.chi j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [C.generatedColumn_sub_credit_at_last_eq_case5_term
              AUX hΓ hγlo hγhi hθpos ht3last j]
    _ = I.program.epsilon *
          Finset.sum Finset.univ (fun j => C.muBC j - (C.memberships).muD j * C.chi j) := by
            rw [Finset.mul_sum]
    _ = I.program.epsilon *
          (Finset.sum Finset.univ C.muBC -
            Finset.sum Finset.univ (fun j => (C.memberships).muD j * C.chi j)) := by
              congr 1
              rw [Finset.sum_sub_distrib]
    _ = I.program.epsilon *
          (Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC -
            Finset.sum Finset.univ (fun j => (C.memberships).muD j * C.chi j)) := by
              rw [C.sum_univ_muBC_eq_sum_interval_t1_t3 hΓ]

theorem poolValue_nonneg_at_last_of_case5_claim
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht3last : Γ.t3Star < lastIdx n)
    (hclaim :
      Finset.sum Finset.univ (fun j => (C.memberships).muD j * C.chi j) ≤
        Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC) :
    0 ≤ C.poolValue AUX (lastIdx n) := by
  rw [C.poolValue_at_last_eq_case5_gap AUX hΓ hγlo hγhi hθpos ht3last]
  have hεnonneg : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  exact mul_nonneg hεnonneg (sub_nonneg.mpr hclaim)

theorem constructedDualSolution_poolCredit_nonneg_at_last_of_case5_claim
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht3last : Γ.t3Star < lastIdx n)
    (hclaim :
      Finset.sum Finset.univ (fun j => (C.memberships).muD j * C.chi j) ≤
        Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC) :
    0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) (lastIdx n) := by
  rw [C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX (lastIdx n),
    C.shiftedPoolValue_eq_poolValue_at_last AUX hΓ hγlo hγhi]
  exact C.poolValue_nonneg_at_last_of_case5_claim AUX hΓ hγlo hγhi hθpos ht3last hclaim

theorem generatedMassPrefix_eq_totalGeneratedMass_at_t3Star
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    C.generatedMassPrefix AUX Γ.t3Star = C.totalGeneratedMass AUX := by
  unfold ProfileData.generatedMassPrefix ProfileData.totalGeneratedMass
  have hset : (Finset.univ.filter fun p : Idx n => p ≤ Γ.t3Star) = prefixRange Γ.t3Star := by
    ext p
    simp [prefixRange]
  have hzero :
      Finset.sum (Finset.univ.filter fun p : Idx n => ¬ p ≤ Γ.t3Star)
        (fun p => Finset.sum Finset.univ (fun j => C.gValue AUX p j)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hgt3 : Γ.t3Star < p := lt_of_not_ge (Finset.mem_filter.mp hp).2
    apply Finset.sum_eq_zero
    intro j hj
    exact C.gValue_eq_zero_of_t3_lt AUX hΓ hγlo hγhi hθpos hgt3
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun p : Idx n => p ≤ Γ.t3Star)
      (fun p => Finset.sum Finset.univ (fun j => C.gValue AUX p j))
  rw [hset, hzero, add_zero] at hsplit
  simpa using hsplit

theorem poolValue_eq_totalGeneratedMass_sub_creditSum_at_t3Star
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    C.poolValue AUX Γ.t3Star =
      C.totalGeneratedMass AUX -
        Finset.sum (prefixRange Γ.t3Star) (fun j => C.creditValue AUX Γ.t3Star j) := by
  rw [C.poolValue_eq_generatedMassPrefix_sub_creditSum AUX Γ.t3Star,
    C.generatedMassPrefix_eq_totalGeneratedMass_at_t3Star AUX hΓ hγlo hγhi hθpos]

theorem generatedColumn_sub_credit_at_t3Star_ge_case4_terms
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hjt3 : j ≤ Γ.t3Star) :
    C.case4BCLift j - C.case4FrontierDeficit j ≤
      C.generatedColumnValue AUX j - C.creditValue AUX Γ.t3Star j := by
  by_cases hlt : I.firstBidTime j < Γ.t3Star
  · have hμD0 : Γ.muD j = 0 := Advice.muD_eq_zero Γ hlt
    have hA :
        (C.memberships).muA j * C.creditAfterA AUX Γ.t3Star j =
          (C.memberships).muA j *
            (1 - I.program.epsilon *
              (1 -
                posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
                  I.program.theta)) := by
      by_cases hμA0 : (C.memberships).muA j = 0
      · simp [hμA0]
      · have hμApos : 0 < (C.memberships).muA j := by
          have hμAnonneg := (C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds).1 j
          exact lt_of_le_of_ne hμAnonneg (Ne.symm hμA0)
        rw [C.creditAfterA_at_t3Star_eq AUX hγlo hγhi hθpos hμApos hlt]
    have hcredit :
        C.creditValue AUX Γ.t3Star j =
          1 -
            I.program.epsilon *
              ((C.memberships).muA j *
                  (1 -
                    posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
                      I.program.theta) +
                C.muBC j) := by
      rw [C.creditValue_after_eq_weighted AUX hΓ hγlo hγhi hθpos hjt3 (le_of_lt hlt)]
      unfold weightedCreditAfter ProfileData.muBC creditAfterB creditAfterC creditAfterD
      rw [hA, C.memberships_muD, hμD0]
      simp [hlt]
      have htotal :
          (C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j = 1 := by
        have htotal' := C.memberships_total j
        rw [MembershipWeights.total, C.memberships_muD, hμD0] at htotal'
        linarith
      linarith
    have hgen :=
      C.generatedColumnValue_eq_one_sub_epsilon_mul AUX hΓ hγlo hγhi hθpos j
    rw [ProfileData.case4BCLift, if_pos hlt, ProfileData.case4FrontierDeficit,
      if_neg (ne_of_lt hlt), hgen, hcredit, C.memberships_muD, hμD0]
    ring_nf
    exact le_rfl
  · by_cases heq : I.firstBidTime j = Γ.t3Star
    · have hcredit : C.creditValue AUX Γ.t3Star j = 1 := by
        exact C.creditValue_eq_one_of_eq_firstBidTime AUX hΓ hγlo hγhi hθpos hjt3 heq.symm
      have htail0 : tailBudget C.hatG Γ.t3Star = 0 :=
        C.tailBudget_eq_zero_of_t3_le hγlo hγhi hθpos le_rfl
      have hfactor0 :
          1 -
              posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) /
                I.program.theta = 0 := by
        rw [heq, htail0, sub_zero, posPart_of_nonneg (le_of_lt hθpos)]
        field_simp [ne_of_gt hθpos]
        ring
      have hgen :=
        C.generatedColumnValue_eq_one_sub_epsilon_mul AUX hΓ hγlo hγhi hθpos j
      rw [ProfileData.case4BCLift, if_neg (by simp [heq]),
        ProfileData.case4FrontierDeficit, if_pos heq, hgen, hcredit, hfactor0]
      ring_nf
      exact le_rfl
    · have hgt : Γ.t3Star < I.firstBidTime j := lt_of_not_ge (by
          intro hle
          exact hlt (lt_of_le_of_ne hle heq))
      have hμD1 : Γ.muD j = 1 := Advice.muD_eq_one Γ hgt
      have htail0 : tailBudget C.hatG Γ.t3Star = 0 :=
        C.tailBudget_eq_zero_of_t3_le hγlo hγhi hθpos le_rfl
      have hcredit :
          C.creditValue AUX Γ.t3Star j = beforeBudget C.hatG j := by
        calc
          C.creditValue AUX Γ.t3Star j =
              beforeBudget C.hatG j - tailBudget C.hatG Γ.t3Star := by
                simpa using
                  C.creditValue_D_before_eq_of_integralD AUX hΓ hγlo hγhi hθpos hμD1 hjt3 hgt
          _ = beforeBudget C.hatG j := by rw [htail0, sub_zero]
      have hA0 : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_muD_eq_one hΓ hμD1
      have hgen :
          C.generatedColumnValue AUX j = 1 - I.program.epsilon * C.chi j := by
        rw [C.generatedColumnValue_eq_one_sub_epsilon_mul AUX hΓ hγlo hγhi hθpos j,
          hA0, C.memberships_muD, hμD1]
        ring
      rw [ProfileData.case4BCLift,
        if_neg (show ¬ I.firstBidTime j < Γ.t3Star from hlt),
        ProfileData.case4FrontierDeficit, if_neg heq, hgen, hcredit]
      linarith [C.beforeBudget_le_one_sub_epsilon_mul_chi hΓ hγlo hγhi hθpos j]

theorem poolValue_ge_case4_reduction
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j) -
        Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) +
        Finset.sum (strictSuffixRange Γ.t3Star) (fun j => C.generatedColumnValue AUX j) ≤
      C.poolValue AUX Γ.t3Star := by
  have hprefix :
      Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j - C.case4FrontierDeficit j) ≤
        Finset.sum (prefixRange Γ.t3Star)
          (fun j => C.generatedColumnValue AUX j - C.creditValue AUX Γ.t3Star j) := by
    exact Finset.sum_le_sum (fun j hj =>
      C.generatedColumn_sub_credit_at_t3Star_ge_case4_terms AUX hΓ hγlo hγhi hθpos
        (hjt3 := mem_prefixRange.mp hj))
  rw [C.poolValue_eq_totalGeneratedMass_sub_creditSum_at_t3Star AUX hΓ hγlo hγhi hθpos,
    C.totalGeneratedMass_eq_sum_generatedColumnValue AUX,
    sum_univ_eq_prefix_add_strictSuffix (f := fun j => C.generatedColumnValue AUX j) Γ.t3Star]
  rw [← Finset.sum_sub_distrib]
  have hprefix' := hprefix
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hprefix'
  have hbc :
      Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j - C.case4FrontierDeficit j) =
        Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j) -
          Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) := by
    rw [Finset.sum_sub_distrib]
  rw [hbc]
  linarith

theorem muBC_eq_zero_of_lt_t1
    (C : ProfileData I Γ) {j : Idx n} (hjt1 : j < C.t1) :
    C.muBC j = 0 := by
  rw [C.muBC_eq_muB_add_muC, C.memberships_muB_eq_zero_of_lt_t1 hjt1,
    C.memberships_muC_eq_zero_of_lt_t1 hjt1]
  ring

theorem case4BCLift_eq_epsilon_mul_muBC_of_lt_pStar
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) (hpos : C.frontierPositive.Nonempty)
    {j : Idx n} (hjp : j < C.pStar hpos) :
    C.case4BCLift j = I.program.epsilon * C.muBC j := by
  by_cases hlt : I.firstBidTime j < Γ.t3Star
  · simp [ProfileData.case4BCLift, hlt]
  · have hge : Γ.t3Star ≤ I.firstBidTime j := not_lt.mp hlt
    by_cases hfront : I.firstBidTime j = Γ.t3Star
    · have hμ : Γ.muD j = 1 :=
        C.muD_eq_one_of_onFrontier_of_lt_pStar hΓ hpos hfront hjp
      rw [ProfileData.case4BCLift, if_neg hlt, C.muBC_eq_zero_of_muD_eq_one hΓ hμ]
      ring
    · have hgt : Γ.t3Star < I.firstBidTime j := by
        exact lt_of_le_of_ne hge (by
          intro hEq
          exact hfront hEq.symm)
      have hμ : Γ.muD j = 1 := Advice.muD_eq_one Γ hgt
      rw [ProfileData.case4BCLift, if_neg hlt, C.muBC_eq_zero_of_muD_eq_one hΓ hμ]
      ring

theorem case4FrontierDeficit_le_epsilon_mul_muDchi_of_lt_pStar
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (hpos : C.frontierPositive.Nonempty)
    {j : Idx n} (hjp : j < C.pStar hpos) :
    C.case4FrontierDeficit j ≤
      I.program.epsilon * (if C.t1 < j then Γ.muD j * C.chi j else 0) := by
  have hεnonneg : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hχnonneg : 0 ≤ C.chi j := C.chi_nonneg j
  have hμnonneg : 0 ≤ Γ.muD j := Advice.muD_nonneg_of_admissible Γ hΓ j
  by_cases hfront : I.firstBidTime j = Γ.t3Star
  · have hμ : Γ.muD j = 1 :=
      C.muD_eq_one_of_onFrontier_of_lt_pStar hΓ hpos hfront hjp
    by_cases ht1j : C.t1 < j
    · rw [ProfileData.case4FrontierDeficit, if_pos hfront, if_pos ht1j, C.memberships_muD, hμ]
      simp
    · have hjle : j ≤ C.t1 := not_lt.mp ht1j
      have hjt2 : j ≤ C.t2 := le_trans hjle C.t1_le_t2
      have hχ0 : C.chi j = 0 := C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos hjt2
      rw [ProfileData.case4FrontierDeficit, if_pos hfront, if_neg ht1j, C.memberships_muD, hμ,
        hχ0]
      simp
  · rw [ProfileData.case4FrontierDeficit, if_neg hfront]
    by_cases ht1j : C.t1 < j
    · rw [if_pos ht1j]
      exact mul_nonneg hεnonneg (mul_nonneg hμnonneg hχnonneg)
    · simp [ht1j]

theorem case4FrontierDeficit_eq_zero_of_pStar_lt
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) (hpos : C.frontierPositive.Nonempty)
    {j : Idx n} (hpj : C.pStar hpos < j) :
    C.case4FrontierDeficit j = 0 := by
  by_cases hfront : I.firstBidTime j = Γ.t3Star
  · have hμ : Γ.muD j = 0 :=
      C.muD_eq_zero_of_onFrontier_of_pStar_lt hΓ hpos hfront hpj
    rw [ProfileData.case4FrontierDeficit, if_pos hfront, C.memberships_muD, hμ]
    ring
  · simp [ProfileData.case4FrontierDeficit, hfront]

theorem case4_frontier_claim
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) ≤
      Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j) := by
  have hεnonneg : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have hBnonneg : ∀ j, 0 ≤ C.muBC j := by
    intro j
    rw [C.muBC_eq_muB_add_muC]
    linarith [hμnonneg.2.1 j, hμnonneg.2.2.1 j]
  have hcase4Bnonneg :
      0 ≤ Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j) := by
    apply Finset.sum_nonneg
    intro j hj
    by_cases hlt : I.firstBidTime j < Γ.t3Star
    · rw [ProfileData.case4BCLift, if_pos hlt]
      exact mul_nonneg hεnonneg (hBnonneg j)
    · simp [ProfileData.case4BCLift, hlt]
  by_cases hpos : C.frontierPositive.Nonempty
  · by_cases hp_t2 : C.pStar hpos ≤ C.t2
    · have hdef0 :
          Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        by_cases hfront : I.firstBidTime j = Γ.t3Star
        · by_cases hμ0 : Γ.muD j = 0
          · rw [ProfileData.case4FrontierDeficit, if_pos hfront, C.memberships_muD, hμ0]
            ring
          · have hμj_nonneg : 0 ≤ Γ.muD j := Advice.muD_nonneg_of_admissible Γ hΓ j
            have hμj_pos : 0 < Γ.muD j := lt_of_le_of_ne hμj_nonneg (Ne.symm hμ0)
            have hjmem : j ∈ C.frontierPositive := by
              exact C.mem_frontierPositive.mpr ⟨hfront, hμj_pos⟩
            have hjle : j ≤ C.pStar hpos := C.le_pStar_of_mem_frontierPositive hpos hjmem
            have hjt2 : j ≤ C.t2 := le_trans hjle hp_t2
            have hχ0 : C.chi j = 0 := C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos hjt2
            rw [ProfileData.case4FrontierDeficit, if_pos hfront, C.memberships_muD, hχ0]
            ring
        · simp [ProfileData.case4FrontierDeficit, hfront]
      rw [hdef0]
      exact hcase4Bnonneg
    · have hp_t2' : C.t2 < C.pStar hpos := lt_of_not_ge hp_t2
      have hi0 : 0 < (C.pStar hpos).1 := by
        have hvals : C.t2.1 < (C.pStar hpos).1 := Fin.lt_def.mp hp_t2'
        omega
      have ht1p : C.t1 < C.pStar hpos := lt_of_le_of_lt C.t1_le_t2 hp_t2'
      have hcore :=
        C.sum_interval_muBC_ge_case4_chi_core
          hΓ hγlo hγhi hθpos hi0 ht1p (C.pStar_le_t3Star hpos)
      have hltset :
          Finset.univ.filter (fun j : Idx n => j < C.pStar hpos) =
            prefixRange (predIdx hi0) := by
        ext j
        constructor
        · intro hj
          rcases Finset.mem_filter.mp hj with ⟨_, hjlt⟩
          exact mem_prefixRange.mpr <| Fin.le_def.mpr (by
            have hvals : j.1 < (C.pStar hpos).1 := Fin.lt_def.mp hjlt
            change j.1 ≤ (C.pStar hpos).1 - 1
            omega)
        · intro hj
          refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
          exact lt_of_le_of_lt (mem_prefixRange.mp hj) (predIdx_lt hi0)
      have hmuPrefix :
          Finset.sum (prefixRange (predIdx hi0)) C.muBC =
            Finset.sum (intervalRange C.t1 (predIdx hi0)) C.muBC := by
        have hset :
            (prefixRange (predIdx hi0)).filter (fun j => C.t1 ≤ j) =
              intervalRange C.t1 (predIdx hi0) := by
          ext j
          constructor
          · intro hj
            rcases Finset.mem_filter.mp hj with ⟨hjp, ht1j⟩
            exact mem_intervalRange.mpr ⟨ht1j, mem_prefixRange.mp hjp⟩
          · intro hj
            rcases mem_intervalRange.mp hj with ⟨ht1j, hjp⟩
            exact Finset.mem_filter.mpr ⟨mem_prefixRange.mpr hjp, ht1j⟩
        have hzero :
            Finset.sum ((prefixRange (predIdx hi0)).filter fun j => ¬ C.t1 ≤ j) C.muBC = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjt1 : j < C.t1 := lt_of_not_ge (Finset.mem_filter.mp hj).2
          rw [C.muBC_eq_zero_of_lt_t1 hjt1]
        have hsplit :=
          Finset.sum_filter_add_sum_filter_not
            (s := prefixRange (predIdx hi0)) (p := fun j => C.t1 ≤ j) C.muBC
        rw [hset, hzero, add_zero] at hsplit
        simpa using hsplit.symm
      have hBlt :
          Finset.sum (Finset.univ.filter fun j : Idx n => j < C.pStar hpos)
              (fun j => C.case4BCLift j) =
            I.program.epsilon *
              Finset.sum (intervalRange C.t1 (predIdx hi0)) C.muBC := by
        rw [hltset]
        calc
          Finset.sum (prefixRange (predIdx hi0)) (fun j => C.case4BCLift j)
            = Finset.sum (prefixRange (predIdx hi0)) (fun j => I.program.epsilon * C.muBC j) := by
                apply Finset.sum_congr rfl
                intro j hj
                have hjlt : j < C.pStar hpos := by
                  exact lt_of_le_of_lt (mem_prefixRange.mp hj) (predIdx_lt hi0)
                exact C.case4BCLift_eq_epsilon_mul_muBC_of_lt_pStar hΓ hpos hjlt
          _ = I.program.epsilon * Finset.sum (prefixRange (predIdx hi0)) C.muBC := by
                rw [Finset.mul_sum]
          _ = I.program.epsilon * Finset.sum (intervalRange C.t1 (predIdx hi0)) C.muBC := by
                rw [hmuPrefix]
      have hDefLt :
          Finset.sum (Finset.univ.filter fun j : Idx n => j < C.pStar hpos)
              (fun j => C.case4FrontierDeficit j) ≤
            I.program.epsilon *
              Finset.sum (intervalRange C.t1 (predIdx hi0))
                (fun l => if C.t1 < l then Γ.muD l * C.chi l else 0) := by
        rw [hltset]
        calc
          Finset.sum (prefixRange (predIdx hi0)) (fun j => C.case4FrontierDeficit j)
            ≤ Finset.sum (prefixRange (predIdx hi0))
                (fun j => I.program.epsilon * (if C.t1 < j then Γ.muD j * C.chi j else 0)) := by
                  apply Finset.sum_le_sum
                  intro j hj
                  have hjlt : j < C.pStar hpos := by
                    exact lt_of_le_of_lt (mem_prefixRange.mp hj) (predIdx_lt hi0)
                  exact C.case4FrontierDeficit_le_epsilon_mul_muDchi_of_lt_pStar
                    hΓ hγlo hγhi hθpos hpos hjlt
          _ = I.program.epsilon *
                Finset.sum (prefixRange (predIdx hi0))
                  (fun j => if C.t1 < j then Γ.muD j * C.chi j else 0) := by
                    rw [Finset.mul_sum]
          _ = I.program.epsilon *
                Finset.sum (intervalRange C.t1 (predIdx hi0))
                  (fun l => if C.t1 < l then Γ.muD l * C.chi l else 0) := by
                    apply congrArg (HMul.hMul I.program.epsilon)
                    have hset :
                        (prefixRange (predIdx hi0)).filter (fun j => C.t1 ≤ j) =
                          intervalRange C.t1 (predIdx hi0) := by
                      ext j
                      constructor
                      · intro hj
                        rcases Finset.mem_filter.mp hj with ⟨hjp, ht1j⟩
                        exact mem_intervalRange.mpr ⟨ht1j, mem_prefixRange.mp hjp⟩
                      · intro hj
                        rcases mem_intervalRange.mp hj with ⟨ht1j, hjp⟩
                        exact Finset.mem_filter.mpr ⟨mem_prefixRange.mpr hjp, ht1j⟩
                    have hzero :
                        Finset.sum
                            ((prefixRange (predIdx hi0)).filter fun j => ¬ C.t1 ≤ j)
                            (fun j => if C.t1 < j then Γ.muD j * C.chi j else 0) = 0 := by
                      apply Finset.sum_eq_zero
                      intro j hj
                      have hjt1 : j < C.t1 := lt_of_not_ge (Finset.mem_filter.mp hj).2
                      simp [not_lt_of_gt hjt1]
                    have hsplit :=
                      Finset.sum_filter_add_sum_filter_not
                        (s := prefixRange (predIdx hi0))
                        (p := fun j => C.t1 ≤ j)
                        (fun j => if C.t1 < j then Γ.muD j * C.chi j else 0)
                    rw [hset, hzero, add_zero] at hsplit
                    simpa using hsplit.symm
      have hDefSelf :
          C.case4FrontierDeficit (C.pStar hpos) ≤ I.program.epsilon * C.chi (C.pStar hpos) := by
        have hμle : Γ.muD (C.pStar hpos) ≤ 1 :=
          Advice.muD_le_one_of_admissible Γ hΓ (C.pStar hpos)
        have hχnonneg : 0 ≤ C.chi (C.pStar hpos) := C.chi_nonneg (C.pStar hpos)
        rw [ProfileData.case4FrontierDeficit, if_pos (C.pStar_onFrontier hpos), C.memberships_muD]
        have hmul :
            I.program.epsilon * (Γ.muD (C.pStar hpos) * C.chi (C.pStar hpos)) ≤
              I.program.epsilon * (1 * C.chi (C.pStar hpos)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hμle hχnonneg) hεnonneg
        simpa [mul_assoc] using hmul
      have hDefSuffix0 :
          Finset.sum (strictSuffixRange (C.pStar hpos))
              (fun j => C.case4FrontierDeficit j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact C.case4FrontierDeficit_eq_zero_of_pStar_lt hΓ hpos (mem_strictSuffixRange.mp hj)
      have hBself : C.case4BCLift (C.pStar hpos) = 0 := by
        simp [ProfileData.case4BCLift, C.pStar_onFrontier hpos]
      have hBsuffixNonneg :
          0 ≤ Finset.sum (strictSuffixRange (C.pStar hpos)) (fun j => C.case4BCLift j) := by
        apply Finset.sum_nonneg
        intro j hj
        by_cases hlt : I.firstBidTime j < Γ.t3Star
        · rw [ProfileData.case4BCLift, if_pos hlt]
          exact mul_nonneg hεnonneg (hBnonneg j)
        · simp [ProfileData.case4BCLift, hlt]
      have hDefAfterT3 :
          Finset.sum (strictSuffixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have ht3j : Γ.t3Star < j := mem_strictSuffixRange.mp hj
        have hfront : ¬ I.firstBidTime j = Γ.t3Star := by
          intro hEq
          exact (not_le_of_gt ht3j) (by simpa [hEq] using I.le_firstBidTime j)
        simp [ProfileData.case4FrontierDeficit, hfront]
      have hBAfterT3 :
          Finset.sum (strictSuffixRange Γ.t3Star) (fun j => C.case4BCLift j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have ht3j : Γ.t3Star < j := mem_strictSuffixRange.mp hj
        have hlt : ¬ I.firstBidTime j < Γ.t3Star := by
          intro hif
          exact (not_le_of_gt ht3j) (le_trans (I.le_firstBidTime j) (le_of_lt hif))
        simp [ProfileData.case4BCLift, hlt]
      have hDefPrefixUniv :
          Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) =
            Finset.sum Finset.univ (fun j => C.case4FrontierDeficit j) := by
        have hsum :=
          sum_univ_eq_prefix_add_strictSuffix
            (f := fun j => C.case4FrontierDeficit j) Γ.t3Star
        rw [hDefAfterT3, add_zero] at hsum
        exact hsum.symm
      have hBPrefixUniv :
          Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j) =
            Finset.sum Finset.univ (fun j => C.case4BCLift j) := by
        have hsum :=
          sum_univ_eq_prefix_add_strictSuffix
            (f := fun j => C.case4BCLift j) Γ.t3Star
        rw [hBAfterT3, add_zero] at hsum
        exact hsum.symm
      have hDefUnivLe :
          Finset.sum Finset.univ (fun j => C.case4FrontierDeficit j) ≤
            I.program.epsilon *
              (C.chi (C.pStar hpos) +
                Finset.sum (intervalRange C.t1 (predIdx hi0))
                  (fun l => if C.t1 < l then Γ.muD l * C.chi l else 0)) := by
        rw [sum_univ_eq_filter_lt_add_self_add_strictSuffix
          (f := fun j => C.case4FrontierDeficit j) (C.pStar hpos), hDefSuffix0]
        linarith
      have hBUnivGe :
          I.program.epsilon * Finset.sum (intervalRange C.t1 (predIdx hi0)) C.muBC ≤
            Finset.sum Finset.univ (fun j => C.case4BCLift j) := by
        rw [sum_univ_eq_filter_lt_add_self_add_strictSuffix
          (f := fun j => C.case4BCLift j) (C.pStar hpos), hBself, add_zero, hBlt]
        linarith
      have hcoreε :
          I.program.epsilon *
              (C.chi (C.pStar hpos) +
                Finset.sum (intervalRange C.t1 (predIdx hi0))
                  (fun l => if C.t1 < l then Γ.muD l * C.chi l else 0)) ≤
            I.program.epsilon * Finset.sum (intervalRange C.t1 (predIdx hi0)) C.muBC := by
        exact mul_le_mul_of_nonneg_left hcore hεnonneg
      rw [hDefPrefixUniv, hBPrefixUniv]
      linarith
  · have hdef0 :
        Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hfront : I.firstBidTime j = Γ.t3Star
      · have hμnonneg' : 0 ≤ Γ.muD j := Advice.muD_nonneg_of_admissible Γ hΓ j
        have hμ0 : Γ.muD j = 0 := by
          by_contra hμ0
          have hμpos : 0 < Γ.muD j := lt_of_le_of_ne hμnonneg' (Ne.symm hμ0)
          exact hpos ⟨j, C.mem_frontierPositive.mpr ⟨hfront, hμpos⟩⟩
        rw [ProfileData.case4FrontierDeficit, if_pos hfront, C.memberships_muD, hμ0]
        ring
      · simp [ProfileData.case4FrontierDeficit, hfront]
    rw [hdef0]
    exact hcase4Bnonneg

theorem poolValue_nonneg_at_t3Star
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    0 ≤ C.poolValue AUX Γ.t3Star := by
  have hgenNonneg :
      0 ≤ Finset.sum (strictSuffixRange Γ.t3Star) (fun j => C.generatedColumnValue AUX j) := by
    apply Finset.sum_nonneg
    intro j hj
    exact C.generatedColumnValue_nonneg AUX hΓ hγlo hγhi j
  have hclaim :
      Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) ≤
        Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j) +
          Finset.sum (strictSuffixRange Γ.t3Star) (fun j => C.generatedColumnValue AUX j) := by
    have hfrontier := C.case4_frontier_claim hΓ hγlo hγhi hθpos
    linarith
  have hred := C.poolValue_ge_case4_reduction AUX hΓ hγlo hγhi hθpos
  linarith

theorem constructedDualSolution_poolCredit_nonneg_at_t3Star
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) Γ.t3Star := by
  rw [C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX Γ.t3Star,
    C.shiftedPoolValue_eq_poolValue_at_t3Star AUX hΓ hγlo hγhi hθpos]
  exact C.poolValue_nonneg_at_t3Star AUX hΓ hγlo hγhi hθpos

theorem poolValue_nonneg_at_t3Star_of_case4_claim
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    (hclaim :
      Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) ≤
        Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j) +
          Finset.sum (strictSuffixRange Γ.t3Star) (fun j => C.generatedColumnValue AUX j)) :
    0 ≤ C.poolValue AUX Γ.t3Star := by
  have hred := C.poolValue_ge_case4_reduction AUX hΓ hγlo hγhi hθpos
  linarith

theorem constructedDualSolution_poolCredit_nonneg_at_t3Star_of_case4_claim
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    (hclaim :
      Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4FrontierDeficit j) ≤
        Finset.sum (prefixRange Γ.t3Star) (fun j => C.case4BCLift j) +
          Finset.sum (strictSuffixRange Γ.t3Star) (fun j => C.generatedColumnValue AUX j)) :
    0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) Γ.t3Star := by
  rw [C.constructedDualSolution_poolCredit_eq_shiftedPoolValue AUX Γ.t3Star,
    C.shiftedPoolValue_eq_poolValue_at_t3Star AUX hΓ hγlo hγhi hθpos]
  exact C.poolValue_nonneg_at_t3Star_of_case4_claim AUX hΓ hγlo hγhi hθpos hclaim

theorem sum_strictSuffix_muDchi_eq_futureCount
    (C : ProfileData I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    Finset.sum (strictSuffixRange Γ.t3Star) (fun j => (C.memberships).muD j * C.chi j) =
      futureCount Γ.t3Star := by
  calc
    Finset.sum (strictSuffixRange Γ.t3Star) (fun j => (C.memberships).muD j * C.chi j)
      = Finset.sum (strictSuffixRange Γ.t3Star) (fun _ => (1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have ht3j : Γ.t3Star < j := mem_strictSuffixRange.mp hj
          have hμ : Γ.muD j = 1 :=
            Advice.muD_eq_one Γ (lt_of_lt_of_le ht3j (I.le_firstBidTime j))
          have hχ : C.chi j = 1 := C.chi_eq_one_of_t3_lt hγlo hγhi hθpos ht3j
          simp [hμ, hχ]
    _ = futureCount Γ.t3Star := by
          simp [futureCount, card_strictSuffixRange]

theorem sum_prefix_muDchi_eq_sum_interval_t1_t3
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    Finset.sum (prefixRange Γ.t3Star) (fun j => (C.memberships).muD j * C.chi j) =
      Finset.sum (intervalRange C.t1 Γ.t3Star) (fun j => (C.memberships).muD j * C.chi j) := by
  have hset :
      (prefixRange Γ.t3Star).filter (fun j => C.t1 ≤ j) = intervalRange C.t1 Γ.t3Star := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hpre, ht1j⟩
      exact mem_intervalRange.mpr ⟨ht1j, mem_prefixRange.mp hpre⟩
    · intro hj
      rcases mem_intervalRange.mp hj with ⟨ht1j, hjt3⟩
      exact Finset.mem_filter.mpr ⟨mem_prefixRange.mpr hjt3, ht1j⟩
  have hzero :
      Finset.sum ((prefixRange Γ.t3Star).filter fun j => ¬ C.t1 ≤ j)
        (fun j => (C.memberships).muD j * C.chi j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjt1 : j < C.t1 := lt_of_not_ge (Finset.mem_filter.mp hj).2
    have hjt2 : j ≤ C.t2 := le_trans (le_of_lt hjt1) C.t1_le_t2
    have hχ0 : C.chi j = 0 := C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos hjt2
    rw [hχ0]
    ring
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := prefixRange Γ.t3Star) (p := fun j => C.t1 ≤ j)
      (fun j => (C.memberships).muD j * C.chi j)
  rw [hset, hzero, add_zero] at hsplit
  simpa using hsplit.symm

theorem sum_univ_muDchi_eq_sum_interval_t1_t3_add_futureCount
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    Finset.sum Finset.univ (fun j => (C.memberships).muD j * C.chi j) =
      Finset.sum (intervalRange C.t1 Γ.t3Star) (fun j => (C.memberships).muD j * C.chi j) +
        futureCount Γ.t3Star := by
  have hsplit :=
    sum_univ_eq_prefix_add_strictSuffix
      (f := fun j => (C.memberships).muD j * C.chi j) Γ.t3Star
  rw [C.sum_prefix_muDchi_eq_sum_interval_t1_t3 hΓ hγlo hγhi hθpos,
    C.sum_strictSuffix_muDchi_eq_futureCount hγlo hγhi hθpos] at hsplit
  exact hsplit

theorem case5_mass_inequality_of_t3_lt_last
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht3last : Γ.t3Star < lastIdx n) :
    Finset.sum Finset.univ (fun j => (C.memberships).muD j * C.chi j) ≤
      Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC := by
  let gap : Idx n → ℝ := fun l =>
    (I.program.barTau - beforeBudget C.hatG l) / (beforeBudget C.hatG l + I.program.tau)
  have ht1t3 : C.t1 ≤ Γ.t3Star := C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos
  have hτpos : 0 < I.program.tau := tau_pos_of_theta_pos I.program hγlo hθpos
  have htail0 : tailBudget C.hatG Γ.t3Star = 0 :=
    C.tailBudget_eq_zero_of_t3_le hγlo hγhi hθpos le_rfl
  have hquot :=
    C.futureCount_div_tailBudget_eq_t1_mass_sub_weightQuotient
      hΓ hγlo hγhi hθpos (ht1i := ht1t3) (hit3 := le_rfl) ht3last
  rw [htail0, zero_add] at hquot
  have hweights :
      Finset.sum (intervalRange C.t1 Γ.t3Star)
          (fun l => C.phaseTwoWeight C.t1 l / (tailBudget C.hatG C.t1 + I.program.tau)) =
        Finset.sum (intervalRange C.t1 Γ.t3Star)
          (fun l =>
            if C.t1 < l then Γ.muD l / (beforeBudget C.hatG l + I.program.tau) else 0) := by
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlt : C.t1 < l
    · rw [if_pos hlt, C.phaseTwoWeight_t1_div_boundary_of_lt hΓ hγlo hθpos hlt]
    · simp [ProfileData.phaseTwoWeight, hlt]
  have hmuSplit :
      Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC =
        C.muBC C.t1 +
          Finset.sum
            (intervalRange C.t1 Γ.t3Star)
            (fun l => if C.t1 < l then C.muBC l else 0) := by
    have hmem : C.t1 ∈ intervalRange C.t1 Γ.t3Star := mem_intervalRange.mpr ⟨le_rfl, ht1t3⟩
    calc
      Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC
        = Finset.sum (intervalRange C.t1 Γ.t3Star)
            (fun l =>
              (if l = C.t1 then C.muBC C.t1 else 0) +
                (if C.t1 < l then C.muBC l else 0)) := by
              apply Finset.sum_congr rfl
              intro l hl
              by_cases hEq : l = C.t1
              · subst l
                simp
              · have hlt : C.t1 < l := lt_of_le_of_ne (mem_intervalRange.mp hl).1 (Ne.symm hEq)
                simp [hEq, hlt]
      _ =
          Finset.sum (intervalRange C.t1 Γ.t3Star)
            (fun l => if l = C.t1 then C.muBC C.t1 else 0) +
            Finset.sum (intervalRange C.t1 Γ.t3Star)
              (fun l => if C.t1 < l then C.muBC l else 0) := by
              rw [Finset.sum_add_distrib]
      _ = C.muBC C.t1 +
            Finset.sum (intervalRange C.t1 Γ.t3Star)
              (fun l => if C.t1 < l then C.muBC l else 0) := by
              rw [Finset.sum_eq_single C.t1]
              · simp
              · intro l hl hne
                simp [hne]
              · intro hnot
                exact False.elim (hnot hmem)
  have hstrict :=
    C.sum_interval_strict_muBC_add_muD_eq_futureCount_sub
      (ht1j := le_rfl) (hji := ht1t3) (hit3 := le_rfl)
  have hstrictSplit :
      Finset.sum (intervalRange C.t1 Γ.t3Star)
          (fun l => if C.t1 < l then (C.muBC l + Γ.muD l) else 0) =
        Finset.sum (intervalRange C.t1 Γ.t3Star) (fun l => if C.t1 < l then C.muBC l else 0) +
          Finset.sum
            (intervalRange C.t1 Γ.t3Star)
            (fun l => if C.t1 < l then Γ.muD l else 0) := by
    calc
      Finset.sum (intervalRange C.t1 Γ.t3Star)
          (fun l => if C.t1 < l then (C.muBC l + Γ.muD l) else 0)
        = Finset.sum (intervalRange C.t1 Γ.t3Star)
            (fun l => (if C.t1 < l then C.muBC l else 0) + (if C.t1 < l then Γ.muD l else 0)) := by
              apply Finset.sum_congr rfl
              intro l hl
              by_cases hlt : C.t1 < l <;> simp [hlt]
      _ =
          Finset.sum (intervalRange C.t1 Γ.t3Star)
            (fun l => if C.t1 < l then C.muBC l else 0) +
            Finset.sum (intervalRange C.t1 Γ.t3Star)
              (fun l => if C.t1 < l then Γ.muD l else 0) := by
              rw [Finset.sum_add_distrib]
  have hcount :
      Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC +
          Finset.sum (intervalRange C.t1 Γ.t3Star) (fun l => if C.t1 < l then Γ.muD l else 0) =
        futureCount C.t1 + C.muBC C.t1 - futureCount Γ.t3Star := by
    have haux :
        Finset.sum (intervalRange C.t1 Γ.t3Star) (fun l => if C.t1 < l then C.muBC l else 0) +
            Finset.sum (intervalRange C.t1 Γ.t3Star)
              (fun l => if C.t1 < l then Γ.muD l else 0) =
          futureCount C.t1 - futureCount Γ.t3Star := by
      rw [← hstrictSplit, hstrict]
    calc
      Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC +
          Finset.sum (intervalRange C.t1 Γ.t3Star) (fun l => if C.t1 < l then Γ.muD l else 0)
        = C.muBC C.t1 +
            (Finset.sum (intervalRange C.t1 Γ.t3Star)
                (fun l => if C.t1 < l then C.muBC l else 0) +
              Finset.sum (intervalRange C.t1 Γ.t3Star)
                (fun l => if C.t1 < l then Γ.muD l else 0)) := by
              rw [hmuSplit]
              ring
      _ = C.muBC C.t1 + (futureCount C.t1 - futureCount Γ.t3Star) := by
            rw [haux]
      _ = futureCount C.t1 + C.muBC C.t1 - futureCount Γ.t3Star := by
            ring
  have hgapSum :
      Finset.sum (intervalRange C.t1 Γ.t3Star)
          (fun l => if C.t1 < l then Γ.muD l / (beforeBudget C.hatG l + I.program.tau) else 0) -
        Finset.sum (intervalRange C.t1 Γ.t3Star) (fun l => if C.t1 < l then Γ.muD l else 0) =
      Finset.sum (intervalRange C.t1 Γ.t3Star)
        (fun l => if C.t1 < l then Γ.muD l * gap l else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlt : C.t1 < l
    · have hhatnonneg := C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
      have hbefore_nonneg : 0 ≤ beforeBudget C.hatG l := by
        exact beforeBudget_nonneg_of_nonneg hhatnonneg l
      have hden_pos : 0 < beforeBudget C.hatG l + I.program.tau := by
        linarith
      rw [if_pos hlt, if_pos hlt, if_pos hlt]
      unfold gap
      field_simp [hden_pos.ne']
      rw [DualProgram.barTau]
      ring
    · simp [hlt]
  have hfutureTerm :
      futureCount Γ.t3Star / I.program.tau - futureCount Γ.t3Star =
        futureCount Γ.t3Star * (I.program.barTau / I.program.tau) := by
    calc
      futureCount Γ.t3Star / I.program.tau - futureCount Γ.t3Star
        = futureCount Γ.t3Star * (1 / I.program.tau - 1) := by ring
      _ = futureCount Γ.t3Star * (I.program.barTau / I.program.tau) := by
            congr 1
            rw [DualProgram.barTau]
            field_simp [ne_of_gt hτpos]
  have hrepr :
      Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC =
        futureCount Γ.t3Star * (I.program.barTau / I.program.tau) +
          Finset.sum (intervalRange C.t1 Γ.t3Star)
            (fun l => if C.t1 < l then Γ.muD l * gap l else 0) := by
    rw [hweights] at hquot
    have htmp :
        Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC =
          futureCount Γ.t3Star / I.program.tau - futureCount Γ.t3Star +
            (Finset.sum (intervalRange C.t1 Γ.t3Star)
                (fun l =>
                  if C.t1 < l then Γ.muD l / (beforeBudget C.hatG l + I.program.tau) else 0) -
              Finset.sum (intervalRange C.t1 Γ.t3Star)
                (fun l => if C.t1 < l then Γ.muD l else 0)) := by
      linarith
    rw [hfutureTerm, hgapSum] at htmp
    exact htmp
  have hratio_ge_one : 1 ≤ I.program.barTau / I.program.tau := by
    have hτlebar : I.program.tau ≤ I.program.barTau :=
      tau_le_barTau_of_le_153_div_125 I.program hγlo hγhi
    exact (one_le_div hτpos).2 hτlebar
  have hfuture_le :
      futureCount Γ.t3Star ≤ futureCount Γ.t3Star * (I.program.barTau / I.program.tau) := by
    simpa using mul_le_mul_of_nonneg_left hratio_ge_one (futureCount_nonneg Γ.t3Star)
  have hchi_le :
      Finset.sum (intervalRange C.t1 Γ.t3Star) (fun j => (C.memberships).muD j * C.chi j) ≤
        Finset.sum (intervalRange C.t1 Γ.t3Star)
          (fun l => if C.t1 < l then Γ.muD l * gap l else 0) := by
    apply Finset.sum_le_sum
    intro l hl
    by_cases hlt : C.t1 < l
    · rw [C.memberships_muD, if_pos hlt]
      exact mul_le_mul_of_nonneg_left
        (C.case4Gap_ge_chi_of_t1_lt hΓ hγlo hγhi hθpos hlt)
        (Advice.muD_nonneg_of_admissible Γ hΓ l)
    · have hlt2 : l ≤ C.t2 := le_trans (not_lt.mp hlt) C.t1_le_t2
      have hχ0 : C.chi l = 0 := C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos hlt2
      rw [C.memberships_muD, hχ0]
      simp [hlt]
  have hinterval :
      futureCount Γ.t3Star +
          Finset.sum (intervalRange C.t1 Γ.t3Star) (fun j => (C.memberships).muD j * C.chi j) ≤
        Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC := by
    rw [hrepr]
    linarith
  rw [C.sum_univ_muDchi_eq_sum_interval_t1_t3_add_futureCount hΓ hγlo hγhi hθpos]
  linarith

theorem constructedDualSolution_satisfiesPoolConstraints_of_case5_claim
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    (hcase5 :
      Finset.sum Finset.univ (fun j => (C.memberships).muD j * C.chi j) ≤
        Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC) :
    DualSolution.SatisfiesPoolConstraints (C.constructedDualSolution AUX) := by
  intro i
  by_cases hit1 : i < C.t1
  · exact C.constructedDualSolution_poolCredit_nonneg_of_lt_t1 AUX hΓ hγlo hγhi hθpos hit1
  · have ht1i : C.t1 ≤ i := le_of_not_gt hit1
    by_cases hi_t1 : i = C.t1
    · subst i
      by_cases ht1t3 : C.t1 < Γ.t3Star
      · exact C.constructedDualSolution_poolCredit_nonneg_at_t1_of_lt_t3 AUX hΓ hγlo hγhi ht1t3
      · have ht1le : C.t1 ≤ Γ.t3Star := C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos
        have ht1eqt3 : C.t1 = Γ.t3Star := le_antisymm ht1le (not_lt.mp ht1t3)
        simpa [ht1eqt3] using
          C.constructedDualSolution_poolCredit_nonneg_at_t3Star AUX hΓ hγlo hγhi hθpos
    · have ht1i' : C.t1 < i := lt_of_le_of_ne ht1i (Ne.symm hi_t1)
      by_cases hit3 : i < Γ.t3Star
      · exact
          C.constructedDualSolution_poolCredit_nonneg_of_between_t1_t3
            AUX hΓ hγlo hγhi hθpos ht1i' hit3
      · by_cases hi_t3 : i = Γ.t3Star
        · subst i
          exact C.constructedDualSolution_poolCredit_nonneg_at_t3Star AUX hΓ hγlo hγhi hθpos
        · have ht3i : Γ.t3Star < i := lt_of_le_of_ne (not_lt.mp hit3) (Ne.symm hi_t3)
          have ht3last : Γ.t3Star < lastIdx n := lt_of_lt_of_le ht3i (le_lastIdx i)
          have hlast :
              0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) (lastIdx n) := by
            exact
              C.constructedDualSolution_poolCredit_nonneg_at_last_of_case5_claim
                AUX hΓ hγlo hγhi hθpos ht3last hcase5
          exact
            C.constructedDualSolution_poolCredit_nonneg_of_after_t3_of_last_nonneg
              AUX hΓ hγlo hγhi hθpos ht3i hlast

theorem constructedDualSolution_satisfiesPoolConstraints
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    DualSolution.SatisfiesPoolConstraints (C.constructedDualSolution AUX) := by
  intro i
  by_cases hit1 : i < C.t1
  · exact C.constructedDualSolution_poolCredit_nonneg_of_lt_t1 AUX hΓ hγlo hγhi hθpos hit1
  · have ht1i : C.t1 ≤ i := le_of_not_gt hit1
    by_cases hi_t1 : i = C.t1
    · subst i
      by_cases ht1t3 : C.t1 < Γ.t3Star
      · exact C.constructedDualSolution_poolCredit_nonneg_at_t1_of_lt_t3 AUX hΓ hγlo hγhi ht1t3
      · have ht1le : C.t1 ≤ Γ.t3Star := C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos
        have ht1eqt3 : C.t1 = Γ.t3Star := le_antisymm ht1le (not_lt.mp ht1t3)
        simpa [ht1eqt3] using
          C.constructedDualSolution_poolCredit_nonneg_at_t3Star AUX hΓ hγlo hγhi hθpos
    · have ht1i' : C.t1 < i := lt_of_le_of_ne ht1i (Ne.symm hi_t1)
      by_cases hit3 : i < Γ.t3Star
      · exact
          C.constructedDualSolution_poolCredit_nonneg_of_between_t1_t3
            AUX hΓ hγlo hγhi hθpos ht1i' hit3
      · by_cases hi_t3 : i = Γ.t3Star
        · subst i
          exact C.constructedDualSolution_poolCredit_nonneg_at_t3Star AUX hΓ hγlo hγhi hθpos
        · have ht3i : Γ.t3Star < i := lt_of_le_of_ne (not_lt.mp hit3) (Ne.symm hi_t3)
          have ht3last : Γ.t3Star < lastIdx n := lt_of_lt_of_le ht3i (le_lastIdx i)
          have hcase5 :
              Finset.sum Finset.univ (fun j => (C.memberships).muD j * C.chi j) ≤
                Finset.sum (intervalRange C.t1 Γ.t3Star) C.muBC :=
            C.case5_mass_inequality_of_t3_lt_last hΓ hγlo hγhi hθpos ht3last
          have hlast :
              0 ≤ DualSolution.poolCredit (C.constructedDualSolution AUX) (lastIdx n) := by
            exact
              C.constructedDualSolution_poolCredit_nonneg_at_last_of_case5_claim
                AUX hΓ hγlo hγhi hθpos ht3last hcase5
          exact
            C.constructedDualSolution_poolCredit_nonneg_of_after_t3_of_last_nonneg
              AUX hΓ hγlo hγhi hθpos ht3i hlast

end ProfileData

end

end KMedian195


