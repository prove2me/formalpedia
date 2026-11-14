-- Prove2me | Definitions.Def_KMedian195_CreditLemmas
-- name    : KMedian195_CreditLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:29.987601+00:00
-- url     : https://prove2.me/theorems/5fd3c919-c69c-4d11-af6a-8e870f0e01a6
-- title:
--   KMedian195.CreditLemmas
-- statement:
--   This is module `KMedian195.CreditLemmas` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 124 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_CreditLemmas`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/CreditLemmas.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/CreditLemmas.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`), and:
* `if_pos`, `if_neg`, `dif_pos`, `dif_neg` (deprecated) are `if_pos`, `if_neg`,
  `dif_pos`, `dif_neg`.
-/
module

public import Definitions.Def_KMedian195_ColumnConstruction
public import Mathlib.Data.Fintype.Fin

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.CreditLemmas` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

noncomputable section

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem card_prefixRange (i : Idx n) : (prefixRange i).card = i.1.succ := by
  unfold prefixRange
  calc
    (Finset.univ.filter fun j : Idx n => j ≤ i).card = min n i.1.succ := by
      simpa only [Fin.le_def, Nat.lt_succ_iff] using
        (Fin.card_filter_val_lt (n := n) (m := i.1.succ))
    _ = i.1.succ := Nat.min_eq_right i.is_lt.succ_le

omit [NeZero n] in
theorem card_strictSuffixRange (j : Idx n) : (strictSuffixRange j).card = futureCountNat j := by
  have hcomp : strictSuffixRange j = Finset.univ \ prefixRange j := by
    ext i
    simp [strictSuffixRange, prefixRange, not_le]
  rw [hcomp, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, futureCountNat]
  have hinter : prefixRange j ∩ Finset.univ = prefixRange j := by
    ext i
    simp
  rw [hinter, card_prefixRange]

omit [NeZero n] in
theorem IsNextIndex.lt {i k : Idx n} (h : IsNextIndex i k) : k < i := by
  unfold IsNextIndex at h
  exact Fin.lt_def.mpr (by omega)

namespace ProfileData

variable {I : ProcedureInput n} {Γ : Advice I}

def integralClientCredit
    (g s t : Idx n → Idx n → ℝ) (i j : Idx n) : ℝ :=
  Finset.sum (strictSuffixRange j) (fun q => g j q) +
    Finset.sum (intervalRange j i) (fun p => g p j + t p j - s p j)

def creditB (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  integralClientCredit (C.gB AUX) (C.sB AUX) (C.tB AUX) i j

def creditC (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  integralClientCredit (C.gC AUX) (C.sC AUX) (C.tC AUX) i j

def creditValue (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (i j : Idx n) : ℝ :=
  integralClientCredit (C.gValue AUX) (C.sValue AUX) (C.tValue AUX) i j

theorem sum_interval_shiftedSValue_eq_of_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    {j i : Idx n} (hji : j < i) :
    Finset.sum (intervalRange j i) (fun p => C.shiftedSValue AUX p j) =
      Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j) := by
  let next : Idx n := ⟨j.1.succ, by
    have hji' : j.1 < i.1 := Fin.lt_def.mp hji
    omega⟩
  have hnext_mem : next ∈ intervalRange j i := by
    refine mem_intervalRange.mpr ?_
    change j ≤ next ∧ next ≤ i
    constructor
    · exact Fin.le_def.mpr (by
        dsimp [next]
        omega)
    · exact Fin.le_def.mpr (by
        dsimp [next]
        have hji' : j.1 < i.1 := Fin.lt_def.mp hji
        omega)
  have hnext_spec : IsNextIndex next j := by
    unfold IsNextIndex
    simp [next]
  have hraw_split :
      Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j) =
        C.sValue AUX j j +
          Finset.sum (intervalRange j i) (fun p => if j < p then C.sValue AUX p j else 0) := by
    have hfilter :
        (intervalRange j i).filter (fun p => ¬ j < p) = {j} := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_filter.mp hp with ⟨hpInt, hpNot⟩
        rcases mem_intervalRange.mp hpInt with ⟨hjp, _⟩
        have hpj : p = j := le_antisymm (not_lt.mp hpNot) hjp
        simp [hpj]
      · intro hp
        have hp' : p = j := by simpa using hp
        subst p
        exact
          Finset.mem_filter.mpr
            ⟨mem_intervalRange.mpr ⟨le_rfl, le_of_lt hji⟩, not_lt.mpr le_rfl⟩
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not
        (s := intervalRange j i) (p := fun p => j < p) (fun p => C.sValue AUX p j)
    rw [hfilter] at hsplit
    simp at hsplit
    calc
      Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j)
        =
          Finset.sum (intervalRange j i) (fun p => if j < p then C.sValue AUX p j else 0) +
            C.sValue AUX j j := by
              simpa [Finset.sum_filter] using hsplit.symm
      _ =
          C.sValue AUX j j +
            Finset.sum (intervalRange j i) (fun p => if j < p then C.sValue AUX p j else 0) := by
              ring
  have hdiag_transfer :
      Finset.sum (intervalRange j i)
          (fun p => if IsNextIndex p j then C.sValue AUX j j else 0) =
        C.sValue AUX j j := by
    rw [Finset.sum_eq_single next]
    · simp [hnext_spec]
    · intro p hp hpne
      have hnot : ¬ IsNextIndex p j := by
        intro hpnext
        unfold IsNextIndex at hpnext hnext_spec
        apply hpne
        apply Fin.ext
        omega
      simp [hnot]
    · intro hnotmem
      exact False.elim (hnotmem hnext_mem)
  calc
    Finset.sum (intervalRange j i) (fun p => C.shiftedSValue AUX p j)
      =
        Finset.sum (intervalRange j i)
          (fun p =>
            (if j < p then C.sValue AUX p j else 0) +
              (if IsNextIndex p j then C.sValue AUX j j else 0)) := by
                apply Finset.sum_congr rfl
                intro p hp
                by_cases hjp : j < p
                · simp [ProfileData.shiftedSValue, hjp]
                · have hnotNext : ¬ IsNextIndex p j := by
                    intro hpnext
                    have hjp' : j < p := by
                      unfold IsNextIndex at hpnext
                      exact Fin.lt_def.mpr (by omega)
                    exact hjp hjp'
                  simp [ProfileData.shiftedSValue, hjp, hnotNext]
    _ =
        Finset.sum (intervalRange j i) (fun p => if j < p then C.sValue AUX p j else 0) +
          Finset.sum (intervalRange j i)
            (fun p => if IsNextIndex p j then C.sValue AUX j j else 0) := by
              rw [Finset.sum_add_distrib]
    _ =
        Finset.sum (intervalRange j i) (fun p => if j < p then C.sValue AUX p j else 0) +
          C.sValue AUX j j := by rw [hdiag_transfer]
    _ = Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j) := by
          rw [hraw_split]
          ring

theorem sum_strictSuffix_shiftedSValue_le
    (C : ProfileData I Γ) (H : NonnegHypotheses C) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum (strictSuffixRange j) (fun i => C.shiftedSValue AUX i j) ≤
      Finset.sum (suffixRange j) (fun i => C.sValue AUX i j) := by
  by_cases hjlast : j < lastIdx n
  · let next : Idx n := ⟨j.1.succ, by
      have hj' : j.1 < (lastIdx n).1 := Fin.lt_def.mp hjlast
      omega⟩
    have hnext_mem : next ∈ strictSuffixRange j := by
      exact mem_strictSuffixRange.mpr (by
        change j.1 < next.1
        dsimp [next]
        omega)
    have hnext_spec : IsNextIndex next j := by
      unfold IsNextIndex
      simp [next]
    have hdiag_transfer :
        Finset.sum (strictSuffixRange j)
            (fun i => if IsNextIndex i j then C.sValue AUX j j else 0) =
          C.sValue AUX j j := by
      rw [Finset.sum_eq_single next]
      · simp [hnext_spec]
      · intro i hi hineq
        have hnot : ¬ IsNextIndex i j := by
          intro hinext
          unfold IsNextIndex at hinext hnext_spec
          apply hineq
          apply Fin.ext
          omega
        simp [hnot]
      · intro hnotmem
        exact False.elim (hnotmem hnext_mem)
    have hraw_suffix :
        Finset.sum (suffixRange j) (fun i => C.sValue AUX i j) =
          C.sValue AUX j j +
            Finset.sum (strictSuffixRange j) (fun i => C.sValue AUX i j) := by
      unfold suffixRange strictSuffixRange
      rw [show Finset.univ.filter (fun i : Idx n => j ≤ i) =
          insert j (Finset.univ.filter (fun i : Idx n => j < i)) by
            ext i
            constructor
            · intro hi
              by_cases hij : i = j
              · simp [hij]
              · have hji : j < i := lt_of_le_of_ne (by simpa using hi) (Ne.symm hij)
                simp [hij, hji]
            · intro hi
              rcases Finset.mem_insert.mp hi with rfl | hi'
              · simp
              · have hji : j < i := by simpa using hi'
                simp [le_of_lt hji]]
      rw [Finset.sum_insert]
      simp
    calc
      Finset.sum (strictSuffixRange j) (fun i => C.shiftedSValue AUX i j)
        =
          Finset.sum (strictSuffixRange j)
            (fun i =>
              C.sValue AUX i j +
                (if IsNextIndex i j then C.sValue AUX j j else 0)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  have hji : j < i := mem_strictSuffixRange.mp hi
                  simp [ProfileData.shiftedSValue, hji]
      _ =
          Finset.sum (strictSuffixRange j) (fun i => C.sValue AUX i j) +
            Finset.sum (strictSuffixRange j)
              (fun i => if IsNextIndex i j then C.sValue AUX j j else 0) := by
                rw [Finset.sum_add_distrib]
      _ =
          Finset.sum (strictSuffixRange j) (fun i => C.sValue AUX i j) +
            C.sValue AUX j j := by rw [hdiag_transfer]
      _ ≤ Finset.sum (suffixRange j) (fun i => C.sValue AUX i j) := by
            rw [hraw_suffix]
            show
              Finset.sum (strictSuffixRange j) (fun i => C.sValue AUX i j) + C.sValue AUX j j ≤
                C.sValue AUX j j + Finset.sum (strictSuffixRange j) (fun i => C.sValue AUX i j)
            ring_nf
            exact le_rfl
  · have hstrict_empty : strictSuffixRange j = ∅ := by
      have hjEq : j = lastIdx n := le_antisymm (le_lastIdx j) (not_lt.mp hjlast)
      ext i
      simp [hjEq, mem_strictSuffixRange, not_lt.mpr (le_lastIdx i)]
    rw [hstrict_empty]
    have hsuffix_nonneg :
        0 ≤ Finset.sum (suffixRange j) (fun i => C.sValue AUX i j) := by
      apply Finset.sum_nonneg
      intro i hi
      exact C.sValue_nonneg H AUX i j
    exact hsuffix_nonneg

theorem tailBudget_eq_phaseTwo_afterBudget_of_lt_t1
    (C : ProfileData I Γ) {j : Idx n} (ht1j : C.t1 < j) :
    tailBudget C.hatG j = C.phaseTwo.afterBudget j := by
  unfold tailBudget PhaseTwoData.afterBudget
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact C.copied_above_t1 (lt_of_lt_of_le ht1j (le_of_lt (mem_strictSuffixRange.mp hi)))

theorem beforeBudget_lt_barTau_of_lt_t1
    (C : ProfileData I Γ) {j : Idx n} (ht1j : C.t1 < j) :
    beforeBudget C.hatG j < I.program.barTau := by
  rw [C.beforeBudget_eq_phaseTwo_beforeBudget_of_lt_t1 ht1j]
  exact C.phaseTwo_beforeBudget_lt_barTau_above_t1 ht1j

theorem futureCount_mul_hatG_eq_tailBudget_add_tau_of_lt_t1_of_firstBid_lt_t3
    (C : ProfileData I Γ) {j : Idx n}
    (ht1j : C.t1 < j) (hfj : I.firstBidTime j < Γ.t3Star) :
    futureCount j * C.hatG j = tailBudget C.hatG j + I.program.tau := by
  have hjt3 : j ≤ Γ.t3Star := le_trans (I.le_firstBidTime j) (le_of_lt hfj)
  have hjltlast : j < lastIdx n := by
    exact lt_of_lt_of_le (lt_of_le_of_lt (I.le_firstBidTime j) hfj) (le_lastIdx _)
  have hfcpos : 0 < futureCount j := by
    change 0 < (futureCountNat j : ℝ)
    have hjval : j.1 < Nat.pred n := Fin.lt_def.mp hjltlast
    have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
    have hsucc : j.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt hjval) hpredlt
    exact_mod_cast Nat.sub_pos_of_lt hsucc
  have hcopy : C.hatG j = C.phaseTwo.hatG2 j := C.copied_above_t1 ht1j
  have hmu : Γ.muD j = 0 := Advice.muD_eq_zero Γ hfj
  have hspecial : ¬ (j = lastIdx n ∧ Γ.t3Star = lastIdx n) := by
    intro h
    have hjeq : j = lastIdx n := h.1
    have hfeq : I.firstBidTime j = lastIdx n := by
      apply le_antisymm
      · exact le_lastIdx _
      · simpa [hjeq] using I.le_firstBidTime j
    have : ¬ I.firstBidTime j < Γ.t3Star := by
      rw [h.2]
      exact not_lt.mpr (le_of_eq hfeq.symm)
    exact this hfj
  have hstep := C.phaseTwo.step_eq j hjt3
  have hstep' : C.phaseTwo.hatG2 j =
      (C.phaseTwo.afterBudget j + I.program.tau) / futureCount j := by
    simpa [PhaseTwoData.afterBudget, hmu, hspecial] using hstep
  calc
    futureCount j * C.hatG j = futureCount j * C.phaseTwo.hatG2 j := by rw [hcopy]
    _ = futureCount j * ((C.phaseTwo.afterBudget j + I.program.tau) / futureCount j) := by
          rw [hstep']
    _ = C.phaseTwo.afterBudget j + I.program.tau := by
          field_simp [ne_of_gt hfcpos]
    _ = tailBudget C.hatG j + I.program.tau := by
          rw [← C.tailBudget_eq_phaseTwo_afterBudget_of_lt_t1 ht1j]

theorem sum_strictSuffix_gB_row_eq_tailBudget_add_tau_of_lt_t1_of_firstBid_lt_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j : Idx n}
    (ht1j : C.t1 < j) (hfj : I.firstBidTime j < Γ.t3Star) :
    Finset.sum (strictSuffixRange j) (fun q => C.gB AUX j q) =
      tailBudget C.hatG j + I.program.tau := by
  calc
    Finset.sum (strictSuffixRange j) (fun q => C.gB AUX j q) = futureCount j * C.hatG j := by
      calc
        Finset.sum (strictSuffixRange j) (fun q => C.gB AUX j q)
          = Finset.sum (strictSuffixRange j) (fun _ => C.hatG j) := by
              simp [ProfileData.gB]
        _ = ((strictSuffixRange j).card : ℝ) * C.hatG j := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = futureCount j * C.hatG j := by
              simp [futureCount, card_strictSuffixRange]
    _ = tailBudget C.hatG j + I.program.tau :=
      C.futureCount_mul_hatG_eq_tailBudget_add_tau_of_lt_t1_of_firstBid_lt_t3 ht1j hfj

theorem sum_strictSuffix_gC_row_eq_tailBudget_add_tau_of_lt_t1_of_firstBid_lt_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j : Idx n}
    (ht1j : C.t1 < j) (hfj : I.firstBidTime j < Γ.t3Star) :
    Finset.sum (strictSuffixRange j) (fun q => C.gC AUX j q) =
      tailBudget C.hatG j + I.program.tau := by
  calc
    Finset.sum (strictSuffixRange j) (fun q => C.gC AUX j q) = futureCount j * C.hatG j := by
      calc
        Finset.sum (strictSuffixRange j) (fun q => C.gC AUX j q)
          = Finset.sum (strictSuffixRange j) (fun _ => C.hatG j) := by
              simp [ProfileData.gC]
        _ = ((strictSuffixRange j).card : ℝ) * C.hatG j := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = futureCount j * C.hatG j := by
              simp [futureCount, card_strictSuffixRange]
    _ = tailBudget C.hatG j + I.program.tau :=
      C.futureCount_mul_hatG_eq_tailBudget_add_tau_of_lt_t1_of_firstBid_lt_t3 ht1j hfj

theorem sum_interval_hatG_eq_before_sub_tail
    (C : ProfileData I Γ) {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) C.hatG =
      beforeBudget C.hatG j - tailBudget C.hatG i := by
  have hleft : (suffixRange j).filter (fun p => p ≤ i) = intervalRange j i := by
    ext p
    simp [suffixRange, intervalRange]
  have hright : (suffixRange j).filter (fun p => ¬ p ≤ i) = strictSuffixRange i := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hpnot⟩
      have hip : i < p := lt_of_not_ge hpnot
      exact mem_strictSuffixRange.mpr hip
    · intro hp
      have hip : i < p := mem_strictSuffixRange.mp hp
      exact Finset.mem_filter.mpr ⟨by simpa [suffixRange] using le_trans hji (le_of_lt hip),
        not_le.mpr hip⟩
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := suffixRange j) (p := fun p => p ≤ i) C.hatG
  rw [hleft, hright] at hsplit
  have hsplit' : Finset.sum (intervalRange j i) C.hatG + tailBudget C.hatG i =
      beforeBudget C.hatG j := by
    simpa [beforeBudget, tailBudget] using hsplit
  linarith

theorem sum_interval_strict_right_hatG_eq_tail_sub_tail
    (C : ProfileData I Γ) {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => if j < p then C.hatG p else 0) =
      tailBudget C.hatG j - tailBudget C.hatG i := by
  rw [← Finset.sum_filter]
  have hfilter : (intervalRange j i).filter (fun p => ¬ j < p) = {j} := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpInt, hpNot⟩
      rcases mem_intervalRange.mp hpInt with ⟨hjp, _⟩
      have hpj : p = j := le_antisymm (not_lt.mp hpNot) hjp
      simp [hpj]
    · intro hp
      have hp' : p = j := by simpa using hp
      subst p
      exact Finset.mem_filter.mpr ⟨by simp [intervalRange, hji], not_lt.mpr le_rfl⟩
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := intervalRange j i) (p := fun p => j < p) C.hatG
  rw [hfilter] at hsplit
  simp at hsplit
  have hinterval := C.sum_interval_hatG_eq_before_sub_tail hji
  have hbefore := beforeBudget_eq_self_add_tail C.hatG j
  linarith

theorem sum_interval_gA_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.gA AUX p j) =
      beforeBudget C.hatG j - tailBudget C.hatG i -
        Finset.sum (intervalRange j i) (fun p => AUX.delta p j) := by
  unfold ProfileData.gA
  rw [Finset.sum_sub_distrib, C.sum_interval_hatG_eq_before_sub_tail hji]

theorem sum_interval_sA_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.sA AUX p j) =
      beforeBudget C.hatG j - tailBudget C.hatG i -
        Finset.sum (intervalRange j i) (fun p => AUX.sigma p j) := by
  calc
    Finset.sum (intervalRange j i) (fun p => C.sA AUX p j)
      = Finset.sum (intervalRange j i) (fun p => C.hatG p - AUX.sigma p j) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [ProfileData.sA, (mem_intervalRange.mp hp).1]
    _ = beforeBudget C.hatG j - tailBudget C.hatG i -
        Finset.sum (intervalRange j i) (fun p => AUX.sigma p j) := by
          rw [Finset.sum_sub_distrib, C.sum_interval_hatG_eq_before_sub_tail hji]

theorem sum_interval_sigma_eq_of_firstBid_le
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hj : 0 < (C.memberships).muA j) (hif : I.firstBidTime j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => AUX.sigma p j) =
      posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) := by
  have hleft :
      (intervalRange j i).filter (fun p => p ≤ I.firstBidTime j) =
        intervalRange j (I.firstBidTime j) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpInt, hpLe⟩
      exact mem_intervalRange.mpr ⟨(mem_intervalRange.mp hpInt).1, hpLe⟩
    · intro hp
      rcases mem_intervalRange.mp hp with ⟨hpj, hpLe⟩
      exact Finset.mem_filter.mpr ⟨mem_intervalRange.mpr ⟨hpj, le_trans hpLe hif⟩, hpLe⟩
  have hzero :
      Finset.sum ((intervalRange j i).filter (fun p => ¬ p ≤ I.firstBidTime j))
          (fun p => AUX.sigma p j) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨-, hpNot⟩
    exact AUX.sigma_eq_zero p j hj (Or.inr (lt_of_not_ge hpNot))
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := intervalRange j i) (p := fun p => p ≤ I.firstBidTime j) (fun p => AUX.sigma p j)
  rw [hleft, hzero, add_zero] at hsplit
  simpa [AUX.sigma_sum_eq j hj] using hsplit.symm

theorem sum_interval_delta_eq_zero_of_lt_firstBid
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hj : 0 < (C.memberships).muA j) (hif : i < I.firstBidTime j) :
    Finset.sum (intervalRange j i) (fun p => AUX.delta p j) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hpLe : p ≤ I.firstBidTime j :=
    le_trans (mem_intervalRange.mp hp).2 (le_of_lt hif)
  exact AUX.delta_eq_zero p j hj hpLe

theorem sum_interval_sA_eq_after_firstBid
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hj : 0 < (C.memberships).muA j) (hji : j ≤ i) (hif : I.firstBidTime j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.sA AUX p j) =
      beforeBudget C.hatG j - tailBudget C.hatG i -
        posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) := by
  rw [C.sum_interval_sA_eq AUX hji, C.sum_interval_sigma_eq_of_firstBid_le AUX hj hif]

theorem sum_interval_gA_tA_sub_sA_eq_after_firstBid
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hj : 0 < (C.memberships).muA j) (hji : j ≤ i) (hif : I.firstBidTime j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j) =
      posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) -
        Finset.sum (intervalRange j i) (fun p => AUX.delta p j) := by
  rw [show (fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j) =
      (fun p => C.gA AUX p j - C.sA AUX p j) by
        funext p
        simp [ProfileData.tA]]
  rw [Finset.sum_sub_distrib, C.sum_interval_gA_eq AUX hji,
    C.sum_interval_sA_eq_after_firstBid AUX hj hji hif]
  ring

theorem sum_interval_gA_tA_sub_sA_eq_before_firstBid
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hj : 0 < (C.memberships).muA j) (_hji : j ≤ i) (hif : i < I.firstBidTime j) :
    Finset.sum (intervalRange j i) (fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j) =
      Finset.sum (intervalRange j i) (fun p => AUX.sigma p j) := by
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : j ≤ p := (mem_intervalRange.mp hp).1
  have hpLe : p ≤ I.firstBidTime j :=
    le_trans (mem_intervalRange.mp hp).2 (le_of_lt hif)
  simp [ProfileData.gA, ProfileData.tA, ProfileData.sA, hpj, AUX.delta_eq_zero p j hj hpLe]

theorem tailBudget_eq_phaseTwo_afterBudget_at_t1
    (C : ProfileData I Γ) :
    tailBudget C.hatG C.t1 = C.phaseTwo.afterBudget C.t1 := by
  unfold tailBudget PhaseTwoData.afterBudget
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact C.copied_above_t1 (mem_strictSuffixRange.mp hi)

theorem beforeBudget_t1_ge_barTau
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    I.program.barTau ≤ beforeBudget C.hatG C.t1 := by
  have htail : tailBudget C.hatG C.t1 = C.phaseTwo.afterBudget C.t1 :=
    C.tailBudget_eq_phaseTwo_afterBudget_at_t1
  have hbefore : beforeBudget C.hatG C.t1 = C.hatG C.t1 + C.phaseTwo.afterBudget C.t1 := by
    rw [beforeBudget_eq_self_add_tail, htail]
  by_cases ht1 : C.t1 = lastIdx n
  · have hgt1A : C.boundaryHatGA = 0 := by
      simp [ProfileData.boundaryHatGA, C.hatGT1A_eq, ht1]
    have hgt1B : C.boundaryHatGB = C.phaseTwo.hatG2 C.t1 := by
      simp [ProfileData.boundaryHatGB, C.hatGT1B_eq, ht1]
    have hhat : C.hatG C.t1 = C.phaseTwo.hatG2 C.t1 := by
      calc
        C.hatG C.t1 = C.boundaryHatGA + C.boundaryHatGB := C.boundary_eq
        _ = 0 + C.phaseTwo.hatG2 C.t1 := by rw [hgt1A, hgt1B]
        _ = C.phaseTwo.hatG2 C.t1 := by ring
    have hafter0 : C.phaseTwo.afterBudget C.t1 = 0 := by
      unfold PhaseTwoData.afterBudget tailBudget
      apply Finset.sum_eq_zero
      intro x hx
      rw [ht1] at hx
      exact (False.elim ((not_lt_of_ge (le_lastIdx x)) (mem_strictSuffixRange.mp hx)))
    have hphase : I.program.barTau ≤ C.phaseTwo.beforeBudget C.t1 := C.t1_beforeBudget_ge_barTau
    have hphase' : I.program.barTau ≤ C.phaseTwo.hatG2 C.t1 := by
      have hpb :
          C.phaseTwo.beforeBudget C.t1 =
            C.phaseTwo.hatG2 C.t1 + C.phaseTwo.afterBudget C.t1 :=
        C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1
      linarith
    linarith
  · have hA : 0 ≤ C.boundaryHatGA :=
      C.boundaryHatGA_nonneg_of_admissible hΓ hγlo hγhi
    have hB :
        C.boundaryHatGB = I.program.barTau - C.phaseTwo.afterBudget C.t1 := by
      simp [ProfileData.boundaryHatGB, C.hatGT1B_eq, ht1]
    have hhat : C.hatG C.t1 =
        C.boundaryHatGA + (I.program.barTau - C.phaseTwo.afterBudget C.t1) := by
      rw [C.boundary_eq]
      change C.hatGT1A + C.hatGT1B = C.hatGT1A + (I.program.barTau - C.phaseTwo.afterBudget C.t1)
      rw [C.hatGT1B_eq, if_neg ht1]
    linarith

theorem beforeBudget_t2_ge_theta
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    I.program.theta ≤ beforeBudget C.hatG C.t2 := by
  by_cases ht : C.t1 < C.t2
  · rw [C.beforeBudget_eq_phaseTwo_beforeBudget_of_lt_t1 ht]
    exact C.t2_beforeBudget_ge_theta
  · have hEq : C.t1 = C.t2 := le_antisymm C.t1_le_t2 (le_of_not_gt ht)
    rw [← hEq]
    have hbar : I.program.barTau ≤ beforeBudget C.hatG C.t1 :=
      C.beforeBudget_t1_ge_barTau hΓ hγlo hγhi
    have hθbar : I.program.theta ≤ I.program.barTau :=
      I.program.theta_le_barTau_of_le_153_div_125 hγlo hγhi
    linarith

theorem chi_eq_zero_of_le_t2
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {q : Idx n} (hq : q ≤ C.t2) :
    C.chi q = 0 := by
  let hhatG : ∀ i, 0 ≤ C.hatG i :=
    C.hatG_nonneg_of_admissible_and_coeff_bounds hΓ hγlo hγhi
  have hb_t2 : I.program.theta ≤ beforeBudget C.hatG C.t2 :=
    C.beforeBudget_t2_ge_theta hΓ hγlo hγhi
  have hb_q : I.program.theta ≤ beforeBudget C.hatG q := by
    exact le_trans hb_t2 (beforeBudget_antitone_of_nonneg hhatG hq)
  have hdiv : 1 ≤ beforeBudget C.hatG q / I.program.theta := by
    exact (le_div_iff₀ hθpos).2 (by simpa using hb_q)
  have hinner : 1 - beforeBudget C.hatG q / I.program.theta ≤ 0 := by
    linarith
  simp [ProfileData.chi, posPart_of_nonpos hinner]

theorem sum_strictSuffix_muD_chi_eq_z_of_lt_t1
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hjt1 : j < C.t1) :
    Finset.sum (strictSuffixRange j) (fun q => (C.memberships).muD q * C.chi q) = C.z := by
  have hjt2 : j < C.t2 := lt_of_lt_of_le hjt1 C.t1_le_t2
  have hzero :
      Finset.sum ((strictSuffixRange j).filter (fun q => q ≤ C.t2))
          (fun q => (C.memberships).muD q * C.chi q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨-, hqt2⟩
    rw [C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos hqt2]
    ring
  have hright :
      (strictSuffixRange j).filter (fun q => ¬ q ≤ C.t2) = strictSuffixRange C.t2 := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨-, hnot⟩
      exact mem_strictSuffixRange.mpr (lt_of_not_ge hnot)
    · intro hq
      exact Finset.mem_filter.mpr ⟨
        mem_strictSuffixRange.mpr (lt_of_lt_of_le hjt2 (le_of_lt (mem_strictSuffixRange.mp hq))),
        not_le.mpr (mem_strictSuffixRange.mp hq)⟩
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := strictSuffixRange j) (p := fun q => q ≤ C.t2)
      (fun q => (C.memberships).muD q * C.chi q)
  rw [hzero, zero_add, hright] at hsplit
  have hmain :
      Finset.sum (strictSuffixRange j) (fun q => (C.memberships).muD q * C.chi q) =
        Finset.sum (strictSuffixRange C.t2) (fun q => (C.memberships).muD q * C.chi q) := by
    simpa using hsplit.symm
  rw [hmain, C.z_eq]
  apply Finset.sum_congr rfl
  intro q hq
  have ht1q : C.t1 < q := lt_of_le_of_lt C.t1_le_t2 (mem_strictSuffixRange.mp hq)
  rw [C.memberships_muD, ProfileData.chi, C.beforeBudget_eq_phaseTwo_beforeBudget_of_lt_t1 ht1q]
  ring

theorem gValue_row_eq_of_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j q : Idx n} (hjt1 : j < C.t1) (hq : j < q) :
    C.gValue AUX j q =
      C.hatG j - (C.memberships).muD q * C.chi q * I.program.frac * C.hatG j := by
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have hA :
      (C.memberships).muA q * C.gA AUX j q = (C.memberships).muA q * C.hatG j := by
    by_cases hμA : (C.memberships).muA q = 0
    · simp [hμA]
    · have hμA_nonneg : 0 ≤ (C.memberships).muA q := hμnonneg.1 q
      have hμA_pos : 0 < (C.memberships).muA q := by
        exact lt_of_le_of_ne hμA_nonneg (Ne.symm hμA)
      have hdelta : AUX.delta j q = 0 := by
        exact AUX.delta_eq_zero j q hμA_pos (le_trans (le_of_lt hq) (I.le_firstBidTime q))
      simp [ProfileData.gA, hdelta]
  have hD : C.gD AUX j q = C.hatG j - C.chi q * I.program.frac * C.hatG j := by
    simp [ProfileData.gD, hjt1]
  have htot : (C.memberships).total q = 1 := C.memberships_total q
  unfold MembershipWeights.total at htot
  have htot' :
      (C.memberships).muA q + (C.memberships).muB q + (C.memberships).muC q + Γ.muD q = 1 := by
    simpa [C.memberships_muD] using htot
  have hsimp :
      (C.memberships).muA q * C.hatG j +
          (C.memberships).muB q * C.hatG j +
          (C.memberships).muC q * C.hatG j +
          Γ.muD q * (C.hatG j - C.chi q * I.program.frac * C.hatG j) =
        C.hatG j - Γ.muD q * C.chi q * I.program.frac * C.hatG j := by
    have hsum :
        (C.memberships).muA q * C.hatG j +
            (C.memberships).muB q * C.hatG j +
            (C.memberships).muC q * C.hatG j +
            Γ.muD q * C.hatG j =
          C.hatG j := by
      calc
        (C.memberships).muA q * C.hatG j +
            (C.memberships).muB q * C.hatG j +
            (C.memberships).muC q * C.hatG j +
            Γ.muD q * C.hatG j
          = ((C.memberships).muA q + (C.memberships).muB q +
              (C.memberships).muC q + Γ.muD q) * C.hatG j := by
                ring
        _ = C.hatG j := by rw [htot']; ring
    calc
      (C.memberships).muA q * C.hatG j +
          (C.memberships).muB q * C.hatG j +
          (C.memberships).muC q * C.hatG j +
          Γ.muD q * (C.hatG j - C.chi q * I.program.frac * C.hatG j)
        = ((C.memberships).muA q * C.hatG j + (C.memberships).muB q * C.hatG j +
            (C.memberships).muC q * C.hatG j + Γ.muD q * C.hatG j) -
            Γ.muD q * C.chi q * I.program.frac * C.hatG j := by
              ring
      _ = C.hatG j - Γ.muD q * C.chi q * I.program.frac * C.hatG j := by
            rw [hsum]
  simpa [ProfileData.gValue, hA, ProfileData.gB, ProfileData.gC, hD, C.memberships_muD] using hsimp

theorem sum_strictSuffix_gValue_row_eq_of_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hjt1 : j < C.t1) :
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) =
      (futureCount j - I.program.frac * C.z) * C.hatG j := by
  calc
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q)
      = Finset.sum (strictSuffixRange j)
          (fun q => C.hatG j - (C.memberships).muD q * C.chi q * I.program.frac * C.hatG j) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact C.gValue_row_eq_of_lt_t1 AUX hΓ hjt1 (mem_strictSuffixRange.mp hq)
    _ = Finset.sum (strictSuffixRange j) (fun _ => C.hatG j) -
          Finset.sum (strictSuffixRange j)
            (fun q => (C.memberships).muD q * C.chi q * I.program.frac * C.hatG j) := by
          rw [Finset.sum_sub_distrib]
    _ = futureCount j * C.hatG j -
          Finset.sum (strictSuffixRange j)
            (fun q => (C.memberships).muD q * C.chi q * I.program.frac * C.hatG j) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [futureCount, card_strictSuffixRange]
    _ = futureCount j * C.hatG j -
          ((Finset.sum (strictSuffixRange j) (fun q => (C.memberships).muD q * C.chi q)) *
            (I.program.frac * C.hatG j)) := by
          congr 1
          calc
            Finset.sum (strictSuffixRange j)
                (fun q => (C.memberships).muD q * C.chi q * I.program.frac * C.hatG j)
              = Finset.sum (strictSuffixRange j)
                  (fun q => ((C.memberships).muD q * C.chi q) * (I.program.frac * C.hatG j)) := by
                    apply Finset.sum_congr rfl
                    intro q hq
                    ring
            _ = (Finset.sum (strictSuffixRange j) (fun q => (C.memberships).muD q * C.chi q)) *
                  (I.program.frac * C.hatG j) := by
                    rw [Finset.sum_mul]
    _ = futureCount j * C.hatG j - (C.z * (I.program.frac * C.hatG j)) := by
          rw [C.sum_strictSuffix_muD_chi_eq_z_of_lt_t1 hΓ hγlo hγhi hθpos hjt1]
    _ = (futureCount j - I.program.frac * C.z) * C.hatG j := by
          ring

theorem gValue_row_eq_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j q : Idx n} (ht1j : C.t1 < j) (hjq : j < q) :
    C.gValue AUX j q = C.hatG j := by
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have hA :
      (C.memberships).muA q * C.gA AUX j q = (C.memberships).muA q * C.hatG j := by
    by_cases hμA : (C.memberships).muA q = 0
    · simp [hμA]
    · have hμA_nonneg : 0 ≤ (C.memberships).muA q := hμnonneg.1 q
      have hμA_pos : 0 < (C.memberships).muA q := lt_of_le_of_ne hμA_nonneg (Ne.symm hμA)
      have hdelta : AUX.delta j q = 0 := by
        exact AUX.delta_eq_zero j q hμA_pos (le_trans (le_of_lt hjq) (I.le_firstBidTime q))
      simp [ProfileData.gA, hdelta]
  have hnotlt : ¬ j < C.t1 := not_lt.mpr (le_of_lt ht1j)
  have hneq : j ≠ C.t1 := ne_of_gt ht1j
  have hD : C.gD AUX j q = C.hatG j := by
    simp [ProfileData.gD, hnotlt, hneq]
  have htot : (C.memberships).total q = 1 := C.memberships_total q
  unfold MembershipWeights.total at htot
  have htot' :
      (C.memberships).muA q + (C.memberships).muB q + (C.memberships).muC q + Γ.muD q = 1 := by
    simpa [C.memberships_muD] using htot
  have hsimp :
      (C.memberships).muA q * C.hatG j +
          (C.memberships).muB q * C.hatG j +
          (C.memberships).muC q * C.hatG j +
          Γ.muD q * C.hatG j =
        C.hatG j := by
    calc
      (C.memberships).muA q * C.hatG j +
          (C.memberships).muB q * C.hatG j +
          (C.memberships).muC q * C.hatG j +
          Γ.muD q * C.hatG j
        = ((C.memberships).muA q + (C.memberships).muB q +
            (C.memberships).muC q + Γ.muD q) * C.hatG j := by
              ring
      _ = C.hatG j := by rw [htot']; ring
  simpa [ProfileData.gValue, hA, ProfileData.gB, ProfileData.gC, hD, C.memberships_muD] using hsimp

theorem sum_strictSuffix_gValue_row_eq_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j : Idx n} (ht1j : C.t1 < j) :
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) =
      futureCount j * C.hatG j := by
  calc
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q)
      = Finset.sum (strictSuffixRange j) (fun _ => C.hatG j) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact C.gValue_row_eq_of_t1_lt AUX hΓ ht1j (mem_strictSuffixRange.mp hq)
    _ = ((strictSuffixRange j).card : ℝ) * C.hatG j := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = futureCount j * C.hatG j := by
      simp [futureCount, card_strictSuffixRange]

omit [NeZero n] in
theorem frac_lt_one_of_theta_pos
    (P : DualProgram n) (hγlo : 1 ≤ P.Mcoeff) (hθpos : 0 < P.theta) :
    P.frac < 1 := by
  have hεnonneg : 0 ≤ P.epsilon := P.epsilon_nonneg_of_one_le_Mcoeff hγlo
  have hτpos : 0 < P.tau := by
    rw [← P.epsilon_add_theta_eq_tau]
    linarith
  have hεltτ : P.epsilon < P.tau := by
    rw [← P.epsilon_add_theta_eq_tau]
    linarith
  rw [DualProgram.frac]
  exact (div_lt_one hτpos).2 hεltτ

theorem futureCount_pos_of_lt_t1
    (C : ProfileData I Γ) {j : Idx n} (hjt1 : j < C.t1) :
    0 < futureCount j := by
  change 0 < (futureCountNat j : ℝ)
  have hjltlast : j < lastIdx n := lt_of_lt_of_le hjt1 (le_lastIdx _)
  have hjval : j.1 < Nat.pred n := Fin.lt_def.mp hjltlast
  have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
  have hsucc : j.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt hjval) hpredlt
  exact_mod_cast Nat.sub_pos_of_lt hsucc

theorem futureCount_pos_of_ne_last
    (j : Idx n) (hjlast : j ≠ lastIdx n) :
    0 < futureCount j := by
  change 0 < (futureCountNat j : ℝ)
  have hjltlast : j < lastIdx n := lt_of_le_of_ne (le_lastIdx _) hjlast
  have hjval : j.1 < Nat.pred n := Fin.lt_def.mp hjltlast
  have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
  have hsucc : j.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt hjval) hpredlt
  exact_mod_cast Nat.sub_pos_of_lt hsucc

theorem phase1Denom_pos_of_lt_t1_of_theta_pos
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (_hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hjt1 : j < C.t1) :
    0 < C.phase1Denom j := by
  unfold ProfileData.phase1Denom ProfileData.phaseTwoZ
  have hfrac_nonneg : 0 ≤ I.program.frac := I.program.frac_nonneg_of_one_le_Mcoeff hγlo
  have hfrac_lt : I.program.frac < 1 := frac_lt_one_of_theta_pos I.program hγlo hθpos
  have hfcpos : 0 < futureCount j := C.futureCount_pos_of_lt_t1 hjt1
  have hznonneg : 0 ≤ C.z := C.z_nonneg_of_admissible hΓ
  have hzle : C.z ≤ futureCount j := by
    exact le_trans C.z_le_futureCount_t1 (futureCount_antitone (le_of_lt hjt1))
  by_cases hz0 : C.z = 0
  · simp [hz0, hfcpos]
  · have hzpos : 0 < C.z := lt_of_le_of_ne hznonneg (Ne.symm hz0)
    have hfracz_lt : I.program.frac * C.z < C.z := by
      have htmp := mul_lt_mul_of_pos_right hfrac_lt hzpos
      simpa using htmp
    have hfracz_lt_fc : I.program.frac * C.z < futureCount j := lt_of_lt_of_le hfracz_lt hzle
    linarith

theorem sum_strictSuffix_gValue_row_eq_one_sub_posPart_of_integralA
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hjt1 : j < C.t1) (hμ : Γ.muD j = 0) :
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) =
      1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) := by
  have hrow := C.sum_strictSuffix_gValue_row_eq_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjt1
  have hdenpos : 0 < C.phase1Denom j :=
    C.phase1Denom_pos_of_lt_t1_of_theta_pos hΓ hγlo hγhi hθpos hjt1
  have hdenne : futureCount j - I.program.frac * C.z ≠ 0 := ne_of_gt hdenpos
  calc
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q)
      = (futureCount j - I.program.frac * C.z) * C.hatG j := hrow
    _ =
        (futureCount j - I.program.frac * C.z) *
          (((1 - Γ.muD j) *
              (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)))) /
            (futureCount j - I.program.frac * C.z)) := by
          rw [C.phase1_eq hjt1]
    _ = 1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) := by
          rw [hμ]
          field_simp [hdenne]
          ring

theorem gValue_eq_gA_of_integralA_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    {i j : Idx n} (hjt1 : j < C.t1) (hμ : Γ.muD j = 0) :
    C.gValue AUX i j = C.gA AUX i j := by
  have hA : (C.memberships).muA j = 1 := C.memberships_muA_eq_one_of_lt_t1_of_muD_eq_zero hjt1 hμ
  have hB : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_lt_t1 hjt1
  have hC : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_lt_t1 hjt1
  simp [ProfileData.gValue, hA, hB, hC, hμ]

theorem sValue_eq_sA_of_integralA_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    {i j : Idx n} (hjt1 : j < C.t1) (hμ : Γ.muD j = 0) :
    C.sValue AUX i j = C.sA AUX i j := by
  have hA : (C.memberships).muA j = 1 := C.memberships_muA_eq_one_of_lt_t1_of_muD_eq_zero hjt1 hμ
  have hB : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_lt_t1 hjt1
  have hC : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_lt_t1 hjt1
  simp [ProfileData.sValue, hA, hB, hC, hμ]

theorem tValue_eq_tA_of_integralA_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C)
    {i j : Idx n} (hjt1 : j < C.t1) (hμ : Γ.muD j = 0) :
    C.tValue AUX i j = C.tA AUX i j := by
  have hA : (C.memberships).muA j = 1 := C.memberships_muA_eq_one_of_lt_t1_of_muD_eq_zero hjt1 hμ
  have hB : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_lt_t1 hjt1
  have hC : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_lt_t1 hjt1
  simp [ProfileData.tValue, hA, hB, hC, hμ]

theorem creditValue_A_after_eq_of_integralA
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hjt1 : j < C.t1) (hμ : Γ.muD j = 0)
    (hji : j ≤ i) (hif : I.firstBidTime j ≤ i) :
    C.creditValue AUX i j = 1 - Finset.sum (intervalRange j i) (fun p => AUX.delta p j) := by
  have hμA : 0 < (C.memberships).muA j := by
    rw [C.memberships_muA_eq_one_of_lt_t1_of_muD_eq_zero hjt1 hμ]
    norm_num
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gValue_row_eq_one_sub_posPart_of_integralA
    AUX hΓ hγlo hγhi hθpos hjt1 hμ]
  have hfun :
      (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j) =
        fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j := by
      funext p
      simp [C.gValue_eq_gA_of_integralA_lt_t1 AUX hjt1 hμ,
        C.sValue_eq_sA_of_integralA_lt_t1 AUX hjt1 hμ,
        C.tValue_eq_tA_of_integralA_lt_t1 AUX hjt1 hμ]
  rw [hfun, C.sum_interval_gA_tA_sub_sA_eq_after_firstBid AUX hμA hji hif]
  ring

theorem creditValue_A_before_eq_of_integralA
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hjt1 : j < C.t1) (hμ : Γ.muD j = 0)
    (hji : j ≤ i) (hif : i < I.firstBidTime j) :
    C.creditValue AUX i j =
      1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) +
        Finset.sum (intervalRange j i) (fun p => AUX.sigma p j) := by
  have hμA : 0 < (C.memberships).muA j := by
    rw [C.memberships_muA_eq_one_of_lt_t1_of_muD_eq_zero hjt1 hμ]
    norm_num
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gValue_row_eq_one_sub_posPart_of_integralA
    AUX hΓ hγlo hγhi hθpos hjt1 hμ]
  have hfun :
      (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j) =
        fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j := by
      funext p
      simp [C.gValue_eq_gA_of_integralA_lt_t1 AUX hjt1 hμ,
        C.sValue_eq_sA_of_integralA_lt_t1 AUX hjt1 hμ,
        C.tValue_eq_tA_of_integralA_lt_t1 AUX hjt1 hμ]
  rw [hfun, C.sum_interval_gA_tA_sub_sA_eq_before_firstBid AUX hμA hji hif]

theorem memberships_muA_eq_zero_of_muD_eq_one
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) {j : Idx n} (hμ : Γ.muD j = 1) :
    (C.memberships).muA j = 0 := by
  have hnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have htot : (C.memberships).total j = 1 := C.memberships_total j
  unfold MembershipWeights.total at htot
  have hsum : (C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j = 0 := by
    simpa [C.memberships_muD, hμ] using htot
  nlinarith [hnonneg.1 j, hnonneg.2.1 j, hnonneg.2.2.1 j, hsum]

theorem memberships_muB_eq_zero_of_muD_eq_one
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) {j : Idx n} (hμ : Γ.muD j = 1) :
    (C.memberships).muB j = 0 := by
  have hnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have htot : (C.memberships).total j = 1 := C.memberships_total j
  unfold MembershipWeights.total at htot
  have hsum : (C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j = 0 := by
    simpa [C.memberships_muD, hμ] using htot
  nlinarith [hnonneg.1 j, hnonneg.2.1 j, hnonneg.2.2.1 j, hsum]

theorem memberships_muC_eq_zero_of_muD_eq_one
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) {j : Idx n} (hμ : Γ.muD j = 1) :
    (C.memberships).muC j = 0 := by
  have hnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have htot : (C.memberships).total j = 1 := C.memberships_total j
  unfold MembershipWeights.total at htot
  have hsum : (C.memberships).muA j + (C.memberships).muB j + (C.memberships).muC j = 0 := by
    simpa [C.memberships_muD, hμ] using htot
  nlinarith [hnonneg.1 j, hnonneg.2.1 j, hnonneg.2.2.1 j, hsum]

theorem gValue_eq_gD_of_integralD
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {i j : Idx n} (hμ : Γ.muD j = 1) :
    C.gValue AUX i j = C.gD AUX i j := by
  have hA : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_muD_eq_one hΓ hμ
  have hB : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_muD_eq_one hΓ hμ
  have hC : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_muD_eq_one hΓ hμ
  simp [ProfileData.gValue, hA, hB, hC, hμ]

theorem sValue_eq_sD_of_integralD
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {i j : Idx n} (hμ : Γ.muD j = 1) :
    C.sValue AUX i j = C.sD AUX i j := by
  have hA : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_muD_eq_one hΓ hμ
  have hB : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_muD_eq_one hΓ hμ
  have hC : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_muD_eq_one hΓ hμ
  simp [ProfileData.sValue, hA, hB, hC, hμ]

theorem tValue_eq_tD_of_integralD
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {i j : Idx n} (hμ : Γ.muD j = 1) :
    C.tValue AUX i j = C.tD AUX i j := by
  have hA : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_muD_eq_one hΓ hμ
  have hB : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_muD_eq_one hΓ hμ
  have hC : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_muD_eq_one hΓ hμ
  simp [ProfileData.tValue, hA, hB, hC, hμ]

theorem t3_le_firstBidTime_of_muD_eq_one
    (Γ : Advice I) {j : Idx n} (hμ : Γ.muD j = 1) :
    Γ.t3Star ≤ I.firstBidTime j := by
  by_cases hlt : Γ.t3Star < I.firstBidTime j
  · exact le_of_lt hlt
  · by_cases heq : I.firstBidTime j = Γ.t3Star
    · exact le_of_eq heq.symm
    · have hzero : Γ.muD j = 0 := by
        simp [Advice.muD, hlt, heq]
      linarith

theorem t1_le_t3Star_of_theta_pos
    (C : ProfileData I Γ) (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) (hθpos : 0 < I.program.theta) :
    C.t1 ≤ Γ.t3Star := by
  by_contra hgt
  have ht3t1 : Γ.t3Star < C.t1 := lt_of_not_ge hgt
  have hbefore0 : C.phaseTwo.beforeBudget C.t1 = 0 := by
    unfold PhaseTwoData.beforeBudget beforeBudget
    apply Finset.sum_eq_zero
    intro x hx
    have ht3x : Γ.t3Star < x := lt_of_lt_of_le ht3t1 (mem_suffixRange.mp hx)
    exact C.phaseTwo.zero_above_t3 ht3x
  have hbarpos : 0 < I.program.barTau := by
    have hθbar : I.program.theta ≤ I.program.barTau :=
      I.program.theta_le_barTau_of_le_153_div_125 hγlo hγhi
    linarith
  linarith [C.t1_beforeBudget_ge_barTau, hbefore0]

theorem muD_eq_one_at_t1_implies_last
    (C : ProfileData I Γ) (_hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (hμ : Γ.muD C.t1 = 1) :
    C.t1 = lastIdx n := by
  by_contra hne
  have ht1le : C.t1 ≤ Γ.t3Star := C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos
  have hspecial : ¬ (C.t1 = lastIdx n ∧ Γ.t3Star = lastIdx n) := by
    intro h
    exact hne h.1
  have hstep := C.phaseTwo.step_eq C.t1 ht1le
  have hzero : C.phaseTwo.hatG2 C.t1 = 0 := by
    simpa [hμ, hspecial] using hstep
  have hbefore :
      C.phaseTwo.beforeBudget C.t1 =
        C.phaseTwo.hatG2 C.t1 + C.phaseTwo.afterBudget C.t1 :=
    C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1
  linarith [C.t1_beforeBudget_ge_barTau, C.phaseTwo_afterBudget_t1_lt_barTau hne, hbefore]

theorem hatG_eq_zero_of_integralD_lt_t1
    (C : ProfileData I Γ) {j : Idx n} (hjt1 : j < C.t1) (hμ : Γ.muD j = 1) :
    C.hatG j = 0 := by
  rw [C.phase1_eq hjt1, hμ]
  simp

theorem hatG_eq_zero_of_integralD_gt_t1_of_ne_last
    (C : ProfileData I Γ) {j : Idx n}
    (ht1j : C.t1 < j) (hμ : Γ.muD j = 1) (hnotlast : j ≠ lastIdx n) :
    C.hatG j = 0 := by
  have hcopy : C.hatG j = C.phaseTwo.hatG2 j := C.copied_above_t1 ht1j
  by_cases hjt3 : j ≤ Γ.t3Star
  · have hspecial : ¬ (j = lastIdx n ∧ Γ.t3Star = lastIdx n) := by
      intro h
      exact hnotlast h.1
    have hstep := C.phaseTwo.step_eq j hjt3
    rw [hcopy]
    simpa [hμ, hspecial] using hstep
  · have hgt3 : Γ.t3Star < j := lt_of_not_ge hjt3
    rw [hcopy, C.phaseTwo.zero_above_t3 hgt3]

theorem tailBudget_eq_zero_of_t3_le
    (C : ProfileData I Γ) (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) (hθpos : 0 < I.program.theta)
    {i : Idx n} (hi : Γ.t3Star ≤ i) :
    tailBudget C.hatG i = 0 := by
  have ht1le : C.t1 ≤ Γ.t3Star := C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos
  unfold tailBudget
  apply Finset.sum_eq_zero
  intro x hx
  have hix : i < x := mem_strictSuffixRange.mp hx
  have ht3x : Γ.t3Star < x := lt_of_le_of_lt hi hix
  have ht1x : C.t1 < x := lt_of_le_of_lt ht1le ht3x
  rw [C.copied_above_t1 ht1x, C.phaseTwo.zero_above_t3 ht3x]

theorem gD_eq_hatG_of_col_le_t1_of_chi_zero
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {i j : Idx n}
    (_hj : j ≤ C.t1) (hchi : C.chi j = 0) :
    C.gD AUX i j = C.hatG i := by
  by_cases hi : i < C.t1
  · simp [ProfileData.gD, hi, hchi]
  · by_cases hieq : i = C.t1
    · simp [ProfileData.gD, hieq, hchi]
    · simp [ProfileData.gD, hi, hieq]

theorem sum_interval_gD_eq_of_col_le_t1_of_chi_zero
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (hj : j ≤ C.t1) (hchi : C.chi j = 0) :
    Finset.sum (intervalRange j i) (fun p => C.gD AUX p j) =
      beforeBudget C.hatG j - tailBudget C.hatG i := by
  calc
    Finset.sum (intervalRange j i) (fun p => C.gD AUX p j)
      = Finset.sum (intervalRange j i) C.hatG := by
          apply Finset.sum_congr rfl
          intro p hp
          exact C.gD_eq_hatG_of_col_le_t1_of_chi_zero AUX hj hchi
    _ = beforeBudget C.hatG j - tailBudget C.hatG i :=
      C.sum_interval_hatG_eq_before_sub_tail hji

theorem sum_interval_sD_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j i : Idx n) :
    Finset.sum (intervalRange j i) (fun p => C.sD AUX p j) = 0 := by
  simp [ProfileData.sD]

theorem sum_strictSuffix_gD_row_eq_zero_of_row_lt_t1_of_hatG_zero
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j : Idx n}
    (hjt1 : j < C.t1) (hhat : C.hatG j = 0) :
    Finset.sum (strictSuffixRange j) (fun q => C.gD AUX j q) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  simp [ProfileData.gD, hjt1, hhat]

theorem sum_interval_gB_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.gB AUX p j) =
      beforeBudget C.hatG j - tailBudget C.hatG i := by
  simpa [ProfileData.gB] using C.sum_interval_hatG_eq_before_sub_tail hji

theorem sum_interval_gC_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.gC AUX p j) =
      beforeBudget C.hatG j - tailBudget C.hatG i := by
  simpa [ProfileData.gC] using C.sum_interval_hatG_eq_before_sub_tail hji

theorem sum_strictSuffix_gB_row
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum (strictSuffixRange j) (fun q => C.gB AUX j q) =
      futureCount j * C.hatG j := by
  calc
    Finset.sum (strictSuffixRange j) (fun q => C.gB AUX j q)
      = Finset.sum (strictSuffixRange j) (fun _ => C.hatG j) := by simp [ProfileData.gB]
    _ = ((strictSuffixRange j).card : ℝ) * C.hatG j := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = futureCount j * C.hatG j := by
      simp [futureCount, card_strictSuffixRange]

theorem sum_strictSuffix_gC_row
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j : Idx n) :
    Finset.sum (strictSuffixRange j) (fun q => C.gC AUX j q) =
      futureCount j * C.hatG j := by
  calc
    Finset.sum (strictSuffixRange j) (fun q => C.gC AUX j q)
      = Finset.sum (strictSuffixRange j) (fun _ => C.hatG j) := by simp [ProfileData.gC]
    _ = ((strictSuffixRange j).card : ℝ) * C.hatG j := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = futureCount j * C.hatG j := by
      simp [futureCount, card_strictSuffixRange]

theorem sum_interval_nextIndex_const
    (j i : Idx n) (c : ℝ) :
    Finset.sum (intervalRange j i)
        (fun p => if IsNextIndex p (I.firstBidTime j) then c else 0) =
      if I.firstBidTime j < i then c else 0 := by
  classical
  by_cases hfi : I.firstBidTime j < i
  · let p : Idx n :=
      ⟨(I.firstBidTime j).1.succ, lt_of_le_of_lt (Nat.succ_le_of_lt hfi) i.is_lt⟩
    have hpnext : IsNextIndex p (I.firstBidTime j) := by
      unfold IsNextIndex
      simp [p]
    have hmem : p ∈ intervalRange j i := by
      have hpj : j ≤ p := le_trans (I.le_firstBidTime j) (le_of_lt (IsNextIndex.lt hpnext))
      have hpi : p ≤ i := by
        exact Fin.le_iff_val_le_val.mpr (Nat.succ_le_of_lt hfi)
      simp [hpj, hpi]
    rw [if_pos hfi]
    have hsingle :
        Finset.sum (intervalRange j i)
            (fun p => if IsNextIndex p (I.firstBidTime j) then c else 0) =
          if IsNextIndex p (I.firstBidTime j) then c else 0 := by
      refine Finset.sum_eq_single_of_mem p hmem ?_
      intro q hq hqne
      by_cases hnext : IsNextIndex q (I.firstBidTime j)
      · exfalso
        apply hqne
        apply Fin.ext
        exact hnext.symm.trans hpnext
      · simp [hnext]
    simpa [hpnext] using hsingle
  · rw [if_neg hfi]
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hnext : IsNextIndex p (I.firstBidTime j)
    · exfalso
      apply hfi
      exact lt_of_lt_of_le (IsNextIndex.lt hnext) (mem_intervalRange.mp hp).2
    · simp [hnext]

theorem sum_interval_sB_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.sB AUX p j) =
      tailBudget C.hatG j - tailBudget C.hatG i +
        (if I.firstBidTime j < i then I.program.epsilon else 0) := by
  calc
    Finset.sum (intervalRange j i) (fun p => C.sB AUX p j)
      = Finset.sum (intervalRange j i)
          (fun p =>
            (if j < p then C.hatG p else 0) +
              (if IsNextIndex p (I.firstBidTime j) then I.program.epsilon else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hnext : IsNextIndex p (I.firstBidTime j)
          · have hjp : j < p := lt_of_le_of_lt (I.le_firstBidTime j) (IsNextIndex.lt hnext)
            simp [ProfileData.sB, hnext, hjp]
          · by_cases hjp : j < p
            · simp [ProfileData.sB, hnext, hjp]
            · have hpj : p = j := le_antisymm (not_lt.mp hjp) (mem_intervalRange.mp hp).1
              subst hpj
              simp [ProfileData.sB, hnext]
    _ = Finset.sum (intervalRange j i) (fun p => if j < p then C.hatG p else 0) +
          Finset.sum (intervalRange j i)
            (fun p => if IsNextIndex p (I.firstBidTime j) then I.program.epsilon else 0) := by
          rw [Finset.sum_add_distrib]
    _ = tailBudget C.hatG j - tailBudget C.hatG i +
          (if I.firstBidTime j < i then I.program.epsilon else 0) := by
          rw [C.sum_interval_strict_right_hatG_eq_tail_sub_tail hji,
            sum_interval_nextIndex_const (I := I) j i I.program.epsilon]

theorem sum_interval_sC_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} (hji : j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.sC AUX p j) =
      tailBudget C.hatG j - tailBudget C.hatG i +
        (if I.firstBidTime j < i then I.program.epsilon else 0) := by
  calc
    Finset.sum (intervalRange j i) (fun p => C.sC AUX p j)
      = Finset.sum (intervalRange j i)
          (fun p =>
            (if j < p then C.hatG p else 0) +
              (if IsNextIndex p (I.firstBidTime j) then I.program.epsilon else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hnext : IsNextIndex p (I.firstBidTime j)
          · have hjp : j < p := lt_of_le_of_lt (I.le_firstBidTime j) (IsNextIndex.lt hnext)
            simp [ProfileData.sC, hnext, hjp]
          · by_cases hjp : j < p
            · simp [ProfileData.sC, hnext, hjp]
            · have hpj : p = j := le_antisymm (not_lt.mp hjp) (mem_intervalRange.mp hp).1
              subst hpj
              simp [ProfileData.sC, hnext]
    _ = Finset.sum (intervalRange j i) (fun p => if j < p then C.hatG p else 0) +
          Finset.sum (intervalRange j i)
            (fun p => if IsNextIndex p (I.firstBidTime j) then I.program.epsilon else 0) := by
          rw [Finset.sum_add_distrib]
    _ = tailBudget C.hatG j - tailBudget C.hatG i +
          (if I.firstBidTime j < i then I.program.epsilon else 0) := by
          rw [C.sum_interval_strict_right_hatG_eq_tail_sub_tail hji,
            sum_interval_nextIndex_const (I := I) j i I.program.epsilon]

theorem sum_interval_tA_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j i : Idx n) :
    Finset.sum (intervalRange j i) (fun p => C.tA AUX p j) = 0 := by
  simp [ProfileData.tA]

theorem sum_interval_tB_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j i : Idx n) :
    Finset.sum (intervalRange j i) (fun p => C.tB AUX p j) =
      if I.firstBidTime j ≤ i then
        posPart (1 - beforeBudget C.hatG j - I.program.tau)
      else
        0 := by
  classical
  by_cases hfi : I.firstBidTime j ≤ i
  · rw [if_pos hfi]
    have hmem : I.firstBidTime j ∈ intervalRange j i := by
      simp [I.le_firstBidTime j, hfi]
    rw [Finset.sum_eq_single_of_mem (I.firstBidTime j) hmem]
    · simp [ProfileData.tB]
    · intro p hp hpne
      simp [ProfileData.tB, hpne]
  · rw [if_neg hfi]
    apply Finset.sum_eq_zero
    intro p hp
    have hpne : p ≠ I.firstBidTime j := by
      intro hpeq
      exact hfi (hpeq ▸ (mem_intervalRange.mp hp).2)
    simp [ProfileData.tB, hpne]

theorem sum_interval_tC_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j i : Idx n) :
    Finset.sum (intervalRange j i) (fun p => C.tC AUX p j) =
      if I.firstBidTime j ≤ i then
        1 - beforeBudget C.hatG j - I.program.tau
      else
        0 := by
  classical
  by_cases hfi : I.firstBidTime j ≤ i
  · rw [if_pos hfi]
    have hmem : I.firstBidTime j ∈ intervalRange j i := by
      simp [I.le_firstBidTime j, hfi]
    rw [Finset.sum_eq_single_of_mem (I.firstBidTime j) hmem]
    · simp [ProfileData.tC]
    · intro p hp hpne
      simp [ProfileData.tC, hpne]
  · rw [if_neg hfi]
    apply Finset.sum_eq_zero
    intro p hp
    have hpne : p ≠ I.firstBidTime j := by
      intro hpeq
      exact hfi (hpeq ▸ (mem_intervalRange.mp hp).2)
    simp [ProfileData.tC, hpne]

theorem sum_interval_tD_eq
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (j i : Idx n) :
    Finset.sum (intervalRange j i) (fun p => C.tD AUX p j) =
      if I.firstBidTime j ≤ i then
        1 - beforeBudget C.hatG j
      else
        0 := by
  classical
  by_cases hfi : I.firstBidTime j ≤ i
  · rw [if_pos hfi]
    have hmem : I.firstBidTime j ∈ intervalRange j i := by
      simp [I.le_firstBidTime j, hfi]
    rw [Finset.sum_eq_single_of_mem (I.firstBidTime j) hmem]
    · simp [ProfileData.tD]
    · intro p hp hpne
      simp [ProfileData.tD, hpne]
  · rw [if_neg hfi]
    apply Finset.sum_eq_zero
    intro p hp
    have hpne : p ≠ I.firstBidTime j := by
      intro hpeq
      exact hfi (hpeq ▸ (mem_intervalRange.mp hp).2)
    simp [ProfileData.tD, hpne]

theorem gD_eq_hatG_of_row_gt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {i j : Idx n}
    (hti : C.t1 < i) :
    C.gD AUX i j = C.hatG i := by
  have hnotlt : ¬ i < C.t1 := not_lt.mpr (le_of_lt hti)
  have hneq : i ≠ C.t1 := ne_of_gt hti
  simp [ProfileData.gD, hnotlt, hneq]

theorem sum_interval_gD_eq_of_t1_lt_col
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (ht1j : C.t1 < j) :
    Finset.sum (intervalRange j i) (fun p => C.gD AUX p j) =
      beforeBudget C.hatG j - tailBudget C.hatG i := by
  calc
    Finset.sum (intervalRange j i) (fun p => C.gD AUX p j)
      = Finset.sum (intervalRange j i) C.hatG := by
          apply Finset.sum_congr rfl
          intro p hp
          exact C.gD_eq_hatG_of_row_gt_t1 AUX (lt_of_lt_of_le ht1j (mem_intervalRange.mp hp).1)
    _ = beforeBudget C.hatG j - tailBudget C.hatG i :=
      C.sum_interval_hatG_eq_before_sub_tail hji

theorem sum_strictSuffix_gD_row_eq_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j : Idx n}
    (ht1j : C.t1 < j) :
    Finset.sum (strictSuffixRange j) (fun q => C.gD AUX j q) =
      futureCount j * C.hatG j := by
  calc
    Finset.sum (strictSuffixRange j) (fun q => C.gD AUX j q)
      = Finset.sum (strictSuffixRange j) (fun _ => C.hatG j) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact C.gD_eq_hatG_of_row_gt_t1 AUX ht1j
    _ = ((strictSuffixRange j).card : ℝ) * C.hatG j := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = futureCount j * C.hatG j := by
      simp [futureCount, card_strictSuffixRange]

theorem creditValue_D_before_eq_of_integralD
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hμ : Γ.muD j = 1) (hji : j ≤ i) (hif : i < I.firstBidTime j) :
    C.creditValue AUX i j = beforeBudget C.hatG j - tailBudget C.hatG i := by
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  have hcomb :
      (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j) =
        fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j := by
      funext p
      simp [C.gValue_eq_gD_of_integralD AUX hΓ hμ,
        C.sValue_eq_sD_of_integralD AUX hΓ hμ,
        C.tValue_eq_tD_of_integralD AUX hΓ hμ]
  have hrow0 : Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) = 0 := by
    by_cases hlast : j = lastIdx n
    · subst hlast
      apply Finset.sum_eq_zero
      intro q hq
      exact False.elim ((not_lt_of_ge (le_lastIdx q)) (mem_strictSuffixRange.mp hq))
    · by_cases hjlt : j < C.t1
      · rw [C.sum_strictSuffix_gValue_row_eq_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjlt,
          C.hatG_eq_zero_of_integralD_lt_t1 hjlt hμ]
        ring
      · by_cases hjeq : j = C.t1
        · exfalso
          exact hlast (hjeq.trans
            (C.muD_eq_one_at_t1_implies_last hΓ hγlo hγhi hθpos (by simpa [hjeq] using hμ)))
        · have ht1j : C.t1 < j := lt_of_le_of_ne (not_lt.mp hjlt) (Ne.symm hjeq)
          rw [C.sum_strictSuffix_gValue_row_eq_of_t1_lt AUX hΓ ht1j,
            C.hatG_eq_zero_of_integralD_gt_t1_of_ne_last ht1j hμ hlast]
          ring
  have hg :
      Finset.sum (intervalRange j i) (fun p => C.gD AUX p j) =
        beforeBudget C.hatG j - tailBudget C.hatG i := by
    by_cases hj : j ≤ C.t1
    · have hchi : C.chi j = 0 := by
        exact C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos (le_trans hj C.t1_le_t2)
      exact C.sum_interval_gD_eq_of_col_le_t1_of_chi_zero AUX hji hj hchi
    · exact C.sum_interval_gD_eq_of_t1_lt_col AUX hji (lt_of_not_ge hj)
  rw [hrow0, hcomb, Finset.sum_sub_distrib, Finset.sum_add_distrib, hg,
    C.sum_interval_tD_eq AUX, C.sum_interval_sD_eq AUX, if_neg (not_le.mpr hif)]
  ring

theorem creditValue_D_after_eq_of_integralD
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hμ : Γ.muD j = 1) (hji : j ≤ i) (hif : I.firstBidTime j ≤ i) :
    C.creditValue AUX i j = 1 := by
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  have hcomb :
      (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j) =
        fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j := by
      funext p
      simp [C.gValue_eq_gD_of_integralD AUX hΓ hμ,
        C.sValue_eq_sD_of_integralD AUX hΓ hμ,
        C.tValue_eq_tD_of_integralD AUX hΓ hμ]
  have hrow0 : Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) = 0 := by
    by_cases hlast : j = lastIdx n
    · subst hlast
      apply Finset.sum_eq_zero
      intro q hq
      exact False.elim ((not_lt_of_ge (le_lastIdx q)) (mem_strictSuffixRange.mp hq))
    · by_cases hjlt : j < C.t1
      · rw [C.sum_strictSuffix_gValue_row_eq_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjlt,
          C.hatG_eq_zero_of_integralD_lt_t1 hjlt hμ]
        ring
      · by_cases hjeq : j = C.t1
        · exfalso
          exact hlast (hjeq.trans
            (C.muD_eq_one_at_t1_implies_last hΓ hγlo hγhi hθpos (by simpa [hjeq] using hμ)))
        · have ht1j : C.t1 < j := lt_of_le_of_ne (not_lt.mp hjlt) (Ne.symm hjeq)
          rw [C.sum_strictSuffix_gValue_row_eq_of_t1_lt AUX hΓ ht1j,
            C.hatG_eq_zero_of_integralD_gt_t1_of_ne_last ht1j hμ hlast]
          ring
  have hg :
      Finset.sum (intervalRange j i) (fun p => C.gD AUX p j) =
        beforeBudget C.hatG j - tailBudget C.hatG i := by
    by_cases hj : j ≤ C.t1
    · have hchi : C.chi j = 0 := by
        exact C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos (le_trans hj C.t1_le_t2)
      exact C.sum_interval_gD_eq_of_col_le_t1_of_chi_zero AUX hji hj hchi
    · exact C.sum_interval_gD_eq_of_t1_lt_col AUX hji (lt_of_not_ge hj)
  have htail0 : tailBudget C.hatG i = 0 := by
    exact C.tailBudget_eq_zero_of_t3_le hγlo hγhi hθpos
      (le_trans (t3_le_firstBidTime_of_muD_eq_one Γ hμ) hif)
  rw [hrow0, hcomb, Finset.sum_sub_distrib, Finset.sum_add_distrib, hg,
    C.sum_interval_tD_eq AUX, C.sum_interval_sD_eq AUX, if_pos hif, htail0]
  ring

theorem creditB_eq_one_sub_indicator_after
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (ht1j : C.t1 < j) (hfj : I.firstBidTime j < Γ.t3Star)
    (hif : I.firstBidTime j ≤ i) :
    C.creditB AUX i j = 1 - (if I.firstBidTime j < i then I.program.epsilon else 0) := by
  unfold ProfileData.creditB ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gB_row_eq_tailBudget_add_tau_of_lt_t1_of_firstBid_lt_t3 AUX ht1j hfj]
  rw [show (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
      (fun p => (C.gB AUX p j + C.tB AUX p j) - C.sB AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gB_eq AUX hji,
    C.sum_interval_tB_eq AUX, C.sum_interval_sB_eq AUX hji, if_pos hif]
  have ht : 0 ≤ 1 - beforeBudget C.hatG j - I.program.tau := by
    have hbar : beforeBudget C.hatG j < I.program.barTau := C.beforeBudget_lt_barTau_of_lt_t1 ht1j
    have hbar' : beforeBudget C.hatG j < 1 - I.program.tau := by
      simpa [DualProgram.barTau] using hbar
    linarith
  rw [posPart_of_nonneg ht]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  linarith

theorem creditC_eq_one_sub_indicator_after
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (ht1j : C.t1 < j) (hfj : I.firstBidTime j < Γ.t3Star)
    (hif : I.firstBidTime j ≤ i) :
    C.creditC AUX i j = 1 - (if I.firstBidTime j < i then I.program.epsilon else 0) := by
  unfold ProfileData.creditC ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gC_row_eq_tailBudget_add_tau_of_lt_t1_of_firstBid_lt_t3 AUX ht1j hfj]
  rw [show (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
      (fun p => (C.gC AUX p j + C.tC AUX p j) - C.sC AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gC_eq AUX hji,
    C.sum_interval_tC_eq AUX, C.sum_interval_sC_eq AUX hji, if_pos hif]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  linarith

theorem creditB_eq_tau_add_before_before
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (ht1j : C.t1 < j) (hfj : I.firstBidTime j < Γ.t3Star)
    (hif : i < I.firstBidTime j) :
    C.creditB AUX i j = I.program.tau + beforeBudget C.hatG j := by
  unfold ProfileData.creditB ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gB_row_eq_tailBudget_add_tau_of_lt_t1_of_firstBid_lt_t3 AUX ht1j hfj]
  rw [show (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
      (fun p => (C.gB AUX p j + C.tB AUX p j) - C.sB AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gB_eq AUX hji,
    C.sum_interval_tB_eq AUX, C.sum_interval_sB_eq AUX hji, if_neg (not_le.mpr hif),
    if_neg (not_lt.mpr (le_of_lt hif))]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  linarith

theorem creditC_eq_tau_add_before_before
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (ht1j : C.t1 < j) (hfj : I.firstBidTime j < Γ.t3Star)
    (hif : i < I.firstBidTime j) :
    C.creditC AUX i j = I.program.tau + beforeBudget C.hatG j := by
  unfold ProfileData.creditC ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gC_row_eq_tailBudget_add_tau_of_lt_t1_of_firstBid_lt_t3 AUX ht1j hfj]
  rw [show (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
      (fun p => (C.gC AUX p j + C.tC AUX p j) - C.sC AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gC_eq AUX hji,
    C.sum_interval_tC_eq AUX, C.sum_interval_sC_eq AUX hji, if_neg (not_le.mpr hif),
    if_neg (not_lt.mpr (le_of_lt hif))]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  linarith

theorem memberships_muA_eq_zero_of_between_t1_t2
    (C : ProfileData I Γ) {j : Idx n} (ht1j : C.t1 < j) (_hjt2 : j ≤ C.t2) :
    (C.memberships).muA j = 0 := by
  have hnotlt : ¬ j < C.t1 := not_lt.mpr (le_of_lt ht1j)
  have hneq : j ≠ C.t1 := ne_of_gt ht1j
  simp [ProfileData.memberships, hnotlt, hneq]

theorem memberships_muB_eq_of_between_t1_t2
    (C : ProfileData I Γ) {j : Idx n} (ht1j : C.t1 < j) (hjt2 : j ≤ C.t2) :
    (C.memberships).muB j = 1 - Γ.muD j := by
  have hneq : j ≠ C.t1 := ne_of_gt ht1j
  have hcond : C.t1 < j ∧ j ≤ C.t2 := ⟨ht1j, hjt2⟩
  simp [ProfileData.memberships, hneq, hcond]

theorem memberships_muA_eq_at_t1
    (C : ProfileData I Γ) :
    (C.memberships).muA C.t1 = (1 - C.alpha) * (1 - Γ.muD C.t1) := by
  simp [ProfileData.memberships]

theorem memberships_muB_eq_at_t1
    (C : ProfileData I Γ) :
    (C.memberships).muB C.t1 = C.alpha * (1 - Γ.muD C.t1) := by
  simp [ProfileData.memberships]

theorem memberships_muC_eq_zero_at_t1
    (C : ProfileData I Γ) :
    (C.memberships).muC C.t1 = 0 := by
  have hnot : ¬ (C.t2 < C.t1 ∧ C.t1 ≤ Γ.t3Star) := by
    intro h
    exact (not_lt.mpr C.t1_le_t2) h.1
  simp [ProfileData.memberships, hnot]

theorem memberships_muC_eq_zero_of_between_t1_t2
    (C : ProfileData I Γ) {j : Idx n} (_ht1j : C.t1 < j) (hjt2 : j ≤ C.t2) :
    (C.memberships).muC j = 0 := by
  have hnot : ¬ (C.t2 < j ∧ j ≤ Γ.t3Star) := by
    intro h
    exact (not_lt.mpr hjt2) h.1
  simp [ProfileData.memberships, hnot]

theorem memberships_muA_eq_zero_of_between_t2_t3
    (C : ProfileData I Γ) {j : Idx n} (ht2j : C.t2 < j) (_hjt3 : j ≤ Γ.t3Star) :
    (C.memberships).muA j = 0 := by
  have hnotlt : ¬ j < C.t1 := not_lt.mpr (le_trans C.t1_le_t2 (le_of_lt ht2j))
  have hneq : j ≠ C.t1 := by
    exact ne_of_gt (lt_of_le_of_lt C.t1_le_t2 ht2j)
  simp [ProfileData.memberships, hnotlt, hneq]

theorem memberships_muB_eq_zero_of_between_t2_t3
    (C : ProfileData I Γ) {j : Idx n} (ht2j : C.t2 < j) (_hjt3 : j ≤ Γ.t3Star) :
    (C.memberships).muB j = 0 := by
  have hneq : j ≠ C.t1 := by
    exact ne_of_gt (lt_of_le_of_lt C.t1_le_t2 ht2j)
  have hnot : ¬ (C.t1 < j ∧ j ≤ C.t2) := by
    intro h
    exact (not_lt.mpr h.2) ht2j
  simp [ProfileData.memberships, hneq, hnot]

theorem memberships_muC_eq_of_between_t2_t3
    (C : ProfileData I Γ) {j : Idx n} (ht2j : C.t2 < j) (hjt3 : j ≤ Γ.t3Star) :
    (C.memberships).muC j = 1 - Γ.muD j := by
  have hcond : C.t2 < j ∧ j ≤ Γ.t3Star := ⟨ht2j, hjt3⟩
  simp [ProfileData.memberships, hcond]

theorem sum_strictSuffix_muD_chi_eq_z_at_t1
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    Finset.sum (strictSuffixRange C.t1) (fun q => (C.memberships).muD q * C.chi q) = C.z := by
  have hzero :
      Finset.sum ((strictSuffixRange C.t1).filter (fun q => q ≤ C.t2))
          (fun q => (C.memberships).muD q * C.chi q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨-, hqt2⟩
    rw [C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos hqt2]
    ring
  have hright :
      (strictSuffixRange C.t1).filter (fun q => ¬ q ≤ C.t2) = strictSuffixRange C.t2 := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_filter.mp hq with ⟨-, hnot⟩
      exact mem_strictSuffixRange.mpr (lt_of_not_ge hnot)
    · intro hq
      exact Finset.mem_filter.mpr ⟨
        mem_strictSuffixRange.mpr
          (lt_of_le_of_lt C.t1_le_t2 (mem_strictSuffixRange.mp hq)),
        not_le.mpr (mem_strictSuffixRange.mp hq)⟩
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := strictSuffixRange C.t1) (p := fun q => q ≤ C.t2)
      (fun q => (C.memberships).muD q * C.chi q)
  rw [hzero, zero_add, hright] at hsplit
  have hmain :
      Finset.sum (strictSuffixRange C.t1) (fun q => (C.memberships).muD q * C.chi q) =
        Finset.sum (strictSuffixRange C.t2) (fun q => (C.memberships).muD q * C.chi q) := by
    simpa using hsplit.symm
  rw [hmain, C.z_eq]
  apply Finset.sum_congr rfl
  intro q hq
  have ht1q : C.t1 < q := lt_of_le_of_lt C.t1_le_t2 (mem_strictSuffixRange.mp hq)
  rw [C.memberships_muD, ProfileData.chi, C.beforeBudget_eq_phaseTwo_beforeBudget_of_lt_t1 ht1q]
  ring

theorem gValue_row_eq_at_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {q : Idx n} (ht1q : C.t1 < q) :
    C.gValue AUX C.t1 q =
      C.hatG C.t1 -
        (C.memberships).muD q * C.chi q * I.program.frac * C.boundaryHatGA := by
  have hμnonneg := C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds
  have hA :
      (C.memberships).muA q * C.gA AUX C.t1 q = (C.memberships).muA q * C.hatG C.t1 := by
    by_cases hμA : (C.memberships).muA q = 0
    · simp [hμA]
    · have hμA_nonneg : 0 ≤ (C.memberships).muA q := hμnonneg.1 q
      have hμA_pos : 0 < (C.memberships).muA q := lt_of_le_of_ne hμA_nonneg (Ne.symm hμA)
      have hdelta : AUX.delta C.t1 q = 0 := by
        exact AUX.delta_eq_zero C.t1 q hμA_pos (le_trans (le_of_lt ht1q) (I.le_firstBidTime q))
      simp [ProfileData.gA, hdelta]
  have hD :
      C.gD AUX C.t1 q = C.hatG C.t1 - C.chi q * I.program.frac * C.boundaryHatGA := by
    simp [ProfileData.gD]
  have htot : (C.memberships).total q = 1 := C.memberships_total q
  unfold MembershipWeights.total at htot
  have htot' :
      (C.memberships).muA q + (C.memberships).muB q + (C.memberships).muC q + Γ.muD q = 1 := by
    simpa [C.memberships_muD] using htot
  have hsimp :
      (C.memberships).muA q * C.hatG C.t1 +
          (C.memberships).muB q * C.hatG C.t1 +
          (C.memberships).muC q * C.hatG C.t1 +
          Γ.muD q * (C.hatG C.t1 - C.chi q * I.program.frac * C.boundaryHatGA) =
        C.hatG C.t1 - Γ.muD q * C.chi q * I.program.frac * C.boundaryHatGA := by
    have hsum :
        (C.memberships).muA q * C.hatG C.t1 +
            (C.memberships).muB q * C.hatG C.t1 +
            (C.memberships).muC q * C.hatG C.t1 +
            Γ.muD q * C.hatG C.t1 =
          C.hatG C.t1 := by
      calc
        (C.memberships).muA q * C.hatG C.t1 +
            (C.memberships).muB q * C.hatG C.t1 +
            (C.memberships).muC q * C.hatG C.t1 +
            Γ.muD q * C.hatG C.t1
          = ((C.memberships).muA q + (C.memberships).muB q +
              (C.memberships).muC q + Γ.muD q) * C.hatG C.t1 := by
                ring
        _ = C.hatG C.t1 := by rw [htot']; ring
    calc
      (C.memberships).muA q * C.hatG C.t1 +
          (C.memberships).muB q * C.hatG C.t1 +
          (C.memberships).muC q * C.hatG C.t1 +
          Γ.muD q * (C.hatG C.t1 - C.chi q * I.program.frac * C.boundaryHatGA)
        = ((C.memberships).muA q * C.hatG C.t1 + (C.memberships).muB q * C.hatG C.t1 +
            (C.memberships).muC q * C.hatG C.t1 + Γ.muD q * C.hatG C.t1) -
            Γ.muD q * C.chi q * I.program.frac * C.boundaryHatGA := by
              ring
      _ = C.hatG C.t1 - Γ.muD q * C.chi q * I.program.frac * C.boundaryHatGA := by
            rw [hsum]
  simpa [ProfileData.gValue, hA, ProfileData.gB, ProfileData.gC, hD, C.memberships_muD] using hsimp

theorem sum_strictSuffix_gValue_row_eq_at_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) :
    Finset.sum (strictSuffixRange C.t1) (fun q => C.gValue AUX C.t1 q) =
      futureCount C.t1 * C.boundaryHatGB +
        (futureCount C.t1 - I.program.frac * C.z) * C.boundaryHatGA := by
  calc
    Finset.sum (strictSuffixRange C.t1) (fun q => C.gValue AUX C.t1 q)
      = Finset.sum (strictSuffixRange C.t1)
          (fun q =>
            C.hatG C.t1 -
              (C.memberships).muD q * C.chi q * I.program.frac * C.boundaryHatGA) := by
            apply Finset.sum_congr rfl
            intro q hq
            exact C.gValue_row_eq_at_t1 AUX hΓ (mem_strictSuffixRange.mp hq)
    _ = Finset.sum (strictSuffixRange C.t1) (fun _ => C.hatG C.t1) -
          Finset.sum (strictSuffixRange C.t1)
            (fun q => (C.memberships).muD q * C.chi q * I.program.frac * C.boundaryHatGA) := by
          rw [Finset.sum_sub_distrib]
    _ = futureCount C.t1 * C.hatG C.t1 -
          Finset.sum (strictSuffixRange C.t1)
            (fun q => (C.memberships).muD q * C.chi q * I.program.frac * C.boundaryHatGA) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [futureCount, card_strictSuffixRange]
    _ = futureCount C.t1 * C.hatG C.t1 -
          ((Finset.sum (strictSuffixRange C.t1) (fun q => (C.memberships).muD q * C.chi q)) *
            (I.program.frac * C.boundaryHatGA)) := by
          congr 1
          calc
            Finset.sum (strictSuffixRange C.t1)
                (fun q => (C.memberships).muD q * C.chi q * I.program.frac * C.boundaryHatGA)
              = Finset.sum (strictSuffixRange C.t1)
                  (fun q => ((C.memberships).muD q * C.chi q) *
                    (I.program.frac * C.boundaryHatGA)) := by
                      apply Finset.sum_congr rfl
                      intro q hq
                      ring
            _ = (Finset.sum (strictSuffixRange C.t1) (fun q => (C.memberships).muD q * C.chi q)) *
                  (I.program.frac * C.boundaryHatGA) := by
                    rw [Finset.sum_mul]
    _ = futureCount C.t1 * C.hatG C.t1 - (C.z * (I.program.frac * C.boundaryHatGA)) := by
          rw [C.sum_strictSuffix_muD_chi_eq_z_at_t1 hΓ hγlo hγhi hθpos]
    _ = futureCount C.t1 * C.boundaryHatGB +
          (futureCount C.t1 - I.program.frac * C.z) * C.boundaryHatGA := by
          rw [C.boundary_eq, ProfileData.boundaryHatGA, ProfileData.boundaryHatGB]
          ring_nf

theorem sum_interval_gValue_eq_membership_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} :
    Finset.sum (intervalRange j i) (fun p => C.gValue AUX p j) =
      (C.memberships).muA j * Finset.sum (intervalRange j i) (fun p => C.gA AUX p j) +
      (C.memberships).muB j * Finset.sum (intervalRange j i) (fun p => C.gB AUX p j) +
      (C.memberships).muC j * Finset.sum (intervalRange j i) (fun p => C.gC AUX p j) +
      (C.memberships).muD j * Finset.sum (intervalRange j i) (fun p => C.gD AUX p j) := by
  calc
    Finset.sum (intervalRange j i) (fun p => C.gValue AUX p j)
      = Finset.sum (intervalRange j i) (fun p =>
          (C.memberships).muA j * C.gA AUX p j +
          (C.memberships).muB j * C.gB AUX p j +
          (C.memberships).muC j * C.gC AUX p j +
          (C.memberships).muD j * C.gD AUX p j) := by
            apply Finset.sum_congr rfl
            intro p hp
            simp [ProfileData.gValue]
      _ = (C.memberships).muA j * Finset.sum (intervalRange j i) (fun p => C.gA AUX p j) +
          (C.memberships).muB j * Finset.sum (intervalRange j i) (fun p => C.gB AUX p j) +
          (C.memberships).muC j * Finset.sum (intervalRange j i) (fun p => C.gC AUX p j) +
          (C.memberships).muD j * Finset.sum (intervalRange j i) (fun p => C.gD AUX p j) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

theorem sum_interval_sValue_eq_membership_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} :
    Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j) =
      (C.memberships).muA j * Finset.sum (intervalRange j i) (fun p => C.sA AUX p j) +
      (C.memberships).muB j * Finset.sum (intervalRange j i) (fun p => C.sB AUX p j) +
      (C.memberships).muC j * Finset.sum (intervalRange j i) (fun p => C.sC AUX p j) +
      (C.memberships).muD j * Finset.sum (intervalRange j i) (fun p => C.sD AUX p j) := by
  calc
    Finset.sum (intervalRange j i) (fun p => C.sValue AUX p j)
      = Finset.sum (intervalRange j i) (fun p =>
          (C.memberships).muA j * C.sA AUX p j +
          (C.memberships).muB j * C.sB AUX p j +
          (C.memberships).muC j * C.sC AUX p j +
          (C.memberships).muD j * C.sD AUX p j) := by
            apply Finset.sum_congr rfl
            intro p hp
            simp [ProfileData.sValue]
      _ = (C.memberships).muA j * Finset.sum (intervalRange j i) (fun p => C.sA AUX p j) +
          (C.memberships).muB j * Finset.sum (intervalRange j i) (fun p => C.sB AUX p j) +
          (C.memberships).muC j * Finset.sum (intervalRange j i) (fun p => C.sC AUX p j) +
          (C.memberships).muD j * Finset.sum (intervalRange j i) (fun p => C.sD AUX p j) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

theorem sum_interval_tValue_eq_membership_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} :
    Finset.sum (intervalRange j i) (fun p => C.tValue AUX p j) =
      (C.memberships).muA j * Finset.sum (intervalRange j i) (fun p => C.tA AUX p j) +
      (C.memberships).muB j * Finset.sum (intervalRange j i) (fun p => C.tB AUX p j) +
      (C.memberships).muC j * Finset.sum (intervalRange j i) (fun p => C.tC AUX p j) +
      (C.memberships).muD j * Finset.sum (intervalRange j i) (fun p => C.tD AUX p j) := by
  calc
    Finset.sum (intervalRange j i) (fun p => C.tValue AUX p j)
      = Finset.sum (intervalRange j i) (fun p =>
          (C.memberships).muA j * C.tA AUX p j +
          (C.memberships).muB j * C.tB AUX p j +
          (C.memberships).muC j * C.tC AUX p j +
          (C.memberships).muD j * C.tD AUX p j) := by
            apply Finset.sum_congr rfl
            intro p hp
            simp [ProfileData.tValue]
      _ = (C.memberships).muA j * Finset.sum (intervalRange j i) (fun p => C.tA AUX p j) +
          (C.memberships).muB j * Finset.sum (intervalRange j i) (fun p => C.tB AUX p j) +
          (C.memberships).muC j * Finset.sum (intervalRange j i) (fun p => C.tC AUX p j) +
          (C.memberships).muD j * Finset.sum (intervalRange j i) (fun p => C.tD AUX p j) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

theorem sum_interval_gts_value_eq_membership_combo
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n} :
    Finset.sum (intervalRange j i)
        (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j) =
      (C.memberships).muA j *
        Finset.sum (intervalRange j i) (fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j) +
      (C.memberships).muB j *
        Finset.sum (intervalRange j i) (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) +
      (C.memberships).muC j *
        Finset.sum (intervalRange j i) (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) +
      (C.memberships).muD j *
        Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) := by
  have hA :
      Finset.sum (intervalRange j i) (fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j) =
        Finset.sum (intervalRange j i) (fun p => C.gA AUX p j) +
          Finset.sum (intervalRange j i) (fun p => C.tA AUX p j) -
          Finset.sum (intervalRange j i) (fun p => C.sA AUX p j) := by
    rw [show (fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j) =
        (fun p => (C.gA AUX p j + C.tA AUX p j) - C.sA AUX p j) by
          funext p
          ring,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hB :
      Finset.sum (intervalRange j i) (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
        Finset.sum (intervalRange j i) (fun p => C.gB AUX p j) +
          Finset.sum (intervalRange j i) (fun p => C.tB AUX p j) -
          Finset.sum (intervalRange j i) (fun p => C.sB AUX p j) := by
    rw [show (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
        (fun p => (C.gB AUX p j + C.tB AUX p j) - C.sB AUX p j) by
          funext p
          ring,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hC :
      Finset.sum (intervalRange j i) (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
        Finset.sum (intervalRange j i) (fun p => C.gC AUX p j) +
          Finset.sum (intervalRange j i) (fun p => C.tC AUX p j) -
          Finset.sum (intervalRange j i) (fun p => C.sC AUX p j) := by
    rw [show (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
        (fun p => (C.gC AUX p j + C.tC AUX p j) - C.sC AUX p j) by
          funext p
          ring,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hD :
      Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
        Finset.sum (intervalRange j i) (fun p => C.gD AUX p j) +
          Finset.sum (intervalRange j i) (fun p => C.tD AUX p j) -
          Finset.sum (intervalRange j i) (fun p => C.sD AUX p j) := by
    rw [show (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
        (fun p => (C.gD AUX p j + C.tD AUX p j) - C.sD AUX p j) by
          funext p
          ring,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (fun p => C.gValue AUX p j + C.tValue AUX p j - C.sValue AUX p j) =
      (fun p => (C.gValue AUX p j + C.tValue AUX p j) - C.sValue AUX p j) by
        funext p
        ring,
    Finset.sum_sub_distrib, Finset.sum_add_distrib,
    C.sum_interval_gValue_eq_membership_combo AUX,
    C.sum_interval_tValue_eq_membership_combo AUX,
    C.sum_interval_sValue_eq_membership_combo AUX,
    hA, hB, hC, hD]
  ring

theorem t3_le_firstBidTime_of_muD_pos
    (Γ : Advice I) {j : Idx n} (hμ : 0 < Γ.muD j) :
    Γ.t3Star ≤ I.firstBidTime j := by
  by_cases hlt : Γ.t3Star < I.firstBidTime j
  · exact le_of_lt hlt
  · by_cases heq : I.firstBidTime j = Γ.t3Star
    · exact le_of_eq heq.symm
    · have hzero : Γ.muD j = 0 := by
        simp [Advice.muD, hlt, heq]
      linarith

theorem futureCount_mul_hatG_eq_one_sub_muD_mul_tailBudget_add_tau_of_t1_lt
    (C : ProfileData I Γ) (hΓ : Γ.Admissible) {j : Idx n} (ht1j : C.t1 < j) :
    futureCount j * C.hatG j =
      (1 - Γ.muD j) * (tailBudget C.hatG j + I.program.tau) := by
  by_cases hjt3 : j ≤ Γ.t3Star
  · have hcopy : C.hatG j = C.phaseTwo.hatG2 j := C.copied_above_t1 ht1j
    by_cases hspecial : j = lastIdx n ∧ Γ.t3Star = lastIdx n
    · rcases hΓ with ⟨-, -, -, hall⟩
      rcases hspecial with ⟨hjlast, ht3last⟩
      have hfront : Γ.OnFrontier j := by
        unfold Advice.OnFrontier
        apply le_antisymm
        · calc
            I.firstBidTime j ≤ lastIdx n := le_lastIdx _
            _ = Γ.t3Star := ht3last.symm
        · calc
            Γ.t3Star = lastIdx n := ht3last
            _ = j := hjlast.symm
            _ ≤ I.firstBidTime j := I.le_firstBidTime j
      have hμstar : Γ.muStar j = 1 := hall ht3last hfront
      have hmuD : Γ.muD j = 1 := by
        exact (Advice.muD_eq_muStar Γ hfront).trans hμstar
      subst hjlast
      simp [futureCount_last, hmuD, tailBudget, strictSuffixRange]
    · have hstep := C.phaseTwo.step_eq j hjt3
      have hstep' :
          C.phaseTwo.hatG2 j =
            (1 - Γ.muD j) * (C.phaseTwo.afterBudget j + I.program.tau) / futureCount j := by
        simpa [PhaseTwoData.afterBudget, hspecial] using hstep
      have hjltlast : j < lastIdx n := by
        by_contra hnot
        have hjlast : j = lastIdx n := le_antisymm (le_lastIdx _) (not_lt.mp hnot)
        have ht3last : Γ.t3Star = lastIdx n := le_antisymm (le_lastIdx _) (hjlast ▸ hjt3)
        exact hspecial ⟨hjlast, ht3last⟩
      have hfcpos : 0 < futureCount j := by
        change 0 < (futureCountNat j : ℝ)
        have hjval : j.1 < Nat.pred n := Fin.lt_def.mp hjltlast
        have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
        have hsucc : j.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt hjval) hpredlt
        exact_mod_cast Nat.sub_pos_of_lt hsucc
      calc
        futureCount j * C.hatG j = futureCount j * C.phaseTwo.hatG2 j := by rw [hcopy]
        _ =
            futureCount j *
              (((1 - Γ.muD j) * (C.phaseTwo.afterBudget j + I.program.tau)) /
                futureCount j) := by
              rw [hstep']
        _ = (1 - Γ.muD j) * (C.phaseTwo.afterBudget j + I.program.tau) := by
              field_simp [ne_of_gt hfcpos]
        _ = (1 - Γ.muD j) * (tailBudget C.hatG j + I.program.tau) := by
              rw [← C.tailBudget_eq_phaseTwo_afterBudget_of_lt_t1 ht1j]
  · have hgt3 : Γ.t3Star < j := lt_of_not_ge hjt3
    have hmuD : Γ.muD j = 1 := Advice.muD_eq_one Γ (lt_of_lt_of_le hgt3 (I.le_firstBidTime j))
    have hcopy : C.hatG j = C.phaseTwo.hatG2 j := C.copied_above_t1 ht1j
    rw [hcopy, C.phaseTwo.zero_above_t3 hgt3, hmuD]
    ring

theorem sum_strictSuffix_gValue_row_eq_muA_mul_of_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j : Idx n} (hjt1 : j < C.t1) :
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) =
      (C.memberships).muA j *
        (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j))) := by
  have hrow := C.sum_strictSuffix_gValue_row_eq_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjt1
  have hdenpos : 0 < C.phase1Denom j :=
    C.phase1Denom_pos_of_lt_t1_of_theta_pos hΓ hγlo hγhi hθpos hjt1
  have hdenne : futureCount j - I.program.frac * C.z ≠ 0 := ne_of_gt hdenpos
  calc
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q)
      = (futureCount j - I.program.frac * C.z) * C.hatG j := hrow
    _ =
        (futureCount j - I.program.frac * C.z) *
          (((1 - Γ.muD j) *
              (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)))) /
            (futureCount j - I.program.frac * C.z)) := by
          rw [C.phase1_eq hjt1]
    _ = (1 - Γ.muD j) *
          (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j))) := by
          field_simp [hdenne]
    _ = (C.memberships).muA j *
          (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j))) := by
          rw [C.memberships_muA_eq_of_lt_t1 hjt1]

theorem sum_strictSuffix_gValue_row_eq_muB_mul_tailBudget_add_tau_of_between_t1_t2
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j : Idx n} (ht1j : C.t1 < j) (hjt2 : j ≤ C.t2) :
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) =
      (C.memberships).muB j * (tailBudget C.hatG j + I.program.tau) := by
  rw [C.sum_strictSuffix_gValue_row_eq_of_t1_lt AUX hΓ ht1j,
    C.futureCount_mul_hatG_eq_one_sub_muD_mul_tailBudget_add_tau_of_t1_lt hΓ ht1j,
    C.memberships_muB_eq_of_between_t1_t2 ht1j hjt2]

theorem sum_strictSuffix_gValue_row_eq_muC_mul_tailBudget_add_tau_of_between_t2_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j : Idx n} (ht2j : C.t2 < j) (hjt3 : j ≤ Γ.t3Star) :
    Finset.sum (strictSuffixRange j) (fun q => C.gValue AUX j q) =
      (C.memberships).muC j * (tailBudget C.hatG j + I.program.tau) := by
  have ht1j : C.t1 < j := lt_of_le_of_lt C.t1_le_t2 ht2j
  rw [C.sum_strictSuffix_gValue_row_eq_of_t1_lt AUX hΓ ht1j,
    C.futureCount_mul_hatG_eq_one_sub_muD_mul_tailBudget_add_tau_of_t1_lt hΓ ht1j,
    C.memberships_muC_eq_of_between_t2_t3 ht2j hjt3]

theorem phaseTwo_hatG2_pos_at_t1_of_ne_last
    (C : ProfileData I Γ) (ht1 : C.t1 ≠ lastIdx n) :
    0 < C.phaseTwo.hatG2 C.t1 := by
  have hafter_lt : C.phaseTwo.afterBudget C.t1 < I.program.barTau := by
    exact C.phaseTwo_afterBudget_t1_lt_barTau ht1
  have hbefore :
      C.phaseTwo.beforeBudget C.t1 =
        C.phaseTwo.hatG2 C.t1 + C.phaseTwo.afterBudget C.t1 :=
    C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1
  linarith [C.t1_beforeBudget_ge_barTau, hafter_lt, hbefore]

theorem boundaryDenom_pos_of_ne_last_of_theta_pos
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hθpos : 0 < I.program.theta)
    (ht1 : C.t1 ≠ lastIdx n) :
    0 < C.boundaryDenom := by
  unfold ProfileData.boundaryDenom ProfileData.phaseTwoZ
  have hfrac_lt : I.program.frac < 1 := frac_lt_one_of_theta_pos I.program hγlo hθpos
  have hfcpos : 0 < futureCount C.t1 := futureCount_pos_of_ne_last C.t1 ht1
  have hznonneg : 0 ≤ C.z := C.z_nonneg_of_admissible hΓ
  have hzle : C.z ≤ futureCount C.t1 := C.z_le_futureCount_t1
  have h1μ : 0 ≤ 1 - Γ.muD C.t1 := by
    exact sub_nonneg.mpr (Advice.muD_le_one_of_admissible Γ hΓ C.t1)
  have hαμ : 0 ≤ C.alpha * (1 - Γ.muD C.t1) := mul_nonneg C.alpha_bounds.1 h1μ
  by_cases hz0 : C.z = 0
  · simp [hz0]
    linarith
  · have hzpos : 0 < C.z := lt_of_le_of_ne hznonneg (Ne.symm hz0)
    have hfracz_lt : I.program.frac * C.z < C.z := by
      have htmp := mul_lt_mul_of_pos_right hfrac_lt hzpos
      simpa using htmp
    have hfracz_lt_fc : I.program.frac * C.z < futureCount C.t1 := lt_of_lt_of_le hfracz_lt hzle
    linarith

theorem boundaryHatGB_eq_barTau_sub_tailBudget_of_ne_last
    (C : ProfileData I Γ) (ht1 : C.t1 ≠ lastIdx n) :
    C.boundaryHatGB = I.program.barTau - tailBudget C.hatG C.t1 := by
  rw [ProfileData.boundaryHatGB, C.hatGT1B_eq, if_neg ht1,
    C.tailBudget_eq_phaseTwo_afterBudget_at_t1]

theorem tailBudget_add_tau_add_boundaryHatGB_eq_one_of_ne_last
    (C : ProfileData I Γ) (ht1 : C.t1 ≠ lastIdx n) :
    tailBudget C.hatG C.t1 + I.program.tau + C.boundaryHatGB = 1 := by
  rw [C.boundaryHatGB_eq_barTau_sub_tailBudget_of_ne_last ht1, DualProgram.barTau]
  ring

theorem boundaryHatGA_row_component_eq_of_ne_last
    (C : ProfileData I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hθpos : 0 < I.program.theta)
    (ht1 : C.t1 ≠ lastIdx n) :
    (futureCount C.t1 - I.program.frac * C.z) * C.boundaryHatGA =
      (C.memberships).muA C.t1 *
        (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime C.t1))) -
      (C.memberships).muB C.t1 * C.boundaryHatGA := by
  have hdenpos : 0 < C.boundaryDenom :=
    C.boundaryDenom_pos_of_ne_last_of_theta_pos hΓ hγlo hθpos ht1
  have hdenne : C.boundaryDenom ≠ 0 := ne_of_gt hdenpos
  have hdenne' :
      futureCount C.t1 + C.alpha * (1 - Γ.muD C.t1) - I.program.frac * C.z ≠ 0 := by
    simpa [ProfileData.boundaryDenom, ProfileData.phaseTwoZ] using hdenne
  rw [ProfileData.boundaryHatGA, C.hatGT1A_eq, if_neg ht1, C.memberships_muA_eq_at_t1,
    C.memberships_muB_eq_at_t1]
  field_simp [hdenne']
  ring

theorem futureCount_mul_boundaryHatGB_eq_muB_mul_tailBudget_add_tau_of_ne_last
    (C : ProfileData I Γ) (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) (hθpos : 0 < I.program.theta)
    (ht1 : C.t1 ≠ lastIdx n) :
    futureCount C.t1 * C.boundaryHatGB =
      (C.memberships).muB C.t1 * (tailBudget C.hatG C.t1 + I.program.tau) := by
  have ht1t3 : C.t1 ≤ Γ.t3Star := C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos
  have hstep := C.phaseTwo.step_eq C.t1 ht1t3
  have hspecial : ¬ (C.t1 = lastIdx n ∧ Γ.t3Star = lastIdx n) := by
    intro h
    exact ht1 h.1
  have hstep' :
      C.phaseTwo.hatG2 C.t1 =
        (1 - Γ.muD C.t1) * (C.phaseTwo.afterBudget C.t1 + I.program.tau) / futureCount C.t1 := by
    simpa [PhaseTwoData.afterBudget, hspecial] using hstep
  have hhat2pos : 0 < C.phaseTwo.hatG2 C.t1 := C.phaseTwo_hatG2_pos_at_t1_of_ne_last ht1
  have hhat2ne : C.phaseTwo.hatG2 C.t1 ≠ 0 := ne_of_gt hhat2pos
  have hfcpos : 0 < futureCount C.t1 := futureCount_pos_of_ne_last C.t1 ht1
  have hfcne : futureCount C.t1 ≠ 0 := ne_of_gt hfcpos
  have hhat2mul :
      C.phaseTwo.hatG2 C.t1 * futureCount C.t1 =
        (1 - Γ.muD C.t1) * (C.phaseTwo.afterBudget C.t1 + I.program.tau) := by
    calc
      C.phaseTwo.hatG2 C.t1 * futureCount C.t1
        = (((1 - Γ.muD C.t1) * (C.phaseTwo.afterBudget C.t1 + I.program.tau)) /
            futureCount C.t1) * futureCount C.t1 := by
              rw [hstep']
      _ = (1 - Γ.muD C.t1) * (C.phaseTwo.afterBudget C.t1 + I.program.tau) := by
            field_simp [hfcne]
  calc
    futureCount C.t1 * C.boundaryHatGB
      = futureCount C.t1 * (I.program.barTau - C.phaseTwo.afterBudget C.t1) := by
          rw [ProfileData.boundaryHatGB, C.hatGT1B_eq, if_neg ht1]
    _ = ((I.program.barTau - C.phaseTwo.afterBudget C.t1) / C.phaseTwo.hatG2 C.t1) *
          (C.phaseTwo.hatG2 C.t1 * futureCount C.t1) := by
          field_simp [hhat2ne]
    _ = ((I.program.barTau - C.phaseTwo.afterBudget C.t1) / C.phaseTwo.hatG2 C.t1) *
          ((1 - Γ.muD C.t1) * (C.phaseTwo.afterBudget C.t1 + I.program.tau)) := by
          rw [hhat2mul]
    _ = (((I.program.barTau - C.phaseTwo.afterBudget C.t1) / C.phaseTwo.hatG2 C.t1) *
          (1 - Γ.muD C.t1)) *
          (C.phaseTwo.afterBudget C.t1 + I.program.tau) := by
          ring
    _ = (C.memberships).muB C.t1 * (tailBudget C.hatG C.t1 + I.program.tau) := by
          rw [C.memberships_muB_eq_at_t1, C.alpha_eq, if_neg ht1,
            C.tailBudget_eq_phaseTwo_afterBudget_at_t1]

theorem sum_strictSuffix_gValue_row_eq_weighted_AB_at_t1_of_ne_last
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta) (ht1 : C.t1 ≠ lastIdx n) :
    Finset.sum (strictSuffixRange C.t1) (fun q => C.gValue AUX C.t1 q) =
      (C.memberships).muA C.t1 *
        (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime C.t1))) +
      (C.memberships).muB C.t1 *
        (tailBudget C.hatG C.t1 + I.program.tau - C.boundaryHatGA) := by
  rw [C.sum_strictSuffix_gValue_row_eq_at_t1 AUX hΓ hγlo hγhi hθpos,
    C.boundaryHatGA_row_component_eq_of_ne_last hΓ hγlo hθpos ht1,
    C.futureCount_mul_boundaryHatGB_eq_muB_mul_tailBudget_add_tau_of_ne_last hγlo hγhi hθpos ht1]
  ring

theorem sum_interval_gB_tB_sub_sB_eq_after_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (ht1j : C.t1 < j) (hif : I.firstBidTime j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
      1 - (tailBudget C.hatG j + I.program.tau) -
        (if I.firstBidTime j < i then I.program.epsilon else 0) := by
  rw [show (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
      (fun p => (C.gB AUX p j + C.tB AUX p j) - C.sB AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gB_eq AUX hji,
    C.sum_interval_tB_eq AUX, C.sum_interval_sB_eq AUX hji, if_pos hif]
  have ht : 0 ≤ 1 - beforeBudget C.hatG j - I.program.tau := by
    have hbar : beforeBudget C.hatG j < I.program.barTau := C.beforeBudget_lt_barTau_of_lt_t1 ht1j
    have hbar' : beforeBudget C.hatG j < 1 - I.program.tau := by
      simpa [DualProgram.barTau] using hbar
    linarith
  rw [posPart_of_nonneg ht]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  linarith

theorem sum_interval_gB_tB_sub_sB_eq_before_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (_ht1j : C.t1 < j) (hif : i < I.firstBidTime j) :
    Finset.sum (intervalRange j i) (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
      C.hatG j := by
  rw [show (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
      (fun p => (C.gB AUX p j + C.tB AUX p j) - C.sB AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gB_eq AUX hji,
    C.sum_interval_tB_eq AUX, C.sum_interval_sB_eq AUX hji, if_neg (not_le.mpr hif),
    if_neg (not_lt.mpr (le_of_lt hif))]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  linarith

theorem sum_interval_gB_tB_sub_sB_eq_after_at_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (hji : C.t1 ≤ i) (hif : I.firstBidTime C.t1 ≤ i) :
    Finset.sum (intervalRange C.t1 i)
        (fun p => C.gB AUX p C.t1 + C.tB AUX p C.t1 - C.sB AUX p C.t1) =
      C.hatG C.t1 - (if I.firstBidTime C.t1 < i then I.program.epsilon else 0) := by
  rw [show (fun p => C.gB AUX p C.t1 + C.tB AUX p C.t1 - C.sB AUX p C.t1) =
      (fun p => (C.gB AUX p C.t1 + C.tB AUX p C.t1) - C.sB AUX p C.t1) by
        funext p
        ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gB_eq AUX hji,
    C.sum_interval_tB_eq AUX, C.sum_interval_sB_eq AUX hji, if_pos hif]
  have htB0 : posPart (1 - beforeBudget C.hatG C.t1 - I.program.tau) = 0 := by
    have hnonpos : 1 - beforeBudget C.hatG C.t1 - I.program.tau ≤ 0 := by
      have hbar : I.program.barTau ≤ beforeBudget C.hatG C.t1 :=
        C.beforeBudget_t1_ge_barTau hΓ hγlo hγhi
      have hbar' : 1 - I.program.tau ≤ beforeBudget C.hatG C.t1 := by
        simpa [DualProgram.barTau] using hbar
      linarith
    simp [posPart_of_nonpos hnonpos]
  rw [htB0]
  have hbefore : beforeBudget C.hatG C.t1 = C.hatG C.t1 + tailBudget C.hatG C.t1 :=
    beforeBudget_eq_self_add_tail C.hatG C.t1
  linarith

theorem sum_interval_gB_tB_sub_sB_eq_before_at_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {i : Idx n}
    (hji : C.t1 ≤ i) (hif : i < I.firstBidTime C.t1) :
    Finset.sum (intervalRange C.t1 i)
        (fun p => C.gB AUX p C.t1 + C.tB AUX p C.t1 - C.sB AUX p C.t1) =
      C.hatG C.t1 := by
  rw [show (fun p => C.gB AUX p C.t1 + C.tB AUX p C.t1 - C.sB AUX p C.t1) =
      (fun p => (C.gB AUX p C.t1 + C.tB AUX p C.t1) - C.sB AUX p C.t1) by
        funext p
        ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gB_eq AUX hji,
    C.sum_interval_tB_eq AUX, C.sum_interval_sB_eq AUX hji, if_neg (not_le.mpr hif),
    if_neg (not_lt.mpr (le_of_lt hif))]
  have hbefore : beforeBudget C.hatG C.t1 = C.hatG C.t1 + tailBudget C.hatG C.t1 :=
    beforeBudget_eq_self_add_tail C.hatG C.t1
  linarith

theorem sum_interval_gC_tC_sub_sC_eq_after_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (_ht1j : C.t1 < j) (hif : I.firstBidTime j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
      1 - (tailBudget C.hatG j + I.program.tau) -
        (if I.firstBidTime j < i then I.program.epsilon else 0) := by
  rw [show (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
      (fun p => (C.gC AUX p j + C.tC AUX p j) - C.sC AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gC_eq AUX hji,
    C.sum_interval_tC_eq AUX, C.sum_interval_sC_eq AUX hji, if_pos hif]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  linarith

theorem sum_interval_gC_tC_sub_sC_eq_before_of_t1_lt
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (_ht1j : C.t1 < j) (hif : i < I.firstBidTime j) :
    Finset.sum (intervalRange j i) (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
      C.hatG j := by
  rw [show (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
      (fun p => (C.gC AUX p j + C.tC AUX p j) - C.sC AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, C.sum_interval_gC_eq AUX hji,
    C.sum_interval_tC_eq AUX, C.sum_interval_sC_eq AUX hji, if_neg (not_le.mpr hif),
    if_neg (not_lt.mpr (le_of_lt hif))]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  linarith

theorem sum_interval_gD_tD_sub_sD_eq_after_of_col_le_t1_of_chi_zero
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (hj : j ≤ C.t1) (hchi : C.chi j = 0) (hif : I.firstBidTime j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
      1 - tailBudget C.hatG i := by
  rw [show (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
      (fun p => (C.gD AUX p j + C.tD AUX p j) - C.sD AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    C.sum_interval_gD_eq_of_col_le_t1_of_chi_zero AUX hji hj hchi,
    C.sum_interval_tD_eq AUX, C.sum_interval_sD_eq AUX, if_pos hif]
  ring

theorem sum_interval_gD_tD_sub_sD_eq_before_of_col_le_t1_of_chi_zero
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (hj : j ≤ C.t1) (hchi : C.chi j = 0) (hif : i < I.firstBidTime j) :
    Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
      beforeBudget C.hatG j - tailBudget C.hatG i := by
  rw [show (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
      (fun p => (C.gD AUX p j + C.tD AUX p j) - C.sD AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    C.sum_interval_gD_eq_of_col_le_t1_of_chi_zero AUX hji hj hchi,
    C.sum_interval_tD_eq AUX, C.sum_interval_sD_eq AUX, if_neg (not_le.mpr hif)]
  ring

theorem sum_interval_gD_tD_sub_sD_eq_after_of_t1_lt_col
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (ht1j : C.t1 < j) (hif : I.firstBidTime j ≤ i) :
    Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
      1 - tailBudget C.hatG i := by
  rw [show (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
      (fun p => (C.gD AUX p j + C.tD AUX p j) - C.sD AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    C.sum_interval_gD_eq_of_t1_lt_col AUX hji ht1j,
    C.sum_interval_tD_eq AUX, C.sum_interval_sD_eq AUX, if_pos hif]
  ring

theorem sum_interval_gD_tD_sub_sD_eq_before_of_t1_lt_col
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) {j i : Idx n}
    (hji : j ≤ i) (ht1j : C.t1 < j) (hif : i < I.firstBidTime j) :
    Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
      beforeBudget C.hatG j - tailBudget C.hatG i := by
  rw [show (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
      (fun p => (C.gD AUX p j + C.tD AUX p j) - C.sD AUX p j) by
        funext p; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    C.sum_interval_gD_eq_of_t1_lt_col AUX hji ht1j,
    C.sum_interval_tD_eq AUX, C.sum_interval_sD_eq AUX, if_neg (not_le.mpr hif)]
  ring

theorem creditValue_after_eq_weighted_AD_of_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hjt1 : j < C.t1) (hji : j ≤ i) (hif : I.firstBidTime j ≤ i) :
    C.creditValue AUX i j =
      (C.memberships).muA j *
        (1 - Finset.sum (intervalRange j i) (fun p => AUX.delta p j)) +
      (C.memberships).muD j * (1 - tailBudget C.hatG i) := by
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gValue_row_eq_muA_mul_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjt1,
    C.sum_interval_gts_value_eq_membership_combo AUX]
  have hB0 : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_lt_t1 hjt1
  have hC0 : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_lt_t1 hjt1
  have hA :
      (C.memberships).muA j *
          Finset.sum (intervalRange j i) (fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j) =
        (C.memberships).muA j *
          (posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) -
            Finset.sum (intervalRange j i) (fun p => AUX.delta p j)) := by
    by_cases hμA0 : (C.memberships).muA j = 0
    · simp [hμA0]
    · have hμA_nonneg : 0 ≤ (C.memberships).muA j :=
        (C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds).1 j
      have hμApos : 0 < (C.memberships).muA j := lt_of_le_of_ne hμA_nonneg (Ne.symm hμA0)
      rw [C.sum_interval_gA_tA_sub_sA_eq_after_firstBid AUX hμApos hji hif]
  have hchi : C.chi j = 0 :=
    C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos (le_trans (le_of_lt hjt1) C.t1_le_t2)
  have hD :
      (C.memberships).muD j *
          Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
        (C.memberships).muD j * (1 - tailBudget C.hatG i) := by
    rw [C.sum_interval_gD_tD_sub_sD_eq_after_of_col_le_t1_of_chi_zero
      AUX hji (le_of_lt hjt1) hchi hif]
  rw [hB0, hC0, hA, hD]
  ring

theorem creditValue_before_eq_weighted_AD_of_lt_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {j i : Idx n} (hjt1 : j < C.t1) (hji : j ≤ i) (hif : i < I.firstBidTime j) :
    C.creditValue AUX i j =
      (C.memberships).muA j *
        (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime j)) +
          Finset.sum (intervalRange j i) (fun p => AUX.sigma p j)) +
      (C.memberships).muD j * (beforeBudget C.hatG j - tailBudget C.hatG i) := by
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gValue_row_eq_muA_mul_of_lt_t1 AUX hΓ hγlo hγhi hθpos hjt1,
    C.sum_interval_gts_value_eq_membership_combo AUX]
  have hB0 : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_lt_t1 hjt1
  have hC0 : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_lt_t1 hjt1
  have hA :
      (C.memberships).muA j *
          Finset.sum (intervalRange j i) (fun p => C.gA AUX p j + C.tA AUX p j - C.sA AUX p j) =
        (C.memberships).muA j *
          Finset.sum (intervalRange j i) (fun p => AUX.sigma p j) := by
    by_cases hμA0 : (C.memberships).muA j = 0
    · simp [hμA0]
    · have hμA_nonneg : 0 ≤ (C.memberships).muA j :=
        (C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds).1 j
      have hμApos : 0 < (C.memberships).muA j := lt_of_le_of_ne hμA_nonneg (Ne.symm hμA0)
      rw [C.sum_interval_gA_tA_sub_sA_eq_before_firstBid AUX hμApos hji hif]
  have hchi : C.chi j = 0 :=
    C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos (le_trans (le_of_lt hjt1) C.t1_le_t2)
  have hD :
      (C.memberships).muD j *
          Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
        (C.memberships).muD j * (beforeBudget C.hatG j - tailBudget C.hatG i) := by
    rw [C.sum_interval_gD_tD_sub_sD_eq_before_of_col_le_t1_of_chi_zero
      AUX hji (le_of_lt hjt1) hchi hif]
  rw [hB0, hC0, hA, hD]
  ring

theorem creditValue_after_eq_weighted_ABD_at_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (hji : C.t1 ≤ i) (hif : I.firstBidTime C.t1 ≤ i) :
    C.creditValue AUX i C.t1 =
      (C.memberships).muA C.t1 *
        (1 - Finset.sum (intervalRange C.t1 i) (fun p => AUX.delta p C.t1)) +
      (C.memberships).muB C.t1 * (1 - (if I.firstBidTime C.t1 < i then I.program.epsilon else 0)) +
      (C.memberships).muD C.t1 * 1 := by
  by_cases ht1 : C.t1 = lastIdx n
  · have hi : i = C.t1 := by
      apply le_antisymm
      · exact ht1.symm ▸ le_lastIdx i
      · exact hji
    have hfb : I.firstBidTime C.t1 = C.t1 := by
      apply le_antisymm
      · exact ht1.symm ▸ le_lastIdx (I.firstBidTime C.t1)
      · exact I.le_firstBidTime C.t1
    have ht3last : Γ.t3Star = lastIdx n := by
      apply le_antisymm
      · exact le_lastIdx _
      · simpa [ht1] using C.t1_le_t3Star_of_theta_pos hγlo hγhi hθpos
    have hfront : I.firstBidTime C.t1 = Γ.t3Star := by rw [hfb, ht1, ht3last]
    have hall : Γ.AllOnesAtLast := hΓ.2.2.2
    have hμstar : Γ.muStar C.t1 = 1 := hall ht3last hfront
    have hμD : Γ.muD C.t1 = 1 := (Advice.muD_eq_muStar Γ hfront).trans hμstar
    have hcredit : C.creditValue AUX i C.t1 = 1 := by
      simpa [hi] using C.creditValue_D_after_eq_of_integralD AUX hΓ hγlo hγhi hθpos hμD hji hif
    have hA0 : (C.memberships).muA C.t1 = 0 := by
      rw [C.memberships_muA_eq_at_t1, C.alpha_eq, if_pos ht1, hμD]
      ring
    have hB0 : (C.memberships).muB C.t1 = 0 := by
      rw [C.memberships_muB_eq_at_t1, C.alpha_eq, if_pos ht1, hμD]
      ring
    rw [hcredit, hA0, hB0, C.memberships_muD, hμD]
    ring
  · unfold ProfileData.creditValue ProfileData.integralClientCredit
    rw [C.sum_strictSuffix_gValue_row_eq_weighted_AB_at_t1_of_ne_last
      AUX hΓ hγlo hγhi hθpos ht1, C.sum_interval_gts_value_eq_membership_combo AUX]
    have hC0 : (C.memberships).muC C.t1 = 0 := C.memberships_muC_eq_zero_at_t1
    have hA :
        (C.memberships).muA C.t1 *
            Finset.sum (intervalRange C.t1 i)
              (fun p => C.gA AUX p C.t1 + C.tA AUX p C.t1 - C.sA AUX p C.t1) =
          (C.memberships).muA C.t1 *
            (posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime C.t1)) -
              Finset.sum (intervalRange C.t1 i) (fun p => AUX.delta p C.t1)) := by
      by_cases hμA0 : (C.memberships).muA C.t1 = 0
      · simp [hμA0]
      · have hμA_nonneg : 0 ≤ (C.memberships).muA C.t1 :=
          (C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds).1 C.t1
        have hμApos : 0 < (C.memberships).muA C.t1 := lt_of_le_of_ne hμA_nonneg (Ne.symm hμA0)
        rw [C.sum_interval_gA_tA_sub_sA_eq_after_firstBid AUX hμApos hji hif]
    have hB :
        (C.memberships).muB C.t1 *
            Finset.sum (intervalRange C.t1 i)
              (fun p => C.gB AUX p C.t1 + C.tB AUX p C.t1 - C.sB AUX p C.t1) =
          (C.memberships).muB C.t1 *
            (C.hatG C.t1 - (if I.firstBidTime C.t1 < i then I.program.epsilon else 0)) := by
      rw [C.sum_interval_gB_tB_sub_sB_eq_after_at_t1 AUX hΓ hγlo hγhi hji hif]
    have hchi : C.chi C.t1 = 0 := C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos C.t1_le_t2
    have hD :
        (C.memberships).muD C.t1 *
            Finset.sum (intervalRange C.t1 i)
              (fun p => C.gD AUX p C.t1 + C.tD AUX p C.t1 - C.sD AUX p C.t1) =
          (C.memberships).muD C.t1 * (1 - tailBudget C.hatG i) := by
      rw [C.sum_interval_gD_tD_sub_sD_eq_after_of_col_le_t1_of_chi_zero
        AUX hji le_rfl hchi hif]
    have hD1 :
        (C.memberships).muD C.t1 * (1 - tailBudget C.hatG i) =
          (C.memberships).muD C.t1 * 1 := by
      by_cases hμD0 : Γ.muD C.t1 = 0
      · simp [hμD0]
      · have hμD_nonneg : 0 ≤ Γ.muD C.t1 := Advice.muD_nonneg_of_admissible Γ hΓ C.t1
        have hμDpos : 0 < Γ.muD C.t1 := lt_of_le_of_ne hμD_nonneg (Ne.symm hμD0)
        have ht3le : Γ.t3Star ≤ i := le_trans (t3_le_firstBidTime_of_muD_pos Γ hμDpos) hif
        have htail0 : tailBudget C.hatG i = 0 := by
          exact C.tailBudget_eq_zero_of_t3_le hγlo hγhi hθpos ht3le
        rw [C.memberships_muD, htail0]
        ring
    have hhat : C.hatG C.t1 = C.boundaryHatGA + C.boundaryHatGB := C.boundary_eq
    have htail : tailBudget C.hatG C.t1 + I.program.tau + C.boundaryHatGB = 1 :=
      C.tailBudget_add_tau_add_boundaryHatGB_eq_one_of_ne_last ht1
    have hBcomb :
        (C.memberships).muB C.t1 * (tailBudget C.hatG C.t1 + I.program.tau - C.boundaryHatGA) +
          (C.memberships).muB C.t1 *
            (C.boundaryHatGA + C.boundaryHatGB -
              if I.firstBidTime C.t1 < i then I.program.epsilon else 0) =
        (C.memberships).muB C.t1 *
          (1 - if I.firstBidTime C.t1 < i then I.program.epsilon else 0) := by
      have hinner :
          tailBudget C.hatG C.t1 + I.program.tau - C.boundaryHatGA +
              (C.boundaryHatGA + C.boundaryHatGB -
                if I.firstBidTime C.t1 < i then I.program.epsilon else 0) =
            1 - if I.firstBidTime C.t1 < i then I.program.epsilon else 0 := by
        linarith
      calc
        (C.memberships).muB C.t1 * (tailBudget C.hatG C.t1 + I.program.tau - C.boundaryHatGA) +
            (C.memberships).muB C.t1 *
              (C.boundaryHatGA + C.boundaryHatGB -
                if I.firstBidTime C.t1 < i then I.program.epsilon else 0)
          = (C.memberships).muB C.t1 *
              (tailBudget C.hatG C.t1 + I.program.tau - C.boundaryHatGA +
                (C.boundaryHatGA + C.boundaryHatGB -
                  if I.firstBidTime C.t1 < i then I.program.epsilon else 0)) := by
              ring
        _ =
            (C.memberships).muB C.t1 *
              (1 - if I.firstBidTime C.t1 < i then I.program.epsilon else 0) := by
              rw [hinner]
    rw [hC0, hA, hB, hD, hD1, hhat]
    nlinarith [hBcomb]

theorem creditValue_before_eq_weighted_ABD_at_t1
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (hθpos : 0 < I.program.theta)
    {i : Idx n} (hji : C.t1 ≤ i) (hif : i < I.firstBidTime C.t1) :
    C.creditValue AUX i C.t1 =
      (C.memberships).muA C.t1 *
        (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime C.t1)) +
          Finset.sum (intervalRange C.t1 i) (fun p => AUX.sigma p C.t1)) +
      (C.memberships).muB C.t1 * 1 +
      (C.memberships).muD C.t1 * (beforeBudget C.hatG C.t1 - tailBudget C.hatG i) := by
  have ht1 : C.t1 ≠ lastIdx n := by
    intro hlast
    have hi : i = C.t1 := by
      apply le_antisymm
      · exact hlast.symm ▸ le_lastIdx i
      · exact hji
    have hfb : I.firstBidTime C.t1 = C.t1 := by
      apply le_antisymm
      · exact hlast.symm ▸ le_lastIdx (I.firstBidTime C.t1)
      · exact I.le_firstBidTime C.t1
    have hge : I.firstBidTime C.t1 ≤ i := by simp [hi, hfb]
    exact (not_lt_of_ge hge) hif
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gValue_row_eq_weighted_AB_at_t1_of_ne_last AUX hΓ hγlo hγhi hθpos ht1,
    C.sum_interval_gts_value_eq_membership_combo AUX]
  have hC0 : (C.memberships).muC C.t1 = 0 := C.memberships_muC_eq_zero_at_t1
  have hA :
      (C.memberships).muA C.t1 *
          Finset.sum (intervalRange C.t1 i)
            (fun p => C.gA AUX p C.t1 + C.tA AUX p C.t1 - C.sA AUX p C.t1) =
        (C.memberships).muA C.t1 *
          Finset.sum (intervalRange C.t1 i) (fun p => AUX.sigma p C.t1) := by
    by_cases hμA0 : (C.memberships).muA C.t1 = 0
    · simp [hμA0]
    · have hμA_nonneg : 0 ≤ (C.memberships).muA C.t1 :=
        (C.memberships_nonnegative_of_admissible hΓ C.alpha_bounds).1 C.t1
      have hμApos : 0 < (C.memberships).muA C.t1 := lt_of_le_of_ne hμA_nonneg (Ne.symm hμA0)
      rw [C.sum_interval_gA_tA_sub_sA_eq_before_firstBid AUX hμApos hji hif]
  have hB :
      (C.memberships).muB C.t1 *
          Finset.sum (intervalRange C.t1 i)
            (fun p => C.gB AUX p C.t1 + C.tB AUX p C.t1 - C.sB AUX p C.t1) =
        (C.memberships).muB C.t1 * C.hatG C.t1 := by
    rw [C.sum_interval_gB_tB_sub_sB_eq_before_at_t1 AUX hji hif]
  have hchi : C.chi C.t1 = 0 := C.chi_eq_zero_of_le_t2 hΓ hγlo hγhi hθpos C.t1_le_t2
  have hD :
      (C.memberships).muD C.t1 *
          Finset.sum (intervalRange C.t1 i)
            (fun p => C.gD AUX p C.t1 + C.tD AUX p C.t1 - C.sD AUX p C.t1) =
        (C.memberships).muD C.t1 * (beforeBudget C.hatG C.t1 - tailBudget C.hatG i) := by
    rw [C.sum_interval_gD_tD_sub_sD_eq_before_of_col_le_t1_of_chi_zero
      AUX hji le_rfl hchi hif]
  have hhat : C.hatG C.t1 = C.boundaryHatGA + C.boundaryHatGB := C.boundary_eq
  have htail : tailBudget C.hatG C.t1 + I.program.tau + C.boundaryHatGB = 1 :=
    C.tailBudget_add_tau_add_boundaryHatGB_eq_one_of_ne_last ht1
  have hBcomb :
      (C.memberships).muB C.t1 * (tailBudget C.hatG C.t1 + I.program.tau - C.boundaryHatGA) +
        (C.memberships).muB C.t1 * (C.boundaryHatGA + C.boundaryHatGB) =
        (C.memberships).muB C.t1 * 1 := by
    have hinner :
        tailBudget C.hatG C.t1 + I.program.tau - C.boundaryHatGA +
            (C.boundaryHatGA + C.boundaryHatGB) = 1 := by
      linarith
    calc
      (C.memberships).muB C.t1 * (tailBudget C.hatG C.t1 + I.program.tau - C.boundaryHatGA) +
          (C.memberships).muB C.t1 * (C.boundaryHatGA + C.boundaryHatGB)
        = (C.memberships).muB C.t1 *
            (tailBudget C.hatG C.t1 + I.program.tau - C.boundaryHatGA +
              (C.boundaryHatGA + C.boundaryHatGB)) := by
            ring
      _ = (C.memberships).muB C.t1 * 1 := by rw [hinner]
  rw [hC0, hA, hB, hD, hhat]
  nlinarith [hBcomb]

theorem creditValue_after_eq_weighted_BD_of_between_t1_t2
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j i : Idx n} (ht1j : C.t1 < j) (hjt2 : j ≤ C.t2)
    (hji : j ≤ i) (hif : I.firstBidTime j ≤ i) :
    C.creditValue AUX i j =
      (C.memberships).muB j * (1 - (if I.firstBidTime j < i then I.program.epsilon else 0)) +
      (C.memberships).muD j * (1 - tailBudget C.hatG i) := by
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gValue_row_eq_muB_mul_tailBudget_add_tau_of_between_t1_t2
    AUX hΓ ht1j hjt2, C.sum_interval_gts_value_eq_membership_combo AUX]
  have hA0 : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_between_t1_t2 ht1j hjt2
  have hC0 : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_between_t1_t2 ht1j hjt2
  have hB :
      (C.memberships).muB j *
          Finset.sum (intervalRange j i) (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
        (C.memberships).muB j *
          (1 - (tailBudget C.hatG j + I.program.tau) -
            (if I.firstBidTime j < i then I.program.epsilon else 0)) := by
    rw [C.sum_interval_gB_tB_sub_sB_eq_after_of_t1_lt AUX hji ht1j hif]
  have hD :
      (C.memberships).muD j *
          Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
        (C.memberships).muD j * (1 - tailBudget C.hatG i) := by
    rw [C.sum_interval_gD_tD_sub_sD_eq_after_of_t1_lt_col AUX hji ht1j hif]
  rw [hA0, hC0, hB, hD]
  ring

theorem creditValue_before_eq_weighted_BD_of_between_t1_t2
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j i : Idx n} (ht1j : C.t1 < j) (hjt2 : j ≤ C.t2)
    (hji : j ≤ i) (hif : i < I.firstBidTime j) :
    C.creditValue AUX i j =
      (C.memberships).muB j * (I.program.tau + beforeBudget C.hatG j) +
      (C.memberships).muD j * (beforeBudget C.hatG j - tailBudget C.hatG i) := by
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gValue_row_eq_muB_mul_tailBudget_add_tau_of_between_t1_t2
    AUX hΓ ht1j hjt2, C.sum_interval_gts_value_eq_membership_combo AUX]
  have hA0 : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_between_t1_t2 ht1j hjt2
  have hC0 : (C.memberships).muC j = 0 := C.memberships_muC_eq_zero_of_between_t1_t2 ht1j hjt2
  have hB :
      (C.memberships).muB j *
          Finset.sum (intervalRange j i) (fun p => C.gB AUX p j + C.tB AUX p j - C.sB AUX p j) =
        (C.memberships).muB j * C.hatG j := by
    rw [C.sum_interval_gB_tB_sub_sB_eq_before_of_t1_lt AUX hji ht1j hif]
  have hD :
      (C.memberships).muD j *
          Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
        (C.memberships).muD j * (beforeBudget C.hatG j - tailBudget C.hatG i) := by
    rw [C.sum_interval_gD_tD_sub_sD_eq_before_of_t1_lt_col AUX hji ht1j hif]
  rw [hA0, hC0, hB, hD]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  rw [hbefore]
  ring

theorem creditValue_after_eq_weighted_CD_of_between_t2_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j i : Idx n} (ht2j : C.t2 < j) (hjt3 : j ≤ Γ.t3Star) (hji : j ≤ i)
    (hif : I.firstBidTime j ≤ i) :
    C.creditValue AUX i j =
      (C.memberships).muC j * (1 - (if I.firstBidTime j < i then I.program.epsilon else 0)) +
      (C.memberships).muD j * (1 - tailBudget C.hatG i) := by
  have ht1j : C.t1 < j := lt_of_le_of_lt C.t1_le_t2 ht2j
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gValue_row_eq_muC_mul_tailBudget_add_tau_of_between_t2_t3
    AUX hΓ ht2j hjt3, C.sum_interval_gts_value_eq_membership_combo AUX]
  have hA0 : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_between_t2_t3 ht2j hjt3
  have hB0 : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_between_t2_t3 ht2j hjt3
  have hC :
      (C.memberships).muC j *
          Finset.sum (intervalRange j i) (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
        (C.memberships).muC j *
          (1 - (tailBudget C.hatG j + I.program.tau) -
            (if I.firstBidTime j < i then I.program.epsilon else 0)) := by
    rw [C.sum_interval_gC_tC_sub_sC_eq_after_of_t1_lt AUX hji ht1j hif]
  have hD :
      (C.memberships).muD j *
          Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
        (C.memberships).muD j * (1 - tailBudget C.hatG i) := by
    rw [C.sum_interval_gD_tD_sub_sD_eq_after_of_t1_lt_col AUX hji ht1j hif]
  rw [hA0, hB0, hC, hD]
  ring

theorem creditValue_before_eq_weighted_CD_of_between_t2_t3
    (C : ProfileData I Γ) (AUX : AuxiliaryCorrections C) (hΓ : Γ.Admissible)
    {j i : Idx n} (ht2j : C.t2 < j) (hjt3 : j ≤ Γ.t3Star) (hji : j ≤ i)
    (hif : i < I.firstBidTime j) :
    C.creditValue AUX i j =
      (C.memberships).muC j * (I.program.tau + beforeBudget C.hatG j) +
      (C.memberships).muD j * (beforeBudget C.hatG j - tailBudget C.hatG i) := by
  have ht1j : C.t1 < j := lt_of_le_of_lt C.t1_le_t2 ht2j
  unfold ProfileData.creditValue ProfileData.integralClientCredit
  rw [C.sum_strictSuffix_gValue_row_eq_muC_mul_tailBudget_add_tau_of_between_t2_t3
    AUX hΓ ht2j hjt3, C.sum_interval_gts_value_eq_membership_combo AUX]
  have hA0 : (C.memberships).muA j = 0 := C.memberships_muA_eq_zero_of_between_t2_t3 ht2j hjt3
  have hB0 : (C.memberships).muB j = 0 := C.memberships_muB_eq_zero_of_between_t2_t3 ht2j hjt3
  have hC :
      (C.memberships).muC j *
          Finset.sum (intervalRange j i) (fun p => C.gC AUX p j + C.tC AUX p j - C.sC AUX p j) =
        (C.memberships).muC j * C.hatG j := by
    rw [C.sum_interval_gC_tC_sub_sC_eq_before_of_t1_lt AUX hji ht1j hif]
  have hD :
      (C.memberships).muD j *
          Finset.sum (intervalRange j i) (fun p => C.gD AUX p j + C.tD AUX p j - C.sD AUX p j) =
        (C.memberships).muD j * (beforeBudget C.hatG j - tailBudget C.hatG i) := by
    rw [C.sum_interval_gD_tD_sub_sD_eq_before_of_t1_lt_col AUX hji ht1j hif]
  rw [hA0, hB0, hC, hD]
  have hbefore : beforeBudget C.hatG j = C.hatG j + tailBudget C.hatG j :=
    beforeBudget_eq_self_add_tail C.hatG j
  rw [hbefore]
  ring

end ProfileData

end

end KMedian195


