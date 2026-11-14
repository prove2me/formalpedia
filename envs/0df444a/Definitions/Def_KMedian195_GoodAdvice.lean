-- Prove2me | Definitions.Def_KMedian195_GoodAdvice
-- name    : KMedian195_GoodAdvice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:50.030634+00:00
-- url     : https://prove2.me/theorems/3c5d9855-615c-4fce-bd3d-1f1f4dc8907f
-- title:
--   KMedian195.GoodAdvice
-- statement:
--   This is module `KMedian195.GoodAdvice` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   **Contents.** The module is published as a whole: 428 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_GoodAdvice`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/GoodAdvice.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/GoodAdvice.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`), and:
* `if_pos`, `if_neg`, `dif_pos`, `dif_neg` (deprecated) are `if_pos`, `if_neg`,
  `dif_pos`, `dif_neg`.
* In 62 places, `simpa ... using e` is `simpa ... using! e`: our Lean's `simpa` matches the
  simplified `e` against the goal only up to reducible unfolding; `using!` matches as before.
* The case of `Nat.strong_induction_on` is named `ind` (was `h`).
* `continuous_finset_prod`, `continuous_finset_sum`, `continuousOn_finset_sum` are
  `continuous_finsetProd`, `continuous_finsetSum`, `continuousOn_finsetSum`, and
  `Set.mem_setOf_eq` (deprecated) is `Set.mem_ofPred_eq`.
* In `sectionPhaseTwoData_toNextSectionLeft_eq`, an `erw [PhaseTwoData.toNextSectionLeft_hatG2]`
  before the `simp`, and in `canonicalSectionOutput_toNextSectionLeft_eq`, `erw` instead of `rw`
  for `RawProcedureOutput.toNextSectionLeft_phaseTwo`: these lemmas are stated for
  `Advice.sectionRight`, which our Lean no longer unfolds when matching them.
* In the statement of `ProcedureRun.eq_sectionProcedureRunOfPhaseTwoThresholds`, the implicit
  arguments are given, `(t1 := C.t1) (t2 := C.t2)`: our Lean no longer infers them from the
  tactic blocks that follow.
-/
module

public import Definitions.Def_KMedian195_ProfileConstruction
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.GoodAdvice` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
@[expose] public section

namespace KMedian195

variable {n : ℕ}

/-- The first paper index `1`, represented in zero-based `Fin n` notation. -/
def firstIdx (n : ℕ) [NeZero n] : Idx n :=
  ⟨0, Nat.pos_of_neZero n⟩

@[simp] theorem firstIdx_le [NeZero n] (i : Idx n) : firstIdx n ≤ i := by
  exact Fin.le_iff_val_le_val.mpr (Nat.zero_le i.1)

/-- The next zero-based index, used to step from section `ℓ` to section `ℓ+1`. -/
def succIdx [NeZero n] (i : Idx n) (h : i < lastIdx n) : Idx n :=
  ⟨i.1.succ, by
    have hi : i.1 < Nat.pred n := h
    have hisucc : i.1.succ ≤ Nat.pred n := Nat.succ_le_of_lt hi
    exact lt_of_le_of_lt hisucc (Nat.pred_lt (show n ≠ 0 from NeZero.ne n))⟩

@[simp] theorem succIdx_val [NeZero n] (i : Idx n) (h : i < lastIdx n) :
    (succIdx i h).1 = i.1.succ := rfl

@[simp] theorem lt_succIdx [NeZero n] (i : Idx n) (h : i < lastIdx n) :
    i < succIdx i h := by
  exact Fin.lt_def.mpr (Nat.lt_succ_self i.1)

@[simp] theorem succIdx_le_iff [NeZero n] {i j : Idx n} (h : j < lastIdx n) :
    succIdx j h ≤ i ↔ j < i := by
  constructor
  · intro hle
    exact lt_of_lt_of_le (lt_succIdx j h) hle
  · intro hlt
    exact Fin.le_def.mpr (Nat.succ_le_of_lt hlt)

@[simp] theorem lt_succIdx_iff [NeZero n] {i j : Idx n} (h : j < lastIdx n) :
    i < succIdx j h ↔ i ≤ j := by
  constructor
  · intro hlt
    exact Fin.le_def.mpr (Nat.lt_succ_iff.mp hlt)
  · intro hle
    exact lt_of_le_of_lt hle (lt_succIdx j h)

@[simp] theorem succIdx_pred [NeZero n] {k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    succIdx ⟨k - 1, by
      have hsublt : k - 1 < k := by omega
      exact lt_trans hsublt hkn⟩
      (by
        change k - 1 < Nat.pred n
        have hsublt : k - 1 < k := by omega
        exact lt_of_lt_of_le hsublt (Nat.le_pred_of_lt hkn)) = ⟨k, hkn⟩ := by
  apply Fin.ext
  change k - 1 + 1 = k
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hk0)

@[simp] theorem beforeBudget_firstIdx_eq_totalBudget [NeZero n] (hatG : Idx n → ℝ) :
    beforeBudget hatG (firstIdx n) = totalBudget hatG := by
  unfold beforeBudget totalBudget
  rw [show suffixRange (firstIdx n) = (Finset.univ : Finset (Idx n)) by
    ext i
    simp [suffixRange, firstIdx]]

theorem tailBudget_eq_beforeBudget_succ [NeZero n] (hatG : Idx n → ℝ) {i : Idx n}
    (hi : i < lastIdx n) :
    tailBudget hatG i = beforeBudget hatG (succIdx i hi) := by
  unfold tailBudget beforeBudget
  have hrange : strictSuffixRange i = suffixRange (succIdx i hi) := by
    ext j
    simp [mem_strictSuffixRange, mem_suffixRange, succIdx_le_iff hi]
  rw [hrange]

/-- The positive-part map is continuous on `ℝ`. -/
theorem continuous_posPart : Continuous posPart := by
  simpa [posPart] using! (continuous_id.max continuous_const)

namespace Advice

variable [NeZero n] {I : ProcedureInput n}

omit [NeZero n] in
theorem posPart_mono {x y : ℝ} (hxy : x ≤ y) : posPart x ≤ posPart y := by
  unfold posPart
  exact max_le_max hxy le_rfl

/--
The sectionwise frontier value from `proof-good-tau-existence.tex`.
For `λ ∈ [0,1]`, this is the quantity
`[1 - [n λ - (n-j)]^+]^+` rewritten in the zero-based indexing used here.
-/
def sectionMuValue (lam : ℝ) (j : Idx n) : ℝ :=
  posPart (1 - posPart ((n : ℝ) * lam - futureCount j))

omit [NeZero n] in
@[simp] theorem sectionMuValue_nonneg (lam : ℝ) (j : Idx n) :
    0 ≤ sectionMuValue lam j := by
  simp [sectionMuValue]

omit [NeZero n] in
theorem sectionMuValue_le_one (lam : ℝ) (j : Idx n) :
    sectionMuValue lam j ≤ 1 := by
  unfold sectionMuValue
  by_cases h : 0 ≤ 1 - posPart ((n : ℝ) * lam - futureCount j)
  · rw [posPart_of_nonneg h]
    have hpos : 0 ≤ posPart ((n : ℝ) * lam - futureCount j) := posPart_nonneg _
    linarith
  · rw [posPart_of_nonpos (le_of_not_ge h)]
    norm_num

omit [NeZero n] in
theorem sectionMuValue_zero_eq_one (j : Idx n) : sectionMuValue 0 j = 1 := by
  unfold sectionMuValue
  simp

omit [NeZero n] in
theorem sectionMuValue_antitone (lam : ℝ) {j₁ j₂ : Idx n} (hj : j₁ ≤ j₂) :
    sectionMuValue lam j₂ ≤ sectionMuValue lam j₁ := by
  have hfc : futureCount j₂ ≤ futureCount j₁ := ProfileData.futureCount_antitone hj
  have hx :
      (n : ℝ) * lam - futureCount j₁ ≤ (n : ℝ) * lam - futureCount j₂ := by
    linarith
  unfold sectionMuValue
  exact posPart_mono (sub_le_sub_left (posPart_mono hx) 1)

omit [NeZero n] in
theorem sectionMuValue_antitone_in_lam
    {lam₁ lam₂ : ℝ} (hlam : lam₁ ≤ lam₂) (j : Idx n) :
    sectionMuValue lam₂ j ≤ sectionMuValue lam₁ j := by
  have hnnonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hlin :
      (n : ℝ) * lam₁ - futureCount j ≤ (n : ℝ) * lam₂ - futureCount j := by
    have hmul : (n : ℝ) * lam₁ ≤ (n : ℝ) * lam₂ := by
      exact mul_le_mul_of_nonneg_left hlam hnnonneg
    linarith
  have hinner :
      1 - posPart ((n : ℝ) * lam₂ - futureCount j) ≤
        1 - posPart ((n : ℝ) * lam₁ - futureCount j) := by
    have hpp :
        posPart ((n : ℝ) * lam₁ - futureCount j) ≤
          posPart ((n : ℝ) * lam₂ - futureCount j) :=
      posPart_mono hlin
    linarith
  unfold sectionMuValue
  exact posPart_mono hinner

omit [NeZero n] in
theorem continuous_sectionMuValue (j : Idx n) :
    Continuous fun lam : ℝ => sectionMuValue lam j := by
  unfold sectionMuValue
  have hlin : Continuous fun lam : ℝ => (n : ℝ) * lam - futureCount j := by
    exact (continuous_const.mul continuous_id).sub continuous_const
  exact continuous_posPart.comp (continuous_const.sub (continuous_posPart.comp hlin))

omit [NeZero n] in
theorem sectionMuValue_arg_mem_unit_of_fractional {lam : ℝ} {j : Idx n}
    (hfrac : IsFractional (sectionMuValue lam j)) :
    0 < (n : ℝ) * lam - futureCount j ∧ (n : ℝ) * lam - futureCount j < 1 := by
  rcases hfrac with ⟨hfrac_pos, hfrac_lt⟩
  set x : ℝ := (n : ℝ) * lam - futureCount j
  have harg_pos : 0 < 1 - posPart x := by
    by_cases hnonneg : 0 ≤ 1 - posPart x
    · simpa [sectionMuValue, x, posPart_of_nonneg hnonneg] using hfrac_pos
    · have hzero : sectionMuValue lam j = 0 := by
        simp [sectionMuValue, x, posPart_of_nonpos (le_of_not_ge hnonneg)]
      linarith
  have harg_nonneg : 0 ≤ 1 - posPart x := le_of_lt harg_pos
  have houter_eq : sectionMuValue lam j = 1 - posPart x := by
    simp [sectionMuValue, x, posPart_of_nonneg harg_nonneg]
  have hposPart_pos : 0 < posPart x := by
    have : 1 - posPart x < 1 := by
      simpa [houter_eq] using hfrac_lt
    linarith
  have hposPart_lt : posPart x < 1 := by
    linarith
  have hx_nonneg : 0 ≤ x := by
    by_cases hx : 0 ≤ x
    · exact hx
    · have hzero : posPart x = 0 := posPart_of_nonpos (le_of_not_ge hx)
      linarith
  have hx_eq : posPart x = x := posPart_of_nonneg hx_nonneg
  constructor <;> linarith

omit [NeZero n] in
theorem not_both_fractional_sectionMuValue_of_lt {lam : ℝ} {j₁ j₂ : Idx n}
    (hj : j₁ < j₂) :
    ¬ (IsFractional (sectionMuValue lam j₁) ∧ IsFractional (sectionMuValue lam j₂)) := by
  intro hfrac
  rcases hfrac with ⟨hfrac₁, hfrac₂⟩
  have harg₁ := sectionMuValue_arg_mem_unit_of_fractional hfrac₁
  have harg₂ := sectionMuValue_arg_mem_unit_of_fractional hfrac₂
  have hfc : futureCount j₂ + 1 ≤ futureCount j₁ := by
    change ((futureCountNat j₂ : ℝ) + 1 ≤ (futureCountNat j₁ : ℝ))
    exact_mod_cast Nat.succ_le_of_lt (ProfileData.futureCountNat_lt_of_lt hj)
  have hgap :
      (n : ℝ) * lam - futureCount j₁ + 1 ≤ (n : ℝ) * lam - futureCount j₂ := by
    linarith
  have hone_lt : 1 < (n : ℝ) * lam - futureCount j₂ := by
    linarith
  linarith

/--
The paper's section path `Γ^ℓ(λ)`. For `ℓ < n`, it varies the frontier values.
For `ℓ = n`, it keeps frontier values equal to `1` and varies `\hat g_n^\star = λ`.
-/
def sectionAdvice (I : ProcedureInput n) (ℓ : Idx n) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) : Advice I where
  t3Star := ℓ
  muStar := fun j =>
    if I.firstBidTime j = ℓ then
      if ℓ = lastIdx n then 1 else sectionMuValue lam j
    else
      0
  hatGLast := if ℓ = lastIdx n then lam else 0
  muStar_support := by
    intro j hj
    simp [hj]
  hatGLast_mem := by
    by_cases hlast : ℓ = lastIdx n
    · simp [hlast, hlam.1, hlam.2]
    · simp [hlast]

/-- The left endpoint `Γ₀` from `proof-good-tau-existence.tex`. -/
def gammaZero (I : ProcedureInput n) : Advice I :=
  sectionAdvice I (firstIdx n) 0 (by constructor <;> norm_num)

/-- The right endpoint `Γ₁` from `proof-good-tau-existence.tex`. -/
def gammaOne (I : ProcedureInput n) : Advice I :=
  sectionAdvice I (lastIdx n) 1 (by constructor <;> norm_num)

@[simp] theorem gammaZero_t3Star (I : ProcedureInput n) :
    (gammaZero I).t3Star = firstIdx n := by
  simp [gammaZero, Advice.sectionAdvice]

@[simp] theorem gammaOne_t3Star (I : ProcedureInput n) :
    (gammaOne I).t3Star = lastIdx n := by
  simp [gammaOne, Advice.sectionAdvice]

@[simp] theorem gammaZero_hatGLast (I : ProcedureInput n) :
    (gammaZero I).hatGLast = 0 := by
  simp [gammaZero, Advice.sectionAdvice]

@[simp] theorem gammaOne_hatGLast (I : ProcedureInput n) :
    (gammaOne I).hatGLast = 1 := by
  simp [gammaOne, Advice.sectionAdvice]

theorem sectionAdvice_admissible (I : ProcedureInput n) (ℓ : Idx n) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) :
    (sectionAdvice I ℓ lam hlam).Admissible := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hfront : I.firstBidTime j = ℓ
    · by_cases hlast : ℓ = lastIdx n
      · simp [Advice.sectionAdvice, hfront, hlast]
      · exact ⟨by
            simp [Advice.sectionAdvice, hfront, hlast, sectionMuValue_nonneg],
          by simpa [Advice.sectionAdvice, hfront, hlast] using sectionMuValue_le_one lam j⟩
    · simp [Advice.sectionAdvice, hfront]
  · intro j₁ j₂ hj hfront₁ hfront₂
    by_cases hlast : ℓ = lastIdx n
    · have hf₁ : I.firstBidTime j₁ = lastIdx n := by
        simpa [Advice.OnFrontier, Advice.sectionAdvice, hlast] using hfront₁
      have hf₂ : I.firstBidTime j₂ = lastIdx n := by
        simpa [Advice.OnFrontier, Advice.sectionAdvice, hlast] using hfront₂
      simp [Advice.sectionAdvice, hf₁, hf₂, hlast]
    · have hf₁ : I.firstBidTime j₁ = ℓ := by
        simpa [Advice.OnFrontier, Advice.sectionAdvice] using hfront₁
      have hf₂ : I.firstBidTime j₂ = ℓ := by
        simpa [Advice.OnFrontier, Advice.sectionAdvice] using hfront₂
      simpa [Advice.sectionAdvice, hf₁, hf₂, hlast] using
        sectionMuValue_antitone lam hj
  · intro j₁ j₂ hfront₁ hfront₂ hfrac₁ hfrac₂
    by_cases hlast : ℓ = lastIdx n
    · have hf₁ : I.firstBidTime j₁ = lastIdx n := by
        simpa [Advice.OnFrontier, Advice.sectionAdvice, hlast] using hfront₁
      have hnot : ¬ IsFractional ((sectionAdvice I ℓ lam hlam).muStar j₁) := by
        simp [Advice.sectionAdvice, hf₁, hlast, IsFractional]
      exact False.elim (hnot hfrac₁)
    · by_cases hjeq : j₁ = j₂
      · exact hjeq
      · have hlt_or_gt : j₁ < j₂ ∨ j₂ < j₁ := lt_or_gt_of_ne hjeq
        have hf₁ : I.firstBidTime j₁ = ℓ := by
          simpa [Advice.OnFrontier, Advice.sectionAdvice] using hfront₁
        have hf₂ : I.firstBidTime j₂ = ℓ := by
          simpa [Advice.OnFrontier, Advice.sectionAdvice] using hfront₂
        have hfrac₁' : IsFractional (sectionMuValue lam j₁) := by
          simpa [Advice.sectionAdvice, hf₁, hlast] using hfrac₁
        have hfrac₂' : IsFractional (sectionMuValue lam j₂) := by
          simpa [Advice.sectionAdvice, hf₂, hlast] using hfrac₂
        cases hlt_or_gt with
        | inl hlt =>
            exfalso
            exact not_both_fractional_sectionMuValue_of_lt hlt ⟨hfrac₁', hfrac₂'⟩
        | inr hgt =>
            exfalso
            exact not_both_fractional_sectionMuValue_of_lt hgt ⟨hfrac₂', hfrac₁'⟩
  · intro ht3last j hfront
    have hℓ : ℓ = lastIdx n := by
      simpa [Advice.sectionAdvice] using ht3last
    have hf : I.firstBidTime j = lastIdx n := by
      simpa [Advice.OnFrontier, Advice.sectionAdvice, hℓ] using hfront
    simp [Advice.sectionAdvice, hf, hℓ]

theorem gammaZero_admissible (I : ProcedureInput n) :
    (gammaZero I).Admissible := by
  exact sectionAdvice_admissible I (firstIdx n) 0 (by constructor <;> norm_num)

theorem gammaOne_admissible (I : ProcedureInput n) :
    (gammaOne I).Admissible := by
  exact sectionAdvice_admissible I (lastIdx n) 1 (by constructor <;> norm_num)

theorem gammaZero_muD_eq_one (I : ProcedureInput n) (j : Idx n) :
    (gammaZero I).muD j = 1 := by
  have hle : firstIdx n ≤ I.firstBidTime j := firstIdx_le (I.firstBidTime j)
  by_cases hfront : I.firstBidTime j = firstIdx n
  · rw [Advice.muD_eq_muStar (gammaZero I) hfront]
    simp [gammaZero, Advice.sectionAdvice, hfront, sectionMuValue_zero_eq_one]
  · have hlt : firstIdx n < I.firstBidTime j := lt_of_le_of_ne hle (Ne.symm hfront)
    simpa [gammaZero_t3Star] using Advice.muD_eq_one (gammaZero I) hlt

/-- The sectionwise `μ^D` profile as an explicit function of `λ`. -/
def sectionMuDValue [NeZero n] (I : ProcedureInput n) (ℓ j : Idx n) (lam : ℝ) : ℝ :=
  if ℓ < I.firstBidTime j then
    1
  else if I.firstBidTime j = ℓ then
    if ℓ = lastIdx n then 1 else sectionMuValue lam j
  else
    0

@[simp] theorem sectionMuDValue_eq
    (I : ProcedureInput n) (ℓ j : Idx n) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) :
    sectionMuDValue I ℓ j lam = (sectionAdvice I ℓ lam hlam).muD j := by
  by_cases h₁ : ℓ < I.firstBidTime j
  · rw [sectionMuDValue, if_pos h₁]
    exact (Advice.muD_eq_one (sectionAdvice I ℓ lam hlam) h₁).symm
  · by_cases h₂ : I.firstBidTime j = ℓ
    · rw [sectionMuDValue, if_neg h₁, if_pos h₂]
      rw [Advice.muD_eq_muStar (sectionAdvice I ℓ lam hlam) h₂]
      by_cases hlast : ℓ = lastIdx n
      · simp [Advice.sectionAdvice, h₂, hlast]
      · simp [Advice.sectionAdvice, h₂, hlast]
    · rw [sectionMuDValue, if_neg h₁, if_neg h₂]
      have hlt : I.firstBidTime j < ℓ := lt_of_le_of_ne (not_lt.mp h₁) h₂
      exact (Advice.muD_eq_zero (sectionAdvice I ℓ lam hlam) hlt).symm

theorem sectionMuDValue_nonneg
    (I : ProcedureInput n) (ℓ j : Idx n) (lam : ℝ) :
    0 ≤ sectionMuDValue I ℓ j lam := by
  by_cases h₁ : ℓ < I.firstBidTime j
  · simp [sectionMuDValue, h₁]
  · by_cases h₂ : I.firstBidTime j = ℓ
    · by_cases hlast : ℓ = lastIdx n
      · simp [sectionMuDValue, h₂, hlast]
      · simp [sectionMuDValue, h₂, hlast, sectionMuValue_nonneg]
    · simp [sectionMuDValue, h₁, h₂]

theorem sectionMuDValue_le_one
    (I : ProcedureInput n) (ℓ j : Idx n) (lam : ℝ) :
    sectionMuDValue I ℓ j lam ≤ 1 := by
  by_cases h₁ : ℓ < I.firstBidTime j
  · simp [sectionMuDValue, h₁]
  · by_cases h₂ : I.firstBidTime j = ℓ
    · by_cases hlast : ℓ = lastIdx n
      · simp [sectionMuDValue, h₂, hlast]
      · simp [sectionMuDValue, h₂, hlast, sectionMuValue_le_one]
    · simp [sectionMuDValue, h₁, h₂]

theorem sectionMuDValue_antitone_in_lam
    (I : ProcedureInput n) (ℓ j : Idx n) {lam₁ lam₂ : ℝ}
    (hlam : lam₁ ≤ lam₂) :
    sectionMuDValue I ℓ j lam₂ ≤ sectionMuDValue I ℓ j lam₁ := by
  by_cases h₁ : ℓ < I.firstBidTime j
  · simp [sectionMuDValue, h₁]
  · by_cases h₂ : I.firstBidTime j = ℓ
    · by_cases hlast : ℓ = lastIdx n
      · simp [sectionMuDValue, h₂, hlast]
      · simp [sectionMuDValue, h₂, hlast,
          sectionMuValue_antitone_in_lam hlam]
    · simp [sectionMuDValue, h₁, h₂]

theorem continuous_sectionMuDValue
    (I : ProcedureInput n) (ℓ j : Idx n) :
    Continuous fun lam : ℝ => sectionMuDValue I ℓ j lam := by
  by_cases h₁ : ℓ < I.firstBidTime j
  · simpa [sectionMuDValue, h₁] using (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))
  · by_cases h₂ : I.firstBidTime j = ℓ
    · by_cases hlast : ℓ = lastIdx n
      · simpa [sectionMuDValue, h₂, hlast] using
          (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))
      · simpa [sectionMuDValue, h₂, hlast] using continuous_sectionMuValue j
    · simpa [sectionMuDValue, h₁, h₂] using
        (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))

theorem sectionMuDValue_eq_one_of_section_lt_firstBid
    (I : ProcedureInput n) {ℓ j : Idx n} {lam : ℝ}
    (h : ℓ < I.firstBidTime j) :
    sectionMuDValue I ℓ j lam = 1 := by
  simp [sectionMuDValue, h]

theorem sectionMuDValue_eq_zero_of_firstBid_lt_section
    (I : ProcedureInput n) {ℓ j : Idx n} {lam : ℝ}
    (h : I.firstBidTime j < ℓ) :
    sectionMuDValue I ℓ j lam = 0 := by
  have h₁ : ¬ ℓ < I.firstBidTime j := not_lt.mpr (le_of_lt h)
  have h₂ : I.firstBidTime j ≠ ℓ := ne_of_lt h
  simp [sectionMuDValue, h₁, h₂]

theorem sectionMuDValue_eq_of_firstBid_ne_section
    (I : ProcedureInput n) {ℓ j : Idx n} {lam₁ lam₂ : ℝ}
    (h : I.firstBidTime j ≠ ℓ) :
    sectionMuDValue I ℓ j lam₁ = sectionMuDValue I ℓ j lam₂ := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [sectionMuDValue_eq_zero_of_firstBid_lt_section I hlt,
      sectionMuDValue_eq_zero_of_firstBid_lt_section I hlt]
  · rw [sectionMuDValue_eq_one_of_section_lt_firstBid I hgt,
      sectionMuDValue_eq_one_of_section_lt_firstBid I hgt]

theorem le_section_of_sectionMuD_lt_one
    (I : ProcedureInput n) {ℓ j : Idx n} {lam : ℝ}
    (hμ : sectionMuDValue I ℓ j lam < 1) :
    j ≤ ℓ := by
  by_contra hj
  have hfront : ℓ < I.firstBidTime j := lt_of_lt_of_le (not_le.mp hj) (I.le_firstBidTime j)
  rw [sectionMuDValue_eq_one_of_section_lt_firstBid I hfront] at hμ
  linarith

theorem sectionMuDValue_eq_one_of_eq_one_of_left
    (I : ProcedureInput n) {ℓ j : Idx n} {x lam : ℝ}
    (hx : x ≤ lam)
    (hμ : sectionMuDValue I ℓ j lam = 1) :
    sectionMuDValue I ℓ j x = 1 := by
  by_cases hfb : I.firstBidTime j = ℓ
  · by_cases hlast : ℓ = lastIdx n
    · simp [sectionMuDValue, hfb, hlast]
    · have hμlam : sectionMuValue lam j = 1 := by
        simpa [sectionMuDValue, hfb, hlast] using hμ
      have hanti : sectionMuValue lam j ≤ sectionMuValue x j :=
        sectionMuValue_antitone_in_lam hx j
      have hxle : sectionMuValue x j ≤ 1 := sectionMuValue_le_one x j
      have hμx : sectionMuValue x j = 1 := le_antisymm hxle (by simpa [hμlam] using hanti)
      simpa [sectionMuDValue, hfb, hlast] using hμx
  · have hconst :
        sectionMuDValue I ℓ j x = sectionMuDValue I ℓ j lam :=
      sectionMuDValue_eq_of_firstBid_ne_section (I := I) (lam₁ := x) (lam₂ := lam) hfb
    rw [hconst]
    exact hμ

/-- Indices below `t₁` whose `μ^D` value is strictly below `1`. This is the finite set whose
maximum is the paper's `k` in the left-jump case. -/
noncomputable def belowThresholdNononeSet
    (I : ProcedureInput n) (ℓ t1 : Idx n) (lam : ℝ) : Finset (Idx n) :=
  Finset.univ.filter fun j => j < t1 ∧ Advice.sectionMuDValue I ℓ j lam < 1

theorem mem_belowThresholdNononeSet_iff
    (I : ProcedureInput n) {ℓ t1 j : Idx n} {lam : ℝ} :
    j ∈ belowThresholdNononeSet I ℓ t1 lam ↔
      j < t1 ∧ Advice.sectionMuDValue I ℓ j lam < 1 := by
  simp [belowThresholdNononeSet]

theorem sectionMuDValue_eq_one_of_not_mem_belowThresholdNononeSet
    (I : ProcedureInput n) {ℓ t1 j : Idx n} {lam : ℝ}
    (hjt1 : j < t1)
    (hjnot : j ∉ belowThresholdNononeSet I ℓ t1 lam) :
    Advice.sectionMuDValue I ℓ j lam = 1 := by
  have hjge : 1 ≤ Advice.sectionMuDValue I ℓ j lam := by
    by_cases hlt : Advice.sectionMuDValue I ℓ j lam < 1
    · exfalso
      exact hjnot ((mem_belowThresholdNononeSet_iff I).2 ⟨hjt1, hlt⟩)
    · exact le_of_not_gt hlt
  have hjle : Advice.sectionMuDValue I ℓ j lam ≤ 1 :=
    Advice.sectionMuDValue_le_one I ℓ j lam
  linarith

theorem sectionMuDValue_eq_one_of_between_max_belowThresholdNononeSet
    (I : ProcedureInput n) {ℓ t1 k j : Idx n} {lam : ℝ}
    {hne : (belowThresholdNononeSet I ℓ t1 lam).Nonempty}
    (hk : (belowThresholdNononeSet I ℓ t1 lam).max' hne = k)
    (hkj : k < j) (hjt1 : j < t1) :
    Advice.sectionMuDValue I ℓ j lam = 1 := by
  have hjnot : j ∉ belowThresholdNononeSet I ℓ t1 lam := by
    intro hjmem
    have hjlemax :
        j ≤ (belowThresholdNononeSet I ℓ t1 lam).max' hne :=
      Finset.le_max' _ _ hjmem
    rw [hk] at hjlemax
    exact not_le_of_gt hkj hjlemax
  exact sectionMuDValue_eq_one_of_not_mem_belowThresholdNononeSet I hjt1 hjnot

/-- The sectionwise terminal Phase-2 value `\hat g_n^\star(λ)`. -/
def sectionHatGLastValue [NeZero n] (ℓ : Idx n) (lam : ℝ) : ℝ :=
  if ℓ = lastIdx n then lam else 0

@[simp] theorem sectionHatGLastValue_eq
    (I : ProcedureInput n) (ℓ : Idx n) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 1) :
    sectionHatGLastValue ℓ lam = (sectionAdvice I ℓ lam hlam).hatGLast := by
  simp [sectionHatGLastValue, Advice.sectionAdvice]

theorem continuous_sectionHatGLastValue (ℓ : Idx n) :
    Continuous fun lam : ℝ => sectionHatGLastValue ℓ lam := by
  by_cases hlast : ℓ = lastIdx n
  · simpa [sectionHatGLastValue, hlast] using! (continuous_id : Continuous fun lam : ℝ => lam)
  · simpa [sectionHatGLastValue, hlast] using
      (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))

omit I [NeZero n] in
theorem sectionHatGLastValue_nonneg [NeZero n]
    (ℓ : Idx n) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ sectionHatGLastValue ℓ lam := by
  by_cases hlast : ℓ = lastIdx n
  · simp [sectionHatGLastValue, hlast, hlam]
  · simp [sectionHatGLastValue, hlast]

omit I [NeZero n] in
theorem sectionHatGLastValue_monotone_in_lam [NeZero n]
    (ℓ : Idx n) {lam₁ lam₂ : ℝ} (hlam : lam₁ ≤ lam₂) :
    sectionHatGLastValue ℓ lam₁ ≤ sectionHatGLastValue ℓ lam₂ := by
  by_cases hlast : ℓ = lastIdx n
  · simp [sectionHatGLastValue, hlast, hlam]
  · simp [sectionHatGLastValue, hlast]

omit [NeZero n] in
theorem sectionMuValue_one_eq_zero (j : Idx n) :
    sectionMuValue 1 j = 0 := by
  unfold sectionMuValue
  have hcalc : (n : ℝ) - futureCount j = (j.1.succ : ℝ) := by
    unfold futureCount futureCountNat
    rw [show (n : ℝ) - ((n - j.1.succ : ℕ) : ℝ) =
        ((n - (n - j.1.succ) : ℕ) : ℝ) by
          rw [Nat.cast_sub (Nat.sub_le n j.1.succ)]]
    rw [Nat.sub_sub_self (Nat.succ_le_of_lt j.is_lt)]
  have hnonneg : 0 ≤ (n : ℝ) - futureCount j := by
    rw [hcalc]
    positivity
  have hinner : posPart ((n : ℝ) - futureCount j) = (j.1.succ : ℝ) := by
    rw [posPart_of_nonneg hnonneg, hcalc]
  have houter : 1 - posPart ((n : ℝ) * 1 - futureCount j) ≤ 0 := by
    rw [show (n : ℝ) * 1 - futureCount j = (n : ℝ) - futureCount j by ring, hinner]
    have hone : (1 : ℝ) ≤ (j.1.succ : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le j.1)
    linarith
  rw [posPart_of_nonpos houter]

section PhaseTwoSectionPath

variable (I : ProcedureInput n)

/-- The multiplicative factor in the Phase-2 product formula along a fixed section. -/
noncomputable def sectionPhaseTwoFactor [NeZero n] (ℓ j : Idx n) (lam : ℝ) : ℝ :=
  1 + (1 - Advice.sectionMuDValue I ℓ j lam) / futureCount j

theorem continuous_sectionPhaseTwoFactor [NeZero n] (ℓ j : Idx n) :
    Continuous fun lam : ℝ => sectionPhaseTwoFactor I ℓ j lam := by
  unfold sectionPhaseTwoFactor
  exact continuous_const.add
    ((continuous_const.sub (Advice.continuous_sectionMuDValue I ℓ j)).div_const (futureCount j))

theorem sectionPhaseTwoFactor_one_le [NeZero n]
    (ℓ j : Idx n) {lam : ℝ} (hj : j < lastIdx n) :
    1 ≤ sectionPhaseTwoFactor I ℓ j lam := by
  unfold sectionPhaseTwoFactor
  have hmu : Advice.sectionMuDValue I ℓ j lam ≤ 1 := Advice.sectionMuDValue_le_one I ℓ j lam
  have hnum : 0 ≤ 1 - Advice.sectionMuDValue I ℓ j lam := by
    linarith
  have hfcpos : 0 < futureCount j := by
    unfold futureCount futureCountNat
    have hjval : j.1 < Nat.pred n := Fin.lt_def.mp hj
    have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
    have hsucc : j.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt hjval) hpredlt
    exact_mod_cast Nat.sub_pos_of_lt hsucc
  have hdiv : 0 ≤ (1 - Advice.sectionMuDValue I ℓ j lam) / futureCount j := by
    exact div_nonneg hnum hfcpos.le
  linarith

theorem sectionPhaseTwoFactor_monotone_in_lam [NeZero n]
    (ℓ j : Idx n) {lam₁ lam₂ : ℝ} (hj : j < lastIdx n) (hlam : lam₁ ≤ lam₂) :
    sectionPhaseTwoFactor I ℓ j lam₁ ≤ sectionPhaseTwoFactor I ℓ j lam₂ := by
  unfold sectionPhaseTwoFactor
  have hmu : Advice.sectionMuDValue I ℓ j lam₂ ≤ Advice.sectionMuDValue I ℓ j lam₁ :=
    Advice.sectionMuDValue_antitone_in_lam I ℓ j hlam
  have hnum :
      1 - Advice.sectionMuDValue I ℓ j lam₁ ≤
        1 - Advice.sectionMuDValue I ℓ j lam₂ := by
    linarith
  have hfcpos : 0 < futureCount j := by
    unfold futureCount futureCountNat
    have hjval : j.1 < Nat.pred n := Fin.lt_def.mp hj
    have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
    have hsucc : j.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt hjval) hpredlt
    exact_mod_cast Nat.sub_pos_of_lt hsucc
  have hdiv :
      (1 - Advice.sectionMuDValue I ℓ j lam₁) / futureCount j ≤
        (1 - Advice.sectionMuDValue I ℓ j lam₂) / futureCount j := by
    have hfc_nonneg : 0 ≤ futureCount j := le_of_lt hfcpos
    have hrecip_nonneg : 0 ≤ (futureCount j)⁻¹ := inv_nonneg.mpr hfc_nonneg
    have hmul := mul_le_mul_of_nonneg_right hnum hrecip_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa [add_comm] using add_le_add_left hdiv 1

/-- The closed-form Phase-2 budget `R_i^{(2)}(λ)` from the paper. -/
noncomputable def sectionPhaseTwoBudgetValue [NeZero n] (ℓ i : Idx n) (lam : ℝ) : ℝ :=
  ((Advice.sectionHatGLastValue ℓ lam + I.program.tau) *
      Finset.prod (halfOpenIntervalRange i (lastIdx n)) (fun j =>
        sectionPhaseTwoFactor I ℓ j lam)) -
    I.program.tau

@[simp] theorem sectionPhaseTwoBudgetValue_last [NeZero n] (ℓ : Idx n) (lam : ℝ) :
    sectionPhaseTwoBudgetValue I ℓ (lastIdx n) lam = Advice.sectionHatGLastValue ℓ lam := by
  have hempty : halfOpenIntervalRange (lastIdx n) (lastIdx n) = (∅ : Finset (Idx n)) := by
    ext j
    simp [halfOpenIntervalRange]
  rw [sectionPhaseTwoBudgetValue, hempty, Finset.prod_empty]
  ring

theorem continuous_sectionPhaseTwoBudgetValue [NeZero n] (ℓ i : Idx n) :
    Continuous fun lam : ℝ => sectionPhaseTwoBudgetValue I ℓ i lam := by
  unfold sectionPhaseTwoBudgetValue
  refine
    (((Advice.continuous_sectionHatGLastValue ℓ).add continuous_const).mul ?_).sub
      continuous_const
  refine continuous_finsetProd _ ?_
  intro j hj
  exact continuous_sectionPhaseTwoFactor I ℓ j

/-- The paper's sectionwise `z(λ)` expression written directly from the Phase-2 budget formula. -/
noncomputable def sectionZValue [NeZero n] (ℓ t2 : Idx n) (lam : ℝ) : ℝ :=
  Finset.sum (strictSuffixRange t2) fun m =>
    posPart (1 - sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta) *
      Advice.sectionMuDValue I ℓ m lam

/-- The same `z` expression written as a full sum over all indices. When `t₂` is a valid
threshold, the extra terms on `m ≤ t₂` vanish. -/
noncomputable def sectionZFullValue [NeZero n] (ℓ : Idx n) (lam : ℝ) : ℝ :=
  Finset.sum Finset.univ fun m =>
    posPart (1 - sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta) *
      Advice.sectionMuDValue I ℓ m lam

theorem sectionZFullValue_nonneg [NeZero n] (ℓ : Idx n) (lam : ℝ) :
    0 ≤ sectionZFullValue I ℓ lam := by
  unfold sectionZFullValue
  refine Finset.sum_nonneg ?_
  intro m hm
  exact mul_nonneg (posPart_nonneg _)
    (Advice.sectionMuDValue_nonneg I ℓ m lam)

theorem continuous_sectionZValue [NeZero n] (ℓ t2 : Idx n) :
    Continuous fun lam : ℝ => sectionZValue I ℓ t2 lam := by
  unfold sectionZValue
  refine continuous_finsetSum _ ?_
  intro m hm
  refine (continuous_posPart.comp ?_).mul (Advice.continuous_sectionMuDValue I ℓ m)
  exact
    (continuous_const.sub
      ((continuous_sectionPhaseTwoBudgetValue I ℓ m).div_const I.program.theta))

theorem continuous_sectionZFullValue [NeZero n] (ℓ : Idx n) :
    Continuous fun lam : ℝ => sectionZFullValue I ℓ lam := by
  unfold sectionZFullValue
  refine continuous_finsetSum _ ?_
  intro m hm
  refine (continuous_posPart.comp ?_).mul (Advice.continuous_sectionMuDValue I ℓ m)
  exact
    (continuous_const.sub
      ((continuous_sectionPhaseTwoBudgetValue I ℓ m).div_const I.program.theta))

/-- The sectionwise Phase-2 tail budget `R_i^{(2)}(λ)`. -/
noncomputable def sectionPhaseTwoAfterBudgetValue [NeZero n] (ℓ i : Idx n) (lam : ℝ) : ℝ :=
  if hi : i = lastIdx n then
    0
  else
    sectionPhaseTwoBudgetValue I ℓ
      (succIdx i (lt_of_le_of_ne (le_lastIdx i) hi)) lam

theorem continuous_sectionPhaseTwoAfterBudgetValue [NeZero n] (ℓ i : Idx n) :
    Continuous fun lam : ℝ => sectionPhaseTwoAfterBudgetValue I ℓ i lam := by
  by_cases hi : i = lastIdx n
  · simpa [sectionPhaseTwoAfterBudgetValue, hi] using
      (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  · have hlt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hi
    simpa [sectionPhaseTwoAfterBudgetValue, hi] using
      continuous_sectionPhaseTwoBudgetValue I ℓ (succIdx i hlt)

/-- The sectionwise Phase-2 generated value `\hat g_i^{(2)}(λ)`. -/
noncomputable def sectionPhaseTwoHatG2Value [NeZero n] (ℓ i : Idx n) (lam : ℝ) : ℝ :=
  sectionPhaseTwoBudgetValue I ℓ i lam - sectionPhaseTwoAfterBudgetValue I ℓ i lam

theorem continuous_sectionPhaseTwoHatG2Value [NeZero n] (ℓ i : Idx n) :
    Continuous fun lam : ℝ => sectionPhaseTwoHatG2Value I ℓ i lam := by
  unfold sectionPhaseTwoHatG2Value
  exact (continuous_sectionPhaseTwoBudgetValue I ℓ i).sub
    (continuous_sectionPhaseTwoAfterBudgetValue I ℓ i)

theorem sectionPhaseTwoFactor_eq_one_of_frontier_lt [NeZero n]
    {ℓ j : Idx n} {lam : ℝ} (hℓj : ℓ < j) :
    sectionPhaseTwoFactor I ℓ j lam = 1 := by
  unfold sectionPhaseTwoFactor
  have hmu : Advice.sectionMuDValue I ℓ j lam = 1 := by
    have hfront : ℓ < I.firstBidTime j := lt_of_lt_of_le hℓj (I.le_firstBidTime j)
    simp [Advice.sectionMuDValue, hfront]
  simp [hmu]

theorem sectionPhaseTwoFactor_eq_one_of_muD_eq_one [NeZero n]
    {ℓ j : Idx n} {lam : ℝ}
    (hμ : Advice.sectionMuDValue I ℓ j lam = 1) :
    sectionPhaseTwoFactor I ℓ j lam = 1 := by
  unfold sectionPhaseTwoFactor
  simp [hμ]

omit [NeZero n] in
theorem halfOpenIntervalRange_union
    {a b c : Idx n} (hab : a ≤ b) (hbc : b ≤ c) :
    halfOpenIntervalRange a c =
      halfOpenIntervalRange a b ∪ halfOpenIntervalRange b c := by
  ext j
  constructor
  · intro hj
    have hj' := mem_halfOpenIntervalRange.mp hj
    by_cases hbj : j < b
    · exact Finset.mem_union.mpr <| Or.inl <| mem_halfOpenIntervalRange.mpr ⟨hj'.1, hbj⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        mem_halfOpenIntervalRange.mpr ⟨le_of_not_gt hbj, hj'.2⟩
  · intro hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases mem_halfOpenIntervalRange.mp hj with ⟨haj, hjb⟩
      exact mem_halfOpenIntervalRange.mpr ⟨haj, lt_of_lt_of_le hjb hbc⟩
    · rcases mem_halfOpenIntervalRange.mp hj with ⟨hbj, hjc⟩
      exact mem_halfOpenIntervalRange.mpr ⟨le_trans hab hbj, hjc⟩

omit [NeZero n] in
theorem disjoint_halfOpenIntervalRange
    {a b c : Idx n} :
    Disjoint (halfOpenIntervalRange a b) (halfOpenIntervalRange b c) := by
  refine Finset.disjoint_left.mpr ?_
  intro j h1 h2
  exact not_lt_of_ge (mem_halfOpenIntervalRange.mp h2).1 (mem_halfOpenIntervalRange.mp h1).2

theorem sectionPhaseTwoBudgetValue_eq_of_muD_eq_one_on_halfOpen [NeZero n]
    {ℓ a b : Idx n} {lam : ℝ}
    (hab : a ≤ b)
    (hμ :
      ∀ ⦃j : Idx n⦄, a ≤ j → j < b → Advice.sectionMuDValue I ℓ j lam = 1) :
    sectionPhaseTwoBudgetValue I ℓ a lam = sectionPhaseTwoBudgetValue I ℓ b lam := by
  unfold sectionPhaseTwoBudgetValue
  have hsplit :
      halfOpenIntervalRange a (lastIdx n) =
        halfOpenIntervalRange a b ∪ halfOpenIntervalRange b (lastIdx n) :=
    halfOpenIntervalRange_union (a := a) (b := b) (c := lastIdx n) hab (le_lastIdx b)
  rw [hsplit, Finset.prod_union (disjoint_halfOpenIntervalRange (a := a) (b := b) (c := lastIdx n))]
  have hprod :
      Finset.prod (halfOpenIntervalRange a b) (fun j => sectionPhaseTwoFactor I ℓ j lam) = 1 := by
    refine Finset.prod_eq_one ?_
    intro j hj
    exact sectionPhaseTwoFactor_eq_one_of_muD_eq_one (I := I)
      (hμ (mem_halfOpenIntervalRange.mp hj).1 (mem_halfOpenIntervalRange.mp hj).2)
  rw [hprod, one_mul]

theorem sectionPhaseTwoAfterBudgetValue_eq_budget_of_between_max_belowThresholdNononeSet [NeZero n]
    {ℓ t1 k : Idx n} {lam : ℝ}
    {hne : (Advice.belowThresholdNononeSet I ℓ t1 lam).Nonempty}
    (hk : (Advice.belowThresholdNononeSet I ℓ t1 lam).max' hne = k)
    (hkt1 : k < t1) :
    sectionPhaseTwoAfterBudgetValue I ℓ k lam =
      sectionPhaseTwoBudgetValue I ℓ t1 lam := by
  have hklt : k < lastIdx n := lt_of_lt_of_le hkt1 (le_lastIdx t1)
  have hafter :
      sectionPhaseTwoAfterBudgetValue I ℓ k lam =
        sectionPhaseTwoBudgetValue I ℓ (succIdx k hklt) lam := by
    have hkne : ¬ k = lastIdx n := hklt.ne
    simp [sectionPhaseTwoAfterBudgetValue, hkne]
  rw [hafter]
  exact sectionPhaseTwoBudgetValue_eq_of_muD_eq_one_on_halfOpen (I := I)
    (a := succIdx k hklt) (b := t1) ((succIdx_le_iff hklt).2 hkt1) (fun j hj1 hj2 =>
      Advice.sectionMuDValue_eq_one_of_between_max_belowThresholdNononeSet I hk
        ((succIdx_le_iff hklt).1 hj1) hj2)

theorem sectionPhaseTwoBudgetValue_eq_of_between_max_belowThresholdNononeSet_of_left [NeZero n]
    {ℓ t1 k i : Idx n} {lam x : ℝ}
    {hne : (Advice.belowThresholdNononeSet I ℓ t1 lam).Nonempty}
    (hk : (Advice.belowThresholdNononeSet I ℓ t1 lam).max' hne = k)
    (hxi : x ≤ lam)
    (hki : k < i) (hit1 : i ≤ t1) :
    sectionPhaseTwoBudgetValue I ℓ i x =
      sectionPhaseTwoBudgetValue I ℓ t1 x := by
  by_cases hi : i = t1
  · simp [hi]
  · have hit1' : i < t1 := lt_of_le_of_ne hit1 hi
    exact sectionPhaseTwoBudgetValue_eq_of_muD_eq_one_on_halfOpen (I := I)
      (a := i) (b := t1) hit1 (fun j hij hjt1 =>
        Advice.sectionMuDValue_eq_one_of_eq_one_of_left I hxi
          (Advice.sectionMuDValue_eq_one_of_between_max_belowThresholdNononeSet I hk
            (lt_of_lt_of_le hki hij) hjt1))

theorem sectionPhaseTwoBudgetValue_eq_zero_of_frontier_lt [NeZero n]
    {ℓ i : Idx n} {lam : ℝ} (hℓi : ℓ < i) :
    sectionPhaseTwoBudgetValue I ℓ i lam = 0 := by
  unfold sectionPhaseTwoBudgetValue
  have hlast : ℓ ≠ lastIdx n := ne_of_lt (lt_of_lt_of_le hℓi (le_lastIdx i))
  rw [Advice.sectionHatGLastValue, if_neg hlast]
  have hprod :
      Finset.prod (halfOpenIntervalRange i (lastIdx n))
        (fun j => sectionPhaseTwoFactor I ℓ j lam) = 1 := by
    refine Finset.prod_eq_one ?_
    intro j hj
    exact sectionPhaseTwoFactor_eq_one_of_frontier_lt (I := I)
      (lt_of_lt_of_le hℓi (mem_halfOpenIntervalRange.mp hj).1)
  rw [hprod]
  ring

@[simp] theorem sectionPhaseTwoAfterBudgetValue_last [NeZero n] (ℓ : Idx n) (lam : ℝ) :
    sectionPhaseTwoAfterBudgetValue I ℓ (lastIdx n) lam = 0 := by
  simp [sectionPhaseTwoAfterBudgetValue]

theorem sectionPhaseTwoAfterBudgetValue_eq_budget_succ [NeZero n]
    (ℓ i : Idx n) (lam : ℝ) (hi : i < lastIdx n) :
    sectionPhaseTwoAfterBudgetValue I ℓ i lam =
      sectionPhaseTwoBudgetValue I ℓ (succIdx i hi) lam := by
  simp [sectionPhaseTwoAfterBudgetValue, ne_of_lt hi]

theorem sectionPhaseTwoAfterBudgetValue_eq_zero_of_frontier_le [NeZero n]
    {ℓ i : Idx n} {lam : ℝ} (hℓi : ℓ ≤ i) :
    sectionPhaseTwoAfterBudgetValue I ℓ i lam = 0 := by
  by_cases hi : i = lastIdx n
  · simp [sectionPhaseTwoAfterBudgetValue, hi]
  · have hilt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hi
    rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam hilt]
    exact sectionPhaseTwoBudgetValue_eq_zero_of_frontier_lt (I := I)
      (lt_of_le_of_lt hℓi (lt_succIdx i hilt))

@[simp] theorem sectionPhaseTwoHatG2Value_last [NeZero n] (ℓ : Idx n) (lam : ℝ) :
    sectionPhaseTwoHatG2Value I ℓ (lastIdx n) lam = Advice.sectionHatGLastValue ℓ lam := by
  simp [sectionPhaseTwoHatG2Value, sectionPhaseTwoAfterBudgetValue]

theorem sectionPhaseTwoBudgetValue_step [NeZero n]
    (ℓ i : Idx n) (lam : ℝ) (hi : i < lastIdx n) :
    sectionPhaseTwoBudgetValue I ℓ i lam =
      (sectionPhaseTwoAfterBudgetValue I ℓ i lam + I.program.tau) *
        sectionPhaseTwoFactor I ℓ i lam - I.program.tau := by
  have hsplit :
      halfOpenIntervalRange i (lastIdx n) =
        insert i (halfOpenIntervalRange (succIdx i hi) (lastIdx n)) := by
    ext j
    constructor
    · intro hj
      rcases mem_halfOpenIntervalRange.mp hj with ⟨hij, hjlast⟩
      rcases eq_or_lt_of_le hij with rfl | hij'
      · simp
      · exact Finset.mem_insert.mpr <| Or.inr <|
          mem_halfOpenIntervalRange.mpr ⟨(succIdx_le_iff hi).2 hij', hjlast⟩
    · intro hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact mem_halfOpenIntervalRange.mpr ⟨le_rfl, hi⟩
      · rcases mem_halfOpenIntervalRange.mp hj' with ⟨hsucc, hjlast⟩
        exact mem_halfOpenIntervalRange.mpr ⟨le_of_lt ((succIdx_le_iff hi).1 hsucc), hjlast⟩
  unfold sectionPhaseTwoBudgetValue
  rw [hsplit, Finset.prod_insert]
  · rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam hi]
    unfold sectionPhaseTwoBudgetValue
    ring_nf
  · simp [mem_halfOpenIntervalRange]

theorem sectionPhaseTwoBudgetValue_nonneg [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ i : Idx n) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ sectionPhaseTwoBudgetValue I ℓ i lam := by
  have hmain :
      ∀ m, ∀ i : Idx n,
        futureCountNat i = m → 0 ≤ sectionPhaseTwoBudgetValue I ℓ i lam := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro i hi
        by_cases hilast : i = lastIdx n
        · subst hilast
          simpa [sectionPhaseTwoBudgetValue_last] using
            Advice.sectionHatGLastValue_nonneg (ℓ := ℓ) hlam
        · have hilt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hilast
          have hsuc_lt : futureCountNat (succIdx i hilt) < m := by
            rw [← hi]
            exact ProfileData.futureCountNat_lt_of_lt (lt_succIdx i hilt)
          have hsuc_nonneg : 0 ≤ sectionPhaseTwoBudgetValue I ℓ (succIdx i hilt) lam :=
            ih (futureCountNat (succIdx i hilt)) hsuc_lt (succIdx i hilt) rfl
          have hafter_nonneg : 0 ≤ sectionPhaseTwoAfterBudgetValue I ℓ i lam := by
            rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam hilt]
            exact hsuc_nonneg
          have htau_nonneg : 0 ≤ I.program.tau := I.program.tau_nonneg_of_one_le_Mcoeff hγlo
          have hsum_nonneg : 0 ≤ sectionPhaseTwoAfterBudgetValue I ℓ i lam + I.program.tau := by
            linarith
          have hfactor_ge_one : 1 ≤ sectionPhaseTwoFactor I ℓ i lam :=
            sectionPhaseTwoFactor_one_le (I := I) ℓ i hilt
          have hsum_le_mul :
              sectionPhaseTwoAfterBudgetValue I ℓ i lam + I.program.tau ≤
                (sectionPhaseTwoAfterBudgetValue I ℓ i lam + I.program.tau) *
                  sectionPhaseTwoFactor I ℓ i lam := by
            nlinarith
          rw [sectionPhaseTwoBudgetValue_step (I := I) ℓ i lam hilt]
          linarith
  exact hmain (futureCountNat i) i rfl

theorem sectionPhaseTwoBudgetValue_monotone_in_lam [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ i : Idx n) {lam₁ lam₂ : ℝ} (hlam₁ : 0 ≤ lam₁) (hlam : lam₁ ≤ lam₂) :
    sectionPhaseTwoBudgetValue I ℓ i lam₁ ≤ sectionPhaseTwoBudgetValue I ℓ i lam₂ := by
  have hmain :
      ∀ m, ∀ i : Idx n,
        futureCountNat i = m →
          sectionPhaseTwoBudgetValue I ℓ i lam₁ ≤
            sectionPhaseTwoBudgetValue I ℓ i lam₂ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro i hi
        by_cases hilast : i = lastIdx n
        · subst hilast
          simpa [sectionPhaseTwoBudgetValue_last] using
            Advice.sectionHatGLastValue_monotone_in_lam (ℓ := ℓ) hlam
        · have hilt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hilast
          have hsuc_lt : futureCountNat (succIdx i hilt) < m := by
            rw [← hi]
            exact ProfileData.futureCountNat_lt_of_lt (lt_succIdx i hilt)
          have hsuc_mono :
              sectionPhaseTwoBudgetValue I ℓ (succIdx i hilt) lam₁ ≤
                sectionPhaseTwoBudgetValue I ℓ (succIdx i hilt) lam₂ :=
            ih (futureCountNat (succIdx i hilt)) hsuc_lt (succIdx i hilt) rfl
          have hafter_mono :
              sectionPhaseTwoAfterBudgetValue I ℓ i lam₁ ≤
                sectionPhaseTwoAfterBudgetValue I ℓ i lam₂ := by
            rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam₁ hilt,
              sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam₂ hilt]
            exact hsuc_mono
          have hafter_nonneg :
              0 ≤ sectionPhaseTwoAfterBudgetValue I ℓ i lam₁ := by
            rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam₁ hilt]
            exact sectionPhaseTwoBudgetValue_nonneg (I := I) hγlo ℓ (succIdx i hilt) hlam₁
          have htau_nonneg : 0 ≤ I.program.tau := I.program.tau_nonneg_of_one_le_Mcoeff hγlo
          have hsum_nonneg :
              0 ≤ sectionPhaseTwoAfterBudgetValue I ℓ i lam₁ + I.program.tau := by
            linarith
          have hsum_mono :
              sectionPhaseTwoAfterBudgetValue I ℓ i lam₁ + I.program.tau ≤
                sectionPhaseTwoAfterBudgetValue I ℓ i lam₂ + I.program.tau := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hafter_mono I.program.tau
          have hfactor_mono :
              sectionPhaseTwoFactor I ℓ i lam₁ ≤ sectionPhaseTwoFactor I ℓ i lam₂ :=
            sectionPhaseTwoFactor_monotone_in_lam (I := I) ℓ i hilt hlam
          have hfactor_nonneg₁ :
              0 ≤ sectionPhaseTwoFactor I ℓ i lam₁ := by
            have hge := sectionPhaseTwoFactor_one_le (I := I) ℓ i (lam := lam₁) hilt
            linarith
          have hfactor_nonneg :
              0 ≤ sectionPhaseTwoFactor I ℓ i lam₂ := by
            have hge := sectionPhaseTwoFactor_one_le (I := I) ℓ i (lam := lam₂) hilt
            linarith
          rw [sectionPhaseTwoBudgetValue_step (I := I) ℓ i lam₁ hilt,
            sectionPhaseTwoBudgetValue_step (I := I) ℓ i lam₂ hilt]
          have hmul :
              (sectionPhaseTwoAfterBudgetValue I ℓ i lam₁ + I.program.tau) *
                  sectionPhaseTwoFactor I ℓ i lam₁ ≤
                (sectionPhaseTwoAfterBudgetValue I ℓ i lam₂ + I.program.tau) *
                  sectionPhaseTwoFactor I ℓ i lam₂ := by
            nlinarith
          linarith
  exact hmain (futureCountNat i) i rfl

theorem sectionPhaseTwoAfterBudgetValue_monotone_in_lam [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ i : Idx n) {lam₁ lam₂ : ℝ} (hlam₁ : 0 ≤ lam₁) (hlam : lam₁ ≤ lam₂) :
    sectionPhaseTwoAfterBudgetValue I ℓ i lam₁ ≤
      sectionPhaseTwoAfterBudgetValue I ℓ i lam₂ := by
  by_cases hi : i = lastIdx n
  · simp [sectionPhaseTwoAfterBudgetValue, hi]
  · have hlt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hi
    rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam₁ hlt,
      sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam₂ hlt]
    exact sectionPhaseTwoBudgetValue_monotone_in_lam
      (I := I) hγlo ℓ (succIdx i hlt) hlam₁ hlam

theorem sectionMuDValue_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (j : Idx n) :
    Advice.sectionMuDValue I ℓ j 1 =
      Advice.sectionMuDValue I (succIdx ℓ hℓ) j 0 := by
  by_cases hlt : ℓ < I.firstBidTime j
  · have hsucc : succIdx ℓ hℓ ≤ I.firstBidTime j := (succIdx_le_iff hℓ).2 hlt
    have hold : Advice.sectionMuDValue I ℓ j 1 = 1 := by
      simp [Advice.sectionMuDValue, hlt]
    by_cases hfront : I.firstBidTime j = succIdx ℓ hℓ
    · by_cases hlast : succIdx ℓ hℓ = lastIdx n
      · rw [hold]
        simp [Advice.sectionMuDValue, hfront, hlast]
      · rw [hold]
        simp [Advice.sectionMuDValue, hfront, hlast, sectionMuValue_zero_eq_one]
    · have hfrontgt : succIdx ℓ hℓ < I.firstBidTime j := lt_of_le_of_ne hsucc (Ne.symm hfront)
      rw [hold]
      simp [Advice.sectionMuDValue, hfrontgt]
  · have hle : I.firstBidTime j ≤ ℓ := not_lt.mp hlt
    by_cases hfront : I.firstBidTime j = ℓ
    · have hnewlt : I.firstBidTime j < succIdx ℓ hℓ := by
        rw [hfront]
        exact lt_succIdx ℓ hℓ
      have hnotgt : ¬ succIdx ℓ hℓ < I.firstBidTime j := not_lt.mpr (le_of_lt hnewlt)
      have hneq : I.firstBidTime j ≠ succIdx ℓ hℓ := ne_of_lt hnewlt
      rw [Advice.sectionMuDValue, if_neg hlt, if_pos hfront]
      rw [Advice.sectionMuDValue, if_neg hnotgt, if_neg hneq]
      simp [ne_of_lt hℓ, sectionMuValue_one_eq_zero]
    · have holdlt : I.firstBidTime j < ℓ := lt_of_le_of_ne hle hfront
      have hnewlt : I.firstBidTime j < succIdx ℓ hℓ := by
        exact lt_of_lt_of_le holdlt (le_of_lt (lt_succIdx ℓ hℓ))
      have hnotgt : ¬ succIdx ℓ hℓ < I.firstBidTime j := not_lt.mpr (le_of_lt hnewlt)
      have hneq : I.firstBidTime j ≠ succIdx ℓ hℓ := ne_of_lt hnewlt
      simp [Advice.sectionMuDValue, hlt, hfront, hnotgt, hneq]

theorem sectionPhaseTwoFactor_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (j : Idx n) :
    sectionPhaseTwoFactor I ℓ j 1 =
      sectionPhaseTwoFactor I (succIdx ℓ hℓ) j 0 := by
  unfold sectionPhaseTwoFactor
  rw [sectionMuDValue_endpoint_eq (I := I) hℓ j]

theorem sectionPhaseTwoBudgetValue_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (i : Idx n) :
    sectionPhaseTwoBudgetValue I ℓ i 1 =
      sectionPhaseTwoBudgetValue I (succIdx ℓ hℓ) i 0 := by
  unfold sectionPhaseTwoBudgetValue
  have hrightLast : Advice.sectionHatGLastValue ℓ 1 = 0 := by
    simp [Advice.sectionHatGLastValue, ne_of_lt hℓ]
  have hleftLast : Advice.sectionHatGLastValue (succIdx ℓ hℓ) 0 = 0 := by
    by_cases hlast : succIdx ℓ hℓ = lastIdx n
    · simp [Advice.sectionHatGLastValue, hlast]
    · simp [Advice.sectionHatGLastValue, hlast]
  rw [hrightLast, hleftLast]
  congr 1
  congr 1
  refine Finset.prod_congr rfl ?_
  intro j hj
  exact sectionPhaseTwoFactor_endpoint_eq (I := I) hℓ j

theorem sectionPhaseTwoAfterBudgetValue_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (i : Idx n) :
    sectionPhaseTwoAfterBudgetValue I ℓ i 1 =
      sectionPhaseTwoAfterBudgetValue I (succIdx ℓ hℓ) i 0 := by
  by_cases hi : i = lastIdx n
  · simp [sectionPhaseTwoAfterBudgetValue, hi]
  · have hlt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hi
    rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i 1 hlt,
      sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) (succIdx ℓ hℓ) i 0 hlt]
    exact sectionPhaseTwoBudgetValue_endpoint_eq (I := I) hℓ (succIdx i hlt)

theorem sectionPhaseTwoHatG2Value_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (i : Idx n) :
    sectionPhaseTwoHatG2Value I ℓ i 1 =
      sectionPhaseTwoHatG2Value I (succIdx ℓ hℓ) i 0 := by
  unfold sectionPhaseTwoHatG2Value
  rw [sectionPhaseTwoBudgetValue_endpoint_eq (I := I) hℓ i,
    sectionPhaseTwoAfterBudgetValue_endpoint_eq (I := I) hℓ i]

theorem sectionZValue_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (t2 : Idx n) :
    sectionZValue I ℓ t2 1 =
      sectionZValue I (succIdx ℓ hℓ) t2 0 := by
  unfold sectionZValue
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [sectionPhaseTwoBudgetValue_endpoint_eq (I := I) hℓ j,
    sectionMuDValue_endpoint_eq (I := I) hℓ j]

theorem sectionPhaseTwoHatG2Value_eq_zero_of_frontier_lt [NeZero n]
    {ℓ i : Idx n} {lam : ℝ} (hℓi : ℓ < i) :
    sectionPhaseTwoHatG2Value I ℓ i lam = 0 := by
  unfold sectionPhaseTwoHatG2Value
  rw [sectionPhaseTwoBudgetValue_eq_zero_of_frontier_lt (I := I) hℓi,
    sectionPhaseTwoAfterBudgetValue_eq_zero_of_frontier_le (I := I) hℓi.le]
  ring_nf

theorem sectionPhaseTwoHatG2Value_eq_step [NeZero n]
    (ℓ i : Idx n) (lam : ℝ) (hi : i ≤ ℓ) :
    sectionPhaseTwoHatG2Value I ℓ i lam =
      if i = lastIdx n ∧ ℓ = lastIdx n then
        Advice.sectionHatGLastValue ℓ lam
      else
        (1 - Advice.sectionMuDValue I ℓ i lam) *
          (sectionPhaseTwoAfterBudgetValue I ℓ i lam + I.program.tau) / futureCount i := by
  by_cases hspecial : i = lastIdx n ∧ ℓ = lastIdx n
  · rcases hspecial with ⟨rfl, rfl⟩
    simp [sectionPhaseTwoHatG2Value_last]
  · have hilt : i < lastIdx n := by
      have hilast : i ≠ lastIdx n := by
        intro hii
        apply hspecial
        exact ⟨hii, le_antisymm (le_lastIdx ℓ) (hii ▸ hi)⟩
      exact lt_of_le_of_ne (le_lastIdx i) hilast
    rw [if_neg hspecial, sectionPhaseTwoHatG2Value,
      sectionPhaseTwoBudgetValue_step (I := I) ℓ i lam hilt]
    unfold sectionPhaseTwoFactor
    have hjval : i.1 < Nat.pred n := Fin.lt_def.mp hilt
    have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
    have hsucc : i.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt hjval) hpredlt
    have hfcne : futureCount i ≠ 0 := by
      exact ne_of_gt (by
        unfold futureCount futureCountNat
        exact_mod_cast Nat.sub_pos_of_lt hsucc)
    field_simp [hfcne]
    ring_nf

theorem sectionPhaseTwoBudgetValue_lt_at_predecessor_of_max_belowThresholdNononeSet [NeZero n]
    (hγ : 1 < I.program.Mcoeff)
    {ℓ t1 k : Idx n} {lam : ℝ}
    (hlam : 0 ≤ lam)
    {hne : (Advice.belowThresholdNononeSet I ℓ t1 lam).Nonempty}
    (hk : (Advice.belowThresholdNononeSet I ℓ t1 lam).max' hne = k)
    (hkt1 : k < t1) :
    sectionPhaseTwoBudgetValue I ℓ t1 lam <
      sectionPhaseTwoBudgetValue I ℓ k lam := by
  have hk_mem : k ∈ Advice.belowThresholdNononeSet I ℓ t1 lam := by
    rw [← hk]
    exact Finset.max'_mem _ _
  have hμlt : Advice.sectionMuDValue I ℓ k lam < 1 :=
    (Advice.mem_belowThresholdNononeSet_iff (I := I)).1 hk_mem |>.2
  have hkleℓ : k ≤ ℓ := Advice.le_section_of_sectionMuD_lt_one I hμlt
  have hklt : k < lastIdx n := lt_of_lt_of_le hkt1 (le_lastIdx t1)
  have hhat_pos : 0 < Advice.sectionPhaseTwoHatG2Value I ℓ k lam := by
    rw [sectionPhaseTwoHatG2Value_eq_step (I := I) ℓ k lam hkleℓ]
    have hspecial : ¬ (k = lastIdx n ∧ ℓ = lastIdx n) := by
      intro hs
      exact hklt.ne hs.1
    rw [if_neg hspecial]
    have hafter_eq :
        sectionPhaseTwoAfterBudgetValue I ℓ k lam =
          sectionPhaseTwoBudgetValue I ℓ t1 lam :=
      Advice.sectionPhaseTwoAfterBudgetValue_eq_budget_of_between_max_belowThresholdNononeSet
        (I := I) hk hkt1
    have h1μ : 0 < 1 - Advice.sectionMuDValue I ℓ k lam := by
      linarith
    have hafter_nonneg :
        0 ≤ sectionPhaseTwoAfterBudgetValue I ℓ k lam := by
      rw [hafter_eq]
      exact sectionPhaseTwoBudgetValue_nonneg (I := I) (le_of_lt hγ) ℓ t1 hlam
    have hτ : 0 < I.program.tau := by
      dsimp [DualProgram.tau, DualProgram.epsilon, DualProgram.Mcoeffmone]
      nlinarith
    have hsum_pos :
        0 < sectionPhaseTwoAfterBudgetValue I ℓ k lam + I.program.tau := by
      linarith
    have hfc_pos : 0 < futureCount k := by
      unfold futureCount futureCountNat
      have hjval : k.1 < Nat.pred n := Fin.lt_def.mp hklt
      have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
      have hsucc : k.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt hjval) hpredlt
      exact_mod_cast Nat.sub_pos_of_lt hsucc
    have hnum_pos :
        0 < (1 - Advice.sectionMuDValue I ℓ k lam) *
          (sectionPhaseTwoAfterBudgetValue I ℓ k lam + I.program.tau) :=
      mul_pos h1μ hsum_pos
    exact div_pos hnum_pos hfc_pos
  have hafter_eq :
      Advice.sectionPhaseTwoAfterBudgetValue I ℓ k lam =
        Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam :=
    Advice.sectionPhaseTwoAfterBudgetValue_eq_budget_of_between_max_belowThresholdNononeSet
      (I := I) hk hkt1
  have hhat_eq :
      Advice.sectionPhaseTwoHatG2Value I ℓ k lam =
        Advice.sectionPhaseTwoBudgetValue I ℓ k lam -
          Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam := by
    rw [Advice.sectionPhaseTwoHatG2Value, hafter_eq]
  linarith [hhat_pos, hhat_eq]

theorem sectionPhaseTwoHatG2Value_eq_zero_of_muD_eq_one [NeZero n]
    (ℓ i : Idx n) {lam : ℝ} (hi : i ≤ ℓ)
    (hμ : Advice.sectionMuDValue I ℓ i lam = 1)
    (hlast : i ≠ lastIdx n) :
    sectionPhaseTwoHatG2Value I ℓ i lam = 0 := by
  rw [sectionPhaseTwoHatG2Value_eq_step (I := I) ℓ i lam hi]
  have hspecial : ¬ (i = lastIdx n ∧ ℓ = lastIdx n) := by
    intro hs
    exact hlast hs.1
  rw [if_neg hspecial, hμ]
  ring

theorem sectionPhaseTwoHatG2Value_eq_zero_of_between_max_belowThresholdNononeSet [NeZero n]
    (ℓ t1 k i : Idx n) {lam : ℝ}
    {hne : (Advice.belowThresholdNononeSet I ℓ t1 lam).Nonempty}
    (hiℓ : i ≤ ℓ)
    (hk : (Advice.belowThresholdNononeSet I ℓ t1 lam).max' hne = k)
    (hki : k < i) (hit1 : i < t1) :
    sectionPhaseTwoHatG2Value I ℓ i lam = 0 := by
  have hμ :
      Advice.sectionMuDValue I ℓ i lam = 1 :=
    Advice.sectionMuDValue_eq_one_of_between_max_belowThresholdNononeSet
      I hk hki hit1
  have hlast : i ≠ lastIdx n := ne_of_lt (lt_of_lt_of_le hit1 (le_lastIdx t1))
  exact sectionPhaseTwoHatG2Value_eq_zero_of_muD_eq_one
    (I := I) ℓ i hiℓ hμ hlast

theorem sectionPhaseTwoHatG2Value_nonneg [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ i : Idx n) {lam : ℝ} (hlam : 0 ≤ lam ∧ lam ≤ 1) :
    0 ≤ sectionPhaseTwoHatG2Value I ℓ i lam := by
  by_cases hi : i ≤ ℓ
  · rw [sectionPhaseTwoHatG2Value_eq_step (I := I) ℓ i lam hi]
    by_cases hspecial : i = lastIdx n ∧ ℓ = lastIdx n
    · rcases hspecial with ⟨rfl, rfl⟩
      simpa using Advice.sectionHatGLastValue_nonneg (ℓ := lastIdx n) hlam.1
    · rw [if_neg hspecial]
      have hmu : 0 ≤ 1 - Advice.sectionMuDValue I ℓ i lam := by
        have hle : Advice.sectionMuDValue I ℓ i lam ≤ 1 :=
          Advice.sectionMuDValue_le_one I ℓ i lam
        linarith
      have hilt : i < lastIdx n := by
        have hilast : i ≠ lastIdx n := by
          intro hii
          apply hspecial
          exact ⟨hii, le_antisymm (le_lastIdx ℓ) (hii ▸ hi)⟩
        exact lt_of_le_of_ne (le_lastIdx i) hilast
      have hafter : 0 ≤ sectionPhaseTwoAfterBudgetValue I ℓ i lam := by
        rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam hilt]
        exact sectionPhaseTwoBudgetValue_nonneg (I := I) hγlo ℓ (succIdx i hilt) hlam.1
      have htau : 0 ≤ I.program.tau := I.program.tau_nonneg_of_one_le_Mcoeff hγlo
      have hsum : 0 ≤ sectionPhaseTwoAfterBudgetValue I ℓ i lam + I.program.tau := by
        linarith
      have hjval : i.1 < Nat.pred n := Fin.lt_def.mp hilt
      have hpredlt : Nat.pred n < n := Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
      have hsucc : i.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt hjval) hpredlt
      have hfc : 0 ≤ futureCount i := by
        unfold futureCount futureCountNat
        exact_mod_cast Nat.zero_le (n - i.1.succ)
      exact div_nonneg (mul_nonneg hmu hsum) hfc
  · have hℓi : ℓ < i := lt_of_not_ge hi
    simp [sectionPhaseTwoHatG2Value_eq_zero_of_frontier_lt (I := I) hℓi]

/-- The explicit section Phase-2 profile has the expected closed-form prefix budgets. -/
theorem beforeBudget_eq_sectionPhaseTwoBudgetValue_explicit [NeZero n]
    (ℓ : Idx n) (lam : ℝ) :
    ∀ i : Idx n,
      beforeBudget (fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam) i =
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam := by
  have hmain : ∀ m, ∀ i : Idx n, futureCountNat i = m →
      beforeBudget (fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam) i =
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro i hi
        by_cases hℓi : ℓ < i
        · unfold beforeBudget
          rw [Finset.sum_eq_zero]
          · symm
            exact Advice.sectionPhaseTwoBudgetValue_eq_zero_of_frontier_lt (I := I) hℓi
          · intro j hj
            exact Advice.sectionPhaseTwoHatG2Value_eq_zero_of_frontier_lt (I := I)
              (lt_of_lt_of_le hℓi (mem_suffixRange.mp hj))
        · by_cases hilast : i = lastIdx n
          · subst hilast
            rw [beforeBudget_eq_self_add_tail]
            have htail :
                tailBudget (fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam)
                  (lastIdx n) = 0 := by
              unfold tailBudget
              rw [show strictSuffixRange (lastIdx n) = (∅ : Finset (Idx n)) by
                ext j
                simp [mem_strictSuffixRange, not_lt.mpr (le_lastIdx j)]]
              simp
            rw [htail, Advice.sectionPhaseTwoHatG2Value_last,
              Advice.sectionPhaseTwoBudgetValue_last]
            simp
          · have hilt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hilast
            calc
              beforeBudget (fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam) i
                  =
                Advice.sectionPhaseTwoHatG2Value I ℓ i lam +
                  tailBudget (fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam) i := by
                    rw [beforeBudget_eq_self_add_tail]
              _ =
                Advice.sectionPhaseTwoHatG2Value I ℓ i lam +
                  beforeBudget (fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam)
                    (succIdx i hilt) := by
                    rw [tailBudget_eq_beforeBudget_succ
                      (hatG := fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam) hilt]
              _ =
                Advice.sectionPhaseTwoHatG2Value I ℓ i lam +
                  Advice.sectionPhaseTwoBudgetValue I ℓ (succIdx i hilt) lam := by
                    have hsuc_lt : futureCountNat (succIdx i hilt) < m := by
                      rw [← hi]
                      exact ProfileData.futureCountNat_lt_of_lt (lt_succIdx i hilt)
                    rw [ih (futureCountNat (succIdx i hilt)) hsuc_lt (succIdx i hilt) rfl]
              _ = Advice.sectionPhaseTwoBudgetValue I ℓ i lam := by
                    unfold Advice.sectionPhaseTwoHatG2Value
                    rw [Advice.sectionPhaseTwoAfterBudgetValue_eq_budget_succ
                      (I := I) ℓ i lam hilt]
                    ring
  intro i
  exact hmain (futureCountNat i) i rfl

theorem tailBudget_eq_sectionPhaseTwoAfterBudgetValue_explicit [NeZero n]
    (ℓ i : Idx n) (lam : ℝ) :
    tailBudget (fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam) i =
      Advice.sectionPhaseTwoAfterBudgetValue I ℓ i lam := by
  by_cases hi : i = lastIdx n
  · subst hi
    unfold tailBudget
    rw [show strictSuffixRange (lastIdx n) = (∅ : Finset (Idx n)) by
      ext j
      simp [mem_strictSuffixRange, not_lt.mpr (le_lastIdx j)]]
    simp [Advice.sectionPhaseTwoAfterBudgetValue]
  · have hlt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hi
    rw [tailBudget_eq_beforeBudget_succ
      (hatG := fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam) hlt,
      beforeBudget_eq_sectionPhaseTwoBudgetValue_explicit (I := I) ℓ lam (succIdx i hlt)]
    exact (Advice.sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam hlt).symm

/-- Explicit Phase-2 execution for the section advice `Γ^ℓ(λ)`. -/
noncomputable def sectionPhaseTwoData [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ : Idx n) (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1) :
    PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam) where
  hatG2 := fun i => Advice.sectionPhaseTwoHatG2Value I ℓ i lam
  zero_above_t3 := by
    intro i hi
    exact Advice.sectionPhaseTwoHatG2Value_eq_zero_of_frontier_lt (I := I) hi
  hatG2_nonneg := by
    intro i
    exact Advice.sectionPhaseTwoHatG2Value_nonneg (I := I) hγlo ℓ i hlam
  step_eq := by
    intro i hi
    have hstep := Advice.sectionPhaseTwoHatG2Value_eq_step (I := I) ℓ i lam hi
    simpa [Advice.sectionAdvice,
      Advice.sectionMuDValue_eq (I := I) (ℓ := ℓ) (j := i) (lam := lam) hlam,
      Advice.sectionHatGLastValue_eq (I := I) (ℓ := ℓ) (lam := lam) hlam,
      Advice.tailBudget_eq_sectionPhaseTwoAfterBudgetValue_explicit (I := I) ℓ i lam]
      using hstep

namespace PhaseTwoData

variable {I : ProcedureInput n} {Γ : Advice I}

@[simp] theorem afterBudget_last [NeZero n] (Ξ : PhaseTwoData I Γ) :
    Ξ.afterBudget (lastIdx n) = 0 := by
  unfold PhaseTwoData.afterBudget tailBudget
  have hempty : strictSuffixRange (lastIdx n) = (∅ : Finset (Idx n)) := by
    ext i
    simp [mem_strictSuffixRange, not_lt.mpr (le_lastIdx i)]
  rw [hempty, Finset.sum_empty]

theorem afterBudget_eq_beforeBudget_succ [NeZero n] (Ξ : PhaseTwoData I Γ) {i : Idx n}
    (hi : i < lastIdx n) :
    Ξ.afterBudget i = Ξ.beforeBudget (succIdx i hi) := by
  unfold PhaseTwoData.afterBudget PhaseTwoData.beforeBudget tailBudget KMedian195.beforeBudget
  have hrange : strictSuffixRange i = suffixRange (succIdx i hi) := by
    ext j
    simp [mem_strictSuffixRange, mem_suffixRange, succIdx_le_iff hi]
  rw [hrange]

theorem beforeBudget_ge_barTau_of_t1?_eq_some
    [NeZero n]
    (Ξ : PhaseTwoData I Γ) {t1 : Idx n}
    (ht1 : Ξ.t1? = some t1) :
    I.program.barTau ≤ Ξ.beforeBudget t1 := by
  have hne : Ξ.t1Candidates.Nonempty := by
    unfold PhaseTwoData.t1? finsetMax? at ht1
    by_cases h : Ξ.t1Candidates.Nonempty
    · exact h
    · simp [h] at ht1
  have hmax :
      Ξ.t1Candidates.max' hne = t1 := by
    have : some (Ξ.t1Candidates.max' hne) = some t1 := by
      simpa [PhaseTwoData.t1?, finsetMax?, hne] using ht1
    exact Option.some.inj this
  have hmem : t1 ∈ Ξ.t1Candidates := by
    simpa [hmax] using (Finset.max'_mem Ξ.t1Candidates hne)
  simpa [PhaseTwoData.t1Candidates] using (Finset.mem_filter.mp hmem).2

theorem beforeBudget_lt_barTau_of_t1?_eq_some_of_lt
    [NeZero n]
    (Ξ : PhaseTwoData I Γ) {t1 i : Idx n}
    (ht1 : Ξ.t1? = some t1)
    (hti : t1 < i) :
    Ξ.beforeBudget i < I.program.barTau := by
  have hne : Ξ.t1Candidates.Nonempty := by
    unfold PhaseTwoData.t1? finsetMax? at ht1
    by_cases h : Ξ.t1Candidates.Nonempty
    · exact h
    · simp [h] at ht1
  have hmax :
      Ξ.t1Candidates.max' hne = t1 := by
    have : some (Ξ.t1Candidates.max' hne) = some t1 := by
      simpa [PhaseTwoData.t1?, finsetMax?, hne] using ht1
    exact Option.some.inj this
  have hnotmem : i ∉ Ξ.t1Candidates := by
    intro himem
    have himax : i ≤ Ξ.t1Candidates.max' hne := Finset.le_max' _ _ himem
    have : i ≤ t1 := by simpa [hmax] using himax
    exact not_le_of_gt hti this
  have hnotge : ¬ I.program.barTau ≤ Ξ.beforeBudget i := by
    intro hge
    apply hnotmem
    rw [PhaseTwoData.t1Candidates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩
  linarith

theorem beforeBudget_ge_theta_of_t2?_eq_some
    [NeZero n]
    (Ξ : PhaseTwoData I Γ) {t2 : Idx n}
    (ht2 : Ξ.t2? = some t2) :
    I.program.theta ≤ Ξ.beforeBudget t2 := by
  have hne : Ξ.t2Candidates.Nonempty := by
    unfold PhaseTwoData.t2? finsetMax? at ht2
    by_cases h : Ξ.t2Candidates.Nonempty
    · exact h
    · simp [h] at ht2
  have hmax :
      Ξ.t2Candidates.max' hne = t2 := by
    have : some (Ξ.t2Candidates.max' hne) = some t2 := by
      simpa [PhaseTwoData.t2?, finsetMax?, hne] using ht2
    exact Option.some.inj this
  have hmem : t2 ∈ Ξ.t2Candidates := by
    simpa [hmax] using (Finset.max'_mem Ξ.t2Candidates hne)
  simpa [PhaseTwoData.t2Candidates] using (Finset.mem_filter.mp hmem).2

theorem beforeBudget_lt_theta_of_t2?_eq_some_of_lt
    [NeZero n]
    (Ξ : PhaseTwoData I Γ) {t2 i : Idx n}
    (ht2 : Ξ.t2? = some t2)
    (hti : t2 < i) :
    Ξ.beforeBudget i < I.program.theta := by
  have hne : Ξ.t2Candidates.Nonempty := by
    unfold PhaseTwoData.t2? finsetMax? at ht2
    by_cases h : Ξ.t2Candidates.Nonempty
    · exact h
    · simp [h] at ht2
  have hmax :
      Ξ.t2Candidates.max' hne = t2 := by
    have : some (Ξ.t2Candidates.max' hne) = some t2 := by
      simpa [PhaseTwoData.t2?, finsetMax?, hne] using ht2
    exact Option.some.inj this
  have hnotmem : i ∉ Ξ.t2Candidates := by
    intro himem
    have himax : i ≤ Ξ.t2Candidates.max' hne := Finset.le_max' _ _ himem
    have : i ≤ t2 := by simpa [hmax] using himax
    exact not_le_of_gt hti this
  have hnotge : ¬ I.program.theta ≤ Ξ.beforeBudget i := by
    intro hge
    apply hnotmem
    rw [PhaseTwoData.t2Candidates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩
  linarith

theorem t1?_eq_some_of_beforeBudget_ge_barTau_of_above_lt_barTau
    [NeZero n]
    (Ξ : PhaseTwoData I Γ) {t1 : Idx n}
    (ht1_ge : I.program.barTau ≤ Ξ.beforeBudget t1)
    (habove :
      ∀ ⦃i : Idx n⦄, t1 < i → Ξ.beforeBudget i < I.program.barTau) :
    Ξ.t1? = some t1 := by
  have hmem : t1 ∈ Ξ.t1Candidates := by
    rw [PhaseTwoData.t1Candidates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1_ge⟩
  have hne : Ξ.t1Candidates.Nonempty := ⟨t1, hmem⟩
  have hmaxmem : Ξ.t1Candidates.max' hne ∈ Ξ.t1Candidates :=
    Finset.max'_mem (s := Ξ.t1Candidates) hne
  have hmax : Ξ.t1Candidates.max' hne = t1 := by
    apply le_antisymm
    · by_cases hle : Ξ.t1Candidates.max' hne ≤ t1
      · exact hle
      · have ht1lt : t1 < Ξ.t1Candidates.max' hne := lt_of_not_ge hle
        have hlt : Ξ.beforeBudget (Ξ.t1Candidates.max' hne) < I.program.barTau :=
          habove ht1lt
        have hge : I.program.barTau ≤ Ξ.beforeBudget (Ξ.t1Candidates.max' hne) := by
          simpa [PhaseTwoData.t1Candidates] using (Finset.mem_filter.mp hmaxmem).2
        linarith
    · exact Finset.le_max' _ _ hmem
  unfold PhaseTwoData.t1? finsetMax?
  simp [hne, hmax]

theorem t2?_eq_some_of_beforeBudget_ge_theta_of_above_lt_theta
    [NeZero n]
    (Ξ : PhaseTwoData I Γ) {t2 : Idx n}
    (ht2_ge : I.program.theta ≤ Ξ.beforeBudget t2)
    (habove :
      ∀ ⦃i : Idx n⦄, t2 < i → Ξ.beforeBudget i < I.program.theta) :
    Ξ.t2? = some t2 := by
  have hmem : t2 ∈ Ξ.t2Candidates := by
    rw [PhaseTwoData.t2Candidates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht2_ge⟩
  have hne : Ξ.t2Candidates.Nonempty := ⟨t2, hmem⟩
  have hmaxmem : Ξ.t2Candidates.max' hne ∈ Ξ.t2Candidates :=
    Finset.max'_mem (s := Ξ.t2Candidates) hne
  have hmax : Ξ.t2Candidates.max' hne = t2 := by
    apply le_antisymm
    · by_cases hle : Ξ.t2Candidates.max' hne ≤ t2
      · exact hle
      · have ht2lt : t2 < Ξ.t2Candidates.max' hne := lt_of_not_ge hle
        have hlt : Ξ.beforeBudget (Ξ.t2Candidates.max' hne) < I.program.theta :=
          habove ht2lt
        have hge : I.program.theta ≤ Ξ.beforeBudget (Ξ.t2Candidates.max' hne) := by
          simpa [PhaseTwoData.t2Candidates] using (Finset.mem_filter.mp hmaxmem).2
        linarith
    · exact Finset.le_max' _ _ hmem
  unfold PhaseTwoData.t2? finsetMax?
  simp [hne, hmax]

theorem t1_le_t2_of_some
    [NeZero n]
    (Ξ : PhaseTwoData I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (ht1 : Ξ.t1? = some t1)
    (ht2 : Ξ.t2? = some t2) :
    t1 ≤ t2 := by
  have ht1bar : I.program.barTau ≤ Ξ.beforeBudget t1 :=
    PhaseTwoData.beforeBudget_ge_barTau_of_t1?_eq_some Ξ ht1
  have ht1theta : I.program.theta ≤ Ξ.beforeBudget t1 := by
    exact le_trans (I.program.theta_le_barTau_of_le_153_div_125 hγlo hγhi) ht1bar
  have hmem : t1 ∈ Ξ.t2Candidates := by
    rw [PhaseTwoData.t2Candidates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1theta⟩
  have hne : Ξ.t2Candidates.Nonempty := by
    unfold PhaseTwoData.t2? finsetMax? at ht2
    by_cases h : Ξ.t2Candidates.Nonempty
    · exact h
    · simp [h] at ht2
  have hmax :
      Ξ.t2Candidates.max' hne = t2 := by
    have : some (Ξ.t2Candidates.max' hne) = some t2 := by
      simpa [PhaseTwoData.t2?, finsetMax?, hne] using ht2
    exact Option.some.inj this
  have hle : t1 ≤ Ξ.t2Candidates.max' hne := Finset.le_max' _ _ hmem
  simpa [hmax] using hle

theorem beforeBudget_eq_zero_of_frontier_lt
    [NeZero n]
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam)) {i : Idx n} (hℓi : ℓ < i) :
    Ξ.beforeBudget i = 0 := by
  unfold PhaseTwoData.beforeBudget KMedian195.beforeBudget
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hij : i ≤ j := mem_suffixRange.mp hj
  have hℓj : ℓ < j := lt_of_lt_of_le hℓi hij
  simpa [Advice.sectionAdvice] using Ξ.zero_above_t3 hℓj

theorem beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
    [NeZero n]
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam)) :
    ∀ i : Idx n, Ξ.beforeBudget i = Advice.sectionPhaseTwoBudgetValue I ℓ i lam := by
  have hmain : ∀ m, ∀ i : Idx n, futureCountNat i = m →
      Ξ.beforeBudget i = Advice.sectionPhaseTwoBudgetValue I ℓ i lam := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro i hi
        by_cases hℓi : ℓ < i
        · rw [beforeBudget_eq_zero_of_frontier_lt (Ξ := Ξ) (hlam := hlam) hℓi]
          symm
          exact Advice.sectionPhaseTwoBudgetValue_eq_zero_of_frontier_lt (I := I) hℓi
        · by_cases hlast : i = lastIdx n
          · subst hlast
            have hℓlast : ℓ = lastIdx n := le_antisymm (le_lastIdx ℓ) (not_lt.mp hℓi)
            have hbefore :
                Ξ.beforeBudget (lastIdx n) = Ξ.hatG2 (lastIdx n) := by
              rw [Ξ.beforeBudget_eq_self_add_afterBudget, afterBudget_last (Ξ := Ξ)]
              ring
            have hstep :
                Ξ.hatG2 (lastIdx n) = Advice.sectionHatGLastValue ℓ lam := by
              have hlast_le : lastIdx n ≤ (Advice.sectionAdvice I ℓ lam hlam).t3Star := by
                simp [Advice.sectionAdvice, hℓlast]
              simpa [Advice.sectionAdvice, hℓlast, Advice.sectionHatGLastValue] using
                Ξ.step_eq (lastIdx n) hlast_le
            rw [hbefore, hstep]
            rw [Advice.sectionPhaseTwoBudgetValue_last (I := I) ℓ lam]
          · have hilt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hlast
            have hiℓ : i ≤ ℓ := not_lt.mp hℓi
            have hsucc :
                Ξ.beforeBudget (succIdx i hilt) =
                  Advice.sectionPhaseTwoBudgetValue I ℓ (succIdx i hilt) lam := by
              apply ih (futureCountNat (succIdx i hilt))
              · simpa [hi] using ProfileData.futureCountNat_lt_of_lt (lt_succIdx i hilt)
              · rfl
            have hafter :
                Ξ.afterBudget i = Advice.sectionPhaseTwoAfterBudgetValue I ℓ i lam := by
              rw [afterBudget_eq_beforeBudget_succ (Ξ := Ξ) hilt,
                Advice.sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam hilt,
                hsucc]
            have hmu :
                (Advice.sectionAdvice I ℓ lam hlam).muD i =
                  Advice.sectionMuDValue I ℓ i lam := by
              simpa using (Advice.sectionMuDValue_eq I ℓ i lam hlam).symm
            have hstep :
                Ξ.hatG2 i =
                  (1 - Advice.sectionMuDValue I ℓ i lam) * (Ξ.afterBudget i + I.program.tau) /
                    futureCount i := by
              have hi_t3 : i ≤ (Advice.sectionAdvice I ℓ lam hlam).t3Star := by
                simpa [Advice.sectionAdvice] using hiℓ
              simpa [PhaseTwoData.afterBudget, hlast, hmu] using Ξ.step_eq i hi_t3
            have hfc_nat : 0 < futureCountNat i := by
              have hipred : i.1 < Nat.pred n := by
                simpa [lastIdx] using! hilt
              have hisucc : i.1.succ ≤ Nat.pred n := Nat.succ_le_of_lt hipred
              have hisucc_lt : i.1.succ < n :=
                lt_of_le_of_lt hisucc (Nat.pred_lt (show n ≠ 0 from NeZero.ne n))
              unfold futureCountNat
              omega
            have hfc : futureCount i ≠ 0 := by
              have hfc' : 0 < futureCount i := by
                unfold futureCount
                exact_mod_cast hfc_nat
              linarith
            have hbudget :
                Advice.sectionPhaseTwoBudgetValue I ℓ i lam =
                  Advice.sectionPhaseTwoAfterBudgetValue I ℓ i lam +
                    (1 - Advice.sectionMuDValue I ℓ i lam) *
                      (Advice.sectionPhaseTwoAfterBudgetValue I ℓ i lam + I.program.tau) /
                      futureCount i := by
              rw [Advice.sectionPhaseTwoBudgetValue_step (I := I) ℓ i lam hilt]
              unfold Advice.sectionPhaseTwoFactor
              field_simp [hfc]
              ring
            calc
              Ξ.beforeBudget i = Ξ.hatG2 i + Ξ.afterBudget i := by
                exact Ξ.beforeBudget_eq_self_add_afterBudget i
              _ =
                  (1 - Advice.sectionMuDValue I ℓ i lam) * (Ξ.afterBudget i + I.program.tau) /
                    futureCount i + Ξ.afterBudget i := by rw [hstep]
              _ =
                  (1 - Advice.sectionMuDValue I ℓ i lam) *
                      (Advice.sectionPhaseTwoAfterBudgetValue I ℓ i lam + I.program.tau) /
                      futureCount i +
                    Advice.sectionPhaseTwoAfterBudgetValue I ℓ i lam := by rw [hafter]
              _ = Advice.sectionPhaseTwoBudgetValue I ℓ i lam := by
                linarith [hbudget]
  intro i
  exact hmain (futureCountNat i) i rfl

theorem afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
    [NeZero n]
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam)) (i : Idx n) :
    Ξ.afterBudget i = Advice.sectionPhaseTwoAfterBudgetValue I ℓ i lam := by
  by_cases hi : i = lastIdx n
  · subst hi
    simp [afterBudget_last (Ξ := Ξ)]
  · have hilt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hi
    rw [afterBudget_eq_beforeBudget_succ (Ξ := Ξ) hilt,
      Advice.sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam hilt]
    exact beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice (Ξ := Ξ) (succIdx i hilt)

theorem hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
    [NeZero n]
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam)) (i : Idx n) :
    Ξ.hatG2 i = Advice.sectionPhaseTwoHatG2Value I ℓ i lam := by
  have hbefore := beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice (Ξ := Ξ) i
  have hafter := afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice (Ξ := Ξ) i
  have hself := Ξ.beforeBudget_eq_self_add_afterBudget i
  unfold Advice.sectionPhaseTwoHatG2Value
  linarith

end PhaseTwoData

/-- The numerator shared by the Phase-1 transition formula. -/
noncomputable def sectionTransitionNumeratorValue [NeZero n] (ℓ i : Idx n) (lam : ℝ) : ℝ :=
  1 - posPart (I.program.theta - sectionPhaseTwoAfterBudgetValue I ℓ (I.firstBidTime i) lam)

theorem continuous_sectionTransitionNumeratorValue [NeZero n] (ℓ i : Idx n) :
    Continuous fun lam : ℝ => sectionTransitionNumeratorValue I ℓ i lam := by
  unfold sectionTransitionNumeratorValue
  exact continuous_const.sub
    (continuous_posPart.comp
      (continuous_const.sub
        (continuous_sectionPhaseTwoAfterBudgetValue I ℓ (I.firstBidTime i))))

theorem sectionTransitionNumeratorValue_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (i : Idx n) :
    sectionTransitionNumeratorValue I ℓ i 1 =
      sectionTransitionNumeratorValue I (succIdx ℓ hℓ) i 0 := by
  unfold sectionTransitionNumeratorValue
  rw [sectionPhaseTwoAfterBudgetValue_endpoint_eq (I := I) hℓ (I.firstBidTime i)]

/--
The paper's Phase-1 transition function
`Φ_i(α, λ) = (1-[θ-R_{f_i}^{(2)}(λ)]^+) / (n-i + α(λ)(1-μ_i^D(λ)) - frac*z(λ))`.
-/
noncomputable def sectionPhiValue [NeZero n]
    (ℓ i : Idx n) (alpha z : ℝ → ℝ) (lam : ℝ) : ℝ :=
  sectionTransitionNumeratorValue I ℓ i lam /
    (futureCount i + alpha lam * (1 - Advice.sectionMuDValue I ℓ i lam) - I.program.frac * z lam)

theorem continuous_sectionPhiValue [NeZero n] (ℓ i : Idx n) (alpha z : ℝ → ℝ)
    (halpha : Continuous alpha) (hz : Continuous z)
    (hdenom :
      ∀ lam,
        futureCount i + alpha lam * (1 - Advice.sectionMuDValue I ℓ i lam) -
          I.program.frac * z lam ≠ 0) :
    Continuous fun lam : ℝ => sectionPhiValue I ℓ i alpha z lam := by
  unfold sectionPhiValue
  refine (continuous_sectionTransitionNumeratorValue I ℓ i).div ?_ hdenom
  exact
    (continuous_const.add
      (halpha.mul (continuous_const.sub (Advice.continuous_sectionMuDValue I ℓ i)))).sub
      (continuous_const.mul hz)

theorem continuousOn_sectionPhiValue [NeZero n] (ℓ i : Idx n) (alpha z : ℝ → ℝ)
    {s : Set ℝ}
    (halpha : ContinuousOn alpha s) (hz : ContinuousOn z s)
    (hdenom :
      ∀ lam ∈ s,
        futureCount i + alpha lam * (1 - Advice.sectionMuDValue I ℓ i lam) -
          I.program.frac * z lam ≠ 0) :
    ContinuousOn (fun lam : ℝ => sectionPhiValue I ℓ i alpha z lam) s := by
  unfold sectionPhiValue
  refine ContinuousOn.div ?_ ?_ hdenom
  · exact (continuous_sectionTransitionNumeratorValue I ℓ i).continuousOn
  · exact
      (continuousOn_const.add
        (halpha.mul
          (continuousOn_const.sub (Advice.continuous_sectionMuDValue I ℓ i).continuousOn))).sub
        (continuousOn_const.mul hz)

/-- The Phase-1 formula with `α = 0`. -/
noncomputable def sectionPhase1HatGValue [NeZero n]
    (ℓ i : Idx n) (z : ℝ → ℝ) (lam : ℝ) : ℝ :=
  (1 - Advice.sectionMuDValue I ℓ i lam) *
    sectionPhiValue I ℓ i (fun _ => 0) z lam

theorem continuous_sectionPhase1HatGValue [NeZero n] (ℓ i : Idx n) (z : ℝ → ℝ)
    (hz : Continuous z)
    (hdenom :
      ∀ lam,
        futureCount i - I.program.frac * z lam ≠ 0) :
    Continuous fun lam : ℝ => sectionPhase1HatGValue I ℓ i z lam := by
  unfold sectionPhase1HatGValue
  refine (continuous_const.sub (Advice.continuous_sectionMuDValue I ℓ i)).mul ?_
  refine continuous_sectionPhiValue I ℓ i (fun _ : ℝ => 0) z ?_ hz ?_
  · simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  · intro lam
    simpa using hdenom lam

theorem continuousOn_sectionPhase1HatGValue [NeZero n] (ℓ i : Idx n) (z : ℝ → ℝ)
    {s : Set ℝ}
    (hz : ContinuousOn z s)
    (hdenom :
      ∀ lam ∈ s,
        futureCount i - I.program.frac * z lam ≠ 0) :
    ContinuousOn (fun lam : ℝ => sectionPhase1HatGValue I ℓ i z lam) s := by
  unfold sectionPhase1HatGValue
  refine (continuousOn_const.sub (Advice.continuous_sectionMuDValue I ℓ i).continuousOn).mul ?_
  refine continuousOn_sectionPhiValue I ℓ i (fun _ : ℝ => 0) z ?_ hz ?_
  · simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) s)
  · intro lam hlam
    simpa using hdenom lam hlam

/-- The boundary interpolation factor `α(λ)` for a fixed threshold `t₁`. -/
noncomputable def sectionBoundaryAlphaValue [NeZero n] (ℓ t1 : Idx n) (lam : ℝ) : ℝ :=
  if _ : t1 = lastIdx n then
    1
  else
    (I.program.barTau - sectionPhaseTwoAfterBudgetValue I ℓ t1 lam) /
      sectionPhaseTwoHatG2Value I ℓ t1 lam

theorem continuous_sectionBoundaryAlphaValue [NeZero n] (ℓ t1 : Idx n)
    (hdenom : ∀ lam, sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0) :
    Continuous fun lam : ℝ => sectionBoundaryAlphaValue I ℓ t1 lam := by
  by_cases ht1 : t1 = lastIdx n
  · simpa [sectionBoundaryAlphaValue, ht1] using
      (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))
  · simpa only [sectionBoundaryAlphaValue, ht1, dite_false] using!
      (continuous_const.sub (continuous_sectionPhaseTwoAfterBudgetValue I ℓ t1)).div
        (continuous_sectionPhaseTwoHatG2Value I ℓ t1) hdenom

theorem continuousOn_sectionBoundaryAlphaValue [NeZero n] (ℓ t1 : Idx n) {s : Set ℝ}
    (hdenom : ∀ lam ∈ s, sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0) :
    ContinuousOn (fun lam : ℝ => sectionBoundaryAlphaValue I ℓ t1 lam) s := by
  by_cases ht1 : t1 = lastIdx n
  · simpa [sectionBoundaryAlphaValue, ht1] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) s)
  · simpa only [sectionBoundaryAlphaValue, ht1, dite_false] using!
      (continuousOn_const.sub
        (continuous_sectionPhaseTwoAfterBudgetValue I ℓ t1).continuousOn).div
        (continuous_sectionPhaseTwoHatG2Value I ℓ t1).continuousOn hdenom

theorem sectionBoundaryAlphaValue_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (t1 : Idx n) :
    sectionBoundaryAlphaValue I ℓ t1 1 =
      sectionBoundaryAlphaValue I (succIdx ℓ hℓ) t1 0 := by
  by_cases ht1 : t1 = lastIdx n
  · simp [sectionBoundaryAlphaValue, ht1]
  · simp [sectionBoundaryAlphaValue, ht1,
      sectionPhaseTwoAfterBudgetValue_endpoint_eq (I := I) hℓ t1,
      sectionPhaseTwoHatG2Value_endpoint_eq (I := I) hℓ t1]

/-- The boundary `B` contribution for a fixed threshold `t₁`. -/
noncomputable def sectionBoundaryHatGBValue [NeZero n] (ℓ t1 : Idx n) (lam : ℝ) : ℝ :=
  if _ : t1 = lastIdx n then
    sectionPhaseTwoHatG2Value I ℓ t1 lam
  else
    I.program.barTau - sectionPhaseTwoAfterBudgetValue I ℓ t1 lam

theorem continuous_sectionBoundaryHatGBValue [NeZero n] (ℓ t1 : Idx n) :
    Continuous fun lam : ℝ => sectionBoundaryHatGBValue I ℓ t1 lam := by
  by_cases ht1 : t1 = lastIdx n
  · simpa [sectionBoundaryHatGBValue, ht1] using!
      continuous_sectionPhaseTwoHatG2Value I ℓ t1
  · simpa [sectionBoundaryHatGBValue, ht1] using!
      (continuous_const.sub (continuous_sectionPhaseTwoAfterBudgetValue I ℓ t1))

theorem sectionBoundaryHatGBValue_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (t1 : Idx n) :
    sectionBoundaryHatGBValue I ℓ t1 1 =
      sectionBoundaryHatGBValue I (succIdx ℓ hℓ) t1 0 := by
  by_cases ht1 : t1 = lastIdx n
  · subst t1
    simpa [sectionBoundaryHatGBValue] using
      (sectionPhaseTwoHatG2Value_endpoint_eq (I := I) hℓ (lastIdx n))
  · simp [sectionBoundaryHatGBValue, ht1,
      sectionPhaseTwoAfterBudgetValue_endpoint_eq (I := I) hℓ t1]

/-- The phase-1 index set `{ i | i < t₁ }` for a fixed boundary threshold. -/
def sectionPhaseOneRange (t1 : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun i => i < t1

omit [NeZero n] in
@[simp] theorem mem_sectionPhaseOneRange {t1 i : Idx n} :
    i ∈ sectionPhaseOneRange t1 ↔ i < t1 := by
  simp [sectionPhaseOneRange]

omit [NeZero n] in
theorem sum_sectionPhaseOne_add_beforeBudget (hatG : Idx n → ℝ) (t1 : Idx n) :
    Finset.sum (sectionPhaseOneRange t1) hatG + beforeBudget hatG t1 = totalBudget hatG := by
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i : Idx n => i < t1) hatG
  have hright : Finset.univ.filter (fun i : Idx n => ¬ i < t1) = suffixRange t1 := by
    ext i
    simp [suffixRange, not_lt]
  simpa [sectionPhaseOneRange, beforeBudget, totalBudget, hright] using! hsplit

/-- The boundary `A` contribution for a fixed threshold `t₁`. -/
noncomputable def sectionBoundaryHatGAValue [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ) (lam : ℝ) : ℝ :=
  if _ : t1 = lastIdx n then
    0
  else
    (1 - sectionBoundaryAlphaValue I ℓ t1 lam) *
      (1 - Advice.sectionMuDValue I ℓ t1 lam) *
      sectionPhiValue I ℓ t1 (sectionBoundaryAlphaValue I ℓ t1) z lam

theorem continuous_sectionBoundaryHatGAValue [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ)
    (hz : Continuous z)
    (halphaDenom : ∀ lam, sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0)
    (hphiDenom :
      ∀ lam,
        futureCount t1 +
            sectionBoundaryAlphaValue I ℓ t1 lam *
              (1 - Advice.sectionMuDValue I ℓ t1 lam) -
          I.program.frac * z lam ≠ 0) :
    Continuous fun lam : ℝ => sectionBoundaryHatGAValue I ℓ t1 z lam := by
  by_cases ht1 : t1 = lastIdx n
  · simpa [sectionBoundaryHatGAValue, ht1] using
      (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  · have hAlpha : Continuous fun lam : ℝ => sectionBoundaryAlphaValue I ℓ t1 lam :=
      continuous_sectionBoundaryAlphaValue I ℓ t1 halphaDenom
    have hPhi :
        Continuous fun lam : ℝ =>
          sectionPhiValue I ℓ t1 (sectionBoundaryAlphaValue I ℓ t1) z lam :=
      continuous_sectionPhiValue I ℓ t1 (sectionBoundaryAlphaValue I ℓ t1) z hAlpha hz hphiDenom
    simpa only [sectionBoundaryHatGAValue, ht1, dite_false, mul_assoc] using!
      (continuous_const.sub hAlpha).mul
        ((continuous_const.sub (Advice.continuous_sectionMuDValue I ℓ t1)).mul hPhi)

theorem continuousOn_sectionBoundaryHatGAValue [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ) {s : Set ℝ}
    (hz : ContinuousOn z s)
    (halphaDenom : ∀ lam ∈ s, sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0)
    (hphiDenom :
      ∀ lam ∈ s,
        futureCount t1 +
            sectionBoundaryAlphaValue I ℓ t1 lam *
              (1 - Advice.sectionMuDValue I ℓ t1 lam) -
          I.program.frac * z lam ≠ 0) :
    ContinuousOn (fun lam : ℝ => sectionBoundaryHatGAValue I ℓ t1 z lam) s := by
  by_cases ht1 : t1 = lastIdx n
  · simpa [sectionBoundaryHatGAValue, ht1] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) s)
  · have hAlpha :
      ContinuousOn (fun lam : ℝ => sectionBoundaryAlphaValue I ℓ t1 lam) s :=
      continuousOn_sectionBoundaryAlphaValue I ℓ t1 halphaDenom
    have hPhi :
        ContinuousOn
          (fun lam : ℝ =>
            sectionPhiValue I ℓ t1 (sectionBoundaryAlphaValue I ℓ t1) z lam) s :=
      continuousOn_sectionPhiValue I ℓ t1 (sectionBoundaryAlphaValue I ℓ t1) z
        hAlpha hz hphiDenom
    simpa only [sectionBoundaryHatGAValue, ht1, dite_false, mul_assoc] using!
      (continuousOn_const.sub hAlpha).mul
        ((continuousOn_const.sub (Advice.continuous_sectionMuDValue I ℓ t1).continuousOn).mul
          hPhi)

theorem sectionPhase1HatGValue_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (i t2 : Idx n) :
    sectionPhase1HatGValue I ℓ i (sectionZValue I ℓ t2) 1 =
      sectionPhase1HatGValue I (succIdx ℓ hℓ) i (sectionZValue I (succIdx ℓ hℓ) t2) 0 := by
  unfold sectionPhase1HatGValue sectionPhiValue
  rw [sectionTransitionNumeratorValue_endpoint_eq (I := I) hℓ i,
    sectionMuDValue_endpoint_eq (I := I) hℓ i,
    sectionZValue_endpoint_eq (I := I) hℓ t2]

theorem sectionBoundaryHatGAValue_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (t1 t2 : Idx n) :
    sectionBoundaryHatGAValue I ℓ t1 (sectionZValue I ℓ t2) 1 =
      sectionBoundaryHatGAValue I (succIdx ℓ hℓ) t1
        (sectionZValue I (succIdx ℓ hℓ) t2) 0 := by
  by_cases ht1 : t1 = lastIdx n
  · simp [sectionBoundaryHatGAValue, ht1]
  · unfold sectionBoundaryHatGAValue
    rw [dif_neg ht1, dif_neg ht1]
    unfold sectionPhiValue
    rw [sectionBoundaryAlphaValue_endpoint_eq (I := I) hℓ t1,
      sectionMuDValue_endpoint_eq (I := I) hℓ t1,
      sectionTransitionNumeratorValue_endpoint_eq (I := I) hℓ t1,
      sectionZValue_endpoint_eq (I := I) hℓ t2]

/-- The sectionwise Phase-1 prefix sum below a fixed threshold `t₁`. -/
noncomputable def sectionPhase1PrefixValue [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ) (lam : ℝ) : ℝ :=
  Finset.sum (sectionPhaseOneRange t1) fun i =>
    sectionPhase1HatGValue I ℓ i z lam

theorem continuous_sectionPhase1PrefixValue [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ)
    (hz : Continuous z)
    (hdenom :
      ∀ ⦃i : Idx n⦄, i < t1 → ∀ lam, futureCount i - I.program.frac * z lam ≠ 0) :
    Continuous fun lam : ℝ => sectionPhase1PrefixValue I ℓ t1 z lam := by
  unfold sectionPhase1PrefixValue
  refine continuous_finsetSum _ ?_
  intro i hi
  have hi' : i < t1 := by
    simpa [sectionPhaseOneRange] using hi
  exact continuous_sectionPhase1HatGValue I ℓ i z hz (hdenom hi')

theorem continuousOn_sectionPhase1PrefixValue [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ) {s : Set ℝ}
    (hz : ContinuousOn z s)
    (hdenom :
      ∀ ⦃i : Idx n⦄, i < t1 → ∀ lam ∈ s, futureCount i - I.program.frac * z lam ≠ 0) :
    ContinuousOn (fun lam : ℝ => sectionPhase1PrefixValue I ℓ t1 z lam) s := by
  unfold sectionPhase1PrefixValue
  refine continuousOn_finsetSum _ ?_
  intro i hi
  have hi' : i < t1 := by
    simpa [sectionPhaseOneRange] using hi
  exact continuousOn_sectionPhase1HatGValue I ℓ i z hz (hdenom hi')

/-- The sectionwise boundary budget `R_{t₁-1}(λ)` for a fixed threshold `t₁`. -/
noncomputable def sectionBoundaryBudgetValue [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ) (lam : ℝ) : ℝ :=
  if _ : t1 = lastIdx n then
    sectionPhaseTwoHatG2Value I ℓ t1 lam
  else
    I.program.barTau + sectionBoundaryHatGAValue I ℓ t1 z lam

theorem continuous_sectionBoundaryBudgetValue [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ)
    (hz : Continuous z)
    (halphaDenom : ∀ lam, sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0)
    (hphiDenom :
      ∀ lam,
        futureCount t1 +
            sectionBoundaryAlphaValue I ℓ t1 lam *
              (1 - Advice.sectionMuDValue I ℓ t1 lam) -
          I.program.frac * z lam ≠ 0) :
    Continuous fun lam : ℝ => sectionBoundaryBudgetValue I ℓ t1 z lam := by
  by_cases ht1 : t1 = lastIdx n
  · simpa [sectionBoundaryBudgetValue, ht1] using
      continuous_sectionPhaseTwoHatG2Value I ℓ t1
  · simpa only [sectionBoundaryBudgetValue, ht1, dite_false] using!
      continuous_const.add
        (continuous_sectionBoundaryHatGAValue I ℓ t1 z hz halphaDenom hphiDenom)

theorem continuousOn_sectionBoundaryBudgetValue [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ) {s : Set ℝ}
    (hz : ContinuousOn z s)
    (halphaDenom : ∀ lam ∈ s, sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0)
    (hphiDenom :
      ∀ lam ∈ s,
        futureCount t1 +
            sectionBoundaryAlphaValue I ℓ t1 lam *
              (1 - Advice.sectionMuDValue I ℓ t1 lam) -
          I.program.frac * z lam ≠ 0) :
    ContinuousOn (fun lam : ℝ => sectionBoundaryBudgetValue I ℓ t1 z lam) s := by
  by_cases ht1 : t1 = lastIdx n
  · simpa [sectionBoundaryBudgetValue, ht1] using
      (continuous_sectionPhaseTwoHatG2Value I ℓ t1).continuousOn
  · simpa only [sectionBoundaryBudgetValue, ht1, dite_false] using!
      continuousOn_const.add
        (continuousOn_sectionBoundaryHatGAValue I ℓ t1 z hz halphaDenom hphiDenom)

/-- The fixed-threshold candidate for the final total generated credit `R₀(λ)`. -/
noncomputable def sectionR0ValueAtThreshold [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ) (lam : ℝ) : ℝ :=
  sectionBoundaryBudgetValue I ℓ t1 z lam +
    sectionPhase1PrefixValue I ℓ t1 z lam

theorem continuous_sectionR0ValueAtThreshold [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ)
    (hz : Continuous z)
    (halphaDenom : ∀ lam, sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0)
    (hphiDenom :
      ∀ lam,
        futureCount t1 +
            sectionBoundaryAlphaValue I ℓ t1 lam *
              (1 - Advice.sectionMuDValue I ℓ t1 lam) -
          I.program.frac * z lam ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 → ∀ lam, futureCount i - I.program.frac * z lam ≠ 0) :
    Continuous fun lam : ℝ => sectionR0ValueAtThreshold I ℓ t1 z lam := by
  unfold sectionR0ValueAtThreshold
  exact
    (continuous_sectionBoundaryBudgetValue I ℓ t1 z hz halphaDenom hphiDenom).add
      (continuous_sectionPhase1PrefixValue I ℓ t1 z hz hphase1Denom)

theorem continuousOn_sectionR0ValueAtThreshold [NeZero n]
    (ℓ t1 : Idx n) (z : ℝ → ℝ) {s : Set ℝ}
    (hz : ContinuousOn z s)
    (halphaDenom : ∀ lam ∈ s, sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0)
    (hphiDenom :
      ∀ lam ∈ s,
        futureCount t1 +
            sectionBoundaryAlphaValue I ℓ t1 lam *
              (1 - Advice.sectionMuDValue I ℓ t1 lam) -
          I.program.frac * z lam ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ lam ∈ s, futureCount i - I.program.frac * z lam ≠ 0) :
    ContinuousOn (fun lam : ℝ => sectionR0ValueAtThreshold I ℓ t1 z lam) s := by
  unfold sectionR0ValueAtThreshold
  exact
    (continuousOn_sectionBoundaryBudgetValue I ℓ t1 z hz halphaDenom hphiDenom).add
      (continuousOn_sectionPhase1PrefixValue I ℓ t1 z hz hphase1Denom)

/-- The explicit `\hat g` candidate associated to a fixed threshold pair `(t₁,t₂)` on a section.
Below `t₁` it uses the Phase-1 closed form, at `t₁` it uses the boundary split, and above `t₁`
it copies the Phase-2 profile. -/
noncomputable def sectionHatGValueAtThreshold [NeZero n]
    (ℓ t1 t2 : Idx n) (i : Idx n) (lam : ℝ) : ℝ :=
  if _hi : i < t1 then
    sectionPhase1HatGValue I ℓ i (sectionZValue I ℓ t2) lam
  else if _ht1 : i = t1 then
    sectionBoundaryHatGAValue I ℓ t1 (sectionZValue I ℓ t2) lam +
      sectionBoundaryHatGBValue I ℓ t1 lam
  else
    sectionPhaseTwoHatG2Value I ℓ i lam

theorem sectionHatGValueAtThreshold_eq_phase1 [NeZero n]
    (ℓ t1 t2 : Idx n) {i : Idx n} {lam : ℝ} (hi : i < t1) :
    sectionHatGValueAtThreshold I ℓ t1 t2 i lam =
      sectionPhase1HatGValue I ℓ i (sectionZValue I ℓ t2) lam := by
  simp [sectionHatGValueAtThreshold, hi]

theorem sectionHatGValueAtThreshold_eq_boundary [NeZero n]
    (ℓ t1 t2 : Idx n) {lam : ℝ} :
    sectionHatGValueAtThreshold I ℓ t1 t2 t1 lam =
      sectionBoundaryHatGAValue I ℓ t1 (sectionZValue I ℓ t2) lam +
        sectionBoundaryHatGBValue I ℓ t1 lam := by
  simp [sectionHatGValueAtThreshold]

theorem sectionHatGValueAtThreshold_eq_phase2 [NeZero n]
    (ℓ t1 t2 : Idx n) {i : Idx n} {lam : ℝ} (hi : t1 < i) :
    sectionHatGValueAtThreshold I ℓ t1 t2 i lam =
      sectionPhaseTwoHatG2Value I ℓ i lam := by
  simp [sectionHatGValueAtThreshold, hi.ne', not_lt.mpr (le_of_lt hi)]

theorem tailBudget_sectionHatGValueAtThreshold_of_t1_le [NeZero n]
    (ℓ t1 t2 : Idx n) {j : Idx n} {lam : ℝ} (hj : t1 ≤ j) :
    tailBudget (fun i => sectionHatGValueAtThreshold I ℓ t1 t2 i lam) j =
      sectionPhaseTwoAfterBudgetValue I ℓ j lam := by
  calc
    tailBudget (fun i => sectionHatGValueAtThreshold I ℓ t1 t2 i lam) j
      =
        tailBudget (fun i => sectionPhaseTwoHatG2Value I ℓ i lam) j := by
          unfold tailBudget
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ t1 t2
            (lt_of_le_of_lt hj (mem_strictSuffixRange.mp hi))]
    _ = sectionPhaseTwoAfterBudgetValue I ℓ j lam := by
          exact tailBudget_eq_sectionPhaseTwoAfterBudgetValue_explicit (I := I) ℓ j lam

theorem sectionHatGValueAtThreshold_endpoint_eq [NeZero n]
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) (t1 t2 i : Idx n) :
    sectionHatGValueAtThreshold I ℓ t1 t2 i 1 =
      sectionHatGValueAtThreshold I (succIdx ℓ hℓ) t1 t2 i 0 := by
  by_cases hi : i < t1
  · rw [sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ t1 t2 hi,
      sectionHatGValueAtThreshold_eq_phase1 (I := I) (succIdx ℓ hℓ) t1 t2 hi]
    exact sectionPhase1HatGValue_endpoint_eq (I := I) hℓ i t2
  · by_cases ht1 : i = t1
    · subst i
      rw [sectionHatGValueAtThreshold_eq_boundary (I := I) ℓ t1 t2,
        sectionHatGValueAtThreshold_eq_boundary (I := I) (succIdx ℓ hℓ) t1 t2,
        sectionBoundaryHatGAValue_endpoint_eq (I := I) hℓ t1 t2,
        sectionBoundaryHatGBValue_endpoint_eq (I := I) hℓ t1]
    · have hgt : t1 < i := lt_of_le_of_ne (not_lt.mp hi) (Ne.symm ht1)
      rw [sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ t1 t2 hgt,
        sectionHatGValueAtThreshold_eq_phase2 (I := I) (succIdx ℓ hℓ) t1 t2 hgt]
      exact sectionPhaseTwoHatG2Value_endpoint_eq (I := I) hℓ i

theorem beforeBudget_sectionHatGValueAtThreshold_t1 [NeZero n]
    (ℓ t1 t2 : Idx n) (lam : ℝ) :
    beforeBudget (fun i => sectionHatGValueAtThreshold I ℓ t1 t2 i lam) t1 =
      sectionBoundaryBudgetValue I ℓ t1 (sectionZValue I ℓ t2) lam := by
  rw [beforeBudget_eq_self_add_tail,
    sectionHatGValueAtThreshold_eq_boundary (I := I) ℓ t1 t2,
    tailBudget_sectionHatGValueAtThreshold_of_t1_le (I := I) ℓ t1 t2 le_rfl]
  by_cases ht1 : t1 = lastIdx n
  · simp [sectionBoundaryBudgetValue, sectionBoundaryHatGAValue, sectionBoundaryHatGBValue, ht1]
  · simp [sectionBoundaryBudgetValue, sectionBoundaryHatGBValue, ht1]
    ring

theorem totalBudget_sectionHatGValueAtThreshold [NeZero n]
    (ℓ t1 t2 : Idx n) (lam : ℝ) :
    totalBudget (fun i => sectionHatGValueAtThreshold I ℓ t1 t2 i lam) =
      sectionR0ValueAtThreshold I ℓ t1 (sectionZValue I ℓ t2) lam := by
  rw [← sum_sectionPhaseOne_add_beforeBudget
    (hatG := fun i => sectionHatGValueAtThreshold I ℓ t1 t2 i lam) t1,
    beforeBudget_sectionHatGValueAtThreshold_t1 (I := I) ℓ t1 t2 lam,
    sectionR0ValueAtThreshold]
  have hprefix :
      Finset.sum (sectionPhaseOneRange t1)
        (fun i => sectionHatGValueAtThreshold I ℓ t1 t2 i lam) =
      Finset.sum (sectionPhaseOneRange t1)
      (fun i => sectionPhase1HatGValue I ℓ i (sectionZValue I ℓ t2) lam) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ t1 t2
      (by simpa [sectionPhaseOneRange] using hi)]
  rw [hprefix]
  simp [sectionPhase1PrefixValue, add_comm]

theorem sectionR0ValueAtThreshold_eq_of_budget_eq_barTau_of_max_belowThresholdNononeSet
    [NeZero n]
    {ℓ t1 k t2 : Idx n} {lam : ℝ}
    {hne : (Advice.belowThresholdNononeSet I ℓ t1 lam).Nonempty}
    (ht1ℓ : t1 ≤ ℓ)
    (hk : (Advice.belowThresholdNononeSet I ℓ t1 lam).max' hne = k)
    (hkt1 : k < t1)
    (hbar : Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam = I.program.barTau)
    (halphaDenomT1 : Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0) :
    sectionR0ValueAtThreshold I ℓ k (sectionZValue I ℓ t2) lam =
      sectionR0ValueAtThreshold I ℓ t1 (sectionZValue I ℓ t2) lam := by
  rw [← totalBudget_sectionHatGValueAtThreshold (I := I) ℓ k t2 lam,
    ← totalBudget_sectionHatGValueAtThreshold (I := I) ℓ t1 t2 lam]
  unfold totalBudget
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hik : i < k
  · rw [sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ k t2 hik,
      sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ t1 t2
        (lt_of_lt_of_le hik (le_of_lt hkt1))]
  · by_cases hki : i = k
    · subst i
      rw [sectionHatGValueAtThreshold_eq_boundary (I := I) ℓ k t2,
        sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ t1 t2 hkt1]
      have hknotlast : k ≠ lastIdx n := (lt_of_lt_of_le hkt1 (le_lastIdx t1)).ne
      have hafterK : Advice.sectionPhaseTwoAfterBudgetValue I ℓ k lam = I.program.barTau := by
        rw [Advice.sectionPhaseTwoAfterBudgetValue_eq_budget_of_between_max_belowThresholdNononeSet
          (I := I) hk hkt1, hbar]
      have halphaZero : Advice.sectionBoundaryAlphaValue I ℓ k lam = 0 := by
        unfold Advice.sectionBoundaryAlphaValue
        simp [hknotlast, hafterK]
      simp [sectionBoundaryHatGAValue, sectionBoundaryHatGBValue, sectionPhase1HatGValue,
        sectionPhiValue, hknotlast, hafterK, halphaZero]
    · by_cases hit1 : i < t1
      · have hki' : k < i := lt_of_le_of_ne (not_lt.mp hik) (Ne.symm hki)
        have hiℓ : i ≤ ℓ := le_trans (le_of_lt hit1) ht1ℓ
        have hhat0 :
            Advice.sectionPhaseTwoHatG2Value I ℓ i lam = 0 :=
          sectionPhaseTwoHatG2Value_eq_zero_of_between_max_belowThresholdNononeSet
            (I := I) (ℓ := ℓ) (t1 := t1) (k := k) (i := i) (lam := lam)
            (hne := hne) hiℓ hk hki' hit1
        rw [sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ k t2 hki',
          sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ t1 t2 hit1,
          hhat0,
          sectionPhase1HatGValue]
        have hμ :
            Advice.sectionMuDValue I ℓ i lam = 1 :=
          Advice.sectionMuDValue_eq_one_of_between_max_belowThresholdNononeSet I hk hki' hit1
        simp [hμ]
      · by_cases hit1eq : i = t1
        · subst i
          rw [sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ k t2 hkt1,
            sectionHatGValueAtThreshold_eq_boundary (I := I) ℓ t1 t2]
          by_cases ht1last : t1 = lastIdx n
          · simp [sectionBoundaryHatGAValue, sectionBoundaryHatGBValue, ht1last]
          · have hafter :
                  I.program.barTau - Advice.sectionPhaseTwoAfterBudgetValue I ℓ t1 lam =
                    Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam := by
                unfold Advice.sectionPhaseTwoHatG2Value
                linarith
            have halphaOne : Advice.sectionBoundaryAlphaValue I ℓ t1 lam = 1 := by
              unfold Advice.sectionBoundaryAlphaValue
              simp [ht1last, hafter, halphaDenomT1]
            simp [sectionBoundaryHatGAValue, sectionBoundaryHatGBValue, ht1last,
              halphaOne, hafter]
        · have ht1i : t1 < i := lt_of_le_of_ne (not_lt.mp hit1) (Ne.symm hit1eq)
          rw [sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ k t2
              (lt_trans hkt1 ht1i),
            sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ t1 t2 ht1i]

theorem sectionBoundaryAlphaValue_eq_zero_of_budget_eq_barTau_of_max_belowThresholdNononeSet
    [NeZero n]
    (hγ : 1 < I.program.Mcoeff)
    {ℓ t1 k : Idx n} {lam : ℝ}
    (hlam : 0 ≤ lam)
    {hne : (Advice.belowThresholdNononeSet I ℓ t1 lam).Nonempty}
    (hk : (Advice.belowThresholdNononeSet I ℓ t1 lam).max' hne = k)
    (hkt1 : k < t1)
    (hbar : Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam = I.program.barTau) :
    Advice.sectionBoundaryAlphaValue I ℓ k lam = 0 := by
  have hknotlast : k ≠ lastIdx n := (lt_of_lt_of_le hkt1 (le_lastIdx t1)).ne
  have hafter_eq :
      Advice.sectionPhaseTwoAfterBudgetValue I ℓ k lam =
        Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam :=
    Advice.sectionPhaseTwoAfterBudgetValue_eq_budget_of_between_max_belowThresholdNononeSet
      (I := I) hk hkt1
  have hpred :
      Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam <
        Advice.sectionPhaseTwoBudgetValue I ℓ k lam :=
    Advice.sectionPhaseTwoBudgetValue_lt_at_predecessor_of_max_belowThresholdNononeSet
      (I := I) hγ hlam hk hkt1
  have hhat_nonzero : Advice.sectionPhaseTwoHatG2Value I ℓ k lam ≠ 0 := by
    have hhat_eq :
        Advice.sectionPhaseTwoHatG2Value I ℓ k lam =
          Advice.sectionPhaseTwoBudgetValue I ℓ k lam -
            Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam := by
      rw [Advice.sectionPhaseTwoHatG2Value, hafter_eq]
    have hhat_pos : 0 < Advice.sectionPhaseTwoHatG2Value I ℓ k lam := by
      linarith [hpred, hhat_eq]
    exact ne_of_gt hhat_pos
  unfold Advice.sectionBoundaryAlphaValue
  simp [hknotlast, hafter_eq, hbar]

theorem sectionBoundaryPhiDenom_pos_of_budget_eq_barTau_of_max_belowThresholdNononeSet
    [NeZero n]
    (hγ : 1 < I.program.Mcoeff)
    {ℓ t1 k t2 : Idx n} {lam : ℝ}
    (hlam : 0 ≤ lam)
    {hne : (Advice.belowThresholdNononeSet I ℓ t1 lam).Nonempty}
    (hk : (Advice.belowThresholdNononeSet I ℓ t1 lam).max' hne = k)
    (hkt1 : k < t1)
    (ht1t2 : t1 ≤ t2)
    (hbar : Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam = I.program.barTau) :
    0 <
      futureCount k +
        Advice.sectionBoundaryAlphaValue I ℓ k lam *
            (1 - Advice.sectionMuDValue I ℓ k lam) -
          I.program.frac * Advice.sectionZValue I ℓ t2 lam := by
  have hα0 :
      Advice.sectionBoundaryAlphaValue I ℓ k lam = 0 :=
    Advice.sectionBoundaryAlphaValue_eq_zero_of_budget_eq_barTau_of_max_belowThresholdNononeSet
      (I := I) hγ hlam hk hkt1 hbar
  have hz_nonneg :
      0 ≤ Advice.sectionZValue I ℓ t2 lam := by
    unfold Advice.sectionZValue
    refine Finset.sum_nonneg ?_
    intro m hm
    exact mul_nonneg (posPart_nonneg _) (Advice.sectionMuDValue_nonneg I ℓ m lam)
  have hz_le_t2 :
      Advice.sectionZValue I ℓ t2 lam ≤ futureCount t2 := by
    unfold Advice.sectionZValue
    calc
      Finset.sum (strictSuffixRange t2) (fun m =>
          posPart (1 - Advice.sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta) *
            Advice.sectionMuDValue I ℓ m lam)
        ≤ Finset.sum (strictSuffixRange t2) (fun _ => (1 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          have hpp_le_one :
              posPart
                  (1 - Advice.sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta) ≤
                1 := by
            exact posPart_sub_div_le_one
              (Advice.sectionPhaseTwoBudgetValue_nonneg (I := I) (le_of_lt hγ) ℓ m hlam)
              (I.program.theta_nonneg_of_one_le_Mcoeff (le_of_lt hγ))
          have hμ_nonneg : 0 ≤ Advice.sectionMuDValue I ℓ m lam :=
            Advice.sectionMuDValue_nonneg I ℓ m lam
          have hμ_le_one : Advice.sectionMuDValue I ℓ m lam ≤ 1 :=
            Advice.sectionMuDValue_le_one I ℓ m lam
          nlinarith
      _ = ((strictSuffixRange t2).card : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = futureCount t2 := by
          have hprefix : (prefixRange t2).card = t2.1.succ := by
            unfold prefixRange
            calc
              (Finset.univ.filter fun j : Idx n => j ≤ t2).card = min n t2.1.succ := by
                simpa only [Fin.le_def, Nat.lt_succ_iff] using
                  (Fin.card_filter_val_lt (n := n) (m := t2.1.succ))
              _ = t2.1.succ := Nat.min_eq_right t2.is_lt.succ_le
          have hcomp : strictSuffixRange t2 = Finset.univ \ prefixRange t2 := by
            ext i
            simp [strictSuffixRange, prefixRange, not_le]
          have hinter : prefixRange t2 ∩ Finset.univ = prefixRange t2 := by
            ext i
            simp
          change ((strictSuffixRange t2).card : ℝ) = (futureCountNat t2 : ℝ)
          rw [hcomp, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]
          rw [hinter, futureCountNat, hprefix]
  have ht1_lt_k : futureCount t1 < futureCount k := by
    change ((futureCountNat t1 : ℝ) < (futureCountNat k : ℝ))
    exact_mod_cast ProfileData.futureCountNat_lt_of_lt hkt1
  have ht2_lt_k : futureCount t2 < futureCount k := by
    exact lt_of_le_of_lt (ProfileData.futureCount_antitone ht1t2) ht1_lt_k
  have hfracz_le_z :
      I.program.frac * Advice.sectionZValue I ℓ t2 lam ≤ Advice.sectionZValue I ℓ t2 lam := by
    have hfrac_le : I.program.frac ≤ 1 :=
      I.program.frac_le_one_of_one_le_Mcoeff (le_of_lt hγ)
    nlinarith
  have hfracz_lt_k :
      I.program.frac * Advice.sectionZValue I ℓ t2 lam < futureCount k := by
    exact lt_of_le_of_lt hfracz_le_z (lt_of_le_of_lt hz_le_t2 ht2_lt_k)
  rw [hα0]
  nlinarith

theorem sectionPhaseTwoBudgetValue_eq_sectionR0_of_budget_eq_barTau_empty
    [NeZero n]
    {ℓ t1 t2 : Idx n} {lam : ℝ}
    (ht1ℓ : t1 ≤ ℓ)
    (hempty : Advice.belowThresholdNononeSet I ℓ t1 lam = ∅)
    (hbar : Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam = I.program.barTau)
    (halphaDenomT1 : Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0) :
    Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam =
      sectionR0ValueAtThreshold I ℓ t1 (sectionZValue I ℓ t2) lam := by
  have hphaseTotal :
      beforeBudget (fun i => Advice.sectionPhaseTwoHatG2Value I ℓ i lam) (firstIdx n) =
        totalBudget (fun i => Advice.sectionPhaseTwoHatG2Value I ℓ i lam) := by
    exact
      beforeBudget_firstIdx_eq_totalBudget
        (hatG := fun i => Advice.sectionPhaseTwoHatG2Value I ℓ i lam)
  calc
    Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam
        =
          beforeBudget (fun i => Advice.sectionPhaseTwoHatG2Value I ℓ i lam) (firstIdx n) := by
            symm
            exact Advice.beforeBudget_eq_sectionPhaseTwoBudgetValue_explicit
              (I := I) ℓ lam (firstIdx n)
    _ = totalBudget (fun i => Advice.sectionPhaseTwoHatG2Value I ℓ i lam) := hphaseTotal
    _ = totalBudget (fun i => sectionHatGValueAtThreshold I ℓ t1 t2 i lam) := by
          unfold totalBudget
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hit1 : i < t1
          · have hμ : Advice.sectionMuDValue I ℓ i lam = 1 := by
              apply Advice.sectionMuDValue_eq_one_of_not_mem_belowThresholdNononeSet I hit1
              simp [hempty]
            have hiℓ : i ≤ ℓ := le_trans (le_of_lt hit1) ht1ℓ
            have hilast : i ≠ lastIdx n := ne_of_lt (lt_of_lt_of_le hit1 (le_lastIdx t1))
            have hhat0 : Advice.sectionPhaseTwoHatG2Value I ℓ i lam = 0 := by
              exact sectionPhaseTwoHatG2Value_eq_zero_of_muD_eq_one
                (I := I) ℓ i hiℓ hμ hilast
            rw [sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ t1 t2 hit1,
              sectionPhase1HatGValue]
            simp [hμ, hhat0]
          · by_cases hiEq : i = t1
            · subst i
              rw [sectionHatGValueAtThreshold_eq_boundary (I := I) ℓ t1 t2]
              by_cases ht1last : t1 = lastIdx n
              · simp [sectionBoundaryHatGAValue, sectionBoundaryHatGBValue, ht1last]
              · have hafter :
                    I.program.barTau - Advice.sectionPhaseTwoAfterBudgetValue I ℓ t1 lam =
                      Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam := by
                  unfold Advice.sectionPhaseTwoHatG2Value
                  linarith
                have halphaOne : Advice.sectionBoundaryAlphaValue I ℓ t1 lam = 1 := by
                  unfold Advice.sectionBoundaryAlphaValue
                  simp [ht1last, hafter, halphaDenomT1]
                simp [sectionBoundaryHatGAValue, sectionBoundaryHatGBValue, ht1last,
                  halphaOne, hafter]
            · have ht1i : t1 < i := lt_of_le_of_ne (not_lt.mp hit1) (Ne.symm hiEq)
              rw [sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ t1 t2 ht1i]
    _ = sectionR0ValueAtThreshold I ℓ t1 (sectionZValue I ℓ t2) lam := by
          exact totalBudget_sectionHatGValueAtThreshold (I := I) ℓ t1 t2 lam

theorem sectionPhaseTwoBudgetValue_eq_sectionR0_empty
    [NeZero n]
    {ℓ t1 t2 : Idx n} {lam : ℝ}
    (ht1ℓ : t1 ≤ ℓ)
    (hempty : Advice.belowThresholdNononeSet I ℓ t1 lam = ∅)
    (hbar : Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam = I.program.barTau)
    (halphaDenomT1 : Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0) :
    Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam =
      sectionR0ValueAtThreshold I ℓ t1 (sectionZValue I ℓ t2) lam :=
  sectionPhaseTwoBudgetValue_eq_sectionR0_of_budget_eq_barTau_empty
    (I := I) ht1ℓ hempty hbar halphaDenomT1

theorem sectionTransitionNumerator_eq_of_sectionHatGValueAtThreshold_of_firstBid_ge_t1
    [NeZero n]
    (ℓ t1 t2 : Idx n) {i : Idx n} {lam : ℝ}
    (hfi : t1 ≤ I.firstBidTime i) :
    1 - posPart
        (I.program.theta -
          tailBudget (fun j => sectionHatGValueAtThreshold I ℓ t1 t2 j lam)
            (I.firstBidTime i)) =
      sectionTransitionNumeratorValue I ℓ i lam := by
  rw [tailBudget_sectionHatGValueAtThreshold_of_t1_le (I := I) ℓ t1 t2 hfi]
  unfold sectionTransitionNumeratorValue
  rfl

theorem sectionTransitionNumerator_eq_of_sectionHatGValueAtThreshold_of_tail_ge_theta
    [NeZero n]
    (ℓ t1 t2 : Idx n) {i : Idx n} {lam : ℝ}
    (htail :
      I.program.theta ≤
        tailBudget (fun j => sectionHatGValueAtThreshold I ℓ t1 t2 j lam)
          (I.firstBidTime i))
    (hphase :
      I.program.theta ≤ sectionPhaseTwoAfterBudgetValue I ℓ (I.firstBidTime i) lam) :
    1 - posPart
        (I.program.theta -
          tailBudget (fun j => sectionHatGValueAtThreshold I ℓ t1 t2 j lam)
            (I.firstBidTime i)) =
      sectionTransitionNumeratorValue I ℓ i lam := by
  have htail_nonpos :
      I.program.theta -
          tailBudget (fun j => sectionHatGValueAtThreshold I ℓ t1 t2 j lam)
            (I.firstBidTime i) ≤ 0 := by
    linarith
  have hphase_nonpos :
      I.program.theta - sectionPhaseTwoAfterBudgetValue I ℓ (I.firstBidTime i) lam ≤ 0 := by
    linarith
  unfold sectionTransitionNumeratorValue
  rw [posPart_of_nonpos htail_nonpos, posPart_of_nonpos hphase_nonpos]

theorem sectionHatGValueAtThreshold_eq_phase1Formula_of_firstBid_ge_t1
    [NeZero n]
    (ℓ t1 t2 : Idx n) {i : Idx n} {lam : ℝ}
    (hi : i < t1) (hfi : t1 ≤ I.firstBidTime i) :
    sectionHatGValueAtThreshold I ℓ t1 t2 i lam =
      (1 - Advice.sectionMuDValue I ℓ i lam) *
        (1 - posPart
          (I.program.theta -
            tailBudget (fun j => sectionHatGValueAtThreshold I ℓ t1 t2 j lam)
              (I.firstBidTime i))) /
        (futureCount i - I.program.frac * sectionZValue I ℓ t2 lam) := by
  rw [sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ t1 t2 hi]
  unfold sectionPhase1HatGValue sectionPhiValue
  rw [sectionTransitionNumerator_eq_of_sectionHatGValueAtThreshold_of_firstBid_ge_t1
    (I := I) ℓ t1 t2 hfi]
  ring_nf

theorem sectionHatGValueAtThreshold_eq_phase1Formula_of_tail_ge_theta
    [NeZero n]
    (ℓ t1 t2 : Idx n) {i : Idx n} {lam : ℝ}
    (hi : i < t1)
    (htail :
      I.program.theta ≤
        tailBudget (fun j => sectionHatGValueAtThreshold I ℓ t1 t2 j lam)
          (I.firstBidTime i))
    (hphase :
      I.program.theta ≤ sectionPhaseTwoAfterBudgetValue I ℓ (I.firstBidTime i) lam) :
    sectionHatGValueAtThreshold I ℓ t1 t2 i lam =
      (1 - Advice.sectionMuDValue I ℓ i lam) *
        (1 - posPart
          (I.program.theta -
            tailBudget (fun j => sectionHatGValueAtThreshold I ℓ t1 t2 j lam)
              (I.firstBidTime i))) /
        (futureCount i - I.program.frac * sectionZValue I ℓ t2 lam) := by
  rw [sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ t1 t2 hi]
  unfold sectionPhase1HatGValue sectionPhiValue
  rw [sectionTransitionNumerator_eq_of_sectionHatGValueAtThreshold_of_tail_ge_theta
    (I := I) ℓ t1 t2 htail hphase]
  ring_nf

theorem sectionPhaseTwoAfterBudgetValue_nonneg [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ i : Idx n) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ sectionPhaseTwoAfterBudgetValue I ℓ i lam := by
  by_cases hi : i = lastIdx n
  · simp [sectionPhaseTwoAfterBudgetValue, hi]
  · have hilt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx i) hi
    rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ i lam hilt]
    exact sectionPhaseTwoBudgetValue_nonneg (I := I) hγlo ℓ (succIdx i hilt) hlam

theorem sectionTransitionNumeratorValue_nonneg [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ i : Idx n) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ sectionTransitionNumeratorValue I ℓ i lam := by
  unfold sectionTransitionNumeratorValue
  exact one_sub_posPart_sub_nonneg
    (sectionPhaseTwoAfterBudgetValue_nonneg (I := I) hγlo ℓ (I.firstBidTime i) hlam)
    (I.program.theta_nonneg_of_one_le_Mcoeff hγlo)
    (I.program.theta_le_one_of_le_153_div_125 hγlo hγhi)

theorem sectionZValue_nonneg [NeZero n] (ℓ t2 : Idx n) (lam : ℝ) :
    0 ≤ sectionZValue I ℓ t2 lam := by
  unfold sectionZValue
  refine Finset.sum_nonneg ?_
  intro m hm
  exact mul_nonneg (posPart_nonneg _)
    (Advice.sectionMuDValue_nonneg I ℓ m lam)

theorem sectionZValue_le_futureCount [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ t2 : Idx n) {lam : ℝ} (hlam : 0 ≤ lam) :
    sectionZValue I ℓ t2 lam ≤ futureCount t2 := by
  unfold sectionZValue
  calc
    Finset.sum (strictSuffixRange t2) (fun m =>
        posPart (1 - sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta) *
          sectionMuDValue I ℓ m lam)
      ≤ Finset.sum (strictSuffixRange t2) (fun _ => (1 : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro m hm
        have hpp_le_one :
            posPart (1 - sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta) ≤ 1 := by
          exact posPart_sub_div_le_one
            (sectionPhaseTwoBudgetValue_nonneg (I := I) hγlo ℓ m hlam)
            (I.program.theta_nonneg_of_one_le_Mcoeff hγlo)
        have hμ_nonneg : 0 ≤ sectionMuDValue I ℓ m lam :=
          Advice.sectionMuDValue_nonneg I ℓ m lam
        have hμ_le_one : sectionMuDValue I ℓ m lam ≤ 1 :=
          Advice.sectionMuDValue_le_one I ℓ m lam
        nlinarith
    _ = ((strictSuffixRange t2).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ = futureCount t2 := by
        have hprefix : (prefixRange t2).card = t2.1.succ := by
          unfold prefixRange
          calc
            (Finset.univ.filter fun j : Idx n => j ≤ t2).card = min n t2.1.succ := by
              simpa only [Fin.le_def, Nat.lt_succ_iff] using
                (Fin.card_filter_val_lt (n := n) (m := t2.1.succ))
            _ = t2.1.succ := Nat.min_eq_right t2.is_lt.succ_le
        have hcomp : strictSuffixRange t2 = Finset.univ \ prefixRange t2 := by
          ext i
          simp [strictSuffixRange, prefixRange, not_le]
        have hinter : prefixRange t2 ∩ Finset.univ = prefixRange t2 := by
          ext i
          simp
        change ((strictSuffixRange t2).card : ℝ) = (futureCountNat t2 : ℝ)
        rw [hcomp, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]
        rw [hinter, futureCountNat, hprefix]

theorem sectionZValue_eq_sectionZFullValue_of_t2_spec [NeZero n]
    (hγ : 1 < I.program.Mcoeff)
    (ℓ : Idx n) {t2 : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (ht2 :
      (Advice.sectionPhaseTwoData (I := I) (le_of_lt hγ) ℓ lam hlam).t2? = some t2) :
    sectionZValue I ℓ t2 lam = sectionZFullValue I ℓ lam := by
  let Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam) :=
    Advice.sectionPhaseTwoData (I := I) (le_of_lt hγ) ℓ lam hlam
  let term : Idx n → ℝ := fun m =>
    posPart (1 - sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta) *
      Advice.sectionMuDValue I ℓ m lam
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun m : Idx n => m ≤ t2) term
  have hprefix :
      Finset.univ.filter (fun m : Idx n => m ≤ t2) = prefixRange t2 := by
    ext m
    simp [prefixRange]
  have hsuffix :
      Finset.univ.filter (fun m : Idx n => ¬ m ≤ t2) = strictSuffixRange t2 := by
    ext m
    simp [strictSuffixRange]
  rw [hprefix, hsuffix] at hsplit
  have hθpos : 0 < I.program.theta := by
    dsimp [DualProgram.theta, DualProgram.epsilon, DualProgram.Mcoeffmone]
    nlinarith [hγ]
  have hprefix_zero : Finset.sum (prefixRange t2) term = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    have hmle : m ≤ t2 := by
      simpa [prefixRange] using hm
    have hge_t2 : I.program.theta ≤ Ξ.beforeBudget t2 :=
      Advice.PhaseTwoData.beforeBudget_ge_theta_of_t2?_eq_some (Ξ := Ξ) ht2
    have hmono : Ξ.beforeBudget t2 ≤ Ξ.beforeBudget m := by
      simpa [PhaseTwoData.beforeBudget] using
        (beforeBudget_antitone_of_nonneg Ξ.hatG2_nonneg hmle)
    have hbudget_ge : I.program.theta ≤ sectionPhaseTwoBudgetValue I ℓ m lam := by
      rw [← Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
        (Ξ := Ξ) m]
      exact le_trans hge_t2 hmono
    have hnonpos : 1 - sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta ≤ 0 := by
      have hdiv_ge_one :
          (1 : ℝ) ≤ sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta :=
        (le_div_iff₀ hθpos).2 (by simpa [one_mul] using hbudget_ge)
      linarith
    simp [posPart_of_nonpos hnonpos]
  calc
    sectionZValue I ℓ t2 lam = Finset.sum (strictSuffixRange t2) term := by
      simp [sectionZValue, term]
    _ = Finset.sum (prefixRange t2) term + Finset.sum (strictSuffixRange t2) term := by
      rw [hprefix_zero]
      simp
    _ = sectionZFullValue I ℓ lam := by
      simpa [sectionZFullValue, term] using hsplit

theorem sectionZFullValue_le_futureCount_of_barTau_lt [NeZero n]
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ t1 : Idx n) {lam : ℝ} (hlam : 0 ≤ lam ∧ lam ≤ 1)
    (hbar : I.program.barTau < sectionPhaseTwoBudgetValue I ℓ t1 lam) :
    sectionZFullValue I ℓ lam ≤ futureCount t1 := by
  let Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam) :=
    Advice.sectionPhaseTwoData (I := I) (le_of_lt hγ) ℓ lam hlam
  let term : Idx n → ℝ := fun m =>
    posPart (1 - sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta) *
      Advice.sectionMuDValue I ℓ m lam
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun m : Idx n => m ≤ t1) term
  have hprefix :
      Finset.univ.filter (fun m : Idx n => m ≤ t1) = prefixRange t1 := by
    ext m
    simp [prefixRange]
  have hsuffix :
      Finset.univ.filter (fun m : Idx n => ¬ m ≤ t1) = strictSuffixRange t1 := by
    ext m
    simp [strictSuffixRange]
  rw [hprefix, hsuffix] at hsplit
  have hθbar : I.program.theta ≤ I.program.barTau :=
    I.program.theta_le_barTau_of_le_153_div_125 (le_of_lt hγ) hγhi
  have hθpos : 0 < I.program.theta := by
    dsimp [DualProgram.theta, DualProgram.epsilon, DualProgram.Mcoeffmone]
    nlinarith [hγ]
  have hprefix_zero : Finset.sum (prefixRange t1) term = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    have hmle : m ≤ t1 := by
      simpa [prefixRange] using hm
    have hmono :
        Ξ.beforeBudget t1 ≤ Ξ.beforeBudget m := by
      simpa [PhaseTwoData.beforeBudget] using
        (beforeBudget_antitone_of_nonneg Ξ.hatG2_nonneg hmle)
    have ht1_budget :
        I.program.theta ≤ sectionPhaseTwoBudgetValue I ℓ t1 lam := by
      exact le_trans hθbar (le_of_lt hbar)
    have ht1_budget' : I.program.theta ≤ Ξ.beforeBudget t1 := by
      simpa [← Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
        (Ξ := Ξ) t1] using ht1_budget
    have hbudget_ge : I.program.theta ≤ sectionPhaseTwoBudgetValue I ℓ m lam := by
      have hm_budget' : I.program.theta ≤ Ξ.beforeBudget m := le_trans ht1_budget' hmono
      simpa [← Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
        (Ξ := Ξ) m] using hm_budget'
    have hnonpos : 1 - sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta ≤ 0 := by
      have hdiv_ge_one :
          (1 : ℝ) ≤ sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta :=
        (le_div_iff₀ hθpos).2 (by simpa [one_mul] using hbudget_ge)
      linarith
    simp [posPart_of_nonpos hnonpos]
  calc
    sectionZFullValue I ℓ lam
        = Finset.sum (prefixRange t1) term + Finset.sum (strictSuffixRange t1) term := by
          simpa [sectionZFullValue, term] using hsplit.symm
    _ = Finset.sum (strictSuffixRange t1) term := by rw [hprefix_zero, zero_add]
    _ ≤ Finset.sum (strictSuffixRange t1) (fun _ => (1 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          have hpp_le_one :
              posPart (1 - sectionPhaseTwoBudgetValue I ℓ m lam / I.program.theta) ≤ 1 := by
            exact posPart_sub_div_le_one
              (sectionPhaseTwoBudgetValue_nonneg (I := I) (le_of_lt hγ) ℓ m hlam.1)
              (I.program.theta_nonneg_of_one_le_Mcoeff (le_of_lt hγ))
          have hμ_nonneg : 0 ≤ Advice.sectionMuDValue I ℓ m lam :=
            Advice.sectionMuDValue_nonneg I ℓ m lam
          have hμ_le_one : Advice.sectionMuDValue I ℓ m lam ≤ 1 :=
            Advice.sectionMuDValue_le_one I ℓ m lam
          nlinarith
    _ = ((strictSuffixRange t1).card : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = futureCount t1 := by
          have hprefixCard : (prefixRange t1).card = t1.1.succ := by
            unfold prefixRange
            calc
              (Finset.univ.filter fun j : Idx n => j ≤ t1).card = min n t1.1.succ := by
                simpa only [Fin.le_def, Nat.lt_succ_iff] using
                  (Fin.card_filter_val_lt (n := n) (m := t1.1.succ))
              _ = t1.1.succ := Nat.min_eq_right t1.is_lt.succ_le
          have hcomp : strictSuffixRange t1 = Finset.univ \ prefixRange t1 := by
            ext i
            simp [strictSuffixRange, prefixRange, not_le]
          have hinter : prefixRange t1 ∩ Finset.univ = prefixRange t1 := by
            ext i
            simp
          change ((strictSuffixRange t1).card : ℝ) = (futureCountNat t1 : ℝ)
          rw [hcomp, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]
          rw [hinter, futureCountNat, hprefixCard]

theorem sectionPhase1DenomFull_pos_of_barTau_lt [NeZero n]
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ t1 : Idx n) {i : Idx n} {lam : ℝ}
    (hlam : 0 ≤ lam ∧ lam ≤ 1)
    (hi : i < t1)
    (hbar : I.program.barTau < sectionPhaseTwoBudgetValue I ℓ t1 lam) :
    0 < futureCount i - I.program.frac * sectionZFullValue I ℓ lam := by
  have hz_le_t1 :
      sectionZFullValue I ℓ lam ≤ futureCount t1 :=
    sectionZFullValue_le_futureCount_of_barTau_lt
      (I := I) hγ hγhi ℓ t1 hlam hbar
  have ht1_lt_i : futureCount t1 < futureCount i := by
    change ((futureCountNat t1 : ℝ) < (futureCountNat i : ℝ))
    exact_mod_cast (ProfileData.futureCountNat_lt_of_lt hi)
  have hz_lt_i : sectionZFullValue I ℓ lam < futureCount i := by
    exact lt_of_le_of_lt hz_le_t1 ht1_lt_i
  have hfrac_le : I.program.frac ≤ 1 := I.program.frac_le_one_of_one_le_Mcoeff (le_of_lt hγ)
  have hfracz_le_z :
      I.program.frac * sectionZFullValue I ℓ lam ≤ sectionZFullValue I ℓ lam := by
    nlinarith [sectionZFullValue_nonneg (I := I) ℓ lam]
  have hfracz_lt_i :
      I.program.frac * sectionZFullValue I ℓ lam < futureCount i := by
    exact lt_of_le_of_lt hfracz_le_z hz_lt_i
  linarith

theorem sectionPhase1Denom_pos_of_lt_t1 [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ t1 t2 : Idx n) {i : Idx n} {lam : ℝ}
    (hi : i < t1) (ht1t2 : t1 ≤ t2) (hlam : 0 ≤ lam) :
    0 < futureCount i - I.program.frac * sectionZValue I ℓ t2 lam := by
  have hz_nonneg : 0 ≤ sectionZValue I ℓ t2 lam := sectionZValue_nonneg (I := I) ℓ t2 lam
  have hz_le_t2 : sectionZValue I ℓ t2 lam ≤ futureCount t2 :=
    sectionZValue_le_futureCount (I := I) hγlo ℓ t2 hlam
  have ht2_le_t1 : futureCount t2 ≤ futureCount t1 :=
    ProfileData.futureCount_antitone ht1t2
  have ht1_lt_i : futureCount t1 < futureCount i := by
    change ((futureCountNat t1 : ℝ) < (futureCountNat i : ℝ))
    exact_mod_cast (ProfileData.futureCountNat_lt_of_lt hi)
  have hz_lt_i : sectionZValue I ℓ t2 lam < futureCount i := by
    exact lt_of_le_of_lt hz_le_t2 (lt_of_le_of_lt ht2_le_t1 ht1_lt_i)
  have hfrac_le : I.program.frac ≤ 1 := I.program.frac_le_one_of_one_le_Mcoeff hγlo
  have hfracz_le_z :
      I.program.frac * sectionZValue I ℓ t2 lam ≤ sectionZValue I ℓ t2 lam := by
    nlinarith
  have hfracz_lt_i :
      I.program.frac * sectionZValue I ℓ t2 lam < futureCount i := by
    exact lt_of_le_of_lt hfracz_le_z hz_lt_i
  linarith

theorem sectionPhaseTwoAfterBudgetValue_ge_theta_of_firstBid_lt_t1 [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ : Idx n) {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    {t1 t2 : Idx n}
    (ht2 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t2? = some t2)
    (ht1t2 : t1 ≤ t2)
    {i : Idx n} (hfi : I.firstBidTime i < t1) :
    I.program.theta ≤ sectionPhaseTwoAfterBudgetValue I ℓ (I.firstBidTime i) lam := by
  let Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam) :=
    Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam
  have hfltlast : I.firstBidTime i < lastIdx n := by
    exact lt_of_lt_of_le hfi (le_trans ht1t2 (le_lastIdx t2))
  rw [sectionPhaseTwoAfterBudgetValue_eq_budget_succ (I := I) ℓ (I.firstBidTime i) lam hfltlast]
  have hsucc_le_t2 : succIdx (I.firstBidTime i) hfltlast ≤ t2 := by
    exact (succIdx_le_iff hfltlast).2 (lt_of_lt_of_le hfi ht1t2)
  have hmono :
      Ξ.beforeBudget t2 ≤ Ξ.beforeBudget (succIdx (I.firstBidTime i) hfltlast) := by
    simpa [PhaseTwoData.beforeBudget] using
      (beforeBudget_antitone_of_nonneg Ξ.hatG2_nonneg hsucc_le_t2)
  have htheta_phase : I.program.theta ≤ Ξ.beforeBudget t2 :=
    PhaseTwoData.beforeBudget_ge_theta_of_t2?_eq_some (Ξ := Ξ) ht2
  have hsucc_eq :
      Ξ.beforeBudget (succIdx (I.firstBidTime i) hfltlast) =
        sectionPhaseTwoBudgetValue I ℓ (succIdx (I.firstBidTime i) hfltlast) lam := by
    exact Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := Ξ) (succIdx (I.firstBidTime i) hfltlast)
  linarith

theorem sectionBoundaryAlphaValue_bounds_of_t1_spec [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ : Idx n) {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    {t1 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t1? = some t1) :
    0 ≤ sectionBoundaryAlphaValue I ℓ t1 lam ∧
      sectionBoundaryAlphaValue I ℓ t1 lam ≤ 1 := by
  let Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam) :=
    Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam
  by_cases hlast : t1 = lastIdx n
  · constructor <;> simp [sectionBoundaryAlphaValue, hlast]
  · have hbefore : I.program.barTau ≤ Ξ.beforeBudget t1 :=
      PhaseTwoData.beforeBudget_ge_barTau_of_t1?_eq_some (Ξ := Ξ) ht1
    have hltlast : t1 < lastIdx n := lt_of_le_of_ne (le_lastIdx t1) hlast
    have hafter_lt : Ξ.afterBudget t1 < I.program.barTau := by
      rw [PhaseTwoData.afterBudget_eq_beforeBudget_succ (Ξ := Ξ) hltlast]
      exact PhaseTwoData.beforeBudget_lt_barTau_of_t1?_eq_some_of_lt
        (Ξ := Ξ) ht1 (lt_succIdx t1 hltlast)
    have hafter_eq :
        Ξ.afterBudget t1 = sectionPhaseTwoAfterBudgetValue I ℓ t1 lam := by
      exact Advice.PhaseTwoData.afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
        (Ξ := Ξ) t1
    have hhat_eq : Ξ.hatG2 t1 = sectionPhaseTwoHatG2Value I ℓ t1 lam := by
      exact Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
        (Ξ := Ξ) t1
    have hden_pos : 0 < sectionPhaseTwoHatG2Value I ℓ t1 lam := by
      have hbefore_eq :
          Ξ.beforeBudget t1 = Ξ.hatG2 t1 + Ξ.afterBudget t1 :=
        Ξ.beforeBudget_eq_self_add_afterBudget t1
      linarith
    have hnum_nonneg : 0 ≤ I.program.barTau - sectionPhaseTwoAfterBudgetValue I ℓ t1 lam := by
      linarith
    have hnum_le_den :
        I.program.barTau - sectionPhaseTwoAfterBudgetValue I ℓ t1 lam ≤
          sectionPhaseTwoHatG2Value I ℓ t1 lam := by
      have hbefore_eq :
          Ξ.beforeBudget t1 = Ξ.hatG2 t1 + Ξ.afterBudget t1 :=
        Ξ.beforeBudget_eq_self_add_afterBudget t1
      linarith
    constructor
    · simpa [sectionBoundaryAlphaValue, hlast] using
        (div_nonneg hnum_nonneg hden_pos.le)
    · have hnum_le_den' :
          I.program.barTau - sectionPhaseTwoAfterBudgetValue I ℓ t1 lam ≤
            1 * sectionPhaseTwoHatG2Value I ℓ t1 lam := by
        simpa using hnum_le_den
      simpa [sectionBoundaryAlphaValue, hlast] using
        ((div_le_iff₀ hden_pos).2 hnum_le_den')

theorem sectionPhase1HatGValue_nonneg_of_le_t2 [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ t1 t2 : Idx n) {i : Idx n} {lam : ℝ}
    (hi : i < t1) (ht1t2 : t1 ≤ t2) (hlam : 0 ≤ lam) :
    0 ≤ sectionPhase1HatGValue I ℓ i (sectionZValue I ℓ t2) lam := by
  unfold sectionPhase1HatGValue sectionPhiValue
  have hmu : 0 ≤ 1 - sectionMuDValue I ℓ i lam := by
    exact sub_nonneg.mpr (Advice.sectionMuDValue_le_one I ℓ i lam)
  have hnum :
      0 ≤ sectionTransitionNumeratorValue I ℓ i lam :=
    sectionTransitionNumeratorValue_nonneg (I := I) hγlo hγhi ℓ i hlam
  have hden_pos :
      0 < futureCount i - I.program.frac * sectionZValue I ℓ t2 lam :=
    sectionPhase1Denom_pos_of_lt_t1 (I := I) hγlo ℓ t1 t2 hi ht1t2 hlam
  have hphi :
      0 ≤ sectionPhiValue I ℓ i (fun _ : ℝ => 0) (sectionZValue I ℓ t2) lam := by
    unfold sectionPhiValue
    simpa using div_nonneg hnum hden_pos.le
  exact mul_nonneg hmu hphi

theorem sectionBoundaryHatGBValue_nonneg_of_t1_spec [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ : Idx n) {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    {t1 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t1? = some t1) :
    0 ≤ sectionBoundaryHatGBValue I ℓ t1 lam := by
  let Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam) :=
    Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam
  by_cases hlast : t1 = lastIdx n
  · simpa [sectionBoundaryHatGBValue, hlast] using
      (Advice.sectionPhaseTwoHatG2Value_nonneg (I := I) hγlo ℓ t1 hlam)
  · have hltlast : t1 < lastIdx n := lt_of_le_of_ne (le_lastIdx t1) hlast
    have hafter_lt : Ξ.afterBudget t1 < I.program.barTau := by
      rw [PhaseTwoData.afterBudget_eq_beforeBudget_succ (Ξ := Ξ) hltlast]
      exact PhaseTwoData.beforeBudget_lt_barTau_of_t1?_eq_some_of_lt
        (Ξ := Ξ) ht1 (lt_succIdx t1 hltlast)
    have hafter_eq :
        Ξ.afterBudget t1 = sectionPhaseTwoAfterBudgetValue I ℓ t1 lam := by
      exact Advice.PhaseTwoData.afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
        (Ξ := Ξ) t1
    simp [sectionBoundaryHatGBValue, hlast]
    linarith

theorem sectionBoundaryHatGAValue_nonneg_of_specs [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ : Idx n) {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    {t1 t2 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t1? = some t1)
    (ht1t2 : t1 ≤ t2) :
    0 ≤ sectionBoundaryHatGAValue I ℓ t1 (sectionZValue I ℓ t2) lam := by
  by_cases hlast : t1 = lastIdx n
  · simp [sectionBoundaryHatGAValue, hlast]
  · have hα := sectionBoundaryAlphaValue_bounds_of_t1_spec (I := I) hγlo ℓ ht1
    have h1α : 0 ≤ 1 - sectionBoundaryAlphaValue I ℓ t1 lam := sub_nonneg.mpr hα.2
    have h1μ : 0 ≤ 1 - sectionMuDValue I ℓ t1 lam := by
      exact sub_nonneg.mpr (Advice.sectionMuDValue_le_one I ℓ t1 lam)
    have hnum :
        0 ≤ sectionTransitionNumeratorValue I ℓ t1 lam :=
      sectionTransitionNumeratorValue_nonneg (I := I) hγlo hγhi ℓ t1 hlam.1
    have hz_nonneg : 0 ≤ sectionZValue I ℓ t2 lam :=
      sectionZValue_nonneg (I := I) ℓ t2 lam
    have hz_le_t2 : sectionZValue I ℓ t2 lam ≤ futureCount t2 :=
      sectionZValue_le_futureCount (I := I) hγlo ℓ t2 hlam.1
    have hz_le_t1 : sectionZValue I ℓ t2 lam ≤ futureCount t1 := by
      exact le_trans hz_le_t2 (ProfileData.futureCount_antitone ht1t2)
    have hfrac_le : I.program.frac ≤ 1 := I.program.frac_le_one_of_one_le_Mcoeff hγlo
    have hfracz_le_t1 : I.program.frac * sectionZValue I ℓ t2 lam ≤ futureCount t1 := by
      have hfracz_le_z :
          I.program.frac * sectionZValue I ℓ t2 lam ≤ sectionZValue I ℓ t2 lam := by
        nlinarith
      exact le_trans hfracz_le_z hz_le_t1
    have hden :
        0 ≤ futureCount t1 +
          sectionBoundaryAlphaValue I ℓ t1 lam * (1 - sectionMuDValue I ℓ t1 lam) -
            I.program.frac * sectionZValue I ℓ t2 lam := by
      have hαμ :
          0 ≤ sectionBoundaryAlphaValue I ℓ t1 lam * (1 - sectionMuDValue I ℓ t1 lam) :=
        mul_nonneg hα.1 h1μ
      nlinarith [futureCount_nonneg t1, hαμ, hfracz_le_t1]
    have hphi :
        0 ≤ sectionPhiValue I ℓ t1 (sectionBoundaryAlphaValue I ℓ t1)
          (sectionZValue I ℓ t2) lam := by
      unfold sectionPhiValue
      exact div_nonneg hnum hden
    have hmain :
        0 ≤
          (1 - sectionBoundaryAlphaValue I ℓ t1 lam) *
            (1 - sectionMuDValue I ℓ t1 lam) *
              sectionPhiValue I ℓ t1 (sectionBoundaryAlphaValue I ℓ t1)
                (sectionZValue I ℓ t2) lam := by
      exact mul_nonneg (mul_nonneg h1α h1μ) hphi
    simpa [sectionBoundaryHatGAValue, hlast] using hmain

theorem beforeBudget_sectionHatGValueAtThreshold_ge_barTau_of_specs [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ : Idx n) {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    {t1 t2 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t1? = some t1)
    (ht1t2 : t1 ≤ t2) :
    I.program.barTau ≤
      beforeBudget (fun i => sectionHatGValueAtThreshold I ℓ t1 t2 i lam) t1 := by
  rw [beforeBudget_sectionHatGValueAtThreshold_t1 (I := I) ℓ t1 t2 lam]
  by_cases hlast : t1 = lastIdx n
  · simp [sectionBoundaryBudgetValue, hlast]
    have hbefore :
        I.program.barTau ≤
          (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).beforeBudget t1 :=
      PhaseTwoData.beforeBudget_ge_barTau_of_t1?_eq_some
        (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) ht1
    have hbefore_eq_phase :
        (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).beforeBudget t1 =
          (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).hatG2 t1 := by
      rw [show t1 = lastIdx n by exact hlast]
      rw [PhaseTwoData.beforeBudget_eq_self_add_afterBudget
        (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam),
        PhaseTwoData.afterBudget_last]
      ring
    have hhat_eq :
        (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).hatG2 t1 =
          sectionPhaseTwoHatG2Value I ℓ t1 lam := by
      exact Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
        (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) t1
    have hbefore_eq :
        (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).beforeBudget t1 =
          sectionPhaseTwoHatG2Value I ℓ t1 lam := by
      rw [hbefore_eq_phase, hhat_eq]
    have hgoal : I.program.barTau ≤ sectionPhaseTwoHatG2Value I ℓ t1 lam := by
      simpa [hbefore_eq] using hbefore
    simpa [sectionBoundaryBudgetValue, hlast] using hgoal
  · have hGA :
      0 ≤ sectionBoundaryHatGAValue I ℓ t1 (sectionZValue I ℓ t2) lam :=
      sectionBoundaryHatGAValue_nonneg_of_specs (I := I) hγlo hγhi ℓ ht1 ht1t2
    simp [sectionBoundaryBudgetValue, hlast]
    linarith

theorem sectionHatGValueAtThreshold_nonneg_of_specs [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ : Idx n) {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    {t1 t2 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t1? = some t1)
    (ht1t2 : t1 ≤ t2) :
    ∀ i : Idx n, 0 ≤ sectionHatGValueAtThreshold I ℓ t1 t2 i lam := by
  intro i
  by_cases hi : i < t1
  · rw [sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ t1 t2 hi]
    exact sectionPhase1HatGValue_nonneg_of_le_t2 (I := I) hγlo hγhi ℓ t1 t2 hi ht1t2 hlam.1
  · by_cases hEq : i = t1
    · subst i
      rw [sectionHatGValueAtThreshold_eq_boundary (I := I) ℓ t1 t2]
      have hGA :
          0 ≤ sectionBoundaryHatGAValue I ℓ t1 (sectionZValue I ℓ t2) lam :=
        sectionBoundaryHatGAValue_nonneg_of_specs (I := I) hγlo hγhi ℓ ht1 ht1t2
      have hGB :
          0 ≤ sectionBoundaryHatGBValue I ℓ t1 lam :=
        sectionBoundaryHatGBValue_nonneg_of_t1_spec (I := I) hγlo ℓ ht1
      linarith
    · have hgt : t1 < i := lt_of_le_of_ne (not_lt.mp hi) (Ne.symm hEq)
      rw [sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ t1 t2 hgt]
      exact Advice.sectionPhaseTwoHatG2Value_nonneg (I := I) hγlo ℓ i hlam

theorem tailBudget_sectionHatGValueAtThreshold_ge_theta_at_firstBid_of_lt_t1_of_specs [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ : Idx n) {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    {t1 t2 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t1? = some t1)
    (ht1t2 : t1 ≤ t2)
    {i : Idx n} (hfi : I.firstBidTime i < t1) :
    I.program.theta ≤
      tailBudget (fun j => sectionHatGValueAtThreshold I ℓ t1 t2 j lam) (I.firstBidTime i) := by
  let hatG := fun j => sectionHatGValueAtThreshold I ℓ t1 t2 j lam
  have hnonneg : ∀ j, 0 ≤ hatG j :=
    sectionHatGValueAtThreshold_nonneg_of_specs (I := I) hγlo hγhi ℓ ht1 ht1t2
  have hfltlast : I.firstBidTime i < lastIdx n := by
    exact lt_of_lt_of_le hfi (le_lastIdx t1)
  rw [tailBudget_eq_beforeBudget_succ (hatG := hatG) hfltlast]
  have hsucc_le_t1 : succIdx (I.firstBidTime i) hfltlast ≤ t1 := by
    exact (succIdx_le_iff hfltlast).2 hfi
  have hmono :
      beforeBudget hatG t1 ≤ beforeBudget hatG (succIdx (I.firstBidTime i) hfltlast) := by
    exact beforeBudget_antitone_of_nonneg hnonneg hsucc_le_t1
  have hbar :
      I.program.barTau ≤ beforeBudget hatG t1 :=
    beforeBudget_sectionHatGValueAtThreshold_ge_barTau_of_specs
      (I := I) hγlo hγhi ℓ ht1 ht1t2
  have hθbar : I.program.theta ≤ I.program.barTau :=
    I.program.theta_le_barTau_of_le_153_div_125 hγlo hγhi
  linarith

end PhaseTwoSectionPath

/-- The advice at the right endpoint `λ = 1` of a section. -/
def sectionRight (I : ProcedureInput n) (ℓ : Idx n) : Advice I :=
  sectionAdvice I ℓ 1 (by constructor <;> norm_num)

def nextSectionLeft (I : ProcedureInput n) (ℓ : Idx n) (hℓ : ℓ < lastIdx n) : Advice I :=
  sectionAdvice I (succIdx ℓ hℓ) 0 (by constructor <;> norm_num)

@[simp] theorem sectionRight_t3Star (I : ProcedureInput n) (ℓ : Idx n) :
    (sectionRight I ℓ).t3Star = ℓ := by
  simp [sectionRight, Advice.sectionAdvice]

@[simp] theorem nextSectionLeft_t3Star
    (I : ProcedureInput n) (ℓ : Idx n) (hℓ : ℓ < lastIdx n) :
    (nextSectionLeft I ℓ hℓ).t3Star = succIdx ℓ hℓ := by
  simp [nextSectionLeft, Advice.sectionAdvice]

@[simp] theorem sectionRight_hatGLast (I : ProcedureInput n) {ℓ : Idx n}
    (hℓ : ℓ < lastIdx n) :
    (sectionRight I ℓ).hatGLast = 0 := by
  simp [sectionRight, Advice.sectionAdvice, ne_of_lt hℓ]

@[simp] theorem nextSectionLeft_hatGLast
    (I : ProcedureInput n) (ℓ : Idx n) (hℓ : ℓ < lastIdx n) :
    (nextSectionLeft I ℓ hℓ).hatGLast = 0 := by
  by_cases hlast : succIdx ℓ hℓ = lastIdx n
  · simp [nextSectionLeft, Advice.sectionAdvice, hlast]
  · simp [nextSectionLeft, Advice.sectionAdvice, hlast]

theorem sectionEndpoint_muD_eq (I : ProcedureInput n) {ℓ : Idx n} (hℓ : ℓ < lastIdx n)
    (j : Idx n) :
    (sectionRight I ℓ).muD j = (nextSectionLeft I ℓ hℓ).muD j := by
  by_cases hlt : ℓ < I.firstBidTime j
  · have hsucc : succIdx ℓ hℓ ≤ I.firstBidTime j := (succIdx_le_iff hℓ).2 hlt
    by_cases hfront : I.firstBidTime j = succIdx ℓ hℓ
    · have hold : (sectionRight I ℓ).muD j = 1 := by
        exact Advice.muD_eq_one (sectionRight I ℓ) hlt
      have hnew : (nextSectionLeft I ℓ hℓ).muD j = 1 := by
        rw [Advice.muD_eq_muStar (nextSectionLeft I ℓ hℓ) hfront]
        by_cases hlast : succIdx ℓ hℓ = lastIdx n
        · simp [nextSectionLeft, Advice.sectionAdvice, hfront, hlast]
        · simp [nextSectionLeft, Advice.sectionAdvice, hfront, hlast, sectionMuValue_zero_eq_one]
      rw [hold, hnew]
    · have hfrontgt : succIdx ℓ hℓ < I.firstBidTime j := lt_of_le_of_ne hsucc (Ne.symm hfront)
      rw [Advice.muD_eq_one (sectionRight I ℓ) hlt,
        Advice.muD_eq_one (nextSectionLeft I ℓ hℓ) hfrontgt]
  · have hle : I.firstBidTime j ≤ ℓ := not_lt.mp hlt
    by_cases hfront : I.firstBidTime j = ℓ
    · have hold : (sectionRight I ℓ).muD j = 0 := by
        rw [Advice.muD_eq_muStar (sectionRight I ℓ) hfront]
        simp [sectionRight, Advice.sectionAdvice, ne_of_lt hℓ, sectionMuValue_one_eq_zero]
      have hnewlt : I.firstBidTime j < succIdx ℓ hℓ := by
        rw [hfront]
        exact lt_succIdx ℓ hℓ
      have hnew : (nextSectionLeft I ℓ hℓ).muD j = 0 := by
        exact Advice.muD_eq_zero (nextSectionLeft I ℓ hℓ) hnewlt
      rw [hold, hnew]
    · have holdlt : I.firstBidTime j < ℓ := lt_of_le_of_ne hle hfront
      have hnewlt : I.firstBidTime j < succIdx ℓ hℓ := by
        exact lt_of_lt_of_le holdlt (le_of_lt (lt_succIdx ℓ hℓ))
      rw [Advice.muD_eq_zero (sectionRight I ℓ) holdlt,
        Advice.muD_eq_zero (nextSectionLeft I ℓ hℓ) hnewlt]

end Advice

/--
The output of the profile-construction procedure before imposing the terminal success
condition `R₀ = 1`. This is the natural object to vary continuously along the advice path.
-/
structure ProcedureRun {n : ℕ} [NeZero n] (I : ProcedureInput n) (Γ : Advice I) where
  phaseTwo : PhaseTwoData I Γ
  t1 : Idx n
  t1_spec : phaseTwo.t1? = some t1
  t1_beforeBudget_ge_barTau : I.program.barTau ≤ phaseTwo.beforeBudget t1
  phaseTwo_afterBudget_t1_lt_barTau :
    t1 ≠ lastIdx n → phaseTwo.afterBudget t1 < I.program.barTau
  phaseTwo_beforeBudget_lt_barTau_above_t1 :
    ∀ ⦃i : Idx n⦄, t1 < i → phaseTwo.beforeBudget i < I.program.barTau
  t2 : Idx n
  t2_spec : phaseTwo.t2? = some t2
  t2_beforeBudget_ge_theta : I.program.theta ≤ phaseTwo.beforeBudget t2
  phaseTwo_beforeBudget_lt_theta_above_t2 :
    ∀ ⦃i : Idx n⦄, t2 < i → phaseTwo.beforeBudget i < I.program.theta
  t1_le_t2 : t1 ≤ t2
  z : ℝ
  z_eq :
    z =
      Finset.sum (strictSuffixRange t2) fun ℓ =>
        posPart (1 - phaseTwo.beforeBudget ℓ / I.program.theta) * Γ.muD ℓ
  z_le_futureCount_t2 : z ≤ futureCount t2
  alpha : ℝ
  alpha_eq :
    alpha =
      if t1 = lastIdx n then
        1
      else
        (I.program.barTau - phaseTwo.afterBudget t1) / phaseTwo.hatG2 t1
  hatG : Idx n → ℝ
  hatGT1A : ℝ
  hatGT1A_eq :
    hatGT1A =
      if t1 = lastIdx n then
        0
      else
        (1 - alpha) * (1 - Γ.muD t1) *
          (1 - posPart (I.program.theta - tailBudget hatG (I.firstBidTime t1))) /
          (futureCount t1 + alpha * (1 - Γ.muD t1) - I.program.frac * z)
  hatGT1B : ℝ
  hatGT1B_eq :
    hatGT1B =
      if t1 = lastIdx n then
        phaseTwo.hatG2 t1
      else
        I.program.barTau - phaseTwo.afterBudget t1
  copied_above_t1 : ∀ ⦃i : Idx n⦄, t1 < i → hatG i = phaseTwo.hatG2 i
  boundary_eq : hatG t1 = hatGT1A + hatGT1B
  phase1_eq :
    ∀ ⦃i : Idx n⦄, i < t1 →
      hatG i =
        (1 - Γ.muD i) * (1 - posPart (I.program.theta - tailBudget hatG (I.firstBidTime i))) /
          (futureCount i - I.program.frac * z)

/-- The explicit fixed-threshold formulas assemble into an actual phase-1/phase-2 run at a
section point once the canonical phase-2 thresholds `t₁,t₂` are fixed there. -/
noncomputable def sectionProcedureRunOfPhaseTwoThresholds
    {n : ℕ} [NeZero n]
    (I : ProcedureInput n)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ : Idx n) (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1)
    {t1 t2 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t1? = some t1)
    (ht2 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t2? = some t2) :
    ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam) where
  phaseTwo := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam
  t1 := t1
  t1_spec := ht1
  t1_beforeBudget_ge_barTau :=
    Advice.PhaseTwoData.beforeBudget_ge_barTau_of_t1?_eq_some
      (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) ht1
  phaseTwo_afterBudget_t1_lt_barTau := by
    intro ht1last
    have hltlast : t1 < lastIdx n := lt_of_le_of_ne (le_lastIdx t1) ht1last
    rw [Advice.PhaseTwoData.afterBudget_eq_beforeBudget_succ
      (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) hltlast]
    exact Advice.PhaseTwoData.beforeBudget_lt_barTau_of_t1?_eq_some_of_lt
      (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) ht1 (lt_succIdx t1 hltlast)
  phaseTwo_beforeBudget_lt_barTau_above_t1 := by
    intro i hi
    exact Advice.PhaseTwoData.beforeBudget_lt_barTau_of_t1?_eq_some_of_lt
      (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) ht1 hi
  t2 := t2
  t2_spec := ht2
  t2_beforeBudget_ge_theta :=
    Advice.PhaseTwoData.beforeBudget_ge_theta_of_t2?_eq_some
      (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) ht2
  phaseTwo_beforeBudget_lt_theta_above_t2 := by
    intro i hi
    exact Advice.PhaseTwoData.beforeBudget_lt_theta_of_t2?_eq_some_of_lt
      (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) ht2 hi
  t1_le_t2 := Advice.PhaseTwoData.t1_le_t2_of_some
    (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) hγlo hγhi ht1 ht2
  z := Advice.sectionZValue I ℓ t2 lam
  z_eq := by
    unfold Advice.sectionZValue
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) m]
    rw [Advice.sectionMuDValue_eq (I := I) (ℓ := ℓ) (j := m) (lam := lam) hlam]
  z_le_futureCount_t2 := Advice.sectionZValue_le_futureCount (I := I) hγlo ℓ t2 hlam.1
  alpha := Advice.sectionBoundaryAlphaValue I ℓ t1 lam
  alpha_eq := by
    by_cases ht1last : t1 = lastIdx n
    · simp [Advice.sectionBoundaryAlphaValue, ht1last]
    · have hafter :=
        Advice.PhaseTwoData.afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
          (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) t1
      have hhat :=
        Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
          (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) t1
      simpa [Advice.sectionBoundaryAlphaValue, ht1last] using
        (show
          (I.program.barTau -
                (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).afterBudget t1) /
              (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).hatG2 t1 =
            (I.program.barTau - Advice.sectionPhaseTwoAfterBudgetValue I ℓ t1 lam) /
              Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam from by
            rw [hafter, hhat]).symm
  hatG := fun i => Advice.sectionHatGValueAtThreshold I ℓ t1 t2 i lam
  hatGT1A := Advice.sectionBoundaryHatGAValue I ℓ t1 (Advice.sectionZValue I ℓ t2) lam
  hatGT1A_eq := by
    by_cases ht1last : t1 = lastIdx n
    · simp [Advice.sectionBoundaryHatGAValue, ht1last]
    · rw [Advice.sectionTransitionNumerator_eq_of_sectionHatGValueAtThreshold_of_firstBid_ge_t1
        (I := I) ℓ t1 t2 (i := t1) (lam := lam) (I.le_firstBidTime t1)]
      simp [Advice.sectionBoundaryHatGAValue, Advice.sectionPhiValue, ht1last,
        Advice.sectionBoundaryAlphaValue,
        Advice.sectionMuDValue_eq (I := I) (ℓ := ℓ) (j := t1) (lam := lam) hlam]
      ring_nf
  hatGT1B := Advice.sectionBoundaryHatGBValue I ℓ t1 lam
  hatGT1B_eq := by
    by_cases ht1last : t1 = lastIdx n
    · rw [Advice.sectionBoundaryHatGBValue, if_pos ht1last]
      simpa [ht1last] using
        (Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
          (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) t1).symm
    · have hafter :=
        Advice.PhaseTwoData.afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
          (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) t1
      simpa [Advice.sectionBoundaryHatGBValue, ht1last] using
        (show
          I.program.barTau -
              (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).afterBudget t1 =
            I.program.barTau - Advice.sectionPhaseTwoAfterBudgetValue I ℓ t1 lam from by
          rw [hafter]).symm
  copied_above_t1 := by
    intro i hi
    rw [Advice.sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ t1 t2 hi]
    exact Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
      (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) i
  boundary_eq := by
    rw [Advice.sectionHatGValueAtThreshold_eq_boundary (I := I) ℓ t1 t2]
  phase1_eq := by
    intro i hi
    by_cases hfi : I.firstBidTime i < t1
    · simpa [Advice.sectionMuDValue_eq (I := I) (ℓ := ℓ) (j := i) (lam := lam) hlam] using
        Advice.sectionHatGValueAtThreshold_eq_phase1Formula_of_tail_ge_theta
        (I := I) ℓ t1 t2 (lam := lam) hi
        (Advice.tailBudget_sectionHatGValueAtThreshold_ge_theta_at_firstBid_of_lt_t1_of_specs
          (I := I) hγlo hγhi ℓ ht1
          (Advice.PhaseTwoData.t1_le_t2_of_some
            (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) hγlo hγhi ht1 ht2)
          hfi)
        (Advice.sectionPhaseTwoAfterBudgetValue_ge_theta_of_firstBid_lt_t1
          (I := I) hγlo ℓ ht2
          (Advice.PhaseTwoData.t1_le_t2_of_some
            (Ξ := Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam) hγlo hγhi ht1 ht2)
          hfi)
    · simpa [Advice.sectionMuDValue_eq (I := I) (ℓ := ℓ) (j := i) (lam := lam) hlam] using
        Advice.sectionHatGValueAtThreshold_eq_phase1Formula_of_firstBid_ge_t1
          (I := I) ℓ t1 t2 (lam := lam) hi (le_of_not_gt hfi)

/--
A raw output of the procedure, allowing the case where the phase-2 search never defines `t₁`.
In that case the procedure stops after phase 2 and the relevant budget is `totalBudget hatG2`.
-/
structure RawProcedureOutput {n : ℕ} [NeZero n] (I : ProcedureInput n) (Γ : Advice I) where
  phaseTwo : PhaseTwoData I Γ
  run? : Option (ProcedureRun I Γ)
  run_phaseTwo : ∀ ⦃C : ProcedureRun I Γ⦄, run? = some C → C.phaseTwo = phaseTwo
  noRun_t1_none : run? = none → phaseTwo.t1? = none

theorem sectionPhaseTwoData_exists_t2_of_t1_spec
    {n : ℕ} [NeZero n]
    (I : ProcedureInput n)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ : Idx n) (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1)
    {t1 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t1? = some t1) :
    ∃ t2 : Idx n,
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t2? = some t2 := by
  let Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam) :=
    Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam
  have hbar : I.program.barTau ≤ Ξ.beforeBudget t1 :=
    Advice.PhaseTwoData.beforeBudget_ge_barTau_of_t1?_eq_some (Ξ := Ξ) ht1
  have htheta : I.program.theta ≤ Ξ.beforeBudget t1 := by
    exact le_trans (I.program.theta_le_barTau_of_le_153_div_125 hγlo hγhi) hbar
  have hmem : t1 ∈ Ξ.t2Candidates := by
    rw [PhaseTwoData.t2Candidates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htheta⟩
  have hne : Ξ.t2Candidates.Nonempty := ⟨t1, hmem⟩
  have hsome : Ξ.t2? ≠ none := by
    unfold PhaseTwoData.t2? finsetMax?
    simp [hne]
  exact Option.ne_none_iff_exists'.mp hsome

/-- Canonical raw output at a section point: stop after phase 2 when `t₁` is absent, otherwise
use the explicit fixed-threshold run built from the canonical phase-2 thresholds. -/
noncomputable def canonicalSectionOutput
    {n : ℕ} [NeZero n]
    (I : ProcedureInput n)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ : Idx n) (x : Set.Icc (0 : ℝ) 1) :
    RawProcedureOutput I (Advice.sectionAdvice I ℓ x.1 ⟨x.2.1, x.2.2⟩) :=
  let Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ x.1 ⟨x.2.1, x.2.2⟩) :=
    Advice.sectionPhaseTwoData (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩
  match ht1 : Ξ.t1? with
  | none =>
      { phaseTwo := Ξ
        run? := none
        run_phaseTwo := by
          intro C h
          cases h
        noRun_t1_none := by
          intro _
          exact ht1 }
  | some t1 =>
      let hexists :=
        sectionPhaseTwoData_exists_t2_of_t1_spec I hγlo hγhi ℓ x.1
          ⟨x.2.1, x.2.2⟩ ht1
      let t2 : Idx n := Classical.choose hexists
      let ht2 : Ξ.t2? = some t2 := Classical.choose_spec hexists
      { phaseTwo := Ξ
        run? := some
          (sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi ℓ x.1 ⟨x.2.1, x.2.2⟩ ht1 ht2)
        run_phaseTwo := by
          intro C h
          cases h
          rfl
        noRun_t1_none := by
          intro h
          cases h }

@[ext] theorem PhaseTwoData.ext
    [NeZero n] {I : ProcedureInput n} {Γ : Advice I}
    {Ξ Ξ' : PhaseTwoData I Γ}
    (hhatG2 : Ξ.hatG2 = Ξ'.hatG2) :
    Ξ = Ξ' := by
  cases Ξ
  cases Ξ'
  cases hhatG2
  simp

theorem PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice
    [NeZero n]
    {I : ProcedureInput n}
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam))
    (hγlo : 1 ≤ I.program.Mcoeff) :
    Ξ = Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam := by
  apply PhaseTwoData.ext
  funext i
  simpa [Advice.sectionPhaseTwoData] using
    Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice (Ξ := Ξ) i

@[ext] theorem ProcedureRun.ext
    [NeZero n] {I : ProcedureInput n} {Γ : Advice I}
    {C C' : ProcedureRun I Γ}
    (hphase : C.phaseTwo = C'.phaseTwo)
    (ht1 : C.t1 = C'.t1)
    (ht2 : C.t2 = C'.t2)
    (hz : C.z = C'.z)
    (halpha : C.alpha = C'.alpha)
    (hhatG : C.hatG = C'.hatG)
    (hhatGT1A : C.hatGT1A = C'.hatGT1A)
    (hhatGT1B : C.hatGT1B = C'.hatGT1B) :
    C = C' := by
  cases C
  cases C'
  cases hphase
  cases ht1
  cases ht2
  cases hz
  cases halpha
  cases hhatG
  cases hhatGT1A
  cases hhatGT1B
  simp

@[ext] theorem RawProcedureOutput.ext
    [NeZero n] {I : ProcedureInput n} {Γ : Advice I}
    {O O' : RawProcedureOutput I Γ}
    (hphase : O.phaseTwo = O'.phaseTwo)
    (hrun : O.run? = O'.run?) :
    O = O' := by
  cases O
  cases O'
  cases hphase
  cases hrun
  simp

namespace RawProcedureOutput

variable [NeZero n] {I : ProcedureInput n} {Γ : Advice I}

/--
The paper's `R₀`, interpreted uniformly across both the `t₁ = ⊥`
and `t₁ ≠ ⊥` cases.
-/
def R0 (O : RawProcedureOutput I Γ) : ℝ :=
  match O.run? with
  | some C => totalBudget C.hatG
  | none => totalBudget O.phaseTwo.hatG2

@[simp] theorem R0_eq_of_none (O : RawProcedureOutput I Γ) (h : O.run? = none) :
    O.R0 = totalBudget O.phaseTwo.hatG2 := by
  simp [RawProcedureOutput.R0, h]

@[simp] theorem R0_eq_of_some (O : RawProcedureOutput I Γ) {C : ProcedureRun I Γ}
    (h : O.run? = some C) :
    O.R0 = totalBudget C.hatG := by
  simp [RawProcedureOutput.R0, h]

end RawProcedureOutput

section RawOutput

variable [NeZero n] (I : ProcedureInput n)

theorem barTau_lt_one_of_one_lt_Mcoeff
    (hγ : 1 < I.program.Mcoeff) :
    I.program.barTau < 1 := by
  have hε : 0 < I.program.epsilon := by
    dsimp [DualProgram.epsilon, DualProgram.Mcoeffmone]
    linarith
  have hτ : 0 < I.program.tau := by
    dsimp [DualProgram.tau]
    nlinarith
  dsimp [DualProgram.barTau]
  linarith

theorem RawProcedureOutput.beforeBudget_first_lt_barTau_of_none
    {Γ : Advice I}
    (O : RawProcedureOutput I Γ)
    (hnone : O.run? = none) :
    O.phaseTwo.beforeBudget (firstIdx n) < I.program.barTau := by
  have ht1none : O.phaseTwo.t1? = none := O.noRun_t1_none hnone
  have hnoneCandidates : ¬ O.phaseTwo.t1Candidates.Nonempty := by
    intro hne
    rw [PhaseTwoData.t1?, finsetMax?] at ht1none
    simp [hne] at ht1none
  have hnotmem : firstIdx n ∉ O.phaseTwo.t1Candidates := by
    intro hmem
    exact hnoneCandidates ⟨firstIdx n, hmem⟩
  have hltbar : O.phaseTwo.beforeBudget (firstIdx n) < I.program.barTau := by
    by_contra hge
    apply hnotmem
    rw [PhaseTwoData.t1Candidates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩
  exact hltbar

theorem RawProcedureOutput.R0_lt_one_of_none
    {Γ : Advice I}
    (O : RawProcedureOutput I Γ)
    (hbar : I.program.barTau < 1)
    (hnone : O.run? = none) :
    O.R0 < 1 := by
  have hltbar : O.phaseTwo.beforeBudget (firstIdx n) < I.program.barTau :=
    O.beforeBudget_first_lt_barTau_of_none I hnone
  rw [RawProcedureOutput.R0_eq_of_none O hnone,
    ← beforeBudget_firstIdx_eq_totalBudget (hatG := O.phaseTwo.hatG2)]
  change O.phaseTwo.beforeBudget (firstIdx n) < 1
  linarith

theorem RawProcedureOutput.run_ne_none_of_R0_eq_one
    {Γ : Advice I}
    (O : RawProcedureOutput I Γ)
    (hbar : I.program.barTau < 1)
    (hR0 : O.R0 = 1) :
    O.run? ≠ none := by
  intro hnone
  have hlt : O.R0 < 1 := O.R0_lt_one_of_none I hbar hnone
  linarith

theorem RawProcedureOutput.exists_run_of_R0_eq_one
    {Γ : Advice I}
    (O : RawProcedureOutput I Γ)
    (hbar : I.program.barTau < 1)
    (hR0 : O.R0 = 1) :
    ∃ C : ProcedureRun I Γ, O.run? = some C := by
  cases hrun : O.run? with
  | none =>
      exact False.elim ((O.run_ne_none_of_R0_eq_one I hbar hR0) hrun)
  | some C =>
      exact ⟨C, rfl⟩

theorem RawProcedureOutput.exists_run_of_ne_none
    {Γ : Advice I}
    (O : RawProcedureOutput I Γ)
    (hrun : O.run? ≠ none) :
    ∃ C : ProcedureRun I Γ, O.run? = some C := by
  cases hO : O.run? with
  | none =>
      exact False.elim (hrun hO)
  | some C =>
      exact ⟨C, rfl⟩

theorem RawProcedureOutput.run_eq_none_of_t1_none
    {Γ : Advice I}
    (O : RawProcedureOutput I Γ)
    (ht1 : O.phaseTwo.t1? = none) :
    O.run? = none := by
  cases hrun : O.run? with
  | none =>
      exact rfl
  | some C =>
      have hspec : O.phaseTwo.t1? = some C.t1 := by
        simpa [O.run_phaseTwo hrun] using C.t1_spec
      rw [ht1] at hspec
      cases hspec

theorem RawProcedureOutput.run_ne_none_of_t1_some
    {Γ : Advice I}
    (O : RawProcedureOutput I Γ)
    {t1 : Idx n}
    (ht1 : O.phaseTwo.t1? = some t1) :
    O.run? ≠ none := by
  intro hnone
  have ht1none : O.phaseTwo.t1? = none := O.noRun_t1_none hnone
  rw [ht1none] at ht1
  cases ht1

theorem RawProcedureOutput.exists_run_eq_thresholds_of_phaseTwo
    {Γ : Advice I}
    (O : RawProcedureOutput I Γ)
    {t1 t2 : Idx n}
    (ht1 : O.phaseTwo.t1? = some t1)
    (ht2 : O.phaseTwo.t2? = some t2)
    (hrun : O.run? ≠ none) :
    ∃ C : ProcedureRun I Γ, O.run? = some C ∧ C.t1 = t1 ∧ C.t2 = t2 := by
  rcases O.exists_run_of_ne_none I hrun with ⟨C, hC⟩
  have hphase : C.phaseTwo = O.phaseTwo := O.run_phaseTwo hC
  have ht1C : C.t1 = t1 := by
    have hspec : O.phaseTwo.t1? = some C.t1 := by simpa [hphase] using C.t1_spec
    have : some C.t1 = some t1 := hspec.symm.trans ht1
    exact Option.some.inj this
  have ht2C : C.t2 = t2 := by
    have hspec : O.phaseTwo.t2? = some C.t2 := by simpa [hphase] using C.t2_spec
    have : some C.t2 = some t2 := hspec.symm.trans ht2
    exact Option.some.inj this
  exact ⟨C, hC, ht1C, ht2C⟩

theorem RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam hlam))
    {t1 : Idx n}
    (hbar : I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam)
    (habove :
      ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau) :
    O.phaseTwo.t1? = some t1 := by
  have hbefore : I.program.barTau ≤ O.phaseTwo.beforeBudget t1 := by
    rw [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) t1]
    exact hbar
  have hmem : t1 ∈ O.phaseTwo.t1Candidates := by
    rw [PhaseTwoData.t1Candidates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbefore⟩
  have hne : O.phaseTwo.t1Candidates.Nonempty := ⟨t1, hmem⟩
  have hmaxmem : O.phaseTwo.t1Candidates.max' hne ∈ O.phaseTwo.t1Candidates :=
    Finset.max'_mem (s := O.phaseTwo.t1Candidates) hne
  have hmax : O.phaseTwo.t1Candidates.max' hne = t1 := by
    apply le_antisymm
    · by_cases hle : O.phaseTwo.t1Candidates.max' hne ≤ t1
      · exact hle
      · have ht1lt : t1 < O.phaseTwo.t1Candidates.max' hne := lt_of_not_ge hle
        have hlt :
            O.phaseTwo.beforeBudget (O.phaseTwo.t1Candidates.max' hne) < I.program.barTau := by
          rw [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
            (Ξ := O.phaseTwo) (O.phaseTwo.t1Candidates.max' hne)]
          exact habove ht1lt
        have hge :
            I.program.barTau ≤
              O.phaseTwo.beforeBudget (O.phaseTwo.t1Candidates.max' hne) := by
          simpa [PhaseTwoData.t1Candidates] using (Finset.mem_filter.mp hmaxmem).2
        linarith
    · exact Finset.le_max' _ _ hmem
  unfold PhaseTwoData.t1? finsetMax?
  simp [hne, hmax]

theorem RawProcedureOutput.t2?_eq_some_of_sectionBudget_ge_theta_of_above_lt_theta
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam hlam))
    {t2 : Idx n}
    (htheta : I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 lam)
    (habove :
      ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta) :
    O.phaseTwo.t2? = some t2 := by
  have hbefore : I.program.theta ≤ O.phaseTwo.beforeBudget t2 := by
    rw [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) t2]
    exact htheta
  have hmem : t2 ∈ O.phaseTwo.t2Candidates := by
    rw [PhaseTwoData.t2Candidates]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbefore⟩
  have hne : O.phaseTwo.t2Candidates.Nonempty := ⟨t2, hmem⟩
  have hmaxmem : O.phaseTwo.t2Candidates.max' hne ∈ O.phaseTwo.t2Candidates :=
    Finset.max'_mem (s := O.phaseTwo.t2Candidates) hne
  have hmax : O.phaseTwo.t2Candidates.max' hne = t2 := by
    apply le_antisymm
    · by_cases hle : O.phaseTwo.t2Candidates.max' hne ≤ t2
      · exact hle
      · have ht2lt : t2 < O.phaseTwo.t2Candidates.max' hne := lt_of_not_ge hle
        have hlt :
            O.phaseTwo.beforeBudget (O.phaseTwo.t2Candidates.max' hne) < I.program.theta := by
          rw [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
            (Ξ := O.phaseTwo) (O.phaseTwo.t2Candidates.max' hne)]
          exact habove ht2lt
        have hge :
            I.program.theta ≤
              O.phaseTwo.beforeBudget (O.phaseTwo.t2Candidates.max' hne) := by
          simpa [PhaseTwoData.t2Candidates] using (Finset.mem_filter.mp hmaxmem).2
        linarith
    · exact Finset.le_max' _ _ hmem
  unfold PhaseTwoData.t2? finsetMax?
  simp [hne, hmax]

end RawOutput

section PhaseTwoOnlyOutput

variable [NeZero n] (I : ProcedureInput n)

theorem sectionPhaseTwoData_t1_eq_none_of_total_lt_barTau
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ : Idx n) (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1)
    (htotal : Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau) :
    (Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam).t1? = none := by
  let Ξ : PhaseTwoData I (Advice.sectionAdvice I ℓ lam hlam) :=
    Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam
  have hnone : ¬ Ξ.t1Candidates.Nonempty := by
    intro hne
    rcases hne with ⟨i, hi⟩
    have hbar : I.program.barTau ≤ Ξ.beforeBudget i := by
      simpa [PhaseTwoData.t1Candidates] using (Finset.mem_filter.mp hi).2
    have hle : Ξ.beforeBudget i ≤ totalBudget Ξ.hatG2 := by
      exact beforeBudget_le_totalBudget_of_nonneg Ξ.hatG2_nonneg i
    have hfirst :
        totalBudget Ξ.hatG2 = Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam := by
      rw [← beforeBudget_firstIdx_eq_totalBudget (hatG := Ξ.hatG2)]
      change beforeBudget (fun k => Advice.sectionPhaseTwoHatG2Value I ℓ k lam) (firstIdx n) =
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam
      exact Advice.beforeBudget_eq_sectionPhaseTwoBudgetValue_explicit (I := I) ℓ lam (firstIdx n)
    linarith
  simp [Ξ, PhaseTwoData.t1?, finsetMax?, hnone]

/-- Raw output for a section point known to stay entirely in Phase 2. -/
noncomputable def sectionPhaseTwoOnlyOutput
    (hγlo : 1 ≤ I.program.Mcoeff)
    (ℓ : Idx n) (x : Set.Icc (0 : ℝ) 1)
    (htotal : Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x.1 < I.program.barTau) :
    RawProcedureOutput I (Advice.sectionAdvice I ℓ x.1 ⟨x.2.1, x.2.2⟩) where
  phaseTwo := Advice.sectionPhaseTwoData (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩
  run? := none
  run_phaseTwo := by
    intro C h
    cases h
  noRun_t1_none := by
    intro _
    exact sectionPhaseTwoData_t1_eq_none_of_total_lt_barTau
      (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩ htotal

theorem rawOutput_eq_sectionPhaseTwoOnlyOutput_of_total_lt_barTau
    [NeZero n]
    (hγlo : 1 ≤ I.program.Mcoeff)
    {ℓ : Idx n} {x : Set.Icc (0 : ℝ) 1}
    (htotal : Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x.1 < I.program.barTau)
    (O : RawProcedureOutput I (Advice.sectionAdvice I ℓ x.1 ⟨x.2.1, x.2.2⟩)) :
    O = sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ x htotal := by
  have hphase :
      O.phaseTwo = Advice.sectionPhaseTwoData (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩ :=
    PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice (Ξ := O.phaseTwo) hγlo
  have hnone : O.run? = none := by
    cases hrun : O.run? with
    | none =>
        rfl
    | some C =>
        have hCphase : C.phaseTwo = O.phaseTwo := O.run_phaseTwo hrun
        have ht1none : C.phaseTwo.t1? = none := by
          rw [hCphase, hphase]
          exact sectionPhaseTwoData_t1_eq_none_of_total_lt_barTau
            (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩ htotal
        rw [C.t1_spec] at ht1none
        cases ht1none
  apply RawProcedureOutput.ext
  · simp [sectionPhaseTwoOnlyOutput, hphase]
  · simp [sectionPhaseTwoOnlyOutput, hnone]

end PhaseTwoOnlyOutput

namespace PhaseTwoData

variable [NeZero n] {I : ProcedureInput n} {ℓ : Idx n} (hℓ : ℓ < lastIdx n)

/-- Reuse a phase-2 execution across the section-endpoint jump
`Γ^ℓ(1) -> Γ^(ℓ+1)(0)`. -/
def toNextSectionLeft
    (Ξ : PhaseTwoData I (Advice.sectionRight I ℓ)) :
    PhaseTwoData I (Advice.nextSectionLeft I ℓ hℓ) where
  hatG2 := Ξ.hatG2
  zero_above_t3 := by
    intro i hi
    have hgt : ℓ < i := lt_trans (lt_succIdx ℓ hℓ) hi
    simpa [Advice.sectionRight, Advice.sectionAdvice] using Ξ.zero_above_t3 hgt
  hatG2_nonneg := Ξ.hatG2_nonneg
  step_eq := by
    intro i hi
    by_cases htop : i = succIdx ℓ hℓ
    · subst htop
      have hzero : Ξ.hatG2 (succIdx ℓ hℓ) = 0 := by
        simpa [Advice.sectionRight, Advice.sectionAdvice] using
          Ξ.zero_above_t3 (lt_succIdx ℓ hℓ)
      by_cases hlast : succIdx ℓ hℓ = lastIdx n
      · have hzeroLast : Ξ.hatG2 (lastIdx n) = 0 := by
          simpa [hlast] using hzero
        simp [Advice.nextSectionLeft, Advice.sectionAdvice, hlast, hzeroLast]
      · have hltf : ℓ < I.firstBidTime (succIdx ℓ hℓ) := by
          exact lt_of_lt_of_le (lt_succIdx ℓ hℓ) (I.le_firstBidTime _)
        have hmuRight : (Advice.sectionRight I ℓ).muD (succIdx ℓ hℓ) = 1 := by
          exact Advice.muD_eq_one (Advice.sectionRight I ℓ) hltf
        have hmu : (Advice.nextSectionLeft I ℓ hℓ).muD (succIdx ℓ hℓ) = 1 := by
          rw [← Advice.sectionEndpoint_muD_eq I hℓ (succIdx ℓ hℓ), hmuRight]
        rw [hzero, hmu]
        simp [Advice.nextSectionLeft, Advice.sectionAdvice, hlast]
    · have hiℓ : i ≤ ℓ := by
        exact (lt_succIdx_iff hℓ).1 (lt_of_le_of_ne hi htop)
      have hstep := Ξ.step_eq i hiℓ
      have hneqLast : i ≠ lastIdx n := by
        intro hiLast
        have hlastle : lastIdx n ≤ ℓ := by simpa [hiLast] using hiℓ
        exact (ne_of_lt hℓ) (le_antisymm (le_lastIdx _) hlastle)
      have hmuEq :
          (Advice.sectionRight I ℓ).muD i = (Advice.nextSectionLeft I ℓ hℓ).muD i :=
        Advice.sectionEndpoint_muD_eq I hℓ i
      rw [hmuEq] at hstep
      simpa [Advice.sectionRight, Advice.nextSectionLeft, Advice.sectionAdvice,
        ne_of_lt hℓ, hneqLast] using hstep

@[simp] theorem toNextSectionLeft_hatG2
    (Ξ : PhaseTwoData I (Advice.sectionRight I ℓ)) :
    (Ξ.toNextSectionLeft hℓ).hatG2 = Ξ.hatG2 := rfl

@[simp] theorem toNextSectionLeft_beforeBudget
    (Ξ : PhaseTwoData I (Advice.sectionRight I ℓ)) (i : Idx n) :
    (Ξ.toNextSectionLeft hℓ).beforeBudget i = Ξ.beforeBudget i := rfl

@[simp] theorem toNextSectionLeft_afterBudget
    (Ξ : PhaseTwoData I (Advice.sectionRight I ℓ)) (i : Idx n) :
    (Ξ.toNextSectionLeft hℓ).afterBudget i = Ξ.afterBudget i := rfl

@[simp] theorem toNextSectionLeft_t1Candidates
    (Ξ : PhaseTwoData I (Advice.sectionRight I ℓ)) :
    (Ξ.toNextSectionLeft hℓ).t1Candidates = Ξ.t1Candidates := rfl

@[simp] theorem toNextSectionLeft_t2Candidates
    (Ξ : PhaseTwoData I (Advice.sectionRight I ℓ)) :
    (Ξ.toNextSectionLeft hℓ).t2Candidates = Ξ.t2Candidates := rfl

@[simp] theorem toNextSectionLeft_t1?
    (Ξ : PhaseTwoData I (Advice.sectionRight I ℓ)) :
    (Ξ.toNextSectionLeft hℓ).t1? = Ξ.t1? := rfl

@[simp] theorem toNextSectionLeft_t2?
    (Ξ : PhaseTwoData I (Advice.sectionRight I ℓ)) :
    (Ξ.toNextSectionLeft hℓ).t2? = Ξ.t2? := rfl

end PhaseTwoData

theorem sectionPhaseTwoData_toNextSectionLeft_eq
    [NeZero n] {I : ProcedureInput n} {ℓ : Idx n} (hℓ : ℓ < lastIdx n)
    (hγlo : 1 ≤ I.program.Mcoeff) :
    (Advice.sectionPhaseTwoData (I := I) hγlo ℓ 1
      (by constructor <;> norm_num)).toNextSectionLeft hℓ =
      Advice.sectionPhaseTwoData (I := I) hγlo (succIdx ℓ hℓ) 0
        (by constructor <;> norm_num) := by
  ext i
  erw [PhaseTwoData.toNextSectionLeft_hatG2]
  simp [Advice.sectionPhaseTwoData, Advice.sectionPhaseTwoHatG2Value_endpoint_eq (I := I) hℓ i]

namespace ProcedureRun

variable [NeZero n] {I : ProcedureInput n} {Γ : Advice I}

/-- The paper's terminal quantity `R₀`, encoded as the total generated budget. -/
def R0 (C : ProcedureRun I Γ) : ℝ :=
  totalBudget C.hatG

@[simp] theorem tailBudget_t1_eq_phaseTwo_afterBudget
    (C : ProcedureRun I Γ) :
    tailBudget C.hatG C.t1 = C.phaseTwo.afterBudget C.t1 := by
  unfold tailBudget PhaseTwoData.afterBudget
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact C.copied_above_t1 (mem_strictSuffixRange.mp hi)

@[simp] theorem beforeBudget_t1_eq_boundaryBudget
    (C : ProcedureRun I Γ) :
    beforeBudget C.hatG C.t1 =
      if _ : C.t1 = lastIdx n then
        C.phaseTwo.hatG2 C.t1
      else
        I.program.barTau + C.hatGT1A := by
  rw [beforeBudget_eq_self_add_tail, C.tailBudget_t1_eq_phaseTwo_afterBudget, C.boundary_eq]
  by_cases ht1 : C.t1 = lastIdx n
  · have hA : C.hatGT1A = 0 := by
      rw [C.hatGT1A_eq, if_pos ht1]
    have hB : C.hatGT1B = C.phaseTwo.hatG2 C.t1 := by
      rw [C.hatGT1B_eq, if_pos ht1]
    have hafter : C.phaseTwo.afterBudget C.t1 = 0 := by
      rw [ht1, PhaseTwoData.afterBudget, tailBudget]
      rw [show strictSuffixRange (lastIdx n) = (∅ : Finset (Idx n)) by
        ext i
        simp [mem_strictSuffixRange, not_lt.mpr (le_lastIdx i)]]
      simp
    rw [ht1] at hB hafter ⊢
    simp [hA, hB, hafter]
  · have hB : C.hatGT1B = I.program.barTau - C.phaseTwo.afterBudget C.t1 := by
      rw [C.hatGT1B_eq, if_neg ht1]
    simp [ht1]
    linarith [hB]

theorem R0_eq_boundaryBudget_add_prefix
    (C : ProcedureRun I Γ) :
    C.R0 =
      (if _ : C.t1 = lastIdx n then
        C.phaseTwo.hatG2 C.t1
      else
        I.program.barTau + C.hatGT1A) +
        Finset.sum (Advice.sectionPhaseOneRange C.t1) C.hatG := by
  unfold ProcedureRun.R0
  calc
    totalBudget C.hatG
      = Finset.sum (Advice.sectionPhaseOneRange C.t1) C.hatG + beforeBudget C.hatG C.t1 := by
          symm
          exact Advice.sum_sectionPhaseOne_add_beforeBudget (hatG := C.hatG) C.t1
    _ = Finset.sum (Advice.sectionPhaseOneRange C.t1) C.hatG +
          (if _ : C.t1 = lastIdx n then
            C.phaseTwo.hatG2 C.t1
          else
            I.program.barTau + C.hatGT1A) := by
          rw [C.beforeBudget_t1_eq_boundaryBudget]
    _ = (if _ : C.t1 = lastIdx n then
          C.phaseTwo.hatG2 C.t1
        else
          I.program.barTau + C.hatGT1A) +
          Finset.sum (Advice.sectionPhaseOneRange C.t1) C.hatG := by
          simp [add_comm]

theorem R0_eq_sectionR0ValueAtThreshold_of_data
    (C : ProcedureRun I Γ)
    (ℓ t1 : Idx n) (z : ℝ → ℝ) (lam : ℝ)
    (ht1 : C.t1 = t1)
    (hboundaryA : C.hatGT1A = Advice.sectionBoundaryHatGAValue I ℓ t1 z lam)
    (hprefix :
      Finset.sum (Advice.sectionPhaseOneRange t1) C.hatG =
        Advice.sectionPhase1PrefixValue I ℓ t1 z lam)
    (hphaseTwo :
      C.phaseTwo.hatG2 t1 = Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam) :
    C.R0 = Advice.sectionR0ValueAtThreshold I ℓ t1 z lam := by
  subst t1
  rw [Advice.sectionR0ValueAtThreshold, C.R0_eq_boundaryBudget_add_prefix, hprefix]
  by_cases hlast : C.t1 = lastIdx n
  · rw [hlast] at hphaseTwo
    simp [Advice.sectionBoundaryBudgetValue, hlast, hphaseTwo]
  · simp [Advice.sectionBoundaryBudgetValue, hlast, hboundaryA]

theorem tailBudget_eq_phaseTwo_afterBudget_of_t1_lt
    (C : ProcedureRun I Γ) {j : Idx n} (hj : C.t1 < j) :
    tailBudget C.hatG j = C.phaseTwo.afterBudget j := by
  unfold tailBudget PhaseTwoData.afterBudget
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact C.copied_above_t1 (lt_trans hj (mem_strictSuffixRange.mp hk))

theorem tailBudget_eq_phaseTwo_afterBudget_of_t1_le
    (C : ProcedureRun I Γ) {j : Idx n} (hj : C.t1 ≤ j) :
    tailBudget C.hatG j = C.phaseTwo.afterBudget j := by
  rcases eq_or_lt_of_le hj with rfl | hj'
  · exact C.tailBudget_t1_eq_phaseTwo_afterBudget
  · exact tailBudget_eq_phaseTwo_afterBudget_of_t1_lt (C := C) hj'

theorem phaseTwo_afterBudget_ge_theta_of_firstBid_lt_t1
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    {i : Idx n} (hfi : I.firstBidTime i < C.t1) :
    I.program.theta ≤ C.phaseTwo.afterBudget (I.firstBidTime i) := by
  have hfltlast : I.firstBidTime i < lastIdx n := by
    exact lt_of_lt_of_le hfi (le_trans C.t1_le_t2 (le_lastIdx C.t2))
  rw [Advice.PhaseTwoData.afterBudget_eq_beforeBudget_succ (Ξ := C.phaseTwo) hfltlast]
  have hsucc_le_t2 : succIdx (I.firstBidTime i) hfltlast ≤ C.t2 := by
    exact (succIdx_le_iff hfltlast).2 (lt_of_lt_of_le hfi C.t1_le_t2)
  have hmono :
      C.phaseTwo.beforeBudget C.t2 ≤
        C.phaseTwo.beforeBudget (succIdx (I.firstBidTime i) hfltlast) := by
    simpa [PhaseTwoData.beforeBudget] using
      (beforeBudget_antitone_of_nonneg C.phaseTwo.hatG2_nonneg hsucc_le_t2)
  exact le_trans C.t2_beforeBudget_ge_theta hmono

theorem phase1Numerator_eq_sectionTransitionNumeratorValue_of_firstBid_ge_t1
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    {i : Idx n} (hfi : C.t1 ≤ I.firstBidTime i) :
    1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) =
      Advice.sectionTransitionNumeratorValue I ℓ i lam := by
  unfold Advice.sectionTransitionNumeratorValue
  rw [C.tailBudget_eq_phaseTwo_afterBudget_of_t1_le hfi]
  rw [Advice.PhaseTwoData.afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) (I.firstBidTime i)]

theorem phase1Numerator_eq_sectionTransitionNumeratorValue_of_firstBid_lt_t1_of_theta_le
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    {i : Idx n} (hfi : I.firstBidTime i < C.t1)
    (htailθ : I.program.theta ≤ tailBudget C.hatG (I.firstBidTime i)) :
    1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) =
      Advice.sectionTransitionNumeratorValue I ℓ i lam := by
  have hphaseθ : I.program.theta ≤ C.phaseTwo.afterBudget (I.firstBidTime i) :=
    C.phaseTwo_afterBudget_ge_theta_of_firstBid_lt_t1 hfi
  have htail_nonpos : I.program.theta - tailBudget C.hatG (I.firstBidTime i) ≤ 0 := by
    linarith
  have hphase_nonpos : I.program.theta - C.phaseTwo.afterBudget (I.firstBidTime i) ≤ 0 := by
    linarith
  unfold Advice.sectionTransitionNumeratorValue
  rw [posPart_of_nonpos htail_nonpos]
  rw [← Advice.PhaseTwoData.afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) (I.firstBidTime i)]
  rw [posPart_of_nonpos hphase_nonpos]

theorem z_le_futureCount_t1
    (C : ProcedureRun I Γ) :
    C.z ≤ futureCount C.t1 := by
  calc
    C.z ≤ futureCount C.t2 := C.z_le_futureCount_t2
    _ ≤ futureCount C.t1 := ProfileData.futureCount_antitone C.t1_le_t2

theorem z_nonneg_of_admissible
    (C : ProcedureRun I Γ) (hΓ : Γ.Admissible) :
    0 ≤ C.z := by
  rw [C.z_eq]
  refine Finset.sum_nonneg ?_
  intro j hj
  exact mul_nonneg (posPart_nonneg _) (Advice.muD_nonneg_of_admissible Γ hΓ j)

theorem alpha_bounds
    (C : ProcedureRun I Γ) :
    0 ≤ C.alpha ∧ C.alpha ≤ 1 := by
  by_cases ht1 : C.t1 = lastIdx n
  · constructor <;> simp [C.alpha_eq, ht1]
  · have hafter_lt : C.phaseTwo.afterBudget C.t1 < I.program.barTau := by
      exact C.phaseTwo_afterBudget_t1_lt_barTau ht1
    have hnum_nonneg : 0 ≤ I.program.barTau - C.phaseTwo.afterBudget C.t1 := by
      linarith
    have hden_pos : 0 < C.phaseTwo.hatG2 C.t1 := by
      have hbefore :
          C.phaseTwo.beforeBudget C.t1 =
            C.phaseTwo.hatG2 C.t1 + C.phaseTwo.afterBudget C.t1 :=
        C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1
      linarith [C.t1_beforeBudget_ge_barTau, hafter_lt, hbefore]
    have hnum_le_den :
        I.program.barTau - C.phaseTwo.afterBudget C.t1 ≤ C.phaseTwo.hatG2 C.t1 := by
      have hbefore :
          C.phaseTwo.beforeBudget C.t1 =
            C.phaseTwo.hatG2 C.t1 + C.phaseTwo.afterBudget C.t1 :=
        C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1
      linarith [C.t1_beforeBudget_ge_barTau, hbefore]
    constructor
    · rw [C.alpha_eq, if_neg ht1]
      exact div_nonneg hnum_nonneg hden_pos.le
    · rw [C.alpha_eq, if_neg ht1]
      exact (div_le_iff₀ hden_pos).2 (by linarith)

theorem phaseTwo_hatG2_pos_at_t1_of_ne_last
    (C : ProcedureRun I Γ) (ht1 : C.t1 ≠ lastIdx n) :
    0 < C.phaseTwo.hatG2 C.t1 := by
  have hafter_lt : C.phaseTwo.afterBudget C.t1 < I.program.barTau := by
    exact C.phaseTwo_afterBudget_t1_lt_barTau ht1
  have hbefore :
      C.phaseTwo.beforeBudget C.t1 =
        C.phaseTwo.hatG2 C.t1 + C.phaseTwo.afterBudget C.t1 :=
    C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1
  linarith [C.t1_beforeBudget_ge_barTau, hafter_lt, hbefore]

theorem phaseTwo_hatG2_pos_at_t1_of_le_153_div_125
    (C : ProcedureRun I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    0 < C.phaseTwo.hatG2 C.t1 := by
  by_cases ht1 : C.t1 = lastIdx n
  · have hbarpos : 0 < I.program.barTau :=
      by
        have hεupper : I.program.epsilon ≤ (28 : ℝ) / 125 := by
          dsimp [DualProgram.epsilon, DualProgram.Mcoeffmone]
          linarith
        have hεnonneg : 0 ≤ I.program.epsilon :=
          I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
        dsimp [DualProgram.barTau, DualProgram.tau]
        nlinarith
    have hbefore :
        C.phaseTwo.beforeBudget C.t1 = C.phaseTwo.hatG2 C.t1 := by
      rw [C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1]
      simp [ht1, Advice.PhaseTwoData.afterBudget_last]
    linarith [C.t1_beforeBudget_ge_barTau, hbarpos, hbefore]
  · exact C.phaseTwo_hatG2_pos_at_t1_of_ne_last ht1

theorem boundaryDenom_pos_of_ne_last_of_admissible
    (C : ProcedureRun I Γ) (hΓ : Γ.Admissible)
    (hγ : 1 < I.program.Mcoeff)
    (ht1 : C.t1 ≠ lastIdx n) :
    0 < futureCount C.t1 + C.alpha * (1 - Γ.muD C.t1) - I.program.frac * C.z := by
  have hγlo : 1 ≤ I.program.Mcoeff := le_of_lt hγ
  have hθpos : 0 < I.program.theta := by
    dsimp [DualProgram.theta, DualProgram.epsilon, DualProgram.Mcoeffmone]
    nlinarith [hγ]
  have hfrac_lt : I.program.frac < 1 := by
    have hεnonneg : 0 ≤ I.program.epsilon :=
      I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
    have hτpos : 0 < I.program.tau := by
      rw [← I.program.epsilon_add_theta_eq_tau]
      linarith
    have hεltτ : I.program.epsilon < I.program.tau := by
      rw [← I.program.epsilon_add_theta_eq_tau]
      linarith
    rw [DualProgram.frac]
    exact (div_lt_one hτpos).2 hεltτ
  have hfcpos : 0 < futureCount C.t1 := by
    change 0 < (futureCountNat C.t1 : ℝ)
    have ht1lt : C.t1 < lastIdx n := lt_of_le_of_ne (le_lastIdx _) ht1
    have ht1val : C.t1.1 < Nat.pred n := Fin.lt_def.mp ht1lt
    have hpredlt : Nat.pred n < n :=
      Nat.pred_lt (show n ≠ 0 from NeZero.ne n)
    have hsucc : C.t1.1.succ < n := lt_of_le_of_lt (Nat.succ_le_of_lt ht1val) hpredlt
    exact_mod_cast Nat.sub_pos_of_lt hsucc
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
    have hfracz_lt_fc : I.program.frac * C.z < futureCount C.t1 := by
      exact lt_of_lt_of_le hfracz_lt hzle
    linarith

theorem hatGT1B_nonneg
    (C : ProcedureRun I Γ) : 0 ≤ C.hatGT1B := by
  by_cases ht1 : C.t1 = lastIdx n
  · simp [C.hatGT1B_eq, ht1, C.phaseTwo.hatG2_nonneg]
  · rw [C.hatGT1B_eq, if_neg ht1]
    linarith [C.phaseTwo_afterBudget_t1_lt_barTau ht1]

theorem tailBudget_nonneg_of_t1_le
    (C : ProcedureRun I Γ) {j : Idx n} (hj : C.t1 ≤ j) :
    0 ≤ tailBudget C.hatG j := by
  rw [C.tailBudget_eq_phaseTwo_afterBudget_of_t1_le hj]
  exact C.phaseTwo.afterBudget_nonneg j

theorem hatGT1A_nonneg_of_admissible
    (C : ProcedureRun I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    0 ≤ C.hatGT1A := by
  by_cases ht1 : C.t1 = lastIdx n
  · simp [C.hatGT1A_eq, ht1]
  · have hα := C.alpha_bounds
    have h1α : 0 ≤ 1 - C.alpha := sub_nonneg.mpr hα.2
    have h1μ : 0 ≤ 1 - Γ.muD C.t1 := by
      exact sub_nonneg.mpr (Advice.muD_le_one_of_admissible Γ hΓ C.t1)
    have htail : 0 ≤ tailBudget C.hatG (I.firstBidTime C.t1) := by
      exact C.tailBudget_nonneg_of_t1_le (I.le_firstBidTime C.t1)
    have hθ : 0 ≤ I.program.theta := I.program.theta_nonneg_of_one_le_Mcoeff hγlo
    have hθle : I.program.theta ≤ 1 :=
      I.program.theta_le_one_of_le_153_div_125 hγlo hγhi
    have hnum3 :
        0 ≤ 1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime C.t1)) := by
      exact one_sub_posPart_sub_nonneg htail hθ hθle
    have hznonneg : 0 ≤ C.z := C.z_nonneg_of_admissible hΓ
    have hzle : C.z ≤ futureCount C.t1 := C.z_le_futureCount_t1
    have hfrac_nonneg : 0 ≤ I.program.frac := I.program.frac_nonneg_of_one_le_Mcoeff hγlo
    have hfrac_le : I.program.frac ≤ 1 := I.program.frac_le_one_of_one_le_Mcoeff hγlo
    have hfracz_le : I.program.frac * C.z ≤ futureCount C.t1 := by
      have hfracz_le_z : I.program.frac * C.z ≤ C.z := by
        nlinarith
      exact le_trans hfracz_le_z hzle
    have hden :
        0 ≤ futureCount C.t1 + C.alpha * (1 - Γ.muD C.t1) - I.program.frac * C.z := by
      have hαμ : 0 ≤ C.alpha * (1 - Γ.muD C.t1) := mul_nonneg hα.1 h1μ
      nlinarith [futureCount_nonneg C.t1, hαμ, hfracz_le]
    rw [C.hatGT1A_eq, if_neg ht1]
    exact div_nonneg (mul_nonneg (mul_nonneg h1α h1μ) hnum3) hden

theorem beforeBudget_t1_ge_barTau_of_admissible
    (C : ProcedureRun I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    I.program.barTau ≤ beforeBudget C.hatG C.t1 := by
  by_cases ht1 : C.t1 = lastIdx n
  · have hbeforeBudget :
        beforeBudget C.hatG C.t1 = C.phaseTwo.hatG2 C.t1 := by
      simpa [ht1] using C.beforeBudget_t1_eq_boundaryBudget
    have hafter0 : C.phaseTwo.afterBudget C.t1 = 0 := by
      rw [ht1]
      exact Advice.PhaseTwoData.afterBudget_last (Ξ := C.phaseTwo)
    have hphase :
        C.phaseTwo.beforeBudget C.t1 = beforeBudget C.hatG C.t1 := by
      calc
        C.phaseTwo.beforeBudget C.t1
            = C.phaseTwo.hatG2 C.t1 + C.phaseTwo.afterBudget C.t1 :=
              C.phaseTwo.beforeBudget_eq_self_add_afterBudget C.t1
        _ = C.phaseTwo.hatG2 C.t1 := by simp [hafter0]
        _ = beforeBudget C.hatG C.t1 := by rw [hbeforeBudget]
    simpa [hphase] using C.t1_beforeBudget_ge_barTau
  · have hbeforeBudget :
        beforeBudget C.hatG C.t1 = I.program.barTau + C.hatGT1A := by
      rw [C.beforeBudget_t1_eq_boundaryBudget]
      simp [ht1]
    have hA : 0 ≤ C.hatGT1A := C.hatGT1A_nonneg_of_admissible hΓ hγlo hγhi
    linarith [hbeforeBudget]

theorem tailBudget_nonneg_at_firstBidTime_of_later_nonneg
    (C : ProcedureRun I Γ) {i : Idx n}
    (hlater : ∀ k, i < k → 0 ≤ C.hatG k) :
    0 ≤ tailBudget C.hatG (I.firstBidTime i) := by
  unfold tailBudget
  refine Finset.sum_nonneg ?_
  intro k hk
  exact hlater k (lt_of_le_of_lt (I.le_firstBidTime i) (mem_strictSuffixRange.mp hk))

theorem phase1Numerator_nonneg_of_later_nonneg
    (C : ProcedureRun I Γ)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (hlater : ∀ k, i < k → 0 ≤ C.hatG k) :
    0 ≤ 1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) := by
  have htail : 0 ≤ tailBudget C.hatG (I.firstBidTime i) :=
    C.tailBudget_nonneg_at_firstBidTime_of_later_nonneg hlater
  exact one_sub_posPart_sub_nonneg htail
    (I.program.theta_nonneg_of_one_le_Mcoeff hγlo)
    (I.program.theta_le_one_of_le_153_div_125 hγlo hγhi)

theorem phase1Denom_nonneg_of_lt_t1
    (C : ProcedureRun I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff)
    {i : Idx n} (hi : i < C.t1) :
    0 ≤ futureCount i - I.program.frac * C.z := by
  have hznonneg : 0 ≤ C.z := C.z_nonneg_of_admissible hΓ
  have hzle : C.z ≤ futureCount C.t1 := C.z_le_futureCount_t1
  have hfrac_nonneg : 0 ≤ I.program.frac := I.program.frac_nonneg_of_one_le_Mcoeff hγlo
  have hfrac_le : I.program.frac ≤ 1 := I.program.frac_le_one_of_one_le_Mcoeff hγlo
  have hfracz_le_z : I.program.frac * C.z ≤ C.z := by
    nlinarith
  have hfracz_le_t1 : I.program.frac * C.z ≤ futureCount C.t1 :=
    le_trans hfracz_le_z hzle
  have ht1le : futureCount C.t1 ≤ futureCount i :=
    ProfileData.futureCount_antitone (le_of_lt hi)
  linarith

theorem hatG_nonneg_of_phase1_of_later_nonneg
    (C : ProcedureRun I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (hi : i < C.t1)
    (hlater : ∀ k, i < k → 0 ≤ C.hatG k) :
    0 ≤ C.hatG i := by
  rw [C.phase1_eq hi]
  have hmu : 0 ≤ 1 - Γ.muD i := by
    exact sub_nonneg.mpr (Advice.muD_le_one_of_admissible Γ hΓ i)
  have hnum :
      0 ≤ 1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) :=
    C.phase1Numerator_nonneg_of_later_nonneg hγlo hγhi hlater
  have hden : 0 ≤ futureCount i - I.program.frac * C.z :=
    C.phase1Denom_nonneg_of_lt_t1 hΓ hγlo hi
  exact div_nonneg (mul_nonneg hmu hnum) hden

theorem hatG_nonneg_of_admissible_and_coeff_bounds
    (C : ProcedureRun I Γ) (hΓ : Γ.Admissible)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    ∀ i, 0 ≤ C.hatG i := by
  have hmain : ∀ m, ∀ i : Idx n, futureCountNat i = m → 0 ≤ C.hatG i := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro i hi
        by_cases hgt : C.t1 < i
        · rw [C.copied_above_t1 hgt]
          exact C.phaseTwo.hatG2_nonneg i
        · by_cases heq : i = C.t1
          · subst heq
            have hA : 0 ≤ C.hatGT1A := C.hatGT1A_nonneg_of_admissible hΓ hγlo hγhi
            have hB : 0 ≤ C.hatGT1B := C.hatGT1B_nonneg
            have hEq : C.hatG C.t1 = C.hatGT1A + C.hatGT1B := C.boundary_eq
            linarith
          · have hlt : i < C.t1 := lt_of_le_of_ne (not_lt.mp hgt) heq
            have hlater : ∀ k, i < k → 0 ≤ C.hatG k := by
              intro k hik
              have hklt : futureCountNat k < m := by
                rw [← hi]
                exact ProfileData.futureCountNat_lt_of_lt hik
              exact ih (futureCountNat k) hklt k rfl
            exact C.hatG_nonneg_of_phase1_of_later_nonneg hΓ hγlo hγhi hlt hlater
  intro i
  exact hmain (futureCountNat i) i rfl

theorem tailBudget_ge_theta_at_firstBid_of_firstBid_lt_t1
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (hfi : I.firstBidTime i < C.t1) :
    I.program.theta ≤ tailBudget C.hatG (I.firstBidTime i) := by
  let hhatG : ∀ j, 0 ≤ C.hatG j :=
    C.hatG_nonneg_of_admissible_and_coeff_bounds (Advice.sectionAdvice_admissible I ℓ lam hlam)
      hγlo hγhi
  have hfltlast : I.firstBidTime i < lastIdx n := by
    exact lt_of_lt_of_le hfi (le_lastIdx C.t1)
  rw [tailBudget_eq_beforeBudget_succ (hatG := C.hatG) hfltlast]
  have hsucc_le_t1 : succIdx (I.firstBidTime i) hfltlast ≤ C.t1 := by
    exact (succIdx_le_iff hfltlast).2 hfi
  have hmono :
      beforeBudget C.hatG C.t1 ≤ beforeBudget C.hatG (succIdx (I.firstBidTime i) hfltlast) := by
    exact beforeBudget_antitone_of_nonneg hhatG hsucc_le_t1
  have hbar_t1 : I.program.barTau ≤ beforeBudget C.hatG C.t1 :=
    C.beforeBudget_t1_ge_barTau_of_admissible (Advice.sectionAdvice_admissible I ℓ lam hlam)
      hγlo hγhi
  have hθbar : I.program.theta ≤ I.program.barTau :=
    I.program.theta_le_barTau_of_le_153_div_125 hγlo hγhi
  linarith

theorem phase1Numerator_eq_sectionTransitionNumeratorValue_of_firstBid_lt_t1
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n} (hfi : I.firstBidTime i < C.t1) :
    1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) =
      Advice.sectionTransitionNumeratorValue I ℓ i lam := by
  apply C.phase1Numerator_eq_sectionTransitionNumeratorValue_of_firstBid_lt_t1_of_theta_le hfi
  exact C.tailBudget_ge_theta_at_firstBid_of_firstBid_lt_t1 hγlo hγhi hfi

theorem phase1Numerator_eq_sectionTransitionNumeratorValue
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (i : Idx n) :
    1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) =
      Advice.sectionTransitionNumeratorValue I ℓ i lam := by
  by_cases hfi : I.firstBidTime i < C.t1
  · exact C.phase1Numerator_eq_sectionTransitionNumeratorValue_of_firstBid_lt_t1
      hγlo hγhi hfi
  · exact C.phase1Numerator_eq_sectionTransitionNumeratorValue_of_firstBid_ge_t1
      (le_of_not_gt hfi)

theorem alpha_eq_sectionBoundaryAlphaValue_of_phaseTwo
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hafter :
      C.phaseTwo.afterBudget C.t1 = Advice.sectionPhaseTwoAfterBudgetValue I ℓ C.t1 lam)
    (hhat2 :
      C.phaseTwo.hatG2 C.t1 = Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam) :
    C.alpha = Advice.sectionBoundaryAlphaValue I ℓ C.t1 lam := by
  by_cases ht1 : C.t1 = lastIdx n
  · simp [C.alpha_eq, Advice.sectionBoundaryAlphaValue, ht1]
  · simp [C.alpha_eq, Advice.sectionBoundaryAlphaValue, ht1, hafter, hhat2]

theorem hatG_eq_sectionPhase1HatGValue_of_phaseTwo
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    {zfun : ℝ → ℝ} {i : Idx n}
    (hi : i < C.t1)
    (hz : C.z = zfun lam)
    (hnum :
      1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) =
        Advice.sectionTransitionNumeratorValue I ℓ i lam) :
    C.hatG i = Advice.sectionPhase1HatGValue I ℓ i zfun lam := by
  rw [C.phase1_eq hi]
  unfold Advice.sectionPhase1HatGValue Advice.sectionPhiValue
  rw [Advice.sectionMuDValue_eq I ℓ i lam hlam, ← hz, hnum]
  ring_nf

theorem hatGT1A_eq_sectionBoundaryHatGAValue_of_phaseTwo
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    {zfun : ℝ → ℝ}
    (hz : C.z = zfun lam)
    (hafter :
      C.phaseTwo.afterBudget C.t1 = Advice.sectionPhaseTwoAfterBudgetValue I ℓ C.t1 lam)
    (hhat2 :
      C.phaseTwo.hatG2 C.t1 = Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam)
    (hnum :
      1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime C.t1)) =
        Advice.sectionTransitionNumeratorValue I ℓ C.t1 lam) :
    C.hatGT1A = Advice.sectionBoundaryHatGAValue I ℓ C.t1 zfun lam := by
  by_cases ht1 : C.t1 = lastIdx n
  · simp [C.hatGT1A_eq, Advice.sectionBoundaryHatGAValue, ht1]
  · have hα : C.alpha = Advice.sectionBoundaryAlphaValue I ℓ C.t1 lam :=
      C.alpha_eq_sectionBoundaryAlphaValue_of_phaseTwo hafter hhat2
    simp [C.hatGT1A_eq, Advice.sectionBoundaryHatGAValue, Advice.sectionPhiValue, ht1,
      Advice.sectionMuDValue_eq I ℓ C.t1 lam hlam, ← hα, ← hz, hnum, div_eq_mul_inv,
      mul_assoc, mul_comm]

theorem phase1Prefix_eq_sectionPhase1PrefixValue_of_phaseTwo
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    {zfun : ℝ → ℝ}
    (hz : C.z = zfun lam)
    (hnum :
      ∀ ⦃i : Idx n⦄, i ≤ C.t1 →
        1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) =
          Advice.sectionTransitionNumeratorValue I ℓ i lam) :
    Finset.sum (Advice.sectionPhaseOneRange C.t1) C.hatG =
      Advice.sectionPhase1PrefixValue I ℓ C.t1 zfun lam := by
  unfold Advice.sectionPhase1PrefixValue
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < C.t1 := by
    simpa [Advice.sectionPhaseOneRange] using hi
  exact C.hatG_eq_sectionPhase1HatGValue_of_phaseTwo hi' hz (hnum (le_of_lt hi'))

theorem R0_eq_sectionR0ValueAtThreshold_of_phaseTwo
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    {zfun : ℝ → ℝ}
    (hz : C.z = zfun lam)
    (hafter :
      C.phaseTwo.afterBudget C.t1 = Advice.sectionPhaseTwoAfterBudgetValue I ℓ C.t1 lam)
    (hhat2 :
      C.phaseTwo.hatG2 C.t1 = Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam)
    (hnum :
      ∀ ⦃i : Idx n⦄, i ≤ C.t1 →
        1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) =
          Advice.sectionTransitionNumeratorValue I ℓ i lam) :
    C.R0 = Advice.sectionR0ValueAtThreshold I ℓ C.t1 zfun lam := by
  apply C.R0_eq_sectionR0ValueAtThreshold_of_data (ℓ := ℓ) (t1 := C.t1) (z := zfun) (lam := lam)
  · rfl
  · exact C.hatGT1A_eq_sectionBoundaryHatGAValue_of_phaseTwo hz hafter hhat2 (hnum le_rfl)
  · exact C.phase1Prefix_eq_sectionPhase1PrefixValue_of_phaseTwo hz hnum
  · exact hhat2

theorem R0_eq_sectionR0ValueAtThreshold_of_sectionAdvice
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {zfun : ℝ → ℝ} (hz : C.z = zfun lam) :
    C.R0 = Advice.sectionR0ValueAtThreshold I ℓ C.t1 zfun lam := by
  apply C.R0_eq_sectionR0ValueAtThreshold_of_phaseTwo (zfun := zfun) hz
  · exact Advice.PhaseTwoData.afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1
  · exact Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1
  · intro i hi
    exact C.phase1Numerator_eq_sectionTransitionNumeratorValue hγlo hγhi i

theorem z_eq_sectionZValue_of_sectionAdvice
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam)) :
    C.z = Advice.sectionZValue I ℓ C.t2 lam := by
  rw [C.z_eq, Advice.sectionZValue]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
    (Ξ := C.phaseTwo) m]
  rw [Advice.sectionMuDValue_eq (I := I) (ℓ := ℓ) (j := m) (lam := lam) hlam]

theorem z_eq_sectionZFullValue_of_sectionAdvice
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγ : 1 < I.program.Mcoeff) :
    C.z = Advice.sectionZFullValue I ℓ lam := by
  have hphase :
      C.phaseTwo = Advice.sectionPhaseTwoData (I := I) (le_of_lt hγ) ℓ lam hlam :=
    PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice C.phaseTwo (le_of_lt hγ)
  have ht2 :
      (Advice.sectionPhaseTwoData (I := I) (le_of_lt hγ) ℓ lam hlam).t2? = some C.t2 := by
    simpa [hphase] using C.t2_spec
  rw [C.z_eq_sectionZValue_of_sectionAdvice]
  exact Advice.sectionZValue_eq_sectionZFullValue_of_t2_spec (I := I) hγ ℓ ht2

theorem sectionPhaseTwoHatG2Value_pos_at_t1_of_sectionAdvice_of_ne_last
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (ht1 : C.t1 ≠ lastIdx n) :
    0 < Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam := by
  simpa [Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
    (Ξ := C.phaseTwo) C.t1] using
    C.phaseTwo_hatG2_pos_at_t1_of_ne_last ht1

theorem sectionPhaseTwoHatG2Value_pos_at_t1_of_sectionAdvice_of_le_153_div_125
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    0 < Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam := by
  simpa [Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
    (Ξ := C.phaseTwo) C.t1] using
    C.phaseTwo_hatG2_pos_at_t1_of_le_153_div_125 hγlo hγhi

theorem sectionBoundaryPhiDenom_pos_of_sectionAdvice_of_ne_last
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγ : 1 < I.program.Mcoeff)
    (ht1 : C.t1 ≠ lastIdx n) :
    0 <
      futureCount C.t1 +
        Advice.sectionBoundaryAlphaValue I ℓ C.t1 lam *
            (1 - Advice.sectionMuDValue I ℓ C.t1 lam) -
          I.program.frac * Advice.sectionZValue I ℓ C.t2 lam := by
  have hΓ : (Advice.sectionAdvice I ℓ lam hlam).Admissible :=
    Advice.sectionAdvice_admissible I ℓ lam hlam
  have hden :=
    C.boundaryDenom_pos_of_ne_last_of_admissible hΓ hγ ht1
  have hafter :
      C.phaseTwo.afterBudget C.t1 = Advice.sectionPhaseTwoAfterBudgetValue I ℓ C.t1 lam :=
    Advice.PhaseTwoData.afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1
  have hhat2 :
      C.phaseTwo.hatG2 C.t1 = Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam :=
    Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1
  have hα :
      C.alpha = Advice.sectionBoundaryAlphaValue I ℓ C.t1 lam :=
    C.alpha_eq_sectionBoundaryAlphaValue_of_phaseTwo hafter hhat2
  have hz : C.z = Advice.sectionZValue I ℓ C.t2 lam :=
    C.z_eq_sectionZValue_of_sectionAdvice
  simpa [hα, hz, Advice.sectionMuDValue_eq (I := I) (ℓ := ℓ) (j := C.t1) (lam := lam) hlam]
    using hden

theorem R0_eq_sectionR0ValueAtThreshold_explicit_of_sectionAdvice
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    C.R0 =
      Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2) lam := by
  exact C.R0_eq_sectionR0ValueAtThreshold_of_sectionAdvice hγlo hγhi
    (C.z_eq_sectionZValue_of_sectionAdvice)

theorem R0_eq_sectionR0ValueAtThreshold_full_of_sectionAdvice
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγ : 1 < I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    C.R0 =
      Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ) lam := by
  exact C.R0_eq_sectionR0ValueAtThreshold_of_sectionAdvice (le_of_lt hγ) hγhi
    (C.z_eq_sectionZFullValue_of_sectionAdvice hγ)

theorem eq_sectionProcedureRunOfPhaseTwoThresholds
    {ℓ : Idx n} {lam : ℝ} {hlam : 0 ≤ lam ∧ lam ≤ 1}
    (C : ProcedureRun I (Advice.sectionAdvice I ℓ lam hlam))
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    C =
      sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi ℓ lam hlam (t1 := C.t1) (t2 := C.t2)
        (by
          have hphase :
              C.phaseTwo = Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam :=
            PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice C.phaseTwo hγlo
          simpa [hphase] using C.t1_spec)
        (by
          have hphase :
              C.phaseTwo = Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam :=
            PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice C.phaseTwo hγlo
          simpa [hphase] using C.t2_spec) := by
  have hphase :
      C.phaseTwo = Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam hlam :=
    PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice C.phaseTwo hγlo
  have hafter :
      C.phaseTwo.afterBudget C.t1 = Advice.sectionPhaseTwoAfterBudgetValue I ℓ C.t1 lam :=
    Advice.PhaseTwoData.afterBudget_eq_sectionPhaseTwoAfterBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1
  have hhat2 :
      C.phaseTwo.hatG2 C.t1 = Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam :=
    Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1
  have hz : C.z = Advice.sectionZValue I ℓ C.t2 lam :=
    C.z_eq_sectionZValue_of_sectionAdvice
  apply ProcedureRun.ext
  · exact hphase
  · rfl
  · rfl
  · exact hz
  · exact C.alpha_eq_sectionBoundaryAlphaValue_of_phaseTwo hafter hhat2
  · funext i
    by_cases hi : i < C.t1
    · calc
        C.hatG i = Advice.sectionPhase1HatGValue I ℓ i (Advice.sectionZValue I ℓ C.t2) lam := by
          exact C.hatG_eq_sectionPhase1HatGValue_of_phaseTwo hi hz
            (C.phase1Numerator_eq_sectionTransitionNumeratorValue hγlo hγhi i)
        _ = Advice.sectionHatGValueAtThreshold I ℓ C.t1 C.t2 i lam := by
          symm
          exact Advice.sectionHatGValueAtThreshold_eq_phase1 (I := I) ℓ C.t1 C.t2 hi
    · by_cases hEq : i = C.t1
      · subst hEq
        have hA :
            C.hatGT1A =
              Advice.sectionBoundaryHatGAValue I ℓ C.t1
                (Advice.sectionZValue I ℓ C.t2) lam :=
          C.hatGT1A_eq_sectionBoundaryHatGAValue_of_phaseTwo hz hafter hhat2
            (C.phase1Numerator_eq_sectionTransitionNumeratorValue hγlo hγhi C.t1)
        have hB :
            C.hatGT1B = Advice.sectionBoundaryHatGBValue I ℓ C.t1 lam := by
          by_cases ht1last : C.t1 = lastIdx n
          · calc
              C.hatGT1B = C.phaseTwo.hatG2 C.t1 := by rw [C.hatGT1B_eq, if_pos ht1last]
              _ = Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam := hhat2
              _ = Advice.sectionBoundaryHatGBValue I ℓ C.t1 lam := by
                simp [Advice.sectionBoundaryHatGBValue, ht1last]
          · calc
              C.hatGT1B = I.program.barTau - C.phaseTwo.afterBudget C.t1 := by
                rw [C.hatGT1B_eq, if_neg ht1last]
              _ = I.program.barTau - Advice.sectionPhaseTwoAfterBudgetValue I ℓ C.t1 lam := by
                rw [hafter]
              _ = Advice.sectionBoundaryHatGBValue I ℓ C.t1 lam := by
                simp [Advice.sectionBoundaryHatGBValue, ht1last]
        calc
          C.hatG C.t1 = C.hatGT1A + C.hatGT1B := by simpa using C.boundary_eq
          _ = Advice.sectionBoundaryHatGAValue I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2) lam +
                Advice.sectionBoundaryHatGBValue I ℓ C.t1 lam := by rw [hA, hB]
          _ = Advice.sectionHatGValueAtThreshold I ℓ C.t1 C.t2 C.t1 lam := by
            rw [Advice.sectionHatGValueAtThreshold_eq_boundary (I := I) ℓ C.t1 C.t2]
      · have hgt : C.t1 < i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hEq)
        calc
          C.hatG i = C.phaseTwo.hatG2 i := C.copied_above_t1 hgt
          _ = Advice.sectionPhaseTwoHatG2Value I ℓ i lam := by
            exact Advice.PhaseTwoData.hatG2_eq_sectionPhaseTwoHatG2Value_of_sectionAdvice
              (Ξ := C.phaseTwo) i
          _ = Advice.sectionHatGValueAtThreshold I ℓ C.t1 C.t2 i lam := by
            symm
            exact Advice.sectionHatGValueAtThreshold_eq_phase2 (I := I) ℓ C.t1 C.t2 hgt
  · exact C.hatGT1A_eq_sectionBoundaryHatGAValue_of_phaseTwo hz hafter hhat2
      (C.phase1Numerator_eq_sectionTransitionNumeratorValue hγlo hγhi C.t1)
  · by_cases ht1last : C.t1 = lastIdx n
    · calc
        C.hatGT1B = C.phaseTwo.hatG2 C.t1 := by rw [C.hatGT1B_eq, if_pos ht1last]
        _ = Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam := hhat2
        _ = (sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi ℓ lam hlam
              (by simpa [hphase] using C.t1_spec)
              (by simpa [hphase] using C.t2_spec)).hatGT1B := by
            simp [sectionProcedureRunOfPhaseTwoThresholds,
              Advice.sectionBoundaryHatGBValue, ht1last]
    · calc
        C.hatGT1B = I.program.barTau - C.phaseTwo.afterBudget C.t1 := by
          rw [C.hatGT1B_eq, if_neg ht1last]
        _ = I.program.barTau - Advice.sectionPhaseTwoAfterBudgetValue I ℓ C.t1 lam := by
          rw [hafter]
        _ = (sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi ℓ lam hlam
              (by simpa [hphase] using C.t1_spec)
              (by simpa [hphase] using C.t2_spec)).hatGT1B := by
            simp [sectionProcedureRunOfPhaseTwoThresholds,
              Advice.sectionBoundaryHatGBValue, ht1last]

def toProfileData (C : ProcedureRun I Γ) (hR0 : C.R0 = 1) :
    ProfileData I Γ where
  phaseTwo := C.phaseTwo
  t1 := C.t1
  t1_spec := C.t1_spec
  t1_beforeBudget_ge_barTau := C.t1_beforeBudget_ge_barTau
  phaseTwo_afterBudget_t1_lt_barTau := C.phaseTwo_afterBudget_t1_lt_barTau
  phaseTwo_beforeBudget_lt_barTau_above_t1 := C.phaseTwo_beforeBudget_lt_barTau_above_t1
  t2 := C.t2
  t2_spec := C.t2_spec
  t2_beforeBudget_ge_theta := C.t2_beforeBudget_ge_theta
  phaseTwo_beforeBudget_lt_theta_above_t2 := C.phaseTwo_beforeBudget_lt_theta_above_t2
  t1_le_t2 := C.t1_le_t2
  z := C.z
  z_eq := C.z_eq
  z_le_futureCount_t2 := C.z_le_futureCount_t2
  alpha := C.alpha
  alpha_eq := C.alpha_eq
  hatG := C.hatG
  hatGT1A := C.hatGT1A
  hatGT1A_eq := C.hatGT1A_eq
  hatGT1B := C.hatGT1B
  hatGT1B_eq := C.hatGT1B_eq
  copied_above_t1 := C.copied_above_t1
  boundary_eq := C.boundary_eq
  phase1_eq := C.phase1_eq
  total_eq_one := hR0

theorem exists_profileData_of_exists_R0_eq_one
    (h : ∃ C : ProcedureRun I Γ, C.R0 = 1) :
    Nonempty (ProfileData I Γ) := by
  rcases h with ⟨C, hR0⟩
  exact ⟨C.toProfileData hR0⟩

end ProcedureRun

namespace RawProcedureOutput

variable [NeZero n] {I : ProcedureInput n} {Γ : Advice I}

theorem R0_eq_sectionR0ValueAtThreshold_of_some
    (O : RawProcedureOutput I Γ) {C : ProcedureRun I Γ}
    (hC : O.run? = some C)
    (ℓ t1 : Idx n) (z : ℝ → ℝ) (lam : ℝ)
    (ht1 : C.t1 = t1)
    (hboundaryA : C.hatGT1A = Advice.sectionBoundaryHatGAValue I ℓ t1 z lam)
    (hprefix :
      Finset.sum (Advice.sectionPhaseOneRange t1) C.hatG =
        Advice.sectionPhase1PrefixValue I ℓ t1 z lam)
    (hphaseTwo :
      C.phaseTwo.hatG2 t1 = Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam) :
    O.R0 = Advice.sectionR0ValueAtThreshold I ℓ t1 z lam := by
  rw [RawProcedureOutput.R0_eq_of_some O hC]
  exact C.R0_eq_sectionR0ValueAtThreshold_of_data ℓ t1 z lam ht1 hboundaryA hprefix hphaseTwo

end RawProcedureOutput

namespace ProcedureRun

variable [NeZero n] {I : ProcedureInput n} {ℓ : Idx n} (hℓ : ℓ < lastIdx n)

/-- Reuse a successful run across the section-endpoint jump
`Γ^ℓ(1) -> Γ^(ℓ+1)(0)`. -/
def toNextSectionLeft
    (C : ProcedureRun I (Advice.sectionRight I ℓ)) :
    ProcedureRun I (Advice.nextSectionLeft I ℓ hℓ) where
  phaseTwo := C.phaseTwo.toNextSectionLeft hℓ
  t1 := C.t1
  t1_spec := by simpa using C.t1_spec
  t1_beforeBudget_ge_barTau := by simpa using C.t1_beforeBudget_ge_barTau
  phaseTwo_afterBudget_t1_lt_barTau := by simpa using C.phaseTwo_afterBudget_t1_lt_barTau
  phaseTwo_beforeBudget_lt_barTau_above_t1 := by
    intro i hi
    simpa using C.phaseTwo_beforeBudget_lt_barTau_above_t1 hi
  t2 := C.t2
  t2_spec := by simpa using C.t2_spec
  t2_beforeBudget_ge_theta := by simpa using C.t2_beforeBudget_ge_theta
  phaseTwo_beforeBudget_lt_theta_above_t2 := by
    intro i hi
    simpa using C.phaseTwo_beforeBudget_lt_theta_above_t2 hi
  t1_le_t2 := C.t1_le_t2
  z := C.z
  z_eq := by
    rw [C.z_eq]
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [Advice.sectionEndpoint_muD_eq I hℓ j]
  z_le_futureCount_t2 := C.z_le_futureCount_t2
  alpha := C.alpha
  alpha_eq := by simpa using C.alpha_eq
  hatG := C.hatG
  hatGT1A := C.hatGT1A
  hatGT1A_eq := by
    have hmu := Advice.sectionEndpoint_muD_eq I hℓ C.t1
    simpa [hmu] using C.hatGT1A_eq
  hatGT1B := C.hatGT1B
  hatGT1B_eq := by simpa using C.hatGT1B_eq
  copied_above_t1 := by
    intro i hi
    simpa using C.copied_above_t1 hi
  boundary_eq := C.boundary_eq
  phase1_eq := by
    intro i hi
    have hmu := Advice.sectionEndpoint_muD_eq I hℓ i
    simpa [hmu] using C.phase1_eq hi

@[simp] theorem toNextSectionLeft_hatG
    (C : ProcedureRun I (Advice.sectionRight I ℓ)) :
    (C.toNextSectionLeft hℓ).hatG = C.hatG := rfl

@[simp] theorem toNextSectionLeft_R0
    (C : ProcedureRun I (Advice.sectionRight I ℓ)) :
    (C.toNextSectionLeft hℓ).R0 = C.R0 := rfl

theorem sectionProcedureRunOfPhaseTwoThresholds_toNextSectionLeft_eq
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ 1
        (by constructor <;> norm_num)).t1? = some t1)
    (ht2 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ 1
        (by constructor <;> norm_num)).t2? = some t2)
    (ht1' :
      (Advice.sectionPhaseTwoData (I := I) hγlo (succIdx ℓ hℓ) 0
        (by constructor <;> norm_num)).t1? = some t1)
    (ht2' :
      (Advice.sectionPhaseTwoData (I := I) hγlo (succIdx ℓ hℓ) 0
        (by constructor <;> norm_num)).t2? = some t2) :
    (sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi ℓ 1
      (by constructor <;> norm_num) ht1 ht2).toNextSectionLeft hℓ =
      sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi (succIdx ℓ hℓ) 0
        (by constructor <;> norm_num) ht1' ht2' := by
  apply ProcedureRun.ext
  · simpa [ProcedureRun.toNextSectionLeft] using!
      (sectionPhaseTwoData_toNextSectionLeft_eq (I := I) hℓ hγlo)
  · rfl
  · rfl
  · exact Advice.sectionZValue_endpoint_eq (I := I) hℓ t2
  · exact Advice.sectionBoundaryAlphaValue_endpoint_eq (I := I) hℓ t1
  · funext i
    exact Advice.sectionHatGValueAtThreshold_endpoint_eq (I := I) hℓ t1 t2 i
  · exact Advice.sectionBoundaryHatGAValue_endpoint_eq (I := I) hℓ t1 t2
  · exact Advice.sectionBoundaryHatGBValue_endpoint_eq (I := I) hℓ t1

theorem exists_eq_R0_toNextSectionLeft
    (C : ProcedureRun I (Advice.sectionRight I ℓ)) :
    ∃ C' : ProcedureRun I (Advice.nextSectionLeft I ℓ hℓ), C'.R0 = C.R0 := by
  exact ⟨C.toNextSectionLeft hℓ, by simp⟩

end ProcedureRun

namespace RawProcedureOutput

variable [NeZero n] {I : ProcedureInput n} {ℓ : Idx n} (hℓ : ℓ < lastIdx n)

/-- Reuse a raw procedure output across the section-endpoint jump
`Γ^ℓ(1) -> Γ^(ℓ+1)(0)`. -/
def toNextSectionLeft
    (O : RawProcedureOutput I (Advice.sectionRight I ℓ)) :
    RawProcedureOutput I (Advice.nextSectionLeft I ℓ hℓ) :=
  match hrun : O.run? with
  | none =>
      { phaseTwo := O.phaseTwo.toNextSectionLeft hℓ
        run? := none
        run_phaseTwo := by
          intro C h
          cases h
        noRun_t1_none := by
          intro _
          simpa using O.noRun_t1_none hrun }
  | some C =>
      let hphase :
          C.phaseTwo.toNextSectionLeft hℓ = O.phaseTwo.toNextSectionLeft hℓ := by
            simpa using congrArg (fun X => X.toNextSectionLeft hℓ) (O.run_phaseTwo hrun)
      { phaseTwo := O.phaseTwo.toNextSectionLeft hℓ
        run? := some (C.toNextSectionLeft hℓ)
        run_phaseTwo := by
          intro C' h
          cases h
          simpa [ProcedureRun.toNextSectionLeft] using hphase
        noRun_t1_none := by
          intro hnone
          cases hnone }

@[simp] theorem toNextSectionLeft_phaseTwo
    (O : RawProcedureOutput I (Advice.sectionRight I ℓ)) :
    (O.toNextSectionLeft hℓ).phaseTwo = O.phaseTwo.toNextSectionLeft hℓ := by
  cases O with
  | mk phaseTwo run run_phaseTwo noRun_t1_none =>
      cases run <;> rfl

@[simp] theorem toNextSectionLeft_run_eq_none
    (O : RawProcedureOutput I (Advice.sectionRight I ℓ))
    (h : O.run? = none) :
    (O.toNextSectionLeft hℓ).run? = none := by
  cases O with
  | mk phaseTwo run run_phaseTwo noRun_t1_none =>
      cases run with
      | none =>
          rfl
      | some C =>
          cases h

@[simp] theorem toNextSectionLeft_run_eq_some
    (O : RawProcedureOutput I (Advice.sectionRight I ℓ))
    {C : ProcedureRun I (Advice.sectionRight I ℓ)}
    (h : O.run? = some C) :
    (O.toNextSectionLeft hℓ).run? = some (C.toNextSectionLeft hℓ) := by
  cases O with
  | mk phaseTwo run run_phaseTwo noRun_t1_none =>
      cases run with
      | none =>
          cases h
      | some C' =>
          cases h
          rfl

@[simp] theorem toNextSectionLeft_R0
    (O : RawProcedureOutput I (Advice.sectionRight I ℓ)) :
    (O.toNextSectionLeft hℓ).R0 = O.R0 := by
  cases O with
  | mk phaseTwo run run_phaseTwo noRun_t1_none =>
      cases run with
      | none =>
          simp [RawProcedureOutput.toNextSectionLeft, RawProcedureOutput.R0]
      | some C =>
          simp [RawProcedureOutput.toNextSectionLeft, RawProcedureOutput.R0,
            ProcedureRun.toNextSectionLeft]

theorem exists_eq_R0_toNextSectionLeft
    (O : RawProcedureOutput I (Advice.sectionRight I ℓ)) :
    ∃ O' : RawProcedureOutput I (Advice.nextSectionLeft I ℓ hℓ), O'.R0 = O.R0 := by
  exact ⟨O.toNextSectionLeft hℓ, by simp⟩

theorem sectionPhaseTwoOnlyOutput_toNextSectionLeft_eq
    (hγlo : 1 ≤ I.program.Mcoeff)
    (htotalRight : Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) 1 < I.program.barTau)
    (htotalLeft :
      Advice.sectionPhaseTwoBudgetValue I (succIdx ℓ hℓ) (firstIdx n) 0 < I.program.barTau) :
    (sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ
      ⟨1, by constructor <;> norm_num⟩ htotalRight).toNextSectionLeft hℓ =
      sectionPhaseTwoOnlyOutput
        (I := I) hγlo (succIdx ℓ hℓ) ⟨0, by constructor <;> norm_num⟩
        htotalLeft := by
  ext
  · rename_i i
    exact congrFun
      (congrArg PhaseTwoData.hatG2
        (sectionPhaseTwoData_toNextSectionLeft_eq (I := I) hℓ hγlo))
      i
  · rfl

end RawProcedureOutput

section GammaZero

variable [NeZero n] (I : ProcedureInput n)

def gammaZeroPhaseTwo : PhaseTwoData I (Advice.gammaZero I) where
  hatG2 := fun _ => 0
  zero_above_t3 := by
    intro i hi
    simp
  hatG2_nonneg := by
    intro i
    simp
  step_eq := by
    intro i hi
    have hifirst : i = firstIdx n := le_antisymm hi (firstIdx_le i)
    subst hifirst
    by_cases hlast : firstIdx n = lastIdx n
    · simp [Advice.gammaZero, Advice.sectionAdvice, hlast]
    · have hmu : (Advice.gammaZero I).muD (firstIdx n) = 1 :=
        Advice.gammaZero_muD_eq_one I (firstIdx n)
      have hfactor : 1 - (Advice.gammaZero I).muD (firstIdx n) = 0 := by
        linarith
      rw [hfactor]
      simp

@[simp] theorem gammaZeroPhaseTwo_beforeBudget_eq_zero (i : Idx n) :
    (gammaZeroPhaseTwo I).beforeBudget i = 0 := by
  simp [gammaZeroPhaseTwo, PhaseTwoData.beforeBudget, beforeBudget]

@[simp] theorem gammaZeroPhaseTwo_R0_eq_zero :
    totalBudget (gammaZeroPhaseTwo I).hatG2 = 0 := by
  simp [gammaZeroPhaseTwo, totalBudget]

theorem barTau_pos_of_le_153_div_125
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    0 < I.program.barTau := by
  have hεupper : I.program.epsilon ≤ (28 : ℝ) / 125 := by
    dsimp [DualProgram.epsilon, DualProgram.Mcoeffmone]
    linarith
  have hεnonneg : 0 ≤ I.program.epsilon := I.program.epsilon_nonneg_of_one_le_Mcoeff hγlo
  dsimp [DualProgram.barTau, DualProgram.tau]
  nlinarith

theorem gammaZeroPhaseTwo_t1_eq_none
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    (gammaZeroPhaseTwo I).t1? = none := by
  have hbarpos : 0 < I.program.barTau := barTau_pos_of_le_153_div_125 I hγlo hγhi
  have hnone : ¬ ((gammaZeroPhaseTwo I).t1Candidates).Nonempty := by
    intro hne
    rcases hne with ⟨i, hi⟩
    have hmem : I.program.barTau ≤ (gammaZeroPhaseTwo I).beforeBudget i := by
      simpa [PhaseTwoData.t1Candidates] using (Finset.mem_filter.mp hi).2
    rw [gammaZeroPhaseTwo_beforeBudget_eq_zero I i] at hmem
    linarith
  simp [PhaseTwoData.t1?, finsetMax?, hnone]

theorem sectionPhaseTwoData_t1_eq_none_at_gammaZero
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    (Advice.sectionPhaseTwoData (I := I) hγlo (firstIdx n) 0 (by constructor <;> norm_num)).t1? =
      none := by
  have hphase :
      Advice.sectionPhaseTwoData (I := I) hγlo (firstIdx n) 0 (by constructor <;> norm_num) =
        gammaZeroPhaseTwo I := by
    symm
    simpa [Advice.gammaZero] using
      (PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice
        (I := I)
        (Ξ := gammaZeroPhaseTwo I)
        (ℓ := firstIdx n)
        (lam := 0)
        (hlam := by constructor <;> norm_num)
        hγlo)
  rw [hphase]
  exact gammaZeroPhaseTwo_t1_eq_none I hγlo hγhi

def gammaZeroOutput
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    RawProcedureOutput I (Advice.gammaZero I) where
  phaseTwo := gammaZeroPhaseTwo I
  run? := none
  run_phaseTwo := by
    intro C h
    cases h
  noRun_t1_none := by
    intro _
    exact gammaZeroPhaseTwo_t1_eq_none I hγlo hγhi

@[simp] theorem gammaZeroOutput_R0_eq_zero
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    (gammaZeroOutput I hγlo hγhi).R0 = 0 := by
  simp [gammaZeroOutput, RawProcedureOutput.R0, gammaZeroPhaseTwo_R0_eq_zero]

theorem gammaZeroOutput_R0_le_one
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    (gammaZeroOutput I hγlo hγhi).R0 ≤ 1 := by
  rw [gammaZeroOutput_R0_eq_zero I hγlo hγhi]
  norm_num

end GammaZero

section GammaOne

variable [NeZero n] (I : ProcedureInput n)

theorem gammaOnePhaseTwo_last_eq_one (Ξ : PhaseTwoData I (Advice.gammaOne I)) :
    Ξ.hatG2 (lastIdx n) = 1 := by
  have hstep := Ξ.step_eq (lastIdx n) (le_lastIdx _)
  simpa [Advice.gammaOne, Advice.sectionAdvice] using hstep

theorem gammaOnePhaseTwo_total_ge_one (Ξ : PhaseTwoData I (Advice.gammaOne I)) :
    1 ≤ totalBudget Ξ.hatG2 := by
  calc
    1 = Ξ.hatG2 (lastIdx n) := by rw [gammaOnePhaseTwo_last_eq_one I Ξ]
    _ ≤ totalBudget Ξ.hatG2 := by
      unfold totalBudget
      exact Finset.single_le_sum (fun i _ => Ξ.hatG2_nonneg i) (Finset.mem_univ _)

theorem barTau_le_one_of_one_le_Mcoeff
    (hγlo : 1 ≤ I.program.Mcoeff) :
    I.program.barTau ≤ 1 := by
  have hτ : 0 ≤ I.program.tau := I.program.tau_nonneg_of_one_le_Mcoeff hγlo
  dsimp [DualProgram.barTau]
  linarith

theorem gammaOnePhaseTwo_t1_exists
    (Ξ : PhaseTwoData I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff) :
    Ξ.t1? ≠ none := by
  have hbar : I.program.barTau ≤ 1 := barTau_le_one_of_one_le_Mcoeff I hγlo
  have hbeforelast : Ξ.beforeBudget (lastIdx n) = 1 := by
    rw [PhaseTwoData.beforeBudget, beforeBudget]
    rw [show suffixRange (lastIdx n) = ({lastIdx n} : Finset (Idx n)) by
      ext i
      constructor
      · intro hi
        have hle : lastIdx n ≤ i := mem_suffixRange.mp hi
        simp [le_antisymm (le_lastIdx _) hle]
      · intro hi
        simp only [Finset.mem_singleton] at hi
        subst hi
        exact mem_suffixRange.mpr le_rfl]
    simp [gammaOnePhaseTwo_last_eq_one I Ξ]
  have hmem : lastIdx n ∈ Ξ.t1Candidates := by
    rw [PhaseTwoData.t1Candidates]
    simp [hbeforelast, hbar]
  have hne : Ξ.t1Candidates.Nonempty := ⟨lastIdx n, hmem⟩
  rw [PhaseTwoData.t1?, finsetMax?]
  simp [hne]

theorem gammaOneRawOutput_run_ne_none
    (O : RawProcedureOutput I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff) :
    O.run? ≠ none := by
  intro hnone
  have ht1none : O.phaseTwo.t1? = none := O.noRun_t1_none hnone
  exact gammaOnePhaseTwo_t1_exists I O.phaseTwo hγlo ht1none

@[simp] theorem gammaOnePhaseTwo_beforeBudget_last_eq_one
    (Ξ : PhaseTwoData I (Advice.gammaOne I)) :
    Ξ.beforeBudget (lastIdx n) = 1 := by
  rw [PhaseTwoData.beforeBudget, beforeBudget]
  rw [show suffixRange (lastIdx n) = ({lastIdx n} : Finset (Idx n)) by
    ext i
    constructor
    · intro hi
      have hle : lastIdx n ≤ i := mem_suffixRange.mp hi
      simp [le_antisymm (le_lastIdx _) hle]
    · intro hi
      simp only [Finset.mem_singleton] at hi
      subst hi
      exact mem_suffixRange.mpr le_rfl]
  simp [gammaOnePhaseTwo_last_eq_one I Ξ]

theorem gammaOneRun_t1_eq_last
    (C : ProcedureRun I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff) :
    C.t1 = lastIdx n := by
  have hmem : lastIdx n ∈ C.phaseTwo.t1Candidates := by
    rw [PhaseTwoData.t1Candidates]
    simp [gammaOnePhaseTwo_beforeBudget_last_eq_one I C.phaseTwo,
      barTau_le_one_of_one_le_Mcoeff I hγlo]
  have hne : C.phaseTwo.t1Candidates.Nonempty := ⟨lastIdx n, hmem⟩
  have hmax :
      C.phaseTwo.t1Candidates.max' hne = C.t1 := by
    have hsome :
        some (C.phaseTwo.t1Candidates.max' hne) = some C.t1 := by
      simpa [PhaseTwoData.t1?, finsetMax?, hne] using C.t1_spec
    exact Option.some.inj hsome
  have hle : lastIdx n ≤ C.t1 := by
    rw [← hmax]
    exact Finset.le_max' _ _ hmem
  exact le_antisymm (le_lastIdx _) hle

theorem gammaOneRun_t2_eq_last
    (C : ProcedureRun I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    C.t2 = lastIdx n := by
  have hθle : I.program.theta ≤ 1 :=
    I.program.theta_le_one_of_le_153_div_125 hγlo hγhi
  have hmem : lastIdx n ∈ C.phaseTwo.t2Candidates := by
    rw [PhaseTwoData.t2Candidates]
    simp [gammaOnePhaseTwo_beforeBudget_last_eq_one I C.phaseTwo, hθle]
  have hne : C.phaseTwo.t2Candidates.Nonempty := ⟨lastIdx n, hmem⟩
  have hmax :
      C.phaseTwo.t2Candidates.max' hne = C.t2 := by
    have hsome :
        some (C.phaseTwo.t2Candidates.max' hne) = some C.t2 := by
      simpa [PhaseTwoData.t2?, finsetMax?, hne] using C.t2_spec
    exact Option.some.inj hsome
  have hle : lastIdx n ≤ C.t2 := by
    rw [← hmax]
    exact Finset.le_max' _ _ hmem
  exact le_antisymm (le_lastIdx _) hle

@[simp] theorem gammaOneRun_z_eq_zero
    (C : ProcedureRun I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    C.z = 0 := by
  rw [C.z_eq, gammaOneRun_t2_eq_last I C hγlo hγhi]
  rw [show strictSuffixRange (lastIdx n) = (∅ : Finset (Idx n)) by
    ext i
    simp [mem_strictSuffixRange, not_lt.mpr (le_lastIdx i)]]
  simp

@[simp] theorem gammaOneRun_hatG_last_eq_one
    (C : ProcedureRun I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff) :
    C.hatG (lastIdx n) = 1 := by
  have ht1 : C.t1 = lastIdx n := gammaOneRun_t1_eq_last I C hγlo
  have hA : C.hatGT1A = 0 := by
    rw [C.hatGT1A_eq, if_pos ht1]
  have hB : C.hatGT1B = 1 := by
    rw [C.hatGT1B_eq, if_pos ht1]
    simpa [ht1] using gammaOnePhaseTwo_last_eq_one I C.phaseTwo
  calc
    C.hatG (lastIdx n) = C.hatGT1A + C.hatGT1B := by simpa [ht1] using C.boundary_eq
    _ = 1 := by rw [hA, hB]; ring

theorem gammaOneRun_tailBudget_nonneg_at_firstBidTime_of_later_nonneg
    (C : ProcedureRun I (Advice.gammaOne I))
    {i : Idx n}
    (hlater : ∀ k, i < k → 0 ≤ C.hatG k) :
    0 ≤ tailBudget C.hatG (I.firstBidTime i) := by
  unfold tailBudget
  refine Finset.sum_nonneg ?_
  intro k hk
  exact hlater k (lt_of_le_of_lt (I.le_firstBidTime i) (mem_strictSuffixRange.mp hk))

theorem gammaOneRun_phase1Numerator_nonneg_of_later_nonneg
    (C : ProcedureRun I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {i : Idx n}
    (hlater : ∀ k, i < k → 0 ≤ C.hatG k) :
    0 ≤ 1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) := by
  have htail : 0 ≤ tailBudget C.hatG (I.firstBidTime i) :=
    gammaOneRun_tailBudget_nonneg_at_firstBidTime_of_later_nonneg I C hlater
  exact one_sub_posPart_sub_nonneg htail
    (I.program.theta_nonneg_of_one_le_Mcoeff hγlo)
    (I.program.theta_le_one_of_le_153_div_125 hγlo hγhi)

theorem gammaOneRun_hatG_nonneg
    (C : ProcedureRun I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    ∀ i, 0 ≤ C.hatG i := by
  have ht1 : C.t1 = lastIdx n := gammaOneRun_t1_eq_last I C hγlo
  have hz : C.z = 0 := gammaOneRun_z_eq_zero I C hγlo hγhi
  have hΓ : (Advice.gammaOne I).Admissible := Advice.gammaOne_admissible I
  have hmain : ∀ m, ∀ i : Idx n, futureCountNat i = m → 0 ≤ C.hatG i := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro i hi
        by_cases hlast : i = lastIdx n
        · subst hlast
          simp [gammaOneRun_hatG_last_eq_one I C hγlo]
        · have hlt : i < lastIdx n := lt_of_le_of_ne (le_lastIdx _) hlast
          have hlater : ∀ k, i < k → 0 ≤ C.hatG k := by
            intro k hik
            have hklt : futureCountNat k < m := by
              rw [← hi]
              exact ProfileData.futureCountNat_lt_of_lt hik
            exact ih (futureCountNat k) hklt k rfl
          have hmu : 0 ≤ 1 - (Advice.gammaOne I).muD i := by
            exact sub_nonneg.mpr (Advice.muD_le_one_of_admissible (Advice.gammaOne I) hΓ i)
          have hnum :
              0 ≤ 1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i)) :=
            gammaOneRun_phase1Numerator_nonneg_of_later_nonneg I C hγlo hγhi hlater
          have hfc : 0 ≤ futureCount i := futureCount_nonneg i
          have hlt_t1 : i < C.t1 := by simpa [ht1] using hlt
          have hdiv :
              0 ≤
                (1 - (Advice.gammaOne I).muD i) *
                    (1 - posPart (I.program.theta - tailBudget C.hatG (I.firstBidTime i))) /
                  (futureCount i - I.program.frac * 0) := by
            exact div_nonneg (mul_nonneg hmu hnum) (by simp [hfc])
          simpa [C.phase1_eq hlt_t1, hz] using hdiv
  intro i
  exact hmain (futureCountNat i) i rfl

theorem gammaOneRun_R0_ge_one
    (C : ProcedureRun I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    1 ≤ C.R0 := by
  calc
    1 = C.hatG (lastIdx n) := by rw [gammaOneRun_hatG_last_eq_one I C hγlo]
    _ ≤ totalBudget C.hatG := by
      unfold totalBudget
      exact Finset.single_le_sum
        (fun i _ => gammaOneRun_hatG_nonneg I C hγlo hγhi i)
        (Finset.mem_univ _)

theorem gammaOneOutput_R0_ge_one
    (O : RawProcedureOutput I (Advice.gammaOne I))
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    1 ≤ O.R0 := by
  cases hrun : O.run? with
  | none =>
      exact False.elim ((gammaOneRawOutput_run_ne_none I O hγlo) hrun)
  | some C =>
      rw [RawProcedureOutput.R0_eq_of_some O hrun]
      exact gammaOneRun_R0_ge_one I C hγlo hγhi

end GammaOne

/--
A sectionwise scalar path `F_ℓ(λ)` on `λ ∈ [0,1]`, with continuity on each section,
matching values at section boundaries, and endpoint bounds straddling `1`.
This is the abstract reduction needed before proving continuity for the concrete
`R₀` values produced by the advice path.
-/
structure SectionScalarPath (n : ℕ) [NeZero n] where
  value : Idx n → ℝ → ℝ
  continuous : ∀ ℓ, ContinuousOn (value ℓ) (Set.Icc (0 : ℝ) 1)
  glue : ∀ {ℓ : Idx n} (hℓ : ℓ < lastIdx n), value ℓ 1 = value (succIdx ℓ hℓ) 0
  left_le_one : value (firstIdx n) 0 ≤ 1
  right_ge_one : 1 ≤ value (lastIdx n) 1

namespace SectionScalarPath

variable [NeZero n] (P : SectionScalarPath n)

theorem exists_eq_one :
    ∃ ℓ : Idx n, ∃ lam : ℝ, lam ∈ Set.Icc (0 : ℝ) 1 ∧ P.value ℓ lam = 1 := by
  let p : ℕ → Prop := fun m => ∃ hm : m < n, 1 ≤ P.value ⟨m, hm⟩ 1
  have hex : ∃ m, p m := by
    refine ⟨Nat.pred n, ?_⟩
    refine ⟨Nat.pred_lt (show n ≠ 0 from NeZero.ne n), ?_⟩
    simpa [lastIdx] using P.right_ge_one
  let k := Nat.find hex
  have hk : p k := Nat.find_spec hex
  rcases hk with ⟨hklt, hkge⟩
  let ℓ : Idx n := ⟨k, hklt⟩
  have hstart : P.value ℓ 0 ≤ 1 := by
    by_cases hk0 : k = 0
    · have hℓ : ℓ = firstIdx n := by
        apply Fin.ext
        simp [ℓ, firstIdx, hk0]
      simpa [hℓ] using P.left_le_one
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      let prev : Idx n := ⟨k - 1, by
        have hsublt : k - 1 < k := by omega
        exact lt_trans hsublt hklt⟩
      have hprevnot : ¬ p (k - 1) := Nat.find_min hex (by omega)
      have hprevlast : prev < lastIdx n := by
        change k - 1 < Nat.pred n
        have hsublt : k - 1 < k := by omega
        exact lt_of_lt_of_le hsublt (Nat.le_pred_of_lt hklt)
      have hglue : P.value prev 1 = P.value ℓ 0 := by
        simpa [prev, ℓ, succIdx_pred hkpos hklt] using
          P.glue (ℓ := prev) hprevlast
      by_contra hgt
      have hprevge : 1 ≤ P.value prev 1 := by
        linarith [hglue]
      exact hprevnot ⟨by omega, hprevge⟩
  have hsurj := (P.continuous ℓ).surjOn_Icc (a := (0 : ℝ)) (b := 1) (by simp) (by simp)
  have hend : 1 ≤ P.value ℓ 1 := by
    simpa [ℓ] using hkge
  have htarget : 1 ∈ Set.Icc (P.value ℓ 0) (P.value ℓ 1) := ⟨hstart, hend⟩
  have hhit : 1 ∈ (P.value ℓ) '' Set.Icc (0 : ℝ) 1 := hsurj htarget
  rcases hhit with ⟨lam, hlam, hlamval⟩
  exact ⟨ℓ, lam, hlam, hlamval⟩

end SectionScalarPath

structure SectionRawOutputChoice (n : ℕ) [NeZero n] (I : ProcedureInput n) (ℓ : Idx n) where
  output :
    ∀ x : Set.Icc (0 : ℝ) 1,
      RawProcedureOutput I (Advice.sectionAdvice I ℓ x.1 ⟨x.2.1, x.2.2⟩)

namespace SectionRawOutputChoice

variable [NeZero n] {I : ProcedureInput n} {ℓ : Idx n}

/-- The scalar `R₀` map attached to a single section choice of outputs. -/
noncomputable def value (Q : SectionRawOutputChoice n I ℓ) (lam : ℝ) : ℝ :=
  if hlam : lam ∈ Set.Icc (0 : ℝ) 1 then
    (Q.output ⟨lam, hlam⟩).R0
  else
    0

/--
A local witness that `Q.value` is continuous around a given parameter `λ`,
inside the ambient section interval `[0,1]`.
-/
structure LocalContinuityWitness (Q : SectionRawOutputChoice n I ℓ) (lam : ℝ) where
  s : Set ℝ
  hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1)
  continuousOn_value : ContinuousOn Q.value s

namespace LocalContinuityWitness

theorem continuousWithinAt
    {Q : SectionRawOutputChoice n I ℓ} {lam : ℝ}
    (W : LocalContinuityWitness Q lam)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  have hcont_s : ContinuousWithinAt Q.value W.s lam :=
    W.continuousOn_value lam (mem_of_mem_nhdsWithin hlam W.hs_nhdsWithin)
  exact hcont_s.mono_of_mem_nhdsWithin W.hs_nhdsWithin

end LocalContinuityWitness

theorem continuousOn_of_localWitnesses
    (Q : SectionRawOutputChoice n I ℓ)
    (hlocal :
      ∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 →
        LocalContinuityWitness Q lam) :
    ContinuousOn Q.value (Set.Icc (0 : ℝ) 1) := by
  intro lam hlam
  exact (hlocal lam hlam).continuousWithinAt hlam

theorem continuousWithinAt_interval_iff_left_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ} :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam ↔
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam ∧
        ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam := by
  simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
    (continuousWithinAt_iff_continuous_left_right
      (s := Set.Icc (0 : ℝ) 1) (f := Q.value) (a := lam))

theorem continuousWithinAt_interval_of_left_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hleft : ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam)
    (hright : ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  exact (Q.continuousWithinAt_interval_iff_left_right).2 ⟨hleft, hright⟩

theorem continuousWithinAt_interval_of_eqOn_left_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {fL fR : ℝ → ℝ}
    (hcontL : ContinuousOn fL (Set.Icc (0 : ℝ) 1))
    (hcontR : ContinuousOn fR (Set.Icc (0 : ℝ) 1))
    (hEqL : Set.EqOn Q.value fL (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hEqR : Set.EqOn Q.value fR (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam)) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  have hleftModel : ContinuousWithinAt fL (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam :=
    (hcontL lam hlam).mono (by intro x hx; exact hx.1)
  have hleftEq : Q.value lam = fL lam := by
    exact hEqL ⟨hlam, by simp⟩
  have hleft :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam :=
    hleftModel.congr_mono hEqL (by intro x hx; exact hx) hleftEq
  have hrightModel : ContinuousWithinAt fR (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam :=
    (hcontR lam hlam).mono (by intro x hx; exact hx.1)
  have hrightEq : Q.value lam = fR lam := by
    exact hEqR ⟨hlam, by simp⟩
  have hright :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam :=
    hrightModel.congr_mono hEqR (by intro x hx; exact hx) hrightEq
  exact Q.continuousWithinAt_interval_of_left_right hleft hright

theorem continuousWithinAt_interval_of_eventuallyEq_left_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {fL fR : ℝ → ℝ}
    (hcontL : ContinuousOn fL (Set.Icc (0 : ℝ) 1))
    (hcontR : ContinuousOn fR (Set.Icc (0 : ℝ) 1))
    (hEqL :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam)] fL)
    (hEqR :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam)] fR) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  have hleftModel : ContinuousWithinAt fL (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam :=
    (hcontL lam hlam).mono (by intro x hx; exact hx.1)
  have hleft :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam :=
    hleftModel.congr_of_eventuallyEq_of_mem hEqL ⟨hlam, by simp⟩
  have hrightModel : ContinuousWithinAt fR (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam :=
    (hcontR lam hlam).mono (by intro x hx; exact hx.1)
  have hright :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam :=
    hrightModel.congr_of_eventuallyEq_of_mem hEqR ⟨hlam, by simp⟩
  exact Q.continuousWithinAt_interval_of_left_right hleft hright

theorem continuousWithinAt_interval_of_eqOn_mem_left_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {fL fR : ℝ → ℝ} {sL sR : Set ℝ}
    (hcontL : ContinuousOn fL (Set.Icc (0 : ℝ) 1))
    (hcontR : ContinuousOn fR (Set.Icc (0 : ℝ) 1))
    (hsL : sL ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsR : sR ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hEqL : Set.EqOn Q.value fL sL)
    (hEqR : Set.EqOn Q.value fR sR) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  refine
    Q.continuousWithinAt_interval_of_eventuallyEq_left_right hlam hcontL hcontR ?_ ?_
  · exact Filter.mem_of_superset hsL hEqL
  · exact Filter.mem_of_superset hsR hEqR

theorem continuousWithinAt_interval_iff_left'_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ} :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam ↔
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam ∧
        ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam := by
  constructor
  · intro h
    rcases
      (continuousWithinAt_iff_continuous_left'_right'
        (s := Set.Icc (0 : ℝ) 1) (f := Q.value) (a := lam)).1 h with
      ⟨hleft, hright⟩
    exact ⟨hleft, (continuousWithinAt_inter_Ioi_iff_Ici).1 hright⟩
  · intro h
    rcases h with ⟨hleft, hright⟩
    exact
      (continuousWithinAt_iff_continuous_left'_right'
        (s := Set.Icc (0 : ℝ) 1) (f := Q.value) (a := lam)).2
        ⟨hleft, (continuousWithinAt_inter_Ioi_iff_Ici).2 hright⟩

theorem continuousWithinAt_interval_of_left'_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hleft : ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam)
    (hright : ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  exact (Q.continuousWithinAt_interval_iff_left'_right).2 ⟨hleft, hright⟩

theorem continuousWithinAt_interval_of_eqOn_mem_left'_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {fL fR : ℝ → ℝ} {sL sR : Set ℝ}
    (hcontL : ContinuousOn fL (Set.Icc (0 : ℝ) 1))
    (hcontR : ContinuousOn fR (Set.Icc (0 : ℝ) 1))
    (hsL : sL ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam))
    (hsR : sR ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hEqL : Set.EqOn Q.value fL sL)
    (hEqR : Set.EqOn Q.value fR sR)
    (hEqAtL : Q.value lam = fL lam) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  have hleftModel : ContinuousWithinAt fL (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam :=
    (hcontL lam hlam).mono (by intro x hx; exact hx.1)
  have hEqLEventually :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam)] fL :=
    Filter.mem_of_superset hsL hEqL
  have hleft :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam :=
    hleftModel.congr_of_eventuallyEq hEqLEventually hEqAtL
  have hrightModel : ContinuousWithinAt fR (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam :=
    (hcontR lam hlam).mono (by intro x hx; exact hx.1)
  have hlamRight : lam ∈ sR := by
    have hmem : lam ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam := by
      exact ⟨hlam, by simp⟩
    exact mem_of_mem_nhdsWithin hmem hsR
  have hEqAtR : Q.value lam = fR lam := hEqR hlamRight
  have hEqREventually :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam)] fR :=
    Filter.mem_of_superset hsR hEqR
  have hright :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam :=
    hrightModel.congr_of_eventuallyEq hEqREventually hEqAtR
  exact Q.continuousWithinAt_interval_of_left'_right hleft hright

theorem value_eq_sectionPhaseTwoBudget_of_total_lt_barTau
    (Q : SectionRawOutputChoice n I ℓ)
    (hγlo : 1 ≤ I.program.Mcoeff)
    {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (htotal : Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau) :
    Q.value lam = Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam := by
  let x : Set.Icc (0 : ℝ) 1 := ⟨lam, hlam⟩
  have hEq :
      Q.output x = sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ x htotal :=
    rawOutput_eq_sectionPhaseTwoOnlyOutput_of_total_lt_barTau
      (I := I) hγlo htotal (Q.output x)
  rw [SectionRawOutputChoice.value, dif_pos hlam, hEq]
  rw [RawProcedureOutput.R0_eq_of_none
    (sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ x htotal) rfl]
  rw [← beforeBudget_firstIdx_eq_totalBudget
    (hatG := (sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ x htotal).phaseTwo.hatG2)]
  exact Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
    (Ξ := (sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ x htotal).phaseTwo) (firstIdx n)

def localContinuityWitness_phaseTwoOnly
    (Q : SectionRawOutputChoice n I ℓ)
    (hγlo : 1 ≤ I.program.Mcoeff)
    {lam : ℝ} (s : Set ℝ)
    (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
    (hs_subset : s ⊆ Set.Icc (0 : ℝ) 1)
    (hsmall :
      ∀ x, x ∈ s →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau) :
    LocalContinuityWitness Q lam where
  s := s
  hs_nhdsWithin := hs_nhdsWithin
  continuousOn_value :=
    ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ (firstIdx n)).continuousOn).congr_mono
      (fun x hx =>
        Q.value_eq_sectionPhaseTwoBudget_of_total_lt_barTau hγlo (hs_subset hx) (hsmall x hx))
      (Set.subset_univ s)

end SectionRawOutputChoice

structure PhaseTwoOnlySectionOutputFamily
    (n : ℕ) [NeZero n] (I : ProcedureInput n) (ℓ : Idx n)
    (Q : SectionRawOutputChoice n I ℓ) where
  noRun : ∀ x, (Q.output x).run? = none

namespace PhaseTwoOnlySectionOutputFamily

variable [NeZero n] {I : ProcedureInput n} {ℓ : Idx n}
variable {Q : SectionRawOutputChoice n I ℓ}

theorem value_eq_sectionPhaseTwoBudget
    (F : PhaseTwoOnlySectionOutputFamily n I ℓ Q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    Q.value lam = Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam := by
  let x : Set.Icc (0 : ℝ) 1 := ⟨lam, hlam⟩
  rw [SectionRawOutputChoice.value, dif_pos hlam]
  rw [RawProcedureOutput.R0_eq_of_none (Q.output x) (F.noRun x)]
  rw [← beforeBudget_firstIdx_eq_totalBudget (hatG := (Q.output x).phaseTwo.hatG2)]
  exact Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
    (Ξ := (Q.output x).phaseTwo) (firstIdx n)

theorem continuousOn_value :
    (F : PhaseTwoOnlySectionOutputFamily n I ℓ Q) →
    ContinuousOn (Q.value) (Set.Icc (0 : ℝ) 1) := by
  intro F
  refine
    (Advice.continuous_sectionPhaseTwoBudgetValue I ℓ (firstIdx n)).continuousOn.congr ?_
  intro lam hlam
  exact PhaseTwoOnlySectionOutputFamily.value_eq_sectionPhaseTwoBudget F hlam

end PhaseTwoOnlySectionOutputFamily

structure FixedThresholdSectionOutputFamily
    (n : ℕ) [NeZero n] (I : ProcedureInput n) (ℓ : Idx n)
    (Q : SectionRawOutputChoice n I ℓ) where
  t1 : Idx n
  t2 : Idx n
  run :
    ∀ x : Set.Icc (0 : ℝ) 1,
      ProcedureRun I (Advice.sectionAdvice I ℓ x.1 ⟨x.2.1, x.2.2⟩)
  output_run : ∀ x, (Q.output x).run? = some (run x)
  t1_eq : ∀ x, (run x).t1 = t1
  t2_eq : ∀ x, (run x).t2 = t2
  halphaDenom : ∀ lam, Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0
  hphiDenom :
    ∀ lam,
      futureCount t1 +
          Advice.sectionBoundaryAlphaValue I ℓ t1 lam *
            (1 - Advice.sectionMuDValue I ℓ t1 lam) -
        I.program.frac * Advice.sectionZValue I ℓ t2 lam ≠ 0
  hphase1Denom :
    ∀ ⦃i : Idx n⦄, i < t1 →
      ∀ lam, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 lam ≠ 0

/--
A family of successful section-advice runs with thresholds `t₁,t₂` fixed across
the whole section parameter interval `λ ∈ [0,1]`.
-/
structure FixedThresholdSectionRunFamily
    (n : ℕ) [NeZero n] (I : ProcedureInput n) (ℓ t1 t2 : Idx n) where
  run :
    ∀ x : Set.Icc (0 : ℝ) 1,
      ProcedureRun I (Advice.sectionAdvice I ℓ x.1 ⟨x.2.1, x.2.2⟩)
  t1_eq : ∀ x, (run x).t1 = t1
  t2_eq : ∀ x, (run x).t2 = t2

namespace FixedThresholdSectionRunFamily

variable [NeZero n] {I : ProcedureInput n} {ℓ t1 t2 : Idx n}
variable (F : FixedThresholdSectionRunFamily n I ℓ t1 t2)

/-- The scalar `R₀` map attached to a fixed-threshold section family. -/
noncomputable def value (lam : ℝ) : ℝ :=
  if hlam : lam ∈ Set.Icc (0 : ℝ) 1 then
    (F.run ⟨lam, hlam⟩).R0
  else
    0

theorem value_eq_sectionR0ValueAtThreshold
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    F.value lam =
      Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2) lam := by
  let x : Set.Icc (0 : ℝ) 1 := ⟨lam, hlam⟩
  have hR0 :=
    (F.run x).R0_eq_sectionR0ValueAtThreshold_explicit_of_sectionAdvice hγlo hγhi
  rw [FixedThresholdSectionRunFamily.value, dif_pos hlam]
  simpa [x, F.t1_eq x, F.t2_eq x] using hR0

theorem continuousOn_value
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (halphaDenom : ∀ lam, Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0)
    (hphiDenom :
      ∀ lam,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 lam *
              (1 - Advice.sectionMuDValue I ℓ t1 lam) -
          I.program.frac * Advice.sectionZValue I ℓ t2 lam ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ lam, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 lam ≠ 0) :
    ContinuousOn (F.value) (Set.Icc (0 : ℝ) 1) := by
  refine
    (Advice.continuous_sectionR0ValueAtThreshold I ℓ t1
      (Advice.sectionZValue I ℓ t2)
      (Advice.continuous_sectionZValue I ℓ t2)
      halphaDenom hphiDenom hphase1Denom).continuousOn.congr ?_
  intro lam hlam
  exact F.value_eq_sectionR0ValueAtThreshold hγlo hγhi hlam

end FixedThresholdSectionRunFamily

namespace SectionRawOutputChoice

variable [NeZero n] {I : ProcedureInput n} {ℓ t1 t2 : Idx n}

theorem continuousWithinAt_interval_of_fixedThreshold_left_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1L t2L t1R t2R : Idx n}
    (FL : FixedThresholdSectionRunFamily n I ℓ t1L t2L)
    (FR : FixedThresholdSectionRunFamily n I ℓ t1R t2R)
    (halphaDenomL : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1L x ≠ 0)
    (hphiDenomL :
      ∀ x,
        futureCount t1L +
            Advice.sectionBoundaryAlphaValue I ℓ t1L x *
              (1 - Advice.sectionMuDValue I ℓ t1L x) -
          I.program.frac * Advice.sectionZValue I ℓ t2L x ≠ 0)
    (hphase1DenomL :
      ∀ ⦃i : Idx n⦄, i < t1L →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2L x ≠ 0)
    (halphaDenomR : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1R x ≠ 0)
    (hphiDenomR :
      ∀ x,
        futureCount t1R +
            Advice.sectionBoundaryAlphaValue I ℓ t1R x *
              (1 - Advice.sectionMuDValue I ℓ t1R x) -
          I.program.frac * Advice.sectionZValue I ℓ t2R x ≠ 0)
    (hphase1DenomR :
      ∀ ⦃i : Idx n⦄, i < t1R →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2R x ≠ 0)
    {sL sR : Set ℝ}
    (hsL : sL ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsR : sR ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hEqL : Set.EqOn Q.value FL.value sL)
    (hEqR : Set.EqOn Q.value FR.value sR) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  refine
    Q.continuousWithinAt_interval_of_eqOn_mem_left_right hlam
      (FL.continuousOn_value hγlo hγhi halphaDenomL hphiDenomL hphase1DenomL)
      (FR.continuousOn_value hγlo hγhi halphaDenomR hphiDenomR hphase1DenomR)
      hsL hsR hEqL hEqR

theorem continuousWithinAt_interval_of_phaseTwoOnly_left_fixedThreshold_right
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1R t2R : Idx n}
    (FR : FixedThresholdSectionRunFamily n I ℓ t1R t2R)
    (halphaDenomR : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1R x ≠ 0)
    (hphiDenomR :
      ∀ x,
        futureCount t1R +
            Advice.sectionBoundaryAlphaValue I ℓ t1R x *
              (1 - Advice.sectionMuDValue I ℓ t1R x) -
          I.program.frac * Advice.sectionZValue I ℓ t2R x ≠ 0)
    (hphase1DenomR :
      ∀ ⦃i : Idx n⦄, i < t1R →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2R x ≠ 0)
    {sL sR : Set ℝ}
    (hsL : sL ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsR : sR ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsL_subset : sL ⊆ Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam)
    (hsmallL :
      ∀ x, x ∈ sL →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
    (hEqR : Set.EqOn Q.value FR.value sR) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  refine
    Q.continuousWithinAt_interval_of_eqOn_mem_left_right hlam
      (Advice.continuous_sectionPhaseTwoBudgetValue I ℓ (firstIdx n)).continuousOn
      (FR.continuousOn_value hγlo hγhi halphaDenomR hphiDenomR hphase1DenomR)
      hsL hsR ?_ hEqR
  intro x hx
  exact
    Q.value_eq_sectionPhaseTwoBudget_of_total_lt_barTau
      hγlo (hsL_subset hx).1 (hsmallL x hx)

/--
Paper Case `1.2.b.i` (and similarly `2.b.ii`): the left limit is governed by a
predecessor threshold regime `(t₁⁻, t₂⁻)`, while the value at and to the right of
`λ` is governed by the current threshold regime `(t₁, t₂)`.
-/
theorem continuousWithinAt_case1_2_b_i
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1Minus t2Minus t1 t2 : Idx n}
    (Fminus : FixedThresholdSectionRunFamily n I ℓ t1Minus t2Minus)
    (Fcurr : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hEqLeft : Set.EqOn Q.value Fminus.value sLeft)
    (hEqRight : Set.EqOn Q.value Fcurr.value sRight) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  exact
    Q.continuousWithinAt_interval_of_fixedThreshold_left_right
      hlam hγlo hγhi Fminus Fcurr
      halphaDenomMinus hphiDenomMinus hphase1DenomMinus
      halphaDenomCurr hphiDenomCurr hphase1DenomCurr
      hsLeft hsRight hEqLeft hEqRight

/--
Paper Case `1.2.b.ii` (and similarly `2.b.i` when the right regime has `t₁ = n`):
to the left of `λ` the execution stays entirely in Phase 2, while at and to the
right of `λ` it is governed by a fixed-threshold regime `(t₁, t₂)`.
-/
theorem continuousWithinAt_case1_2_b_ii
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (Fcurr : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam)
    (hsmallLeft :
      ∀ x, x ∈ sLeft →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
    (hEqRight : Set.EqOn Q.value Fcurr.value sRight) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  exact
    Q.continuousWithinAt_interval_of_phaseTwoOnly_left_fixedThreshold_right
      hlam hγlo hγhi Fcurr
      halphaDenomCurr hphiDenomCurr hphase1DenomCurr
      hsLeft hsRight hsLeft_subset hsmallLeft hEqRight

/-- Package a fixed-threshold run family as the corresponding raw-output choice. -/
noncomputable def ofRunFamily
    (F : FixedThresholdSectionRunFamily n I ℓ t1 t2) :
    SectionRawOutputChoice n I ℓ where
  output := fun x =>
    { phaseTwo := (F.run x).phaseTwo
      run? := some (F.run x)
      run_phaseTwo := by
        intro C h
        cases h
        rfl
      noRun_t1_none := by
        intro h
        cases h }

theorem ofRunFamily_endpoint_eq
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n)
    {t1 t2 t1' t2' : Idx n}
    (F : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (F' : FixedThresholdSectionRunFamily n I (succIdx ℓ hℓ) t1' t2')
    (hcompat :
      F'.run ⟨0, by constructor <;> norm_num⟩ =
        (F.run ⟨1, by constructor <;> norm_num⟩).toNextSectionLeft hℓ) :
    ((ofRunFamily F).output ⟨1, by constructor <;> norm_num⟩).toNextSectionLeft hℓ =
      (ofRunFamily F').output ⟨0, by constructor <;> norm_num⟩ := by
  let x : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  let y : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  refine RawProcedureOutput.ext ?_ ?_
  · change ((F.run x).phaseTwo.toNextSectionLeft hℓ) = (F'.run y).phaseTwo
    simpa [x, y, ProcedureRun.toNextSectionLeft] using!
      (congrArg ProcedureRun.phaseTwo hcompat).symm
  · change some ((F.run x).toNextSectionLeft hℓ) = some (F'.run y)
    exact congrArg some hcompat.symm

theorem eqOn_value_ofRunFamily
    {t1 t2 : Idx n}
    (F : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    {s : Set ℝ} (hs : s ⊆ Set.Icc (0 : ℝ) 1) :
    Set.EqOn (SectionRawOutputChoice.ofRunFamily F).value F.value s := by
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := hs hx
  rw [SectionRawOutputChoice.value, FixedThresholdSectionRunFamily.value,
    dif_pos hx', dif_pos hx']
  rw [RawProcedureOutput.R0_eq_of_some
    ((SectionRawOutputChoice.ofRunFamily F).output ⟨x, hx'⟩) rfl]
  simp [ProcedureRun.R0]

theorem eqOn_value_of_eqOn_output
    (Q Q' : SectionRawOutputChoice n I ℓ)
    {s : Set ℝ} (hs : s ⊆ Set.Icc (0 : ℝ) 1)
    (hout :
      ∀ x (hx : x ∈ s),
        Q.output ⟨x, hs hx⟩ = Q'.output ⟨x, hs hx⟩) :
    Set.EqOn Q.value Q'.value s := by
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := hs hx
  rw [SectionRawOutputChoice.value, SectionRawOutputChoice.value, dif_pos hx', dif_pos hx']
  exact congrArg RawProcedureOutput.R0 (hout x hx)

theorem continuousWithinAt_case1_2_b_i_of_eqOn_output
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1Minus t2Minus t1 t2 : Idx n}
    (Fminus : FixedThresholdSectionRunFamily n I ℓ t1Minus t2Minus)
    (Fcurr : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hOutLeft :
      ∀ x (hx : x ∈ sLeft),
        Q.output ⟨x, hsLeft_subset hx⟩ =
          (SectionRawOutputChoice.ofRunFamily Fminus).output ⟨x, hsLeft_subset hx⟩)
    (hOutRight :
      ∀ x (hx : x ∈ sRight),
        Q.output ⟨x, hsRight_subset hx⟩ =
          (SectionRawOutputChoice.ofRunFamily Fcurr).output ⟨x, hsRight_subset hx⟩) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  have hEqLeftChoice :
      Set.EqOn Q.value (SectionRawOutputChoice.ofRunFamily Fminus).value sLeft :=
    Q.eqOn_value_of_eqOn_output (Q' := SectionRawOutputChoice.ofRunFamily Fminus)
      hsLeft_subset hOutLeft
  have hEqRightChoice :
      Set.EqOn Q.value (SectionRawOutputChoice.ofRunFamily Fcurr).value sRight :=
    Q.eqOn_value_of_eqOn_output (Q' := SectionRawOutputChoice.ofRunFamily Fcurr)
      hsRight_subset hOutRight
  have hEqLeft : Set.EqOn Q.value Fminus.value sLeft := by
    intro x hx
    rw [hEqLeftChoice hx, (SectionRawOutputChoice.eqOn_value_ofRunFamily Fminus hsLeft_subset) hx]
  have hEqRight : Set.EqOn Q.value Fcurr.value sRight := by
    intro x hx
    rw [hEqRightChoice hx,
      (SectionRawOutputChoice.eqOn_value_ofRunFamily Fcurr hsRight_subset) hx]
  exact
    Q.continuousWithinAt_case1_2_b_i
      hlam hγlo hγhi Fminus Fcurr
      halphaDenomMinus hphiDenomMinus hphase1DenomMinus
      halphaDenomCurr hphiDenomCurr hphase1DenomCurr
      hsLeft hsRight hEqLeft hEqRight

theorem continuousWithinAt_case1_2_b_ii_of_eqOn_output
    (Q : SectionRawOutputChoice n I ℓ) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (Fcurr : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hsmallLeft :
      ∀ x, x ∈ sLeft →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
    (hOutRight :
      ∀ x (hx : x ∈ sRight),
        Q.output ⟨x, hsRight_subset hx⟩ =
          (SectionRawOutputChoice.ofRunFamily Fcurr).output ⟨x, hsRight_subset hx⟩) :
    ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
  have hEqRightChoice :
      Set.EqOn Q.value (SectionRawOutputChoice.ofRunFamily Fcurr).value sRight :=
    Q.eqOn_value_of_eqOn_output (Q' := SectionRawOutputChoice.ofRunFamily Fcurr)
      hsRight_subset hOutRight
  have hEqRight : Set.EqOn Q.value Fcurr.value sRight := by
    intro x hx
    rw [hEqRightChoice hx,
      (SectionRawOutputChoice.eqOn_value_ofRunFamily Fcurr hsRight_subset) hx]
  exact
    Q.continuousWithinAt_case1_2_b_ii
      hlam hγlo hγhi Fcurr
      halphaDenomCurr hphiDenomCurr hphase1DenomCurr
      hsLeft hsRight hsLeft_subset hsmallLeft hEqRight

end SectionRawOutputChoice

namespace FixedThresholdSectionOutputFamily

variable [NeZero n] {I : ProcedureInput n} {ℓ : Idx n}
variable {Q : SectionRawOutputChoice n I ℓ}

noncomputable def toRunFamily (F : FixedThresholdSectionOutputFamily n I ℓ Q) :
    FixedThresholdSectionRunFamily n I ℓ F.t1 F.t2 where
  run := F.run
  t1_eq := F.t1_eq
  t2_eq := F.t2_eq

theorem value_eq_runValue
    (F : FixedThresholdSectionOutputFamily n I ℓ Q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    Q.value lam = (toRunFamily F).value lam := by
  let x : Set.Icc (0 : ℝ) 1 := ⟨lam, hlam⟩
  rw [SectionRawOutputChoice.value, FixedThresholdSectionRunFamily.value,
    dif_pos hlam, dif_pos hlam]
  rw [RawProcedureOutput.R0_eq_of_some (Q.output x) (F.output_run x)]
  simp [FixedThresholdSectionOutputFamily.toRunFamily, ProcedureRun.R0, x]

theorem continuousOn_value
    (F : FixedThresholdSectionOutputFamily n I ℓ Q)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    ContinuousOn (Q.value) (Set.Icc (0 : ℝ) 1) := by
  refine
    ((toRunFamily F).continuousOn_value hγlo hγhi F.halphaDenom F.hphiDenom
      F.hphase1Denom).congr ?_
  intro lam hlam
  exact value_eq_runValue F hlam

noncomputable def ofRunFamily
    {t1 t2 : Idx n}
    (F : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenom : ∀ lam, Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0)
    (hphiDenom :
      ∀ lam,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 lam *
              (1 - Advice.sectionMuDValue I ℓ t1 lam) -
          I.program.frac * Advice.sectionZValue I ℓ t2 lam ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ lam, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 lam ≠ 0) :
    FixedThresholdSectionOutputFamily n I ℓ (SectionRawOutputChoice.ofRunFamily F) where
  t1 := t1
  t2 := t2
  run := F.run
  output_run := by
    intro x
    rfl
  t1_eq := F.t1_eq
  t2_eq := F.t2_eq
  halphaDenom := halphaDenom
  hphiDenom := hphiDenom
  hphase1Denom := hphase1Denom

end FixedThresholdSectionOutputFamily

namespace SectionRawOutputChoice

variable [NeZero n] {I : ProcedureInput n} {ℓ : Idx n}

def localContinuityWitness_of_eqOn
    (Q : SectionRawOutputChoice n I ℓ)
    {f : ℝ → ℝ} {lam : ℝ} (s : Set ℝ)
    (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
    (hcont : ContinuousOn f s)
    (hEq : ∀ x, x ∈ s → Q.value x = f x) :
    LocalContinuityWitness Q lam where
  s := s
  hs_nhdsWithin := hs_nhdsWithin
  continuousOn_value :=
    hcont.congr_mono (fun x hx => hEq x hx) (by intro x hx; exact hx)

def localContinuityWitness_of_fixedThreshold
    {Q : SectionRawOutputChoice n I ℓ}
    (F : FixedThresholdSectionOutputFamily n I ℓ Q)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {lam : ℝ} :
    LocalContinuityWitness Q lam where
  s := Set.Icc (0 : ℝ) 1
  hs_nhdsWithin := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    intro x hx
    simpa using hx.2
  continuousOn_value := F.continuousOn_value hγlo hγhi

noncomputable def localContinuityWitness_ofRunFamily
    {t1 t2 : Idx n}
    (F : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (halphaDenom : ∀ lam, Advice.sectionPhaseTwoHatG2Value I ℓ t1 lam ≠ 0)
    (hphiDenom :
      ∀ lam,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 lam *
              (1 - Advice.sectionMuDValue I ℓ t1 lam) -
          I.program.frac * Advice.sectionZValue I ℓ t2 lam ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ lam, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 lam ≠ 0)
    {lam : ℝ} :
    LocalContinuityWitness (SectionRawOutputChoice.ofRunFamily F) lam :=
  localContinuityWitness_of_fixedThreshold
    (Q := SectionRawOutputChoice.ofRunFamily F)
    (FixedThresholdSectionOutputFamily.ofRunFamily F halphaDenom hphiDenom hphase1Denom)
    hγlo hγhi

structure FixedThresholdLocalWitnessData
    (Q : SectionRawOutputChoice n I ℓ) (lam : ℝ) where
  s : Set ℝ
  hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1)
  hs_subset : s ⊆ Set.Icc (0 : ℝ) 1
  t1 : Idx n
  t2 : Idx n
  runFamily : FixedThresholdSectionRunFamily n I ℓ t1 t2
  halphaDenom : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0
  hphiDenom :
    ∀ x,
      futureCount t1 +
          Advice.sectionBoundaryAlphaValue I ℓ t1 x *
            (1 - Advice.sectionMuDValue I ℓ t1 x) -
        I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0
  hphase1Denom :
    ∀ ⦃i : Idx n⦄, i < t1 →
      ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0
  hEq :
    ∀ x, x ∈ s →
      Q.value x = (SectionRawOutputChoice.ofRunFamily runFamily).value x

namespace FixedThresholdLocalWitnessData

noncomputable def toLocalContinuityWitness
    {Q : SectionRawOutputChoice n I ℓ} {lam : ℝ}
    (W : FixedThresholdLocalWitnessData (I := I) (ℓ := ℓ) Q lam)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    LocalContinuityWitness Q lam := by
  have hcontGlobal :
      ContinuousOn
        (SectionRawOutputChoice.ofRunFamily W.runFamily).value
        (Set.Icc (0 : ℝ) 1) := by
    exact
      (FixedThresholdSectionOutputFamily.ofRunFamily
        W.runFamily W.halphaDenom W.hphiDenom W.hphase1Denom).continuousOn_value hγlo hγhi
  have hcontLocal :
      ContinuousOn
        (SectionRawOutputChoice.ofRunFamily W.runFamily).value
        W.s := by
    exact hcontGlobal.congr_mono (fun x _ => rfl) W.hs_subset
  exact localContinuityWitness_of_eqOn Q W.s W.hs_nhdsWithin hcontLocal W.hEq

end FixedThresholdLocalWitnessData

/--
Pointwise local continuity cases for a chosen raw-output family on one section.
This matches the paper's proof style more closely than a global section certificate:
around a fixed `λ`, either the run is locally phase-2-only, or it agrees on a
neighborhood with a fixed-threshold run family.
-/
inductive LocalCase
    (Q : SectionRawOutputChoice n I ℓ) (lam : ℝ) where
  | phaseTwoOnly
      (s : Set ℝ)
      (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
      (hs_subset : s ⊆ Set.Icc (0 : ℝ) 1)
      (hsmall :
        ∀ x, x ∈ s →
          Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
  | fixedThreshold
      (W : FixedThresholdLocalWitnessData (I := I) (ℓ := ℓ) Q lam)

namespace LocalCase

noncomputable def phaseTwoOnly_of_total_lt_barTau
    {Q : SectionRawOutputChoice n I ℓ} {lam : ℝ}
    (htotal :
      Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau) :
    LocalCase (I := I) (ℓ := ℓ) Q lam := by
  let f : ℝ → ℝ := Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n)
  let s : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ f ⁻¹' Set.Iio I.program.barTau
  have hcont : ContinuousWithinAt f (Set.Icc (0 : ℝ) 1) lam :=
    (Advice.continuous_sectionPhaseTwoBudgetValue I ℓ (firstIdx n)).continuousWithinAt
  have hpre : f ⁻¹' Set.Iio I.program.barTau ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1) := by
    exact hcont.preimage_mem_nhdsWithin (Iio_mem_nhds htotal)
  refine .phaseTwoOnly s ?_ ?_ ?_
  · exact Filter.inter_mem self_mem_nhdsWithin hpre
  · intro x hx
    exact hx.1
  · intro x hx
    exact hx.2

noncomputable def fixedThreshold_ofRunFamily
    {t1 t2 : Idx n}
    (F : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenom : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenom :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {lam : ℝ} :
    LocalCase (I := I) (ℓ := ℓ) (SectionRawOutputChoice.ofRunFamily F) lam :=
  .fixedThreshold
    { s := Set.Icc (0 : ℝ) 1
      hs_nhdsWithin := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        intro x hx
        simpa using hx.2
      hs_subset := by intro x hx; exact hx
      t1 := t1
      t2 := t2
      runFamily := F
      halphaDenom := halphaDenom
      hphiDenom := hphiDenom
      hphase1Denom := hphase1Denom
      hEq := by intro x hx; rfl }

noncomputable def toLocalContinuityWitness
    {Q : SectionRawOutputChoice n I ℓ} {lam : ℝ}
    (K : LocalCase (I := I) (ℓ := ℓ) Q lam)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    LocalContinuityWitness Q lam := by
  cases K with
  | phaseTwoOnly s hs_nhdsWithin hs_subset hsmall =>
      exact localContinuityWitness_phaseTwoOnly Q hγlo s hs_nhdsWithin hs_subset hsmall
  | fixedThreshold W =>
      exact W.toLocalContinuityWitness hγlo hγhi

end LocalCase

end SectionRawOutputChoice

/--
A choice of raw procedure outputs along the section advice path `Γ^ℓ(λ)`, one for each
section index `ℓ` and parameter `λ ∈ [0,1]`.
-/
structure SectionRawOutputPath (n : ℕ) [NeZero n] (I : ProcedureInput n) where
  output : ∀ (ℓ : Idx n) (x : Set.Icc (0 : ℝ) 1),
    RawProcedureOutput I (Advice.sectionAdvice I ℓ x.1 ⟨x.2.1, x.2.2⟩)

/-- The actual pointwise raw-output choice obtained by running the canonical phase-2 threshold
selection at each section parameter. -/
noncomputable def canonicalPath
    [NeZero n]
    (I : ProcedureInput n)
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    SectionRawOutputPath n I where
  output := fun ℓ x => canonicalSectionOutput I hγlo hγhi ℓ x

namespace SectionRawOutputPath

variable [NeZero n] {I : ProcedureInput n} (P : SectionRawOutputPath n I)

def sectionChoice (ℓ : Idx n) : SectionRawOutputChoice n I ℓ where
  output := P.output ℓ

@[simp] theorem sectionChoice_output (ℓ : Idx n) (x : Set.Icc (0 : ℝ) 1) :
    (P.sectionChoice ℓ).output x = P.output ℓ x := rfl

/-- The scalar path `F_ℓ(λ) = R₀` attached to a sectionwise choice of raw outputs. -/
noncomputable def value (ℓ : Idx n) (lam : ℝ) : ℝ :=
  if hlam : lam ∈ Set.Icc (0 : ℝ) 1 then
    (P.output ℓ ⟨lam, hlam⟩).R0
  else
    0

/-- On a neighborhood where the path output uses the specific run `F.run x`, it equals the
canonical fixed-threshold raw output coming from `F`. -/
theorem output_eq_ofRunFamily_of_run_eq
    {ℓ : Idx n} {t1 t2 : Idx n}
    (F : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    {s : Set ℝ} (hs : s ⊆ Set.Icc (0 : ℝ) 1)
    (hrun :
      ∀ x (hx : x ∈ s),
        (P.output ℓ ⟨x, hs hx⟩).run? = some (F.run ⟨x, hs hx⟩)) :
    ∀ x (hx : x ∈ s),
      P.output ℓ ⟨x, hs hx⟩ =
        (SectionRawOutputChoice.ofRunFamily F).output ⟨x, hs hx⟩ := by
  intro x hx
  refine RawProcedureOutput.ext ?_ ?_
  · symm
    exact (P.output ℓ ⟨x, hs hx⟩).run_phaseTwo (hrun x hx)
  · exact hrun x hx

/-- On a neighborhood where the phase-2 total stays below `\bar τ`, the path output equals the
canonical phase-2-only raw output. -/
theorem output_eq_phaseTwoOnly_of_total_lt_barTau
    {ℓ : Idx n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    {s : Set ℝ} (hs : s ⊆ Set.Icc (0 : ℝ) 1)
    (hsmall :
      ∀ x, x ∈ s →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau) :
    ∀ x (hx : x ∈ s),
      P.output ℓ ⟨x, hs hx⟩ =
        sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ ⟨x, hs hx⟩ (hsmall x hx) := by
  intro x hx
  exact rawOutput_eq_sectionPhaseTwoOnlyOutput_of_total_lt_barTau
    (I := I) hγlo (hsmall x hx) (P.output ℓ ⟨x, hs hx⟩)

theorem eqOn_value_sectionPhaseTwoBudget_of_total_lt_barTau
    {ℓ : Idx n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    {s : Set ℝ} (hs : s ⊆ Set.Icc (0 : ℝ) 1)
    (hsmall :
      ∀ x, x ∈ s →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau) :
    Set.EqOn (P.value ℓ) (Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n)) s := by
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := hs hx
  rw [SectionRawOutputPath.value, dif_pos hx']
  rw [P.output_eq_phaseTwoOnly_of_total_lt_barTau hγlo hs hsmall x hx]
  rw [RawProcedureOutput.R0_eq_of_none
    (sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ ⟨x, hx'⟩ (hsmall x hx)) rfl]
  rw [← beforeBudget_firstIdx_eq_totalBudget
    (hatG := (sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ ⟨x, hx'⟩
      (hsmall x hx)).phaseTwo.hatG2)]
  exact Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
    (Ξ := (sectionPhaseTwoOnlyOutput (I := I) hγlo ℓ ⟨x, hx'⟩
      (hsmall x hx)).phaseTwo) (firstIdx n)

theorem eqOn_value_sectionR0Model_of_localThresholdRuns
    {ℓ : Idx n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n} {s : Set ℝ}
    (hs : s ⊆ Set.Icc (0 : ℝ) 1)
    (hrun :
      ∀ x (hx : x ∈ s),
        ∃ C : ProcedureRun I (Advice.sectionAdvice I ℓ x ⟨(hs hx).1, (hs hx).2⟩),
          (P.output ℓ ⟨x, hs hx⟩).run? = some C ∧ C.t1 = t1 ∧ C.t2 = t2) :
    Set.EqOn
      (P.value ℓ)
      (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2))
      s := by
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := hs hx
  rcases hrun x hx with ⟨C, hC, ht1, ht2⟩
  rw [SectionRawOutputPath.value, dif_pos hx']
  rw [RawProcedureOutput.R0_eq_of_some (P.output ℓ ⟨x, hx'⟩) hC]
  simpa [ProcedureRun.R0, ht1, ht2] using
    (C.R0_eq_sectionR0ValueAtThreshold_explicit_of_sectionAdvice
      (ℓ := ℓ) (lam := x) (hlam := ⟨hx'.1, hx'.2⟩) hγlo hγhi)

theorem continuousOn_sectionR0Model_of_localThresholdRuns
    {ℓ : Idx n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n} {s : Set ℝ}
    (hs : s ⊆ Set.Icc (0 : ℝ) 1)
    (hrun :
      ∀ x (hx : x ∈ s),
        ∃ C : ProcedureRun I (Advice.sectionAdvice I ℓ x ⟨(hs hx).1, (hs hx).2⟩),
          (P.output ℓ ⟨x, hs hx⟩).run? = some C ∧ C.t1 = t1 ∧ C.t2 = t2) :
    ContinuousOn
      (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2))
      s := by
  by_cases ht1last : t1 = lastIdx n
  · have hboundary :
        ContinuousOn
          (fun x =>
            Advice.sectionBoundaryBudgetValue I ℓ t1 (Advice.sectionZValue I ℓ t2) x)
          s := by
      simpa [Advice.sectionBoundaryBudgetValue, ht1last] using
        (Advice.continuous_sectionPhaseTwoHatG2Value I ℓ t1).continuousOn
    have hprefix :
        ContinuousOn
          (fun x =>
            Advice.sectionPhase1PrefixValue I ℓ t1 (Advice.sectionZValue I ℓ t2) x)
          s := by
      refine Advice.continuousOn_sectionPhase1PrefixValue I ℓ t1
        (Advice.sectionZValue I ℓ t2)
        ((Advice.continuous_sectionZValue I ℓ t2).continuousOn.mono hs) ?_
      intro i hi x hx
      rcases hrun x hx with ⟨C, _hC, ht1C, ht2C⟩
      have ht1le2 : t1 ≤ t2 := by
        simpa [ht1C, ht2C] using C.t1_le_t2
      exact ne_of_gt <|
        Advice.sectionPhase1Denom_pos_of_lt_t1
          (I := I) (le_of_lt hγ) ℓ t1 t2 hi ht1le2 (hs hx).1
    simpa [Advice.sectionR0ValueAtThreshold] using! hboundary.add hprefix
  · refine Advice.continuousOn_sectionR0ValueAtThreshold I ℓ t1
      (Advice.sectionZValue I ℓ t2)
      ((Advice.continuous_sectionZValue I ℓ t2).continuousOn.mono hs) ?_ ?_ ?_
    · intro x hx
      rcases hrun x hx with ⟨C, _hC, ht1C, _ht2C⟩
      exact
        by
          have hpos :
              0 < Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 x :=
            C.sectionPhaseTwoHatG2Value_pos_at_t1_of_sectionAdvice_of_le_153_div_125
              (le_of_lt hγ) hγhi
          simpa [ht1C] using ne_of_gt hpos
    · intro x hx
      rcases hrun x hx with ⟨C, _hC, ht1C, ht2C⟩
      have ht1Cne : C.t1 ≠ lastIdx n := by
        intro hlast
        exact ht1last (by simpa [ht1C] using hlast)
      exact
        by
          have hpos :
              0 <
                futureCount C.t1 +
                  Advice.sectionBoundaryAlphaValue I ℓ C.t1 x *
                      (1 - Advice.sectionMuDValue I ℓ C.t1 x) -
                    I.program.frac * Advice.sectionZValue I ℓ C.t2 x :=
            C.sectionBoundaryPhiDenom_pos_of_sectionAdvice_of_ne_last hγ ht1Cne
          simpa [ht1C, ht2C] using ne_of_gt hpos
    · intro i hi x hx
      rcases hrun x hx with ⟨C, _hC, ht1C, ht2C⟩
      have ht1le2 : t1 ≤ t2 := by
        simpa [ht1C, ht2C] using C.t1_le_t2
      exact ne_of_gt <|
        Advice.sectionPhase1Denom_pos_of_lt_t1
          (I := I) (le_of_lt hγ) ℓ t1 t2 hi ht1le2 (hs hx).1

theorem eqOn_value_sectionR0FullModel_of_localT1Runs
    {ℓ : Idx n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 : Idx n} {s : Set ℝ}
    (hs : s ⊆ Set.Icc (0 : ℝ) 1)
    (hrun :
      ∀ x (hx : x ∈ s),
        ∃ C : ProcedureRun I (Advice.sectionAdvice I ℓ x ⟨(hs hx).1, (hs hx).2⟩),
          (P.output ℓ ⟨x, hs hx⟩).run? = some C ∧ C.t1 = t1) :
    Set.EqOn
      (P.value ℓ)
      (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZFullValue I ℓ))
      s := by
  intro x hx
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := hs hx
  rcases hrun x hx with ⟨C, hC, ht1⟩
  rw [SectionRawOutputPath.value, dif_pos hx']
  rw [RawProcedureOutput.R0_eq_of_some (P.output ℓ ⟨x, hx'⟩) hC]
  simpa [ProcedureRun.R0, ht1] using
    (C.R0_eq_sectionR0ValueAtThreshold_full_of_sectionAdvice
      (ℓ := ℓ) (lam := x) (hlam := ⟨hx'.1, hx'.2⟩) hγ hγhi)

theorem continuousOn_sectionR0FullModel_of_localT1Runs
    {ℓ : Idx n}
    (hγ : 1 < I.program.Mcoeff)
    (_hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 : Idx n} {s : Set ℝ}
    (hs : s ⊆ Set.Icc (0 : ℝ) 1)
    (hrun :
      ∀ x (hx : x ∈ s),
        ∃ C : ProcedureRun I (Advice.sectionAdvice I ℓ x ⟨(hs hx).1, (hs hx).2⟩),
          (P.output ℓ ⟨x, hs hx⟩).run? = some C ∧ C.t1 = t1) :
    ContinuousOn
      (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZFullValue I ℓ))
      s := by
  by_cases ht1last : t1 = lastIdx n
  · have hboundary :
        ContinuousOn
          (fun x =>
            Advice.sectionBoundaryBudgetValue I ℓ t1 (Advice.sectionZFullValue I ℓ) x)
          s := by
      simpa [Advice.sectionBoundaryBudgetValue, ht1last] using
        (Advice.continuous_sectionPhaseTwoHatG2Value I ℓ t1).continuousOn
    have hprefix :
        ContinuousOn
          (fun x =>
            Advice.sectionPhase1PrefixValue I ℓ t1 (Advice.sectionZFullValue I ℓ) x)
          s := by
      refine Advice.continuousOn_sectionPhase1PrefixValue I ℓ t1
        (Advice.sectionZFullValue I ℓ)
        (Advice.continuous_sectionZFullValue I ℓ).continuousOn ?_
      intro i hi x hx
      rcases hrun x hx with ⟨C, _hC, ht1C⟩
      have ht1le2 : t1 ≤ C.t2 := by
        simpa [ht1C] using C.t1_le_t2
      have hzEq :
          Advice.sectionZFullValue I ℓ x = Advice.sectionZValue I ℓ C.t2 x := by
        rw [← C.z_eq_sectionZValue_of_sectionAdvice,
          C.z_eq_sectionZFullValue_of_sectionAdvice hγ]
      have hpos :
          0 < futureCount i - I.program.frac * Advice.sectionZValue I ℓ C.t2 x :=
        Advice.sectionPhase1Denom_pos_of_lt_t1
          (I := I) (le_of_lt hγ) ℓ t1 C.t2 hi ht1le2 (hs hx).1
      simpa [hzEq] using ne_of_gt hpos
    simpa [Advice.sectionR0ValueAtThreshold] using! hboundary.add hprefix
  · refine Advice.continuousOn_sectionR0ValueAtThreshold I ℓ t1
      (Advice.sectionZFullValue I ℓ)
      (Advice.continuous_sectionZFullValue I ℓ).continuousOn ?_ ?_ ?_
    · intro x hx
      rcases hrun x hx with ⟨C, _hC, ht1C⟩
      have ht1Cne : C.t1 ≠ lastIdx n := by
        intro hlast
        exact ht1last (by simpa [ht1C] using hlast)
      have hpos :
          0 < Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 x :=
        C.sectionPhaseTwoHatG2Value_pos_at_t1_of_sectionAdvice_of_ne_last ht1Cne
      simpa [ht1C] using ne_of_gt hpos
    · intro x hx
      rcases hrun x hx with ⟨C, _hC, ht1C⟩
      have ht1Cne : C.t1 ≠ lastIdx n := by
        intro hlast
        exact ht1last (by simpa [ht1C] using hlast)
      have hzEq :
          Advice.sectionZFullValue I ℓ x = Advice.sectionZValue I ℓ C.t2 x := by
        rw [← C.z_eq_sectionZValue_of_sectionAdvice,
          C.z_eq_sectionZFullValue_of_sectionAdvice hγ]
      have hpos :
          0 <
            futureCount C.t1 +
              Advice.sectionBoundaryAlphaValue I ℓ C.t1 x *
                  (1 - Advice.sectionMuDValue I ℓ C.t1 x) -
                I.program.frac * Advice.sectionZValue I ℓ C.t2 x :=
        C.sectionBoundaryPhiDenom_pos_of_sectionAdvice_of_ne_last hγ ht1Cne
      simpa [ht1C, hzEq] using ne_of_gt hpos
    · intro i hi x hx
      rcases hrun x hx with ⟨C, _hC, ht1C⟩
      have ht1le2 : t1 ≤ C.t2 := by
        simpa [ht1C] using C.t1_le_t2
      have hzEq :
          Advice.sectionZFullValue I ℓ x = Advice.sectionZValue I ℓ C.t2 x := by
        rw [← C.z_eq_sectionZValue_of_sectionAdvice,
          C.z_eq_sectionZFullValue_of_sectionAdvice hγ]
      have hpos :
          0 < futureCount i - I.program.frac * Advice.sectionZValue I ℓ C.t2 x :=
        Advice.sectionPhase1Denom_pos_of_lt_t1
          (I := I) (le_of_lt hγ) ℓ t1 C.t2 hi ht1le2 (hs hx).1
      simpa [hzEq] using ne_of_gt hpos

/-- Case 0 on an actual path: a neighborhood where the output stays entirely in Phase 2. -/
theorem continuousWithinAt_phaseTwoOnly_of_total_lt_barTau
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    {s : Set ℝ}
    (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
    (hs_subset : s ⊆ Set.Icc (0 : ℝ) 1)
    (hsmall :
      ∀ x, x ∈ s →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let Q := P.sectionChoice ℓ
  have hEqChoice :
      Set.EqOn Q.value (Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n)) s := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := hs_subset hx
    simpa [SectionRawOutputPath.sectionChoice] using!
      (Q.value_eq_sectionPhaseTwoBudget_of_total_lt_barTau hγlo hx' (hsmall x hx))
  have hcontLocal :
      ContinuousOn (Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n)) s := by
    exact
      (Advice.continuous_sectionPhaseTwoBudgetValue I ℓ (firstIdx n)).continuousOn.mono
        hs_subset
  have W :
      SectionRawOutputChoice.LocalContinuityWitness Q lam :=
    SectionRawOutputChoice.localContinuityWitness_of_eqOn
      Q s hs_nhdsWithin hcontLocal (fun x hx => hEqChoice hx)
  simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
    SectionRawOutputChoice.value]
    using! W.continuousWithinAt hlam

/-- Stable-threshold continuity from local pointwise runs matching one fixed threshold model. -/
theorem continuousWithinAt_of_localThresholdRuns
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (halphaDenom : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenom :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {s : Set ℝ}
    (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
    (hs_subset : s ⊆ Set.Icc (0 : ℝ) 1)
    (hrun :
      ∀ x (hx : x ∈ s),
        ∃ C : ProcedureRun I
          (Advice.sectionAdvice I ℓ x ⟨(hs_subset hx).1, (hs_subset hx).2⟩),
          (P.output ℓ ⟨x, hs_subset hx⟩).run? = some C ∧ C.t1 = t1 ∧ C.t2 = t2) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let Q := P.sectionChoice ℓ
  have hEqPath :
      Set.EqOn
        (P.value ℓ)
        (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2))
        s :=
    P.eqOn_value_sectionR0Model_of_localThresholdRuns hγlo hγhi hs_subset hrun
  have hEqModel :
      Set.EqOn
        Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2))
        s := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using!
      (hEqPath hx)
  have hcontLocal :
      ContinuousOn
        (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2))
        s := by
    exact
      (Advice.continuous_sectionR0ValueAtThreshold I ℓ t1
        (Advice.sectionZValue I ℓ t2)
        (Advice.continuous_sectionZValue I ℓ t2)
        halphaDenom hphiDenom hphase1Denom).continuousOn.mono hs_subset
  have W : SectionRawOutputChoice.LocalContinuityWitness Q lam :=
    SectionRawOutputChoice.localContinuityWitness_of_eqOn
      Q s hs_nhdsWithin hcontLocal (fun x hx => hEqModel hx)
  simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
    SectionRawOutputChoice.value] using! W.continuousWithinAt hlam

/-- Stable-threshold continuity from local constancy of the canonical Phase-2 thresholds
and local membership in the `run? = some _` branch. -/
theorem continuousWithinAt_of_localPhaseTwoThresholds
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (halphaDenom : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenom :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {s : Set ℝ}
    (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
    (hs_subset : s ⊆ Set.Icc (0 : ℝ) 1)
    (ht1 :
      ∀ x (hx : x ∈ s),
        (P.output ℓ ⟨x, hs_subset hx⟩).phaseTwo.t1? = some t1)
    (ht2 :
      ∀ x (hx : x ∈ s),
        (P.output ℓ ⟨x, hs_subset hx⟩).phaseTwo.t2? = some t2)
    (hrun :
      ∀ x (hx : x ∈ s),
        (P.output ℓ ⟨x, hs_subset hx⟩).run? ≠ none) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  apply P.continuousWithinAt_of_localThresholdRuns
    hlam hγlo hγhi halphaDenom hphiDenom hphase1Denom hs_nhdsWithin hs_subset
  intro x hx
  exact (P.output ℓ ⟨x, hs_subset hx⟩).exists_run_eq_thresholds_of_phaseTwo I
    (ht1 x hx) (ht2 x hx) (hrun x hx)

/-- Jump continuity when both sides are locally given by explicit fixed-threshold models. -/
theorem continuousWithinAt_case1_2_b_i_of_localThresholdRuns
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1Minus t2Minus t1 t2 : Idx n}
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hrunLeft :
      ∀ x (hx : x ∈ sLeft),
        ∃ C :
          ProcedureRun I (Advice.sectionAdvice I ℓ x
            ⟨(hsLeft_subset hx).1, (hsLeft_subset hx).2⟩),
          (P.output ℓ ⟨x, hsLeft_subset hx⟩).run? = some C ∧
            C.t1 = t1Minus ∧ C.t2 = t2Minus)
    (hrunRight :
      ∀ x (hx : x ∈ sRight),
        ∃ C :
          ProcedureRun I (Advice.sectionAdvice I ℓ x
            ⟨(hsRight_subset hx).1, (hsRight_subset hx).2⟩),
          (P.output ℓ ⟨x, hsRight_subset hx⟩).run? = some C ∧ C.t1 = t1 ∧ C.t2 = t2) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let Q := P.sectionChoice ℓ
  have hEqLeftPath :
      Set.EqOn
        (P.value ℓ)
        (Advice.sectionR0ValueAtThreshold I ℓ t1Minus (Advice.sectionZValue I ℓ t2Minus))
        sLeft :=
    P.eqOn_value_sectionR0Model_of_localThresholdRuns hγlo hγhi hsLeft_subset hrunLeft
  have hEqRightPath :
      Set.EqOn
        (P.value ℓ)
        (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2))
        sRight :=
    P.eqOn_value_sectionR0Model_of_localThresholdRuns hγlo hγhi hsRight_subset hrunRight
  have hEqLeft :
      Set.EqOn
        Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ t1Minus (Advice.sectionZValue I ℓ t2Minus))
        sLeft := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using!
      (hEqLeftPath hx)
  have hEqRight :
      Set.EqOn
        Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2))
        sRight := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using!
      (hEqRightPath hx)
  refine
    Q.continuousWithinAt_interval_of_eqOn_mem_left_right hlam
      ?_ ?_ hsLeft hsRight hEqLeft hEqRight
  · exact
      (Advice.continuous_sectionR0ValueAtThreshold I ℓ t1Minus
        (Advice.sectionZValue I ℓ t2Minus)
        (Advice.continuous_sectionZValue I ℓ t2Minus)
        halphaDenomMinus hphiDenomMinus hphase1DenomMinus).continuousOn
  · exact
      (Advice.continuous_sectionR0ValueAtThreshold I ℓ t1
        (Advice.sectionZValue I ℓ t2)
        (Advice.continuous_sectionZValue I ℓ t2)
        halphaDenomCurr hphiDenomCurr hphase1DenomCurr).continuousOn

/-- Jump continuity from local constancy of the canonical Phase-2 thresholds and local
membership in the `run? = some _` branch on both sides. -/
theorem continuousWithinAt_case1_2_b_i_of_localPhaseTwoThresholds
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1Minus t2Minus t1 t2 : Idx n}
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (ht1Left :
      ∀ x (hx : x ∈ sLeft),
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).phaseTwo.t1? = some t1Minus)
    (ht2Left :
      ∀ x (hx : x ∈ sLeft),
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).phaseTwo.t2? = some t2Minus)
    (hrunLeft :
      ∀ x (hx : x ∈ sLeft),
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).run? ≠ none)
    (ht1Right :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t1? = some t1)
    (ht2Right :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t2? = some t2)
    (hrunRight :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).run? ≠ none) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  apply P.continuousWithinAt_case1_2_b_i_of_localThresholdRuns
    hlam hγlo hγhi
    halphaDenomMinus hphiDenomMinus hphase1DenomMinus
    halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset
  · intro x hx
    exact (P.output ℓ ⟨x, hsLeft_subset hx⟩).exists_run_eq_thresholds_of_phaseTwo I
      (ht1Left x hx) (ht2Left x hx) (hrunLeft x hx)
  · intro x hx
    exact (P.output ℓ ⟨x, hsRight_subset hx⟩).exists_run_eq_thresholds_of_phaseTwo I
      (ht1Right x hx) (ht2Right x hx) (hrunRight x hx)

/-- Jump continuity with a Phase-2-only left side and a threshold-model right side. -/
theorem continuousWithinAt_case1_2_b_ii_of_localThresholdRuns
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hsmallLeft :
      ∀ x, x ∈ sLeft →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
    (hrunRight :
      ∀ x (hx : x ∈ sRight),
        ∃ C :
          ProcedureRun I (Advice.sectionAdvice I ℓ x
            ⟨(hsRight_subset hx).1, (hsRight_subset hx).2⟩),
          (P.output ℓ ⟨x, hsRight_subset hx⟩).run? = some C ∧ C.t1 = t1 ∧ C.t2 = t2) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let Q := P.sectionChoice ℓ
  have hEqLeftPath :
      Set.EqOn (P.value ℓ) (Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n)) sLeft :=
    P.eqOn_value_sectionPhaseTwoBudget_of_total_lt_barTau hγlo hsLeft_subset hsmallLeft
  have hEqRightPath :
      Set.EqOn
        (P.value ℓ)
        (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2))
        sRight :=
    P.eqOn_value_sectionR0Model_of_localThresholdRuns hγlo hγhi hsRight_subset hrunRight
  have hEqLeft :
      Set.EqOn Q.value (Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n)) sLeft := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using!
      (hEqLeftPath hx)
  have hEqRight :
      Set.EqOn
        Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZValue I ℓ t2))
        sRight := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using!
      (hEqRightPath hx)
  refine
    Q.continuousWithinAt_interval_of_eqOn_mem_left_right hlam
      ?_ ?_ hsLeft hsRight hEqLeft hEqRight
  · exact (Advice.continuous_sectionPhaseTwoBudgetValue I ℓ (firstIdx n)).continuousOn
  · exact
      (Advice.continuous_sectionR0ValueAtThreshold I ℓ t1
        (Advice.sectionZValue I ℓ t2)
        (Advice.continuous_sectionZValue I ℓ t2)
        halphaDenomCurr hphiDenomCurr hphase1DenomCurr).continuousOn

/-- Jump continuity with a Phase-2-only left side and locally constant canonical thresholds on
the right. -/
theorem continuousWithinAt_case1_2_b_ii_of_localPhaseTwoThresholds
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hsmallLeft :
      ∀ x, x ∈ sLeft →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
    (ht1Right :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t1? = some t1)
    (ht2Right :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t2? = some t2)
    (hrunRight :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).run? ≠ none) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  apply P.continuousWithinAt_case1_2_b_ii_of_localThresholdRuns
    hlam hγlo hγhi halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset hsmallLeft
  intro x hx
  exact (P.output ℓ ⟨x, hsRight_subset hx⟩).exists_run_eq_thresholds_of_phaseTwo I
    (ht1Right x hx) (ht2Right x hx) (hrunRight x hx)

/-- Stable-threshold continuity from the paper's local Phase-2 budget inequalities. -/
theorem continuousWithinAt_of_localPhaseTwoBudgetBounds
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (halphaDenom : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenom :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {s : Set ℝ}
    (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
    (hs_subset : s ⊆ Set.Icc (0 : ℝ) 1)
    (hbar :
      ∀ x (_hx : x ∈ s),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x)
    (hbarAbove :
      ∀ x (_hx : x ∈ s), ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau)
    (htheta :
      ∀ x (_hx : x ∈ s),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 x)
    (hthetaAbove :
      ∀ x (_hx : x ∈ s), ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)
    (hrun :
      ∀ x (hx : x ∈ s),
        (P.output ℓ ⟨x, hs_subset hx⟩).run? ≠ none) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  apply P.continuousWithinAt_of_localPhaseTwoThresholds
    hlam hγlo hγhi halphaDenom hphiDenom hphase1Denom hs_nhdsWithin hs_subset
  · intro x hx
    exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
      (I := I) (O := P.output ℓ ⟨x, hs_subset hx⟩) (hbar x hx) (hbarAbove x hx)
  · intro x hx
    exact RawProcedureOutput.t2?_eq_some_of_sectionBudget_ge_theta_of_above_lt_theta
      (I := I) (O := P.output ℓ ⟨x, hs_subset hx⟩) (htheta x hx) (hthetaAbove x hx)
  · exact hrun

/-- Fixed/fixed jump continuity from the paper's local Phase-2 budget inequalities. -/
theorem continuousWithinAt_case1_2_b_i_of_localPhaseTwoBudgetBounds
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1Minus t2Minus t1 t2 : Idx n}
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hbarLeft :
      ∀ x (_hx : x ∈ sLeft),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1Minus x)
    (hbarLeftAbove :
      ∀ x (_hx : x ∈ sLeft), ∀ ⦃i : Idx n⦄, t1Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau)
    (hthetaLeft :
      ∀ x (_hx : x ∈ sLeft),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2Minus x)
    (hthetaLeftAbove :
      ∀ x (_hx : x ∈ sLeft), ∀ ⦃i : Idx n⦄, t2Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)
    (hrunLeft :
      ∀ x (hx : x ∈ sLeft),
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).run? ≠ none)
    (hbarRight :
      ∀ x (_hx : x ∈ sRight),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x)
    (hbarRightAbove :
      ∀ x (_hx : x ∈ sRight), ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau)
    (hthetaRight :
      ∀ x (_hx : x ∈ sRight),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 x)
    (hthetaRightAbove :
      ∀ x (_hx : x ∈ sRight), ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)
    (hrunRight :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).run? ≠ none) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  apply P.continuousWithinAt_case1_2_b_i_of_localPhaseTwoThresholds
    hlam hγlo hγhi
    halphaDenomMinus hphiDenomMinus hphase1DenomMinus
    halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset
  · intro x hx
    exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
      (I := I) (O := P.output ℓ ⟨x, hsLeft_subset hx⟩) (hbarLeft x hx) (hbarLeftAbove x hx)
  · intro x hx
    exact RawProcedureOutput.t2?_eq_some_of_sectionBudget_ge_theta_of_above_lt_theta
      (I := I) (O := P.output ℓ ⟨x, hsLeft_subset hx⟩)
      (hthetaLeft x hx) (hthetaLeftAbove x hx)
  · exact hrunLeft
  · intro x hx
    exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
      (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) (hbarRight x hx) (hbarRightAbove x hx)
  · intro x hx
    exact RawProcedureOutput.t2?_eq_some_of_sectionBudget_ge_theta_of_above_lt_theta
      (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩)
      (hthetaRight x hx) (hthetaRightAbove x hx)
  · exact hrunRight

/-- Phase-2/fixed jump continuity from the paper's local Phase-2 budget inequalities. -/
theorem continuousWithinAt_case1_2_b_ii_of_localPhaseTwoBudgetBounds
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hsmallLeft :
      ∀ x, x ∈ sLeft →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
    (hbarRight :
      ∀ x (_hx : x ∈ sRight),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x)
    (hbarRightAbove :
      ∀ x (_hx : x ∈ sRight), ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau)
    (hthetaRight :
      ∀ x (_hx : x ∈ sRight),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 x)
    (hthetaRightAbove :
      ∀ x (_hx : x ∈ sRight), ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)
    (hrunRight :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).run? ≠ none) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  apply P.continuousWithinAt_case1_2_b_ii_of_localPhaseTwoThresholds
    hlam hγlo hγhi halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset hsmallLeft
  · intro x hx
    exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
      (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) (hbarRight x hx) (hbarRightAbove x hx)
  · intro x hx
    exact RawProcedureOutput.t2?_eq_some_of_sectionBudget_ge_theta_of_above_lt_theta
      (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩)
      (hthetaRight x hx) (hthetaRightAbove x hx)
  · exact hrunRight

/-- Stable-threshold case on an actual path: on a neighborhood the path follows one fixed
threshold run family. -/
theorem continuousWithinAt_of_run_eq
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (F : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenom : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenom :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {s : Set ℝ}
    (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
    (hs_subset : s ⊆ Set.Icc (0 : ℝ) 1)
    (hrun :
      ∀ x (hx : x ∈ s),
        (P.output ℓ ⟨x, hs_subset hx⟩).run? = some (F.run ⟨x, hs_subset hx⟩)) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let Q := P.sectionChoice ℓ
  have hEqChoice :
      Set.EqOn Q.value (SectionRawOutputChoice.ofRunFamily F).value s := by
    exact Q.eqOn_value_of_eqOn_output (Q' := SectionRawOutputChoice.ofRunFamily F)
      hs_subset (P.output_eq_ofRunFamily_of_run_eq F hs_subset hrun)
  have hEqModel :
      Set.EqOn Q.value F.value s := by
    intro x hx
    rw [hEqChoice hx, (SectionRawOutputChoice.eqOn_value_ofRunFamily F hs_subset) hx]
  have hcontLocal : ContinuousOn F.value s := by
    exact
      (F.continuousOn_value hγlo hγhi halphaDenom hphiDenom hphase1Denom).mono hs_subset
  have W : SectionRawOutputChoice.LocalContinuityWitness Q lam :=
    SectionRawOutputChoice.localContinuityWitness_of_eqOn
      Q s hs_nhdsWithin hcontLocal (fun x hx => hEqModel hx)
  simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
    SectionRawOutputChoice.value]
    using! W.continuousWithinAt hlam

theorem continuousWithinAt_of_localT1RunsFull
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 : Idx n} {s : Set ℝ}
    (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
    (hs_subset : s ⊆ Set.Icc (0 : ℝ) 1)
    (halphaDenom : ∀ x ∈ s, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenom :
      ∀ x ∈ s,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZFullValue I ℓ x ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x ∈ s, futureCount i - I.program.frac * Advice.sectionZFullValue I ℓ x ≠ 0)
    (hrun :
      ∀ x (hx : x ∈ s),
        ∃ C : ProcedureRun I
          (Advice.sectionAdvice I ℓ x ⟨(hs_subset hx).1, (hs_subset hx).2⟩),
          (P.output ℓ ⟨x, hs_subset hx⟩).run? = some C ∧ C.t1 = t1) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let Q := P.sectionChoice ℓ
  have hEqChoice :
      Set.EqOn Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZFullValue I ℓ))
        s := by
    intro x hx
    simpa [SectionRawOutputPath.sectionChoice] using!
      (P.eqOn_value_sectionR0FullModel_of_localT1Runs hγ hγhi hs_subset hrun hx)
  have hcontLocal :
      ContinuousOn
        (Advice.sectionR0ValueAtThreshold I ℓ t1 (Advice.sectionZFullValue I ℓ))
        s := by
    exact
      Advice.continuousOn_sectionR0ValueAtThreshold I ℓ t1
        (Advice.sectionZFullValue I ℓ)
        (Advice.continuous_sectionZFullValue I ℓ).continuousOn
        halphaDenom hphiDenom hphase1Denom
  have W :
      SectionRawOutputChoice.LocalContinuityWitness Q lam :=
    SectionRawOutputChoice.localContinuityWitness_of_eqOn
      Q s hs_nhdsWithin hcontLocal (fun x hx => hEqChoice hx)
  simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
    SectionRawOutputChoice.value]
    using! W.continuousWithinAt hlam

def rightOutput (ℓ : Idx n) : RawProcedureOutput I (Advice.sectionRight I ℓ) := by
  simpa [Advice.sectionRight] using P.output ℓ ⟨1, by simp⟩

def nextLeftOutput (ℓ : Idx n) (hℓ : ℓ < lastIdx n) :
    RawProcedureOutput I (Advice.nextSectionLeft I ℓ hℓ) := by
  simpa [Advice.nextSectionLeft] using P.output (succIdx ℓ hℓ) ⟨0, by simp⟩

def firstOutput : RawProcedureOutput I (Advice.gammaZero I) := by
  simpa [Advice.gammaZero] using P.output (firstIdx n) ⟨0, by simp⟩

def lastOutput : RawProcedureOutput I (Advice.gammaOne I) := by
  simpa [Advice.gammaOne] using P.output (lastIdx n) ⟨1, by simp⟩

@[simp] theorem value_one_eq_rightOutput_R0 (ℓ : Idx n) :
    P.value ℓ 1 = (P.rightOutput ℓ).R0 := by
  simp [SectionRawOutputPath.value, SectionRawOutputPath.rightOutput]
  rfl

@[simp] theorem value_zero_eq_nextLeftOutput_R0 (ℓ : Idx n) (hℓ : ℓ < lastIdx n) :
    P.value (succIdx ℓ hℓ) 0 = (P.nextLeftOutput ℓ hℓ).R0 := by
  simp [SectionRawOutputPath.value, SectionRawOutputPath.nextLeftOutput]
  rfl

@[simp] theorem value_zero_eq_firstOutput_R0 :
    P.value (firstIdx n) 0 = P.firstOutput.R0 := by
  simp [SectionRawOutputPath.value, SectionRawOutputPath.firstOutput]
  rfl

@[simp] theorem value_one_eq_lastOutput_R0 :
    P.value (lastIdx n) 1 = P.lastOutput.R0 := by
  simp [SectionRawOutputPath.value, SectionRawOutputPath.lastOutput]
  rfl

/-- Adjacent endpoint outputs are chosen by transporting the right endpoint raw output. -/
def EndpointCompatible : Prop :=
  ∀ {ℓ : Idx n} (hℓ : ℓ < lastIdx n),
    P.nextLeftOutput ℓ hℓ = (P.rightOutput ℓ).toNextSectionLeft hℓ

/-- The scalar values agree at the common boundary of consecutive sections. -/
def EndpointGlued : Prop :=
  ∀ {ℓ : Idx n} (hℓ : ℓ < lastIdx n),
    P.value ℓ 1 = P.value (succIdx ℓ hℓ) 0

theorem endpointGlued_of_compatible (hP : P.EndpointCompatible) :
    P.EndpointGlued := by
  intro ℓ hℓ
  rw [P.value_one_eq_rightOutput_R0, P.value_zero_eq_nextLeftOutput_R0]
  rw [hP hℓ]
  exact (RawProcedureOutput.toNextSectionLeft_R0 (hℓ := hℓ) (O := P.rightOutput ℓ)).symm

theorem continuous_of_pointwiseWithin
    (hcont :
      ∀ ℓ, ∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 →
        ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam) :
    ∀ ℓ, ContinuousOn (P.value ℓ) (Set.Icc (0 : ℝ) 1) := by
  intro ℓ lam hlam
  exact hcont ℓ lam hlam

theorem continuousWithinAt_case1_2_b_i_of_eqOn_output
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1Minus t2Minus t1 t2 : Idx n}
    (Fminus : FixedThresholdSectionRunFamily n I ℓ t1Minus t2Minus)
    (Fcurr : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hOutLeft :
      ∀ x (hx : x ∈ sLeft),
        P.output ℓ ⟨x, hsLeft_subset hx⟩ =
          (SectionRawOutputChoice.ofRunFamily Fminus).output ⟨x, hsLeft_subset hx⟩)
    (hOutRight :
      ∀ x (hx : x ∈ sRight),
        P.output ℓ ⟨x, hsRight_subset hx⟩ =
          (SectionRawOutputChoice.ofRunFamily Fcurr).output ⟨x, hsRight_subset hx⟩) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  simpa
      [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
        SectionRawOutputChoice.value]
    using!
      (SectionRawOutputChoice.continuousWithinAt_case1_2_b_i_of_eqOn_output
        (Q := P.sectionChoice ℓ)
        hlam hγlo hγhi Fminus Fcurr
        halphaDenomMinus hphiDenomMinus hphase1DenomMinus
        halphaDenomCurr hphiDenomCurr hphase1DenomCurr
        hsLeft hsRight hsLeft_subset hsRight_subset
        hOutLeft hOutRight)

theorem continuousWithinAt_case1_2_b_i_of_run_eq
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1Minus t2Minus t1 t2 : Idx n}
    (Fminus : FixedThresholdSectionRunFamily n I ℓ t1Minus t2Minus)
    (Fcurr : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hrunLeft :
      ∀ x (hx : x ∈ sLeft),
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).run? = some (Fminus.run ⟨x, hsLeft_subset hx⟩))
    (hrunRight :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).run? =
          some (Fcurr.run ⟨x, hsRight_subset hx⟩)) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  apply P.continuousWithinAt_case1_2_b_i_of_eqOn_output
    hlam hγlo hγhi Fminus Fcurr
    halphaDenomMinus hphiDenomMinus hphase1DenomMinus
    halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset
  · intro x hx
    exact P.output_eq_ofRunFamily_of_run_eq Fminus hsLeft_subset hrunLeft x hx
  · intro x hx
    exact P.output_eq_ofRunFamily_of_run_eq Fcurr hsRight_subset hrunRight x hx

theorem continuousWithinAt_case1_2_b_ii_of_eqOn_output
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (Fcurr : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hsmallLeft :
      ∀ x, x ∈ sLeft →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
    (hOutRight :
      ∀ x (hx : x ∈ sRight),
        P.output ℓ ⟨x, hsRight_subset hx⟩ =
          (SectionRawOutputChoice.ofRunFamily Fcurr).output ⟨x, hsRight_subset hx⟩) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  simpa
      [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
        SectionRawOutputChoice.value]
    using!
      (SectionRawOutputChoice.continuousWithinAt_case1_2_b_ii_of_eqOn_output
        (Q := P.sectionChoice ℓ)
        hlam hγlo hγhi Fcurr
        halphaDenomCurr hphiDenomCurr hphase1DenomCurr
        hsLeft hsRight hsLeft_subset hsRight_subset
        hsmallLeft hOutRight)

theorem continuousWithinAt_case1_2_b_ii_of_run_eq
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {t1 t2 : Idx n}
    (Fcurr : FixedThresholdSectionRunFamily n I ℓ t1 t2)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hsmallLeft :
      ∀ x, x ∈ sLeft →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
    (hrunRight :
      ∀ x (hx : x ∈ sRight),
        (P.output ℓ ⟨x, hsRight_subset hx⟩).run? =
          some (Fcurr.run ⟨x, hsRight_subset hx⟩)) :
    ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  apply P.continuousWithinAt_case1_2_b_ii_of_eqOn_output
    hlam hγlo hγhi Fcurr
    halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset hsmallLeft
  intro x hx
  exact P.output_eq_ofRunFamily_of_run_eq Fcurr hsRight_subset hrunRight x hx

/-- The paper's local continuity cases, stated directly for an actual chosen raw-output path. -/
noncomputable def toScalarPath
    (hcont : ∀ ℓ, ContinuousOn (P.value ℓ) (Set.Icc (0 : ℝ) 1))
    (hglue : P.EndpointGlued)
    (hleft : P.firstOutput.R0 ≤ 1)
    (hright : 1 ≤ P.lastOutput.R0) :
    SectionScalarPath n where
  value := P.value
  continuous := hcont
  glue := hglue
  left_le_one := by simpa using hleft
  right_ge_one := by simpa using! hright

noncomputable def toScalarPath_of_compatible
    (hcont : ∀ ℓ, ContinuousOn (P.value ℓ) (Set.Icc (0 : ℝ) 1))
    (hP : P.EndpointCompatible)
    (hleft : P.firstOutput.R0 ≤ 1)
    (hright : 1 ≤ P.lastOutput.R0) :
    SectionScalarPath n :=
  P.toScalarPath hcont (P.endpointGlued_of_compatible hP) hleft hright

theorem exists_eq_one_of_compatible
    (hcont : ∀ ℓ, ContinuousOn (P.value ℓ) (Set.Icc (0 : ℝ) 1))
    (hP : P.EndpointCompatible)
    (hleft : P.firstOutput.R0 ≤ 1)
    (hright : 1 ≤ P.lastOutput.R0) :
    ∃ ℓ : Idx n, ∃ lam : ℝ, lam ∈ Set.Icc (0 : ℝ) 1 ∧ P.value ℓ lam = 1 := by
  simpa using!
    SectionScalarPath.exists_eq_one
      (P := P.toScalarPath_of_compatible hcont hP hleft hright)

theorem exists_profileData_of_compatible
    (hγ : 1 < I.program.Mcoeff)
    (hcont : ∀ ℓ, ContinuousOn (P.value ℓ) (Set.Icc (0 : ℝ) 1))
    (hP : P.EndpointCompatible)
    (hleft : P.firstOutput.R0 ≤ 1)
    (hright : 1 ≤ P.lastOutput.R0) :
    ∃ Γ : Advice I, Γ.Admissible ∧ Nonempty (ProfileData I Γ) := by
  rcases P.exists_eq_one_of_compatible hcont hP hleft hright with ⟨ℓ, lam, hlam, hval⟩
  let x : Set.Icc (0 : ℝ) 1 := ⟨lam, hlam⟩
  let O : RawProcedureOutput I
      (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩) := P.output ℓ x
  have hvalue : P.value ℓ lam = O.R0 := by
    simp [SectionRawOutputPath.value, x, O, hlam]
  have hR0 : O.R0 = 1 := by
    rw [← hvalue]
    exact hval
  have hbar : I.program.barTau < 1 := barTau_lt_one_of_one_lt_Mcoeff I hγ
  rcases O.exists_run_of_R0_eq_one I hbar hR0 with ⟨C, hC⟩
  have hCR0 : C.R0 = 1 := by
    rw [ProcedureRun.R0]
    linarith [RawProcedureOutput.R0_eq_of_some O hC, hR0]
  refine ⟨Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩,
    Advice.sectionAdvice_admissible I ℓ lam ⟨hlam.1, hlam.2⟩, ?_⟩
  exact ⟨C.toProfileData hCR0⟩

theorem exists_profileData_of_compatible_pointwise
    (hγ : 1 < I.program.Mcoeff)
    (hcont :
      ∀ ℓ, ∀ lam, lam ∈ Set.Icc (0 : ℝ) 1 →
        ContinuousWithinAt (P.value ℓ) (Set.Icc (0 : ℝ) 1) lam)
    (hP : P.EndpointCompatible)
    (hleft : P.firstOutput.R0 ≤ 1)
    (hright : 1 ≤ P.lastOutput.R0) :
    ∃ Γ : Advice I, Γ.Admissible ∧ Nonempty (ProfileData I Γ) := by
  refine P.exists_profileData_of_compatible hγ ?_ hP hleft hright
  exact P.continuous_of_pointwiseWithin hcont

end SectionRawOutputPath

theorem canonicalPath_continuousWithinAt_of_localPhaseTwoBudgetBounds
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1 t2 : Idx n}
    (halphaDenom : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenom :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {s : Set ℝ}
    (hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1))
    (hs_subset : s ⊆ Set.Icc (0 : ℝ) 1)
    (hbar :
      ∀ x (_hx : x ∈ s),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x)
    (hbarAbove :
      ∀ x (_hx : x ∈ s), ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau)
    (htheta :
      ∀ x (_hx : x ∈ s),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 x)
    (hthetaAbove :
      ∀ x (_hx : x ∈ s), ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let P : SectionRawOutputPath n I := canonicalPath I hγlo hγhi
  apply SectionRawOutputPath.continuousWithinAt_of_localPhaseTwoBudgetBounds
    (P := P) hlam hγlo hγhi halphaDenom hphiDenom hphase1Denom
    hs_nhdsWithin hs_subset hbar hbarAbove htheta hthetaAbove
  intro x hx
  have ht1 :
      (P.output ℓ ⟨x, hs_subset hx⟩).phaseTwo.t1? = some t1 := by
    exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
      (I := I) (O := P.output ℓ ⟨x, hs_subset hx⟩) (hbar x hx) (hbarAbove x hx)
  exact RawProcedureOutput.run_ne_none_of_t1_some
    (I := I) (O := P.output ℓ ⟨x, hs_subset hx⟩) ht1

theorem canonicalPath_continuousWithinAt_case1_2_b_i_of_localPhaseTwoBudgetBounds
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1Minus t2Minus t1 t2 : Idx n}
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hbarLeft :
      ∀ x (_hx : x ∈ sLeft),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1Minus x)
    (hbarLeftAbove :
      ∀ x (_hx : x ∈ sLeft), ∀ ⦃i : Idx n⦄, t1Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau)
    (hthetaLeft :
      ∀ x (_hx : x ∈ sLeft),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2Minus x)
    (hthetaLeftAbove :
      ∀ x (_hx : x ∈ sLeft), ∀ ⦃i : Idx n⦄, t2Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)
    (hbarRight :
      ∀ x (_hx : x ∈ sRight),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x)
    (hbarRightAbove :
      ∀ x (_hx : x ∈ sRight), ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau)
    (hthetaRight :
      ∀ x (_hx : x ∈ sRight),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 x)
    (hthetaRightAbove :
      ∀ x (_hx : x ∈ sRight), ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let P : SectionRawOutputPath n I := canonicalPath I hγlo hγhi
  apply SectionRawOutputPath.continuousWithinAt_case1_2_b_i_of_localPhaseTwoBudgetBounds
    (P := P)
    hlam hγlo hγhi
    halphaDenomMinus hphiDenomMinus hphase1DenomMinus
    halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset
    hbarLeft hbarLeftAbove hthetaLeft hthetaLeftAbove ?_
    hbarRight hbarRightAbove hthetaRight hthetaRightAbove ?_
  · intro x hx
    have ht1 :
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).phaseTwo.t1? = some t1Minus := by
      exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
        (I := I) (O := P.output ℓ ⟨x, hsLeft_subset hx⟩) (hbarLeft x hx) (hbarLeftAbove x hx)
    exact RawProcedureOutput.run_ne_none_of_t1_some
      (I := I) (O := P.output ℓ ⟨x, hsLeft_subset hx⟩) ht1
  · intro x hx
    have ht1 :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t1? = some t1 := by
      exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
        (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩)
        (hbarRight x hx) (hbarRightAbove x hx)
    exact RawProcedureOutput.run_ne_none_of_t1_some
      (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) ht1

theorem canonicalPath_continuousWithinAt_case1_2_b_ii_of_localPhaseTwoBudgetBounds
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1 t2 : Idx n}
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    {sLeft sRight : Set ℝ}
    (hsLeft : sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
    (hsRight : sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam))
    (hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1)
    (hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1)
    (hsmallLeft :
      ∀ x, x ∈ sLeft →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau)
    (hbarRight :
      ∀ x (_hx : x ∈ sRight),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x)
    (hbarRightAbove :
      ∀ x (_hx : x ∈ sRight), ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau)
    (hthetaRight :
      ∀ x (_hx : x ∈ sRight),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 x)
    (hthetaRightAbove :
      ∀ x (_hx : x ∈ sRight), ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let P : SectionRawOutputPath n I := canonicalPath I hγlo hγhi
  apply SectionRawOutputPath.continuousWithinAt_case1_2_b_ii_of_localPhaseTwoBudgetBounds
    (P := P)
    hlam hγlo hγhi halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset hsmallLeft
    hbarRight hbarRightAbove hthetaRight hthetaRightAbove
  intro x hx
  have ht1 :
      (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t1? = some t1 := by
    exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
      (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) (hbarRight x hx) (hbarRightAbove x hx)
  exact RawProcedureOutput.run_ne_none_of_t1_some
    (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) ht1

theorem canonicalPath_continuousWithinAt_of_total_lt_barTau
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (htotal :
      Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let P : SectionRawOutputPath n I := canonicalPath I hγlo hγhi
  let K :
      SectionRawOutputChoice.LocalCase (I := I) (ℓ := ℓ) (P.sectionChoice ℓ) lam :=
    SectionRawOutputChoice.LocalCase.phaseTwoOnly_of_total_lt_barTau
      (I := I) (ℓ := ℓ) (Q := P.sectionChoice ℓ) htotal
  exact
    (SectionRawOutputChoice.LocalCase.toLocalContinuityWitness
      (I := I) (ℓ := ℓ) (Q := P.sectionChoice ℓ) (K := K) hγlo hγhi).continuousWithinAt
      hlam

theorem canonicalPath_continuousWithinAt_of_run_none
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hnone :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).run? = none) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩) :=
    (canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩
  have hlt :
      Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau := by
    have hlt' : O.phaseTwo.beforeBudget (firstIdx n) < I.program.barTau :=
      O.beforeBudget_first_lt_barTau_of_none I hnone
    rw [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) (firstIdx n)] at hlt'
    exact hlt'
  exact canonicalPath_continuousWithinAt_of_total_lt_barTau (I := I) hγlo hγhi hlam hlt

theorem canonicalPath_continuousWithinAt_of_t1_none
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (ht1none :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).phaseTwo.t1? = none) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩) :=
    (canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩
  have hnone : O.run? = none :=
    RawProcedureOutput.run_eq_none_of_t1_none (I := I) (O := O) ht1none
  exact canonicalPath_continuousWithinAt_of_run_none (I := I) hγlo hγhi hlam hnone

theorem canonicalPath_continuousWithinAt_of_pointwisePhaseTwoBudgetBounds
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1 t2 : Idx n}
    (halphaDenom : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenom :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hbar :
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam)
    (hbarAbove :
      ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau)
    (htheta :
      I.program.theta < Advice.sectionPhaseTwoBudgetValue I ℓ t2 lam)
    (hthetaAbove :
      ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let rest : Set ℝ := {x |
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x ∧
      (∀ i : Idx n, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau) ∧
      I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 x ∧
      (∀ i : Idx n, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)}
  let s : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ rest
  have hbarStrict :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
        I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ t1 x := by
    have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ t1).continuousWithinAt
      : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ t1 x)
          (Set.Icc (0 : ℝ) 1) lam).preimage_mem_nhdsWithin (Ioi_mem_nhds hbar)
    filter_upwards [hpre] with x hx
    simpa using hx
  have hbarEvt :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x :=
    hbarStrict.mono fun _ hx => le_of_lt hx
  have hbarAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
          t1 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
    intro i
    by_cases hi : t1 < i
    · have hiEvt :
          ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
        have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
          : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
              (Set.Icc (0 : ℝ) 1) lam).preimage_mem_nhdsWithin
                (Iio_mem_nhds (hbarAbove hi))
        filter_upwards [hpre] with x hx
        simpa using hx
      filter_upwards [hiEvt] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hbarAboveEvt :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
        ∀ i : Idx n, t1 < i →
          Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau :=
    Filter.eventually_all.2 hbarAboveEach
  have hthetaStrict :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
        I.program.theta < Advice.sectionPhaseTwoBudgetValue I ℓ t2 x := by
    have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ t2).continuousWithinAt
      : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ t2 x)
          (Set.Icc (0 : ℝ) 1) lam).preimage_mem_nhdsWithin (Ioi_mem_nhds htheta)
    filter_upwards [hpre] with x hx
    simpa using hx
  have hthetaEvt :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 x :=
    hthetaStrict.mono fun _ hx => le_of_lt hx
  have hthetaAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
          t2 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta := by
    intro i
    by_cases hi : t2 < i
    · have hiEvt :
          ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta := by
        have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
          : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
              (Set.Icc (0 : ℝ) 1) lam).preimage_mem_nhdsWithin
                (Iio_mem_nhds (hthetaAbove hi))
        filter_upwards [hpre] with x hx
        simpa using hx
      filter_upwards [hiEvt] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hthetaAboveEvt :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
        ∀ i : Idx n, t2 < i →
          Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta :=
    Filter.eventually_all.2 hthetaAboveEach
  have hrest_nhdsWithin : rest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1) := by
    have hrest_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1), x ∈ rest := by
      exact
        (hbarEvt.and
          ((Filter.eventually_all.2 hbarAboveEach).and
            (hthetaEvt.and (Filter.eventually_all.2 hthetaAboveEach)))).mono
          (fun x hx => by
            rcases hx with ⟨hxbar, hxbarAbove, hxtheta, hxthetaAbove⟩
            exact ⟨hxbar, hxbarAbove, hxtheta, hxthetaAbove⟩)
    simpa only [Filter.Eventually] using! hrest_evt
  have hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1) := by
    simpa [s] using Filter.inter_mem self_mem_nhdsWithin hrest_nhdsWithin
  have hs_subset : s ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1
  apply canonicalPath_continuousWithinAt_of_localPhaseTwoBudgetBounds
    (I := I) hγlo hγhi hlam halphaDenom hphiDenom hphase1Denom
    hs_nhdsWithin hs_subset
  · intro x hx
    exact hx.2.1
  · intro x hx i hi
    exact hx.2.2.1 i hi
  · intro x hx
    exact hx.2.2.2.1
  · intro x hx i hi
    exact hx.2.2.2.2 i hi

theorem canonicalPath_continuousWithinAt_case1_2_b_ii_of_pointwisePhaseTwoBudgetBounds
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1 t2 : Idx n}
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hsmallLeft :
      Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau)
    (hbarRight :
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam)
    (hbarRightAbove :
      ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau)
    (hthetaRight :
      I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 lam)
    (hthetaRightAbove :
      ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let sLeft : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam
  let rightRest : Set ℝ := {x |
      (∀ i : Idx n, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau) ∧
      (∀ i : Idx n, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)}
  let sRight : Set ℝ := (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) ∩ rightRest
  have hsLeft :
      sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) := by
    simpa [sLeft] using
      (self_mem_nhdsWithin :
        Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam ∈
          nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam))
  have hsRightCoreEachBar :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          t1 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
    intro i
    by_cases hi : t1 < i
    · have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds (hbarRightAbove hi))
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hsRightCoreEachTheta :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          t2 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta := by
    intro i
    by_cases hi : t2 < i
    · have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds (hthetaRightAbove hi))
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hsRightCore :
      rightRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    have hs_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam), x ∈ rightRest := by
      exact
        ((Filter.eventually_all.2 hsRightCoreEachBar).and
          (Filter.eventually_all.2 hsRightCoreEachTheta)).mono
          (fun x hx => by
            rcases hx with ⟨hxbar, hxtheta⟩
            exact ⟨hxbar, hxtheta⟩)
    simpa only [Filter.Eventually] using! hs_evt
  have hsRight :
      sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    simpa [sRight] using Filter.inter_mem self_mem_nhdsWithin hsRightCore
  have hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1
  have hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  apply canonicalPath_continuousWithinAt_case1_2_b_ii_of_localPhaseTwoBudgetBounds
    (I := I) hγlo hγhi hlam halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset
  · intro x hx
    have hmono :
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x ≤
          Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam :=
      Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
        (I := I) hγlo ℓ (firstIdx n) hx.1.1 hx.2
    linarith
  · intro x hx
    have hmono :
        Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam ≤
          Advice.sectionPhaseTwoBudgetValue I ℓ t1 x :=
      Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
        (I := I) hγlo ℓ t1 hlam.1 hx.1.2
    linarith
  · intro x hx i hi
    exact hx.2.1 i hi
  · intro x hx
    have hmono :
        Advice.sectionPhaseTwoBudgetValue I ℓ t2 lam ≤
          Advice.sectionPhaseTwoBudgetValue I ℓ t2 x :=
      Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
        (I := I) hγlo ℓ t2 hlam.1 hx.1.2
    linarith
  · intro x hx i hi
    exact hx.2.2 i hi

theorem canonicalPath_continuousWithinAt_case1_2_b_i_of_pointwisePhaseTwoBudgetBounds
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1Minus t2Minus t1 t2 : Idx n}
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hbarLeft :
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ t1Minus lam)
    (hbarLeftAbove :
      ∀ ⦃i : Idx n⦄, t1Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau)
    (hthetaLeft :
      I.program.theta < Advice.sectionPhaseTwoBudgetValue I ℓ t2Minus lam)
    (hthetaLeftAbove :
      ∀ ⦃i : Idx n⦄, t2Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta)
    (hbarRight :
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam)
    (hbarRightAbove :
      ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau)
    (hthetaRight :
      I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 lam)
    (hthetaRightAbove :
      ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let leftRest : Set ℝ := {x |
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1Minus x ∧
      (∀ i : Idx n, t1Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau) ∧
      I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2Minus x ∧
      (∀ i : Idx n, t2Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)}
  let rightRest : Set ℝ := {x |
      (∀ i : Idx n, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau) ∧
      (∀ i : Idx n, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)}
  let sLeft : Set ℝ := (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) ∩ leftRest
  let sRight : Set ℝ := (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) ∩ rightRest
  have hleftBarEvt :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
        I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ t1Minus x := by
    have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ t1Minus).continuousWithinAt
      : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ t1Minus x)
          (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam).preimage_mem_nhdsWithin
            (Ioi_mem_nhds hbarLeft)
    filter_upwards [hpre] with x hx
    simpa using hx
  have hleftBarGe :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1Minus x :=
    hleftBarEvt.mono fun _ hx => le_of_lt hx
  have hleftBarAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
          t1Minus < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
    intro i
    by_cases hi : t1Minus < i
    · have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds (hbarLeftAbove hi))
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hleftThetaEvt :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
        I.program.theta < Advice.sectionPhaseTwoBudgetValue I ℓ t2Minus x := by
    have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ t2Minus).continuousWithinAt
      : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ t2Minus x)
          (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam).preimage_mem_nhdsWithin
            (Ioi_mem_nhds hthetaLeft)
    filter_upwards [hpre] with x hx
    simpa using hx
  have hleftThetaGe :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
        I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2Minus x :=
    hleftThetaEvt.mono fun _ hx => le_of_lt hx
  have hleftThetaAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
          t2Minus < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta := by
    intro i
    by_cases hi : t2Minus < i
    · have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds (hthetaLeftAbove hi))
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hleftRest :
      leftRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) := by
    have hs_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam), x ∈ leftRest := by
      exact
        (hleftBarGe.and
          ((Filter.eventually_all.2 hleftBarAboveEach).and
            (hleftThetaGe.and (Filter.eventually_all.2 hleftThetaAboveEach)))).mono
          (fun x hx => by
            rcases hx with ⟨hxbar, hxbarAbove, hxtheta, hxthetaAbove⟩
            exact ⟨hxbar, hxbarAbove, hxtheta, hxthetaAbove⟩)
    simpa only [Filter.Eventually] using! hs_evt
  have hsLeft :
      sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) := by
    simpa [sLeft] using Filter.inter_mem self_mem_nhdsWithin hleftRest
  have hrightBarAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          t1 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
    intro i
    by_cases hi : t1 < i
    · have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds (hbarRightAbove hi))
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hrightThetaAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          t2 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta := by
    intro i
    by_cases hi : t2 < i
    · have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds (hthetaRightAbove hi))
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hrightRest :
      rightRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    have hs_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam), x ∈ rightRest := by
      exact
        ((Filter.eventually_all.2 hrightBarAboveEach).and
          (Filter.eventually_all.2 hrightThetaAboveEach)).mono
          (fun x hx => by
            rcases hx with ⟨hxbar, hxtheta⟩
            exact ⟨hxbar, hxtheta⟩)
    simpa only [Filter.Eventually] using! hs_evt
  have hsRight :
      sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    simpa [sRight] using Filter.inter_mem self_mem_nhdsWithin hrightRest
  have hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  have hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  apply canonicalPath_continuousWithinAt_case1_2_b_i_of_localPhaseTwoBudgetBounds
    (I := I) hγlo hγhi hlam
    halphaDenomMinus hphiDenomMinus hphase1DenomMinus
    halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsLeft hsRight hsLeft_subset hsRight_subset
  · intro x hx
    exact hx.2.1
  · intro x hx i hi
    exact hx.2.2.1 i hi
  · intro x hx
    exact hx.2.2.2.1
  · intro x hx i hi
    exact hx.2.2.2.2 i hi
  · intro x hx
    have hmono :
        Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam ≤
          Advice.sectionPhaseTwoBudgetValue I ℓ t1 x :=
      Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
        (I := I) hγlo ℓ t1 hlam.1 hx.1.2
    linarith
  · intro x hx i hi
    exact hx.2.1 i hi
  · intro x hx
    have hmono :
        Advice.sectionPhaseTwoBudgetValue I ℓ t2 lam ≤
          Advice.sectionPhaseTwoBudgetValue I ℓ t2 x :=
      Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
        (I := I) hγlo ℓ t2 hlam.1 hx.1.2
    linarith
  · intro x hx i hi
    exact hx.2.2 i hi

theorem canonicalPath_continuousWithinAt_of_thresholdSpecs_strict
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1 t2 : Idx n}
    (ht1 :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).phaseTwo.t1? = some t1)
    (ht2 :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).phaseTwo.t2? = some t2)
    (halphaDenom : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenom :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1Denom :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hbar :
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam)
    (htheta :
      I.program.theta < Advice.sectionPhaseTwoBudgetValue I ℓ t2 lam) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩) :=
    (canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩
  have hbarAbove :
      ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau := by
    intro i hi
    have hlt : O.phaseTwo.beforeBudget i < I.program.barTau :=
      Advice.PhaseTwoData.beforeBudget_lt_barTau_of_t1?_eq_some_of_lt
        (Ξ := O.phaseTwo) ht1 hi
    rw [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) i] at hlt
    exact hlt
  have hthetaAbove :
      ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta := by
    intro i hi
    have hlt : O.phaseTwo.beforeBudget i < I.program.theta :=
      Advice.PhaseTwoData.beforeBudget_lt_theta_of_t2?_eq_some_of_lt
        (Ξ := O.phaseTwo) ht2 hi
    rw [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) i] at hlt
    exact hlt
  exact canonicalPath_continuousWithinAt_of_pointwisePhaseTwoBudgetBounds
    (I := I) hγlo hγhi hlam halphaDenom hphiDenom hphase1Denom
    hbar hbarAbove htheta hthetaAbove

theorem canonicalPath_continuousWithinAt_of_run_some_barTau_strict_full
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (_hrun :
      ((canonicalPath I (le_of_lt hγ) hγhi).output ℓ ⟨lam, hlam⟩).run? = some C)
    (hbar :
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam) :
    ContinuousWithinAt
      ((canonicalPath I (le_of_lt hγ) hγhi).value ℓ)
      (Set.Icc (0 : ℝ) 1)
      lam := by
  let P : SectionRawOutputPath n I := canonicalPath I (le_of_lt hγ) hγhi
  let baseRest : Set ℝ := {x |
    I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x ∧
      ∀ i : Idx n, C.t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau}
  have hbarEvt :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
        I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x := by
    have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ C.t1).continuousWithinAt
      : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x)
          (Set.Icc (0 : ℝ) 1) lam).preimage_mem_nhdsWithin (Ioi_mem_nhds hbar)
    filter_upwards [hpre] with x hx
    simpa using hx
  have haboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
          C.t1 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
    intro i
    by_cases hi : C.t1 < i
    · have hlt : Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau := by
        have hlt' : C.phaseTwo.beforeBudget i < I.program.barTau :=
          C.phaseTwo_beforeBudget_lt_barTau_above_t1 hi
        simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
          (Ξ := C.phaseTwo) i] using hlt'
      have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1) lam).preimage_mem_nhdsWithin (Iio_mem_nhds hlt)
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hbaseRest :
      baseRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1) := by
    exact (hbarEvt.and (Filter.eventually_all.2 haboveEach)).mono (fun _ hx => hx)
  by_cases ht1last : C.t1 = lastIdx n
  · let s : Set ℝ := (Set.Icc (0 : ℝ) 1) ∩ baseRest
    have hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1) := by
      simpa [s] using Filter.inter_mem self_mem_nhdsWithin hbaseRest
    have hs_subset : s ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact hx.1
    have hrun :
        ∀ x (hx : x ∈ s),
          ∃ Cx : ProcedureRun I
            (Advice.sectionAdvice I ℓ x ⟨(hs_subset hx).1, (hs_subset hx).2⟩),
            (P.output ℓ ⟨x, hs_subset hx⟩).run? = some Cx ∧ Cx.t1 = C.t1 := by
      intro x hx
      have ht1x :
          (P.output ℓ ⟨x, hs_subset hx⟩).phaseTwo.t1? = some C.t1 := by
        exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
          (I := I) (O := P.output ℓ ⟨x, hs_subset hx⟩) (le_of_lt hx.2.1)
          (fun i hi => hx.2.2 i hi)
      have hrunx :
          (P.output ℓ ⟨x, hs_subset hx⟩).run? ≠ none :=
        RawProcedureOutput.run_ne_none_of_t1_some
          (I := I) (O := P.output ℓ ⟨x, hs_subset hx⟩) ht1x
      rcases (P.output ℓ ⟨x, hs_subset hx⟩).exists_run_of_ne_none I hrunx with ⟨Cx, hCx⟩
      have hphaseCx :
          (P.output ℓ ⟨x, hs_subset hx⟩).phaseTwo.t1? = some Cx.t1 := by
        simpa [(P.output ℓ ⟨x, hs_subset hx⟩).run_phaseTwo hCx] using Cx.t1_spec
      have ht1Cx : Cx.t1 = C.t1 := by
        exact Option.some.inj (by rw [← hphaseCx, ht1x])
      exact ⟨Cx, hCx, ht1Cx⟩
    let Q := P.sectionChoice ℓ
    have hEqChoice :
        Set.EqOn Q.value
          (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
          s := by
      intro x hx
      simpa [SectionRawOutputPath.sectionChoice] using!
        (P.eqOn_value_sectionR0FullModel_of_localT1Runs hγ hγhi hs_subset hrun hx)
    have hphase1Denom :
        ∀ ⦃i : Idx n⦄, i < C.t1 →
          ∀ x ∈ s, futureCount i - I.program.frac * Advice.sectionZFullValue I ℓ x ≠ 0 := by
      intro i hi x hx
      exact ne_of_gt <|
        Advice.sectionPhase1DenomFull_pos_of_barTau_lt
          (I := I) hγ hγhi ℓ C.t1 ⟨(hs_subset hx).1, (hs_subset hx).2⟩ hi hx.2.1
    have hcontLocal :
        ContinuousOn
          (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
          s := by
      have hboundary :
          ContinuousOn
            (fun x =>
              Advice.sectionBoundaryBudgetValue I ℓ C.t1 (Advice.sectionZFullValue I ℓ) x)
            s := by
        simpa [Advice.sectionBoundaryBudgetValue, ht1last] using
          (Advice.continuous_sectionPhaseTwoHatG2Value I ℓ C.t1).continuousOn
      have hprefix :
          ContinuousOn
            (fun x =>
              Advice.sectionPhase1PrefixValue I ℓ C.t1 (Advice.sectionZFullValue I ℓ) x)
            s :=
        Advice.continuousOn_sectionPhase1PrefixValue I ℓ C.t1
          (Advice.sectionZFullValue I ℓ)
          (Advice.continuous_sectionZFullValue I ℓ).continuousOn
          hphase1Denom
      simpa [Advice.sectionR0ValueAtThreshold] using! hboundary.add hprefix
    have W :
        SectionRawOutputChoice.LocalContinuityWitness Q lam :=
      SectionRawOutputChoice.localContinuityWitness_of_eqOn
        Q s hs_nhdsWithin hcontLocal (fun x hx => hEqChoice hx)
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using! W.continuousWithinAt hlam
  · let phiFull : ℝ → ℝ := fun x =>
      futureCount C.t1 +
        Advice.sectionBoundaryAlphaValue I ℓ C.t1 x *
          (1 - Advice.sectionMuDValue I ℓ C.t1 x) -
        I.program.frac * Advice.sectionZFullValue I ℓ x
    have hhatPos :
        0 < Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam :=
      C.sectionPhaseTwoHatG2Value_pos_at_t1_of_sectionAdvice_of_ne_last ht1last
    have hhatEvt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1),
          0 < Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 x := by
      have hpre := ((Advice.continuous_sectionPhaseTwoHatG2Value I ℓ C.t1).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 x)
            (Set.Icc (0 : ℝ) 1) lam).preimage_mem_nhdsWithin (Ioi_mem_nhds hhatPos)
      simpa only [Set.preimage, Set.mem_ofPred_eq] using! hpre
    have hzEq :
        Advice.sectionZValue I ℓ C.t2 lam = Advice.sectionZFullValue I ℓ lam := by
      rw [← C.z_eq_sectionZValue_of_sectionAdvice,
        C.z_eq_sectionZFullValue_of_sectionAdvice hγ]
    have hphiPos : 0 < phiFull lam := by
      simpa [phiFull, hzEq] using
        (C.sectionBoundaryPhiDenom_pos_of_sectionAdvice_of_ne_last hγ ht1last)
    have hAlphaCont :
        ContinuousWithinAt (fun x => Advice.sectionBoundaryAlphaValue I ℓ C.t1 x)
          (Set.Icc (0 : ℝ) 1) lam := by
      have hnumCont :
          ContinuousWithinAt
            (fun x => I.program.barTau - Advice.sectionPhaseTwoAfterBudgetValue I ℓ C.t1 x)
            (Set.Icc (0 : ℝ) 1) lam :=
        (continuous_const.sub
          (Advice.continuous_sectionPhaseTwoAfterBudgetValue I ℓ C.t1)).continuousWithinAt
      simpa [Advice.sectionBoundaryAlphaValue, ht1last, dite_false] using!
        (hnumCont.div
          (Advice.continuous_sectionPhaseTwoHatG2Value I ℓ C.t1).continuousWithinAt
          (ne_of_gt hhatPos))
    have hphiCont :
        ContinuousWithinAt phiFull (Set.Icc (0 : ℝ) 1) lam := by
      dsimp [phiFull]
      exact
        (continuousWithinAt_const.add
          (hAlphaCont.mul
            (continuousWithinAt_const.sub
              (Advice.continuous_sectionMuDValue I ℓ C.t1).continuousWithinAt))).sub
          (continuousWithinAt_const.mul
            (Advice.continuous_sectionZFullValue I ℓ).continuousWithinAt)
    have hphiEvt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1), 0 < phiFull x := by
      have hpre := hphiCont.preimage_mem_nhdsWithin (Ioi_mem_nhds hphiPos)
      simpa only [Set.preimage, Set.mem_ofPred_eq] using! hpre
    let s : Set ℝ :=
      (Set.Icc (0 : ℝ) 1) ∩
        {x |
          I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x ∧
          (∀ i : Idx n, C.t1 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau) ∧
          0 < Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 x ∧
          0 < phiFull x}
    have hs_nhdsWithin : s ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1) := by
      have hrest :
          {x |
              I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x ∧
              (∀ i : Idx n, C.t1 < i →
                Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau) ∧
              0 < Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 x ∧
              0 < phiFull x} ∈
            nhdsWithin lam (Set.Icc (0 : ℝ) 1) := by
        exact
          (hbarEvt.and
            ((Filter.eventually_all.2 haboveEach).and (hhatEvt.and hphiEvt))).mono
            (fun _ hx => by
              rcases hx with ⟨hxbar, ⟨hxabove, ⟨hxhat, hxphi⟩⟩⟩
              exact ⟨hxbar, hxabove, hxhat, hxphi⟩)
      simpa [s] using Filter.inter_mem self_mem_nhdsWithin hrest
    have hs_subset : s ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact hx.1
    apply P.continuousWithinAt_of_localT1RunsFull
      hlam hγ hγhi hs_nhdsWithin hs_subset
    · intro x hx
      exact ne_of_gt hx.2.2.2.1
    · intro x hx
      exact ne_of_gt hx.2.2.2.2
    · intro i hi x hx
      exact ne_of_gt <|
        Advice.sectionPhase1DenomFull_pos_of_barTau_lt
          (I := I) hγ hγhi ℓ C.t1 ⟨(hs_subset hx).1, (hs_subset hx).2⟩ hi hx.2.1
    · intro x hx
      have ht1x :
          (P.output ℓ ⟨x, hs_subset hx⟩).phaseTwo.t1? = some C.t1 := by
        exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
          (I := I) (O := P.output ℓ ⟨x, hs_subset hx⟩) (le_of_lt hx.2.1)
          (fun i hi => hx.2.2.1 i hi)
      have hrunx :
          (P.output ℓ ⟨x, hs_subset hx⟩).run? ≠ none :=
        RawProcedureOutput.run_ne_none_of_t1_some
          (I := I) (O := P.output ℓ ⟨x, hs_subset hx⟩) ht1x
      rcases (P.output ℓ ⟨x, hs_subset hx⟩).exists_run_of_ne_none I hrunx with ⟨Cx, hCx⟩
      have ht1Cx :
          Cx.t1 = C.t1 := by
        have hphaseCx :
            (P.output ℓ ⟨x, hs_subset hx⟩).phaseTwo.t1? = some Cx.t1 := by
          simpa [(P.output ℓ ⟨x, hs_subset hx⟩).run_phaseTwo hCx] using Cx.t1_spec
        exact Option.some.inj (by rw [← hphaseCx, ht1x])
      exact ⟨Cx, hCx, ht1Cx⟩

theorem canonicalPath_continuousWithinAt_of_run_some_strict
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (hrun :
      ((canonicalPath I (le_of_lt hγ) hγhi).output ℓ ⟨lam, hlam⟩).run? = some C)
    (hbar :
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam) :
    ContinuousWithinAt
      ((canonicalPath I (le_of_lt hγ) hγhi).value ℓ)
      (Set.Icc (0 : ℝ) 1)
      lam := by
  exact canonicalPath_continuousWithinAt_of_run_some_barTau_strict_full
    (I := I) hγ hγhi hlam hrun hbar

theorem canonicalPath_continuousWithinAt_case1_2_b_ii_of_thresholdSpecs
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1 t2 : Idx n}
    (ht1 :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).phaseTwo.t1? = some t1)
    (ht2 :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).phaseTwo.t2? = some t2)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hsmallLeft :
      Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩) :=
    (canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩
  have hbarRight :
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam := by
    have hge : I.program.barTau ≤ O.phaseTwo.beforeBudget t1 :=
      Advice.PhaseTwoData.beforeBudget_ge_barTau_of_t1?_eq_some (Ξ := O.phaseTwo) ht1
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) t1] using hge
  have hbarRightAbove :
      ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau := by
    intro i hi
    have hlt : O.phaseTwo.beforeBudget i < I.program.barTau :=
      Advice.PhaseTwoData.beforeBudget_lt_barTau_of_t1?_eq_some_of_lt
        (Ξ := O.phaseTwo) ht1 hi
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) i] using hlt
  have hthetaRight :
      I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 lam := by
    have hge : I.program.theta ≤ O.phaseTwo.beforeBudget t2 :=
      Advice.PhaseTwoData.beforeBudget_ge_theta_of_t2?_eq_some (Ξ := O.phaseTwo) ht2
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) t2] using hge
  have hthetaRightAbove :
      ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta := by
    intro i hi
    have hlt : O.phaseTwo.beforeBudget i < I.program.theta :=
      Advice.PhaseTwoData.beforeBudget_lt_theta_of_t2?_eq_some_of_lt
        (Ξ := O.phaseTwo) ht2 hi
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) i] using hlt
  exact canonicalPath_continuousWithinAt_case1_2_b_ii_of_pointwisePhaseTwoBudgetBounds
    (I := I) hγlo hγhi hlam halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hsmallLeft hbarRight hbarRightAbove hthetaRight hthetaRightAbove

theorem canonicalPath_continuousWithinAt_case1_2_b_ii_of_run_some
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (hrun :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).run? = some C)
    (hsmallLeft :
      Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩) :=
    (canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩
  have hphase :
      O.phaseTwo =
        Advice.sectionPhaseTwoData (I := I) hγlo ℓ lam ⟨hlam.1, hlam.2⟩ := by
    simpa [O, canonicalPath] using
      (PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice
        (I := I) (Ξ := O.phaseTwo) hγlo)
  have ht1none : O.phaseTwo.t1? = none := by
    rw [hphase]
    exact
      (sectionPhaseTwoData_t1_eq_none_of_total_lt_barTau
        (I := I) hγlo ℓ lam ⟨hlam.1, hlam.2⟩ hsmallLeft)
  have hnone : O.run? = none :=
    RawProcedureOutput.run_eq_none_of_t1_none (I := I) (O := O) ht1none
  have hrun' : O.run? = some C := by
    simpa [O] using hrun
  have hfalse : False := by
    simp [hnone] at hrun'
  exact False.elim hfalse

theorem canonicalPath_continuousWithinAt_case1_2_b_i_of_thresholdSpecs
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1Minus t2Minus t1 t2 : Idx n}
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (ht1 :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).phaseTwo.t1? = some t1)
    (ht2 :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).phaseTwo.t2? = some t2)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount t1 +
            Advice.sectionBoundaryAlphaValue I ℓ t1 x *
              (1 - Advice.sectionMuDValue I ℓ t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2 x ≠ 0)
    (hbarLeft :
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ t1Minus lam)
    (hbarLeftAbove :
      ∀ ⦃i : Idx n⦄, t1Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau)
    (hthetaLeft :
      I.program.theta < Advice.sectionPhaseTwoBudgetValue I ℓ t2Minus lam)
    (hthetaLeftAbove :
      ∀ ⦃i : Idx n⦄, t2Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩) :=
    (canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩
  have hbarRight :
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam := by
    have hge : I.program.barTau ≤ O.phaseTwo.beforeBudget t1 :=
      Advice.PhaseTwoData.beforeBudget_ge_barTau_of_t1?_eq_some (Ξ := O.phaseTwo) ht1
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) t1] using hge
  have hbarRightAbove :
      ∀ ⦃i : Idx n⦄, t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau := by
    intro i hi
    have hlt : O.phaseTwo.beforeBudget i < I.program.barTau :=
      Advice.PhaseTwoData.beforeBudget_lt_barTau_of_t1?_eq_some_of_lt
        (Ξ := O.phaseTwo) ht1 hi
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) i] using hlt
  have hthetaRight :
      I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t2 lam := by
    have hge : I.program.theta ≤ O.phaseTwo.beforeBudget t2 :=
      Advice.PhaseTwoData.beforeBudget_ge_theta_of_t2?_eq_some (Ξ := O.phaseTwo) ht2
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) t2] using hge
  have hthetaRightAbove :
      ∀ ⦃i : Idx n⦄, t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta := by
    intro i hi
    have hlt : O.phaseTwo.beforeBudget i < I.program.theta :=
      Advice.PhaseTwoData.beforeBudget_lt_theta_of_t2?_eq_some_of_lt
        (Ξ := O.phaseTwo) ht2 hi
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := O.phaseTwo) i] using hlt
  exact canonicalPath_continuousWithinAt_case1_2_b_i_of_pointwisePhaseTwoBudgetBounds
    (I := I) hγlo hγhi hlam
    halphaDenomMinus hphiDenomMinus hphase1DenomMinus
    halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hbarLeft hbarLeftAbove hthetaLeft hthetaLeftAbove
    hbarRight hbarRightAbove hthetaRight hthetaRightAbove

theorem canonicalPath_continuousWithinAt_case1_2_b_i_of_run_some
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {t1Minus t2Minus : Idx n}
    (halphaDenomMinus : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ t1Minus x ≠ 0)
    (hphiDenomMinus :
      ∀ x,
        futureCount t1Minus +
            Advice.sectionBoundaryAlphaValue I ℓ t1Minus x *
              (1 - Advice.sectionMuDValue I ℓ t1Minus x) -
          I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    (hphase1DenomMinus :
      ∀ ⦃i : Idx n⦄, i < t1Minus →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ t2Minus x ≠ 0)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (hrun :
      ((canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩).run? = some C)
    (halphaDenomCurr : ∀ x, Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 x ≠ 0)
    (hphiDenomCurr :
      ∀ x,
        futureCount C.t1 +
            Advice.sectionBoundaryAlphaValue I ℓ C.t1 x *
              (1 - Advice.sectionMuDValue I ℓ C.t1 x) -
          I.program.frac * Advice.sectionZValue I ℓ C.t2 x ≠ 0)
    (hphase1DenomCurr :
      ∀ ⦃i : Idx n⦄, i < C.t1 →
        ∀ x, futureCount i - I.program.frac * Advice.sectionZValue I ℓ C.t2 x ≠ 0)
    (hbarLeft :
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ t1Minus lam)
    (hbarLeftAbove :
      ∀ ⦃i : Idx n⦄, t1Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau)
    (hthetaLeft :
      I.program.theta < Advice.sectionPhaseTwoBudgetValue I ℓ t2Minus lam)
    (hthetaLeftAbove :
      ∀ ⦃i : Idx n⦄, t2Minus < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta) :
    ContinuousWithinAt ((canonicalPath I hγlo hγhi).value ℓ) (Set.Icc (0 : ℝ) 1) lam := by
  let O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩) :=
    (canonicalPath I hγlo hγhi).output ℓ ⟨lam, hlam⟩
  have ht1 : O.phaseTwo.t1? = some C.t1 := by
    simpa [O.run_phaseTwo hrun] using C.t1_spec
  have ht2 : O.phaseTwo.t2? = some C.t2 := by
    simpa [O.run_phaseTwo hrun] using C.t2_spec
  exact canonicalPath_continuousWithinAt_case1_2_b_i_of_thresholdSpecs
    (I := I) hγlo hγhi hlam
    halphaDenomMinus hphiDenomMinus hphase1DenomMinus
    ht1 ht2 halphaDenomCurr hphiDenomCurr hphase1DenomCurr
    hbarLeft hbarLeftAbove hthetaLeft hthetaLeftAbove

theorem canonicalPath_continuousWithinAt_of_run_some_leftStable
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (_hrun :
      ((canonicalPath I (le_of_lt hγ) hγhi).output ℓ ⟨lam, hlam⟩).run? = some C)
    (hleftStable :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x) :
    ContinuousWithinAt
      ((canonicalPath I (le_of_lt hγ) hγhi).value ℓ)
      (Set.Icc (0 : ℝ) 1)
      lam := by
  let leftRest : Set ℝ := {x |
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x ∧
      ∀ i : Idx n, C.t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau}
  let sLeft : Set ℝ := (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) ∩ leftRest
  have hleftBarAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
          C.t1 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
    intro i
    by_cases hi : C.t1 < i
    · have hlt : Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau := by
        have hlt' : C.phaseTwo.beforeBudget i < I.program.barTau :=
          C.phaseTwo_beforeBudget_lt_barTau_above_t1 hi
        simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
          (Ξ := C.phaseTwo) i] using hlt'
      have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds hlt)
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hleftRest :
      leftRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) := by
    have hs_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam), x ∈ leftRest := by
      exact
        (hleftStable.and (Filter.eventually_all.2 hleftBarAboveEach)).mono
          (fun x hx => by
            rcases hx with ⟨hxbar, hxbarAbove⟩
            exact ⟨hxbar, hxbarAbove⟩)
    simpa only [Filter.Eventually] using! hs_evt
  have hsLeft :
      sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) := by
    simpa [sLeft] using Filter.inter_mem self_mem_nhdsWithin hleftRest
  have hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  let rightRest : Set ℝ := {x |
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x ∧
      ∀ i : Idx n, C.t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau}
  let sRight : Set ℝ := (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) ∩ rightRest
  have hrightBarAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          C.t1 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
    intro i
    by_cases hi : C.t1 < i
    · have hlt : Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau := by
        have hlt' : C.phaseTwo.beforeBudget i < I.program.barTau :=
          C.phaseTwo_beforeBudget_lt_barTau_above_t1 hi
        simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
          (Ξ := C.phaseTwo) i] using hlt'
      have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds hlt)
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hbarAtT1 :
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam := by
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1] using C.t1_beforeBudget_ge_barTau
  have hrightRest :
      rightRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    have hbarGeEvt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hmono :
        Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam ≤
            Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x :=
        Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
          (I := I) (le_of_lt hγ) ℓ C.t1 hlam.1 hx.2
      exact le_trans hbarAtT1 hmono
    have hs_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam), x ∈ rightRest := by
      exact
        (hbarGeEvt.and (Filter.eventually_all.2 hrightBarAboveEach)).mono
          (fun x hx => by
            rcases hx with ⟨hxbar, hxbarAbove⟩
            exact ⟨hxbar, hxbarAbove⟩)
    simpa only [Filter.Eventually] using! hs_evt
  have hsRight :
      sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    simpa [sRight] using Filter.inter_mem self_mem_nhdsWithin hrightRest
  have hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  let P : SectionRawOutputPath n I := canonicalPath I (le_of_lt hγ) hγhi
  let Q := P.sectionChoice ℓ
  have hrunLeft :
      ∀ x (hx : x ∈ sLeft),
        ∃ Cx : ProcedureRun I (Advice.sectionAdvice I ℓ x
          ⟨(hsLeft_subset hx).1, (hsLeft_subset hx).2⟩),
          (P.output ℓ ⟨x, hsLeft_subset hx⟩).run? = some Cx ∧
            Cx.t1 = C.t1 := by
    intro x hx
    have ht1Left :
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).phaseTwo.t1? = some C.t1 := by
      exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
        (I := I) (O := P.output ℓ ⟨x, hsLeft_subset hx⟩) (hx.2.1)
        (fun i hi => hx.2.2 i hi)
    have hrunLeft' :
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).run? ≠ none :=
      RawProcedureOutput.run_ne_none_of_t1_some
        (I := I) (O := P.output ℓ ⟨x, hsLeft_subset hx⟩) ht1Left
    rcases (P.output ℓ ⟨x, hsLeft_subset hx⟩).exists_run_of_ne_none I hrunLeft' with
      ⟨Cx, hCx⟩
    have hphaseCx :
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).phaseTwo.t1? = some Cx.t1 := by
      simpa [(P.output ℓ ⟨x, hsLeft_subset hx⟩).run_phaseTwo hCx] using Cx.t1_spec
    have ht1Cx : Cx.t1 = C.t1 := by
      exact Option.some.inj (by rw [← hphaseCx, ht1Left])
    exact ⟨Cx, hCx, ht1Cx⟩
  have hrunRight :
      ∀ x (hx : x ∈ sRight),
        ∃ Cx : ProcedureRun I (Advice.sectionAdvice I ℓ x
          ⟨(hsRight_subset hx).1, (hsRight_subset hx).2⟩),
          (P.output ℓ ⟨x, hsRight_subset hx⟩).run? = some Cx ∧
            Cx.t1 = C.t1 := by
    intro x hx
    have ht1Right :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t1? = some C.t1 := by
      exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
        (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) (hx.2.1)
        (fun i hi => hx.2.2 i hi)
    have hrunRight' :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).run? ≠ none :=
      RawProcedureOutput.run_ne_none_of_t1_some
        (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) ht1Right
    rcases (P.output ℓ ⟨x, hsRight_subset hx⟩).exists_run_of_ne_none I hrunRight' with
      ⟨Cx, hCx⟩
    have hphaseCx :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t1? = some Cx.t1 := by
      simpa [(P.output ℓ ⟨x, hsRight_subset hx⟩).run_phaseTwo hCx] using Cx.t1_spec
    have ht1Cx : Cx.t1 = C.t1 := by
      exact Option.some.inj (by rw [← hphaseCx, ht1Right])
    exact ⟨Cx, hCx, ht1Cx⟩
  have hEqLeftPath :
      Set.EqOn
        (P.value ℓ)
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        sLeft :=
    P.eqOn_value_sectionR0FullModel_of_localT1Runs hγ hγhi hsLeft_subset hrunLeft
  have hEqRightPath :
      Set.EqOn
        (P.value ℓ)
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        sRight :=
    P.eqOn_value_sectionR0FullModel_of_localT1Runs hγ hγhi hsRight_subset hrunRight
  have hEqLeft :
      Set.EqOn Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        sLeft := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using! hEqLeftPath hx
  have hEqRight :
      Set.EqOn Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        sRight := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using! hEqRightPath hx
  have hcontLeft :
      ContinuousOn
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        sLeft :=
    P.continuousOn_sectionR0FullModel_of_localT1Runs hγ hγhi hsLeft_subset hrunLeft
  have hcontRight :
      ContinuousOn
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        sRight :=
    P.continuousOn_sectionR0FullModel_of_localT1Runs hγ hγhi hsRight_subset hrunRight
  have hlamLeftMem : lam ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam := by
    exact ⟨hlam, by simp⟩
  have hlamRightMem : lam ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam := by
    exact ⟨hlam, by simp⟩
  have hlamLeft : lam ∈ sLeft := mem_of_mem_nhdsWithin hlamLeftMem hsLeft
  have hlamRight : lam ∈ sRight := mem_of_mem_nhdsWithin hlamRightMem hsRight
  have hleftModel :
      ContinuousWithinAt
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam := by
    exact (hcontLeft lam hlamLeft).mono_of_mem_nhdsWithin hsLeft
  have hrightModel :
      ContinuousWithinAt
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam := by
    exact (hcontRight lam hlamRight).mono_of_mem_nhdsWithin hsRight
  have hEqLEventually :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam)]
        Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ) :=
    Filter.mem_of_superset hsLeft hEqLeft
  have hEqREventually :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam)]
        Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ) :=
    Filter.mem_of_superset hsRight hEqRight
  have hleft :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) lam :=
    hleftModel.congr_of_eventuallyEq_of_mem hEqLEventually hlamLeftMem
  have hright :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam :=
    hrightModel.congr_of_eventuallyEq_of_mem hEqREventually hlamRightMem
  have hcont :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
    exact Q.continuousWithinAt_interval_of_left_right hleft hright
  simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
    SectionRawOutputChoice.value] using! hcont

theorem canonicalPath_continuousWithinAt_case1_2_b_i_of_run_some_leftJump
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (h0lt : 0 < lam)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (_hrun :
      ((canonicalPath I (le_of_lt hγ) hγhi).output ℓ ⟨lam, hlam⟩).run? = some C)
    {k : Idx n}
    {hne : (Advice.belowThresholdNononeSet I ℓ C.t1 lam).Nonempty}
    (hk : (Advice.belowThresholdNononeSet I ℓ C.t1 lam).max' hne = k)
    (hleftJump :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam),
        Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x < I.program.barTau) :
    ContinuousWithinAt
      ((canonicalPath I (le_of_lt hγ) hγhi).value ℓ)
      (Set.Icc (0 : ℝ) 1)
      lam := by
  let P : SectionRawOutputPath n I := canonicalPath I (le_of_lt hγ) hγhi
  let Q := P.sectionChoice ℓ
  have hk_mem : k ∈ Advice.belowThresholdNononeSet I ℓ C.t1 lam := by
    rw [← hk]
    exact Finset.max'_mem _ _
  have hkt1 : k < C.t1 :=
    (Advice.mem_belowThresholdNononeSet_iff (I := I)).1 hk_mem |>.1
  have hbarAtT1 :
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam := by
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1] using C.t1_beforeBudget_ge_barTau
  have hbarAtT1_le :
      Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam ≤ I.program.barTau := by
    by_contra hgt
    have hpre :
        {x | I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x} ∈
          nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
      have hcont :
          ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam :=
        (Advice.continuous_sectionPhaseTwoBudgetValue I ℓ C.t1).continuousWithinAt
      simpa only [Set.preimage, Set.mem_ofPred_eq] using!
        hcont.preimage_mem_nhdsWithin (Ioi_mem_nhds (lt_of_not_ge hgt))
    have hEmpty :
        (∅ : Set ℝ) ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
      refine Filter.mem_of_superset (Filter.inter_mem hpre hleftJump) ?_
      intro x hx
      rcases hx with ⟨hxgt, hxlt⟩
      have hxgt' : I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x := by
        simpa using hxgt
      have hxlt' : Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x < I.program.barTau := by
        simpa using hxlt
      linarith
    have hIco :
        Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam = Set.Ico (0 : ℝ) lam := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
      · intro hx
        exact ⟨⟨hx.1, le_trans (le_of_lt hx.2) hlam.2⟩, hx.2⟩
    have hNeBot :
        Filter.NeBot (nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam)) := by
      simpa [hIco] using
        (right_nhdsWithin_Ico_neBot h0lt :
          Filter.NeBot (nhdsWithin lam (Set.Ico (0 : ℝ) lam)))
    exact hNeBot.ne (Filter.empty_mem_iff_bot.mp hEmpty)
  have hbarEq :
      Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam = I.program.barTau :=
    le_antisymm hbarAtT1_le hbarAtT1
  have ht1ℓ : C.t1 ≤ ℓ := by
    by_contra ht1gt
    have hzero :
        Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam = 0 :=
      Advice.sectionPhaseTwoHatG2Value_eq_zero_of_frontier_lt
        (I := I) (lt_of_not_ge ht1gt)
    exact ne_of_gt
        (C.sectionPhaseTwoHatG2Value_pos_at_t1_of_sectionAdvice_of_le_153_div_125
          (le_of_lt hγ) hγhi) hzero
  have hbarLeft :
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ k lam := by
    have hpred :
        Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam <
          Advice.sectionPhaseTwoBudgetValue I ℓ k lam :=
      Advice.sectionPhaseTwoBudgetValue_lt_at_predecessor_of_max_belowThresholdNononeSet
        (I := I) hγ hlam.1 hk hkt1
    linarith
  let leftRest : Set ℝ := {x |
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ k x ∧
      Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x < I.program.barTau}
  let sLeft : Set ℝ := (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) ∩ leftRest
  have hleftBarEvt :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam),
        I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ k x := by
    have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ k).continuousWithinAt
      : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ k x)
          (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam).preimage_mem_nhdsWithin
            (Ioi_mem_nhds hbarLeft)
    filter_upwards [hpre] with x hx
    simpa using hx
  have hleftRest :
      leftRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
    have hs_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam), x ∈ leftRest := by
      exact (hleftBarEvt.and hleftJump).mono (fun x hx => by
        rcases hx with ⟨hxbar, hxsmall⟩
        exact ⟨hxbar, hxsmall⟩)
    simpa only [Filter.Eventually] using! hs_evt
  have hsLeft :
      sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
    simpa [sLeft] using Filter.inter_mem self_mem_nhdsWithin hleftRest
  have hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  let rightRest : Set ℝ := {x |
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x ∧
      (∀ i : Idx n, C.t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau)}
  let sRight : Set ℝ := (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) ∩ rightRest
  have hrightBarAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          C.t1 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
    intro i
    by_cases hi : C.t1 < i
    · have hlt : Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau := by
        have hlt' : C.phaseTwo.beforeBudget i < I.program.barTau :=
          C.phaseTwo_beforeBudget_lt_barTau_above_t1 hi
        simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
          (Ξ := C.phaseTwo) i] using hlt'
      have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds hlt)
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hrightRest :
      rightRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    have hbarGeEvt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hmono :
          Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam ≤
          Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x :=
        Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
          (I := I) (le_of_lt hγ) ℓ C.t1 hlam.1 hx.2
      exact le_trans hbarAtT1 hmono
    have hs_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam), x ∈ rightRest := by
      exact
        (hbarGeEvt.and (Filter.eventually_all.2 hrightBarAboveEach)).mono
          (fun x hx => by
            rcases hx with ⟨hxbar, hxbarAbove⟩
            exact ⟨hxbar, hxbarAbove⟩)
    simpa only [Filter.Eventually] using! hs_evt
  have hsRight :
      sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    simpa [sRight] using Filter.inter_mem self_mem_nhdsWithin hrightRest
  have hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  have hrunLeft :
      ∀ x (hx : x ∈ sLeft),
        ∃ Cx : ProcedureRun I (Advice.sectionAdvice I ℓ x
          ⟨(hsLeft_subset hx).1, (hsLeft_subset hx).2⟩),
          (P.output ℓ ⟨x, hsLeft_subset hx⟩).run? = some Cx ∧
            Cx.t1 = k := by
    intro x hx
    have ht1Left :
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).phaseTwo.t1? = some k := by
      exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
        (I := I) (O := P.output ℓ ⟨x, hsLeft_subset hx⟩) (le_of_lt hx.2.1)
        (fun i hi => by
          have hxi : x < lam := hx.1.2
          by_cases hi_le : i ≤ C.t1
          · rw [Advice.sectionPhaseTwoBudgetValue_eq_of_between_max_belowThresholdNononeSet_of_left
              (I := I) (t1 := C.t1) (k := k) (i := i) hk (le_of_lt hxi) hi hi_le]
            exact hx.2.2
          · have hi_gt : C.t1 < i := lt_of_not_ge hi_le
            have hmono :
                Advice.sectionPhaseTwoBudgetValue I ℓ i x ≤
                  Advice.sectionPhaseTwoBudgetValue I ℓ i lam :=
              Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
                (I := I) (le_of_lt hγ) ℓ i hx.1.1.1 (le_of_lt hxi)
            have hlt : Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau := by
              have hlt' : C.phaseTwo.beforeBudget i < I.program.barTau :=
                C.phaseTwo_beforeBudget_lt_barTau_above_t1 hi_gt
              simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
                (Ξ := C.phaseTwo) i] using hlt'
            linarith)
    have hrunLeft' :
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).run? ≠ none :=
      RawProcedureOutput.run_ne_none_of_t1_some
        (I := I) (O := P.output ℓ ⟨x, hsLeft_subset hx⟩) ht1Left
    rcases (P.output ℓ ⟨x, hsLeft_subset hx⟩).exists_run_of_ne_none I hrunLeft' with
      ⟨Cx, hCx⟩
    have hphaseCx :
        (P.output ℓ ⟨x, hsLeft_subset hx⟩).phaseTwo.t1? = some Cx.t1 := by
      simpa [(P.output ℓ ⟨x, hsLeft_subset hx⟩).run_phaseTwo hCx] using Cx.t1_spec
    have ht1Cx : Cx.t1 = k := by
      exact Option.some.inj (by rw [← hphaseCx, ht1Left])
    exact ⟨Cx, hCx, ht1Cx⟩
  have hrunRight :
      ∀ x (hx : x ∈ sRight),
        ∃ Cx : ProcedureRun I (Advice.sectionAdvice I ℓ x
          ⟨(hsRight_subset hx).1, (hsRight_subset hx).2⟩),
          (P.output ℓ ⟨x, hsRight_subset hx⟩).run? = some Cx ∧
            Cx.t1 = C.t1 := by
    intro x hx
    have ht1Right :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t1? = some C.t1 := by
      exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
        (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) (hx.2.1)
        (fun i hi => hx.2.2 i hi)
    have hrunRight' :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).run? ≠ none :=
      RawProcedureOutput.run_ne_none_of_t1_some
        (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) ht1Right
    rcases (P.output ℓ ⟨x, hsRight_subset hx⟩).exists_run_of_ne_none I hrunRight' with
      ⟨Cx, hCx⟩
    have hphaseCx :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t1? = some Cx.t1 := by
      simpa [(P.output ℓ ⟨x, hsRight_subset hx⟩).run_phaseTwo hCx] using Cx.t1_spec
    have ht1Cx : Cx.t1 = C.t1 := by
      exact Option.some.inj (by rw [← hphaseCx, ht1Right])
    exact ⟨Cx, hCx, ht1Cx⟩
  have hEqLeftPath :
      Set.EqOn (P.value ℓ)
        (Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZFullValue I ℓ))
        sLeft :=
    P.eqOn_value_sectionR0FullModel_of_localT1Runs hγ hγhi hsLeft_subset hrunLeft
  have hEqRightPath :
      Set.EqOn (P.value ℓ)
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        sRight :=
    P.eqOn_value_sectionR0FullModel_of_localT1Runs hγ hγhi hsRight_subset hrunRight
  have hEqLeft :
      Set.EqOn Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZFullValue I ℓ))
        sLeft := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using! hEqLeftPath hx
  have hEqRight :
      Set.EqOn Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        sRight := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using! hEqRightPath hx
  have hzEq :
      Advice.sectionZValue I ℓ C.t2 lam = Advice.sectionZFullValue I ℓ lam := by
    rw [← C.z_eq_sectionZValue_of_sectionAdvice,
      C.z_eq_sectionZFullValue_of_sectionAdvice hγ]
  have hGlue :
      Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZFullValue I ℓ) lam =
        Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ) lam := by
    open Advice in
    calc
      Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZFullValue I ℓ) lam
          =
            Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZValue I ℓ C.t2) lam := by
              simp [Advice.sectionR0ValueAtThreshold, Advice.sectionBoundaryBudgetValue,
                Advice.sectionPhase1PrefixValue, Advice.sectionBoundaryHatGAValue,
                Advice.sectionPhase1HatGValue, Advice.sectionPhiValue, hzEq]
      _ =
            Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2) lam := by
              exact
                sectionR0ValueAtThreshold_eq_of_budget_eq_barTau_of_max_belowThresholdNononeSet
                  (I := I)
                  ht1ℓ hk hkt1 hbarEq
                  (ne_of_gt
                    (C.sectionPhaseTwoHatG2Value_pos_at_t1_of_sectionAdvice_of_le_153_div_125
                      (le_of_lt hγ) hγhi))
      _ =
            Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ) lam := by
              simp [Advice.sectionR0ValueAtThreshold, Advice.sectionBoundaryBudgetValue,
                Advice.sectionPhase1PrefixValue, Advice.sectionBoundaryHatGAValue,
                Advice.sectionPhase1HatGValue, Advice.sectionPhiValue, hzEq]
  have hlamRight : lam ∈ sRight := by
    have hmem : lam ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam := by
      exact ⟨hlam, by simp⟩
    exact mem_of_mem_nhdsWithin hmem hsRight
  have hEqAtLeft :
      Q.value lam =
        Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZFullValue I ℓ) lam := by
    calc
      Q.value lam =
          Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ) lam :=
        hEqRight hlamRight
      _ = Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZFullValue I ℓ) lam :=
        hGlue.symm
  have hknotlast : k ≠ lastIdx n := (lt_of_lt_of_le hkt1 (le_lastIdx C.t1)).ne
  have hhatPosMinus : 0 < Advice.sectionPhaseTwoHatG2Value I ℓ k lam := by
    have hpred :
        Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam <
          Advice.sectionPhaseTwoBudgetValue I ℓ k lam :=
      Advice.sectionPhaseTwoBudgetValue_lt_at_predecessor_of_max_belowThresholdNononeSet
        (I := I) hγ hlam.1 hk hkt1
    have hafterEq :
        Advice.sectionPhaseTwoAfterBudgetValue I ℓ k lam =
          Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam :=
      Advice.sectionPhaseTwoAfterBudgetValue_eq_budget_of_between_max_belowThresholdNononeSet
        (I := I) hk hkt1
    have hhatEq :
        Advice.sectionPhaseTwoHatG2Value I ℓ k lam =
          Advice.sectionPhaseTwoBudgetValue I ℓ k lam -
            Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam := by
      rw [Advice.sectionPhaseTwoHatG2Value, hafterEq]
    linarith
  let phiMinus : ℝ → ℝ := fun x =>
    futureCount k +
      Advice.sectionBoundaryAlphaValue I ℓ k x *
          (1 - Advice.sectionMuDValue I ℓ k x) -
        I.program.frac * Advice.sectionZFullValue I ℓ x
  have hphiPosMinus : 0 < phiMinus lam := by
    have hpos :
        0 <
          futureCount k +
            Advice.sectionBoundaryAlphaValue I ℓ k lam *
                (1 - Advice.sectionMuDValue I ℓ k lam) -
              I.program.frac * Advice.sectionZValue I ℓ C.t2 lam := by
      exact
        Advice.sectionBoundaryPhiDenom_pos_of_budget_eq_barTau_of_max_belowThresholdNononeSet
          (I := I) hγ hlam.1 hk hkt1 C.t1_le_t2 hbarEq
    simpa [phiMinus, hzEq] using hpos
  have hhatEvtMinus :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam),
        0 < Advice.sectionPhaseTwoHatG2Value I ℓ k x := by
    have hpre := ((Advice.continuous_sectionPhaseTwoHatG2Value I ℓ k).continuousWithinAt
      : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoHatG2Value I ℓ k x)
          (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam).preimage_mem_nhdsWithin
            (Ioi_mem_nhds hhatPosMinus)
    simpa only [Set.preimage, Set.mem_ofPred_eq] using! hpre
  have hAlphaContMinus :
      ContinuousWithinAt (fun x => Advice.sectionBoundaryAlphaValue I ℓ k x)
        (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam := by
    have hnumCont :
        ContinuousWithinAt
          (fun x => I.program.barTau - Advice.sectionPhaseTwoAfterBudgetValue I ℓ k x)
          (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam :=
      (continuousWithinAt_const.sub
        (Advice.continuous_sectionPhaseTwoAfterBudgetValue I ℓ k).continuousWithinAt)
    simpa [Advice.sectionBoundaryAlphaValue, hknotlast, dite_false] using!
      (hnumCont.div
        (Advice.continuous_sectionPhaseTwoHatG2Value I ℓ k).continuousWithinAt
        (ne_of_gt hhatPosMinus))
  have hphiContMinus :
      ContinuousWithinAt phiMinus (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam := by
    dsimp [phiMinus]
    exact
      (continuousWithinAt_const.add
        (hAlphaContMinus.mul
          (continuousWithinAt_const.sub
            (Advice.continuous_sectionMuDValue I ℓ k).continuousWithinAt))).sub
        (continuousWithinAt_const.mul
          (Advice.continuous_sectionZFullValue I ℓ).continuousWithinAt)
  have hphiEvtMinus :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam), 0 < phiMinus x := by
    have hpre := hphiContMinus.preimage_mem_nhdsWithin (Ioi_mem_nhds hphiPosMinus)
    simpa only [Set.preimage, Set.mem_ofPred_eq] using! hpre
  let leftModelRest : Set ℝ := {x |
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ k x ∧
        0 < Advice.sectionPhaseTwoHatG2Value I ℓ k x ∧ 0 < phiMinus x}
  have hleftModelRest :
      leftModelRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
    have hs_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam), x ∈ leftModelRest := by
      exact (hleftBarEvt.and (hhatEvtMinus.and hphiEvtMinus)).mono (fun x hx => by
        rcases hx with ⟨hbar, hhat, hphi⟩
        exact ⟨hbar, hhat, hphi⟩)
    simpa only [Filter.Eventually] using! hs_evt
  have hsIccLeft :
      (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) ∈
        nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro x hx
    show x ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam
    constructor
    · exact hx.1
    · exact le_of_lt (show x < lam from hx.2)
  let sLeftModel : Set ℝ := (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) ∩ leftModelRest
  have hsLeftModel :
      sLeftModel ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
    simpa [sLeftModel] using Filter.inter_mem hsIccLeft hleftModelRest
  have hleftModelMem : lam ∈ sLeftModel := by
    change lam ∈ (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) ∩ leftModelRest
    constructor
    · constructor
      · exact hlam
      · change lam ≤ lam
        exact le_rfl
    · exact ⟨hbarLeft, hhatPosMinus, hphiPosMinus⟩
  have hcontLeft :
      ContinuousOn
        (Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZFullValue I ℓ))
        sLeftModel := by
    refine Advice.continuousOn_sectionR0ValueAtThreshold I ℓ k
        (Advice.sectionZFullValue I ℓ)
        (Advice.continuous_sectionZFullValue I ℓ).continuousOn ?_ ?_ ?_
    · intro x hx
      exact ne_of_gt hx.2.2.1
    · intro x hx
      exact ne_of_gt hx.2.2.2
    · intro i hi x hx
      exact ne_of_gt <|
        Advice.sectionPhase1DenomFull_pos_of_barTau_lt
          (I := I) hγ hγhi ℓ k hx.1.1 hi
          hx.2.1
  have hcontRight :
      ContinuousOn
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        sRight :=
    P.continuousOn_sectionR0FullModel_of_localT1Runs hγ hγhi hsRight_subset hrunRight
  have hlamLeftMem : lam ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam := by
    exact ⟨hlam, by simp⟩
  have hlamRightMem : lam ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam := by
    exact ⟨hlam, by simp⟩
  have hrightMem : lam ∈ sRight := mem_of_mem_nhdsWithin hlamRightMem hsRight
  have hleftModel :
      ContinuousWithinAt
        (Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZFullValue I ℓ))
        (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam := by
    exact (hcontLeft lam hleftModelMem).mono_of_mem_nhdsWithin hsLeftModel
  have hrightModel :
      ContinuousWithinAt
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ))
        (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam := by
    exact (hcontRight lam hrightMem).mono_of_mem_nhdsWithin hsRight
  have hEqLEventually :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam)]
        Advice.sectionR0ValueAtThreshold I ℓ k (Advice.sectionZFullValue I ℓ) :=
    Filter.mem_of_superset hsLeft hEqLeft
  have hEqREventually :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam)]
        Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZFullValue I ℓ) :=
    Filter.mem_of_superset hsRight hEqRight
  have hleft :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam :=
    hleftModel.congr_of_eventuallyEq hEqLEventually hEqAtLeft
  have hright :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam :=
    hrightModel.congr_of_eventuallyEq_of_mem hEqREventually hlamRightMem
  have hcont :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
    exact Q.continuousWithinAt_interval_of_left'_right hleft hright
  simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
    SectionRawOutputChoice.value] using! hcont

theorem canonicalPath_continuousWithinAt_case1_2_b_ii_of_run_some_leftJump_empty
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (h0lt : 0 < lam)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (_hrun :
      ((canonicalPath I (le_of_lt hγ) hγhi).output ℓ ⟨lam, hlam⟩).run? = some C)
    (hbelowEmpty : Advice.belowThresholdNononeSet I ℓ C.t1 lam = ∅)
    (hleftJump :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam),
        Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x < I.program.barTau) :
    ContinuousWithinAt
      ((canonicalPath I (le_of_lt hγ) hγhi).value ℓ)
      (Set.Icc (0 : ℝ) 1)
      lam := by
  let P : SectionRawOutputPath n I := canonicalPath I (le_of_lt hγ) hγhi
  let Q := P.sectionChoice ℓ
  have hbarAtT1 :
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam := by
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1] using C.t1_beforeBudget_ge_barTau
  have hbarAtT1_le :
      Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam ≤ I.program.barTau := by
    by_contra hgt
    have hpre :
        {x | I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x} ∈
          nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
      have hcont :
          ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam :=
        (Advice.continuous_sectionPhaseTwoBudgetValue I ℓ C.t1).continuousWithinAt
      simpa only [Set.preimage, Set.mem_ofPred_eq] using!
        hcont.preimage_mem_nhdsWithin (Ioi_mem_nhds (lt_of_not_ge hgt))
    have hEmpty :
        (∅ : Set ℝ) ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
      refine Filter.mem_of_superset (Filter.inter_mem hpre hleftJump) ?_
      intro x hx
      rcases hx with ⟨hxgt, hxlt⟩
      have hxgt' : I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x := by
        simpa using hxgt
      have hxlt' : Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x < I.program.barTau := by
        simpa using hxlt
      linarith
    have hIco :
        Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam = Set.Ico (0 : ℝ) lam := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
      · intro hx
        exact ⟨⟨hx.1, le_trans (le_of_lt hx.2) hlam.2⟩, hx.2⟩
    have hNeBot :
        Filter.NeBot (nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam)) := by
      simpa [hIco] using
        (right_nhdsWithin_Ico_neBot h0lt :
          Filter.NeBot (nhdsWithin lam (Set.Ico (0 : ℝ) lam)))
    exact hNeBot.ne (Filter.empty_mem_iff_bot.mp hEmpty)
  have hbarEq :
      Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam = I.program.barTau :=
    le_antisymm hbarAtT1_le hbarAtT1
  have ht1ℓ : C.t1 ≤ ℓ := by
    by_contra ht1gt
    have hzero :
        Advice.sectionPhaseTwoHatG2Value I ℓ C.t1 lam = 0 :=
      Advice.sectionPhaseTwoHatG2Value_eq_zero_of_frontier_lt
        (I := I) (lt_of_not_ge ht1gt)
    exact ne_of_gt
        (C.sectionPhaseTwoHatG2Value_pos_at_t1_of_sectionAdvice_of_le_153_div_125
          (le_of_lt hγ) hγhi) hzero
  let sLeft : Set ℝ :=
    (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) ∩
      {x | Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x < I.program.barTau}
  have hsLeftRest :
      {x | Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x < I.program.barTau} ∈
        nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
    simpa only [Filter.Eventually] using hleftJump
  have hsLeft :
      sLeft ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) := by
    simpa [sLeft] using Filter.inter_mem self_mem_nhdsWithin hsLeftRest
  have hsLeft_subset : sLeft ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  have hsmallLeft :
      ∀ x, x ∈ sLeft →
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x < I.program.barTau := by
    intro x hx
    have hxi : x ≤ lam := le_of_lt hx.1.2
    have hEq :
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) x =
          Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x := by
      exact Advice.sectionPhaseTwoBudgetValue_eq_of_muD_eq_one_on_halfOpen
        (I := I) (ℓ := ℓ) (a := firstIdx n) (b := C.t1) (lam := x) (firstIdx_le C.t1)
        (fun j hj1 hj2 => by
          have hjnot : j ∉ Advice.belowThresholdNononeSet I ℓ C.t1 lam := by
            simp [hbelowEmpty]
          have hμlam : Advice.sectionMuDValue I ℓ j lam = 1 :=
            Advice.sectionMuDValue_eq_one_of_not_mem_belowThresholdNononeSet
              (I := I) hj2 hjnot
          exact Advice.sectionMuDValue_eq_one_of_eq_one_of_left I hxi hμlam)
    rw [hEq]
    exact hx.2
  let rightRest : Set ℝ := {x |
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x ∧
      (∀ i : Idx n, C.t1 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau) ∧
      I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t2 x ∧
      (∀ i : Idx n, C.t2 < i →
        Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta)}
  let sRight : Set ℝ := (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) ∩ rightRest
  have hrightBarAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          C.t1 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.barTau := by
    intro i
    by_cases hi : C.t1 < i
    · have hlt : Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.barTau := by
        have hlt' : C.phaseTwo.beforeBudget i < I.program.barTau :=
          C.phaseTwo_beforeBudget_lt_barTau_above_t1 hi
        simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
          (Ξ := C.phaseTwo) i] using hlt'
      have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds hlt)
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hrightThetaAboveEach :
      ∀ i : Idx n,
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          C.t2 < i →
            Advice.sectionPhaseTwoBudgetValue I ℓ i x < I.program.theta := by
    intro i
    by_cases hi : C.t2 < i
    · have hlt : Advice.sectionPhaseTwoBudgetValue I ℓ i lam < I.program.theta := by
        have hlt' : C.phaseTwo.beforeBudget i < I.program.theta :=
          C.phaseTwo_beforeBudget_lt_theta_above_t2 hi
        simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
          (Ξ := C.phaseTwo) i] using hlt'
      have hpre := ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ i).continuousWithinAt
        : ContinuousWithinAt (fun x => Advice.sectionPhaseTwoBudgetValue I ℓ i x)
            (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam).preimage_mem_nhdsWithin
              (Iio_mem_nhds hlt)
      filter_upwards [hpre] with x hx hix
      exact hx
    · exact Filter.Eventually.of_forall fun _ hix => False.elim (hi hix)
  have hbarAtT1 :
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam := by
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t1] using C.t1_beforeBudget_ge_barTau
  have hthetaAtT2 :
      I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t2 lam := by
    simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
      (Ξ := C.phaseTwo) C.t2] using C.t2_beforeBudget_ge_theta
  have hrightRest :
      rightRest ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    have hbarGeEvt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hmono :
          Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam ≤
            Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x :=
        Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
          (I := I) (le_of_lt hγ) ℓ C.t1 hlam.1 hx.2
      exact le_trans hbarAtT1 hmono
    have hthetaGeEvt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam),
          I.program.theta ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t2 x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hmono :
          Advice.sectionPhaseTwoBudgetValue I ℓ C.t2 lam ≤
            Advice.sectionPhaseTwoBudgetValue I ℓ C.t2 x :=
        Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
          (I := I) (le_of_lt hγ) ℓ C.t2 hlam.1 hx.2
      exact le_trans hthetaAtT2 hmono
    have hs_evt :
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam), x ∈ rightRest := by
      exact
        (hbarGeEvt.and
          ((Filter.eventually_all.2 hrightBarAboveEach).and
            (hthetaGeEvt.and (Filter.eventually_all.2 hrightThetaAboveEach)))).mono
          (fun x hx => by
            rcases hx with ⟨hxbar, hxbarAbove, hxtheta, hxthetaAbove⟩
            exact ⟨hxbar, hxbarAbove, hxtheta, hxthetaAbove⟩)
    simpa only [Filter.Eventually] using! hs_evt
  have hsRight :
      sRight ∈ nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) := by
    simpa [sRight] using Filter.inter_mem self_mem_nhdsWithin hrightRest
  have hsRight_subset : sRight ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact hx.1.1
  have hrunRight :
      ∀ x (hx : x ∈ sRight),
        ∃ Cx : ProcedureRun I (Advice.sectionAdvice I ℓ x
          ⟨(hsRight_subset hx).1, (hsRight_subset hx).2⟩),
          (P.output ℓ ⟨x, hsRight_subset hx⟩).run? = some Cx ∧
            Cx.t1 = C.t1 ∧ Cx.t2 = C.t2 := by
    intro x hx
    have ht1Right :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t1? = some C.t1 := by
      exact RawProcedureOutput.t1?_eq_some_of_sectionBudget_ge_barTau_of_above_lt_barTau
        (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) (hx.2.1)
        (fun i hi => hx.2.2.1 i hi)
    have ht2Right :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).phaseTwo.t2? = some C.t2 := by
      exact RawProcedureOutput.t2?_eq_some_of_sectionBudget_ge_theta_of_above_lt_theta
        (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) (hx.2.2.2.1)
        (fun i hi => hx.2.2.2.2 i hi)
    have hrunRight' :
        (P.output ℓ ⟨x, hsRight_subset hx⟩).run? ≠ none :=
      RawProcedureOutput.run_ne_none_of_t1_some
        (I := I) (O := P.output ℓ ⟨x, hsRight_subset hx⟩) ht1Right
    exact (P.output ℓ ⟨x, hsRight_subset hx⟩).exists_run_eq_thresholds_of_phaseTwo
      I ht1Right ht2Right hrunRight'
  have hEqLeftPath :
      Set.EqOn (P.value ℓ)
        (Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n))
        sLeft := by
    exact P.eqOn_value_sectionPhaseTwoBudget_of_total_lt_barTau
      (hγlo := le_of_lt hγ) hsLeft_subset hsmallLeft
  have hEqRightPath :
      Set.EqOn (P.value ℓ)
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2))
        sRight :=
    P.eqOn_value_sectionR0Model_of_localThresholdRuns
      (hγlo := le_of_lt hγ) (hγhi := hγhi) hsRight_subset hrunRight
  have hEqLeft :
      Set.EqOn Q.value
        (Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n))
        sLeft := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using! hEqLeftPath hx
  have hEqRight :
      Set.EqOn Q.value
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2))
        sRight := by
    intro x hx
    simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
      SectionRawOutputChoice.value] using! hEqRightPath hx
  have hGlue :
      Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam =
        Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2) lam := by
    have htmp :
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam =
          Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2) lam := by
      exact
        (open Advice in
          sectionPhaseTwoBudgetValue_eq_sectionR0_empty
            (I := I) ht1ℓ hbelowEmpty hbarEq
            (ne_of_gt
              (C.sectionPhaseTwoHatG2Value_pos_at_t1_of_sectionAdvice_of_le_153_div_125
                (le_of_lt hγ) hγhi)))
    exact htmp
  have hlamRight : lam ∈ sRight := by
    have hmem : lam ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam := by
      exact ⟨hlam, by simp⟩
    exact mem_of_mem_nhdsWithin hmem hsRight
  have hEqAtLeft :
      Q.value lam = Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam := by
    calc
      Q.value lam =
          Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2) lam :=
        hEqRight hlamRight
      _ = Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam := hGlue.symm
  have hcontRight :
      ContinuousOn
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2))
        sRight :=
    P.continuousOn_sectionR0Model_of_localThresholdRuns hγ hγhi hsRight_subset hrunRight
  have hlamRightMem : lam ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam := by
    exact ⟨hlam, by simp⟩
  have hrightMem : lam ∈ sRight := mem_of_mem_nhdsWithin hlamRightMem hsRight
  have hleftModel :
      ContinuousWithinAt
        (Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n))
        (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam := by
    exact
      ((Advice.continuous_sectionPhaseTwoBudgetValue I ℓ (firstIdx n)).continuousOn lam hlam).mono
        (by intro x hx; exact hx.1)
  have hrightModel :
      ContinuousWithinAt
        (Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2))
        (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam := by
    exact (hcontRight lam hrightMem).mono_of_mem_nhdsWithin hsRight
  have hEqLEventually :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam)]
        Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) :=
    Filter.mem_of_superset hsLeft hEqLeft
  have hEqREventually :
      Q.value =ᶠ[nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam)]
        Advice.sectionR0ValueAtThreshold I ℓ C.t1 (Advice.sectionZValue I ℓ C.t2) :=
    Filter.mem_of_superset hsRight hEqRight
  have hleft :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam) lam :=
    hleftModel.congr_of_eventuallyEq hEqLEventually hEqAtLeft
  have hright :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1 ∩ Set.Ici lam) lam :=
    hrightModel.congr_of_eventuallyEq_of_mem hEqREventually hlamRightMem
  have hcont :
      ContinuousWithinAt Q.value (Set.Icc (0 : ℝ) 1) lam := by
    exact Q.continuousWithinAt_interval_of_left'_right hleft hright
  simpa [SectionRawOutputPath.value, SectionRawOutputPath.sectionChoice,
    SectionRawOutputChoice.value] using! hcont

theorem sectionPhaseTwoBudgetValue_leftStable_or_leftJump_of_eq_barTau
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    {ℓ t1 : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hbarEq :
      Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam = I.program.barTau) :
    (∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
      I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x)
    ∨
    (0 < lam ∧
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam),
        Advice.sectionPhaseTwoBudgetValue I ℓ t1 x < I.program.barTau) := by
  classical
  by_cases hstable :
      ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x
  · exact Or.inl hstable
  · refine Or.inr ?_
    have h0lt : 0 < lam := by
      by_contra h0
      have hlam0 : lam = 0 := by linarith [hlam.1]
      have hstable0 :
          ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
            I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 x := by
        refine Filter.mem_of_superset self_mem_nhdsWithin ?_
        intro x hx
        have hxle0 : x ≤ 0 := by simpa [hlam0] using hx.2
        have hxge0 : 0 ≤ x := hx.1.1
        have hx0 : x = 0 := le_antisymm hxle0 hxge0
        have hxlam : x = lam := by simpa [hlam0] using hx0
        simpa [hxlam] using (le_of_eq hbarEq.symm)
      exact hstable hstable0
    refine ⟨h0lt, ?_⟩
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro x hx
    have hmono : Advice.sectionPhaseTwoBudgetValue I ℓ t1 x ≤
        Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam :=
      Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
        (I := I) hγlo ℓ t1 hx.1.1 (le_of_lt hx.2)
    have hle : Advice.sectionPhaseTwoBudgetValue I ℓ t1 x ≤ I.program.barTau := by
      simpa [hbarEq] using hmono
    have hne : Advice.sectionPhaseTwoBudgetValue I ℓ t1 x ≠ I.program.barTau := by
      intro hxeq
      have hstablex :
          ∀ᶠ y in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam),
            I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 y := by
        have hIoi :
            Set.Ioi x ∈ nhds lam := Ioi_mem_nhds hx.2
        have hbase :
            (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) ∩ Set.Ioi x ∈
              nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam) :=
          inter_mem_nhdsWithin _ hIoi
        refine Filter.mem_of_superset hbase ?_
        intro y hy
        have hyx : x < y := hy.2
        have hy_mem : y ∈ Set.Icc (0 : ℝ) 1 ∩ Set.Iic lam := hy.1
        have hx_le_y :
            Advice.sectionPhaseTwoBudgetValue I ℓ t1 x ≤
              Advice.sectionPhaseTwoBudgetValue I ℓ t1 y :=
          Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
            (I := I) hγlo ℓ t1 hx.1.1 (le_of_lt hyx)
        have hy_le_lam :
            Advice.sectionPhaseTwoBudgetValue I ℓ t1 y ≤
              Advice.sectionPhaseTwoBudgetValue I ℓ t1 lam :=
          Advice.sectionPhaseTwoBudgetValue_monotone_in_lam
            (I := I) hγlo ℓ t1 hy_mem.1.1 hy_mem.2
        have hy_eq : Advice.sectionPhaseTwoBudgetValue I ℓ t1 y = I.program.barTau := by
          have hy_ge : I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ t1 y := by
            simpa [hxeq] using hx_le_y
          have hy_le : Advice.sectionPhaseTwoBudgetValue I ℓ t1 y ≤ I.program.barTau := by
            simpa [hbarEq] using hy_le_lam
          exact le_antisymm hy_le hy_ge
        simp [hy_eq]
      exact hstable hstablex
    exact lt_of_le_of_ne hle hne

theorem canonicalPath_continuousWithinAt_of_run_some_theta_strict_cases
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (hrun :
      ((canonicalPath I (le_of_lt hγ) hγhi).output ℓ ⟨lam, hlam⟩).run? = some C)
    (hpred :
      Advice.belowThresholdNononeSet I ℓ C.t1 lam = ∅
      ∨
      ∃ k, ∃ hne : (Advice.belowThresholdNononeSet I ℓ C.t1 lam).Nonempty,
        (Advice.belowThresholdNononeSet I ℓ C.t1 lam).max' hne = k) :
    ContinuousWithinAt
      ((canonicalPath I (le_of_lt hγ) hγhi).value ℓ)
      (Set.Icc (0 : ℝ) 1)
      lam := by
  by_cases hstrict :
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam
  · exact canonicalPath_continuousWithinAt_of_run_some_strict
      (I := I) hγ hγhi hlam hrun hstrict
  · have hbarAtT1 :
        I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam := by
      simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
        (Ξ := C.phaseTwo) C.t1] using C.t1_beforeBudget_ge_barTau
    have hbarEq :
        Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam = I.program.barTau :=
      le_antisymm (le_of_not_gt hstrict) hbarAtT1
    rcases sectionPhaseTwoBudgetValue_leftStable_or_leftJump_of_eq_barTau
        (I := I) (le_of_lt hγ) hlam hbarEq with hstable | ⟨h0lt, hleftJump⟩
    · exact canonicalPath_continuousWithinAt_of_run_some_leftStable
        (I := I) hγ hγhi hlam hrun hstable
    · rcases hpred with hempty | ⟨k, hne, hk⟩
      · exact canonicalPath_continuousWithinAt_case1_2_b_ii_of_run_some_leftJump_empty
          (I := I) hγ hγhi hlam h0lt hrun hempty hleftJump
      · exact canonicalPath_continuousWithinAt_case1_2_b_i_of_run_some_leftJump
          (I := I) hγ hγhi hlam h0lt hrun
          (k := k) (hne := hne) hk hleftJump

theorem canonicalPath_continuousWithinAt_of_run_some_cases
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (hrun :
      ((canonicalPath I (le_of_lt hγ) hγhi).output ℓ ⟨lam, hlam⟩).run? = some C)
    (hcases :
      Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau
      ∨
      (0 < lam ∧
        Advice.belowThresholdNononeSet I ℓ C.t1 lam = ∅ ∧
        ∀ᶠ x in nhdsWithin lam (Set.Icc (0 : ℝ) 1 ∩ Set.Iio lam),
          Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 x < I.program.barTau)
      ∨
      I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam
      ∨
      (Advice.belowThresholdNononeSet I ℓ C.t1 lam = ∅
        ∨
        ∃ k, ∃ hne : (Advice.belowThresholdNononeSet I ℓ C.t1 lam).Nonempty,
          (Advice.belowThresholdNononeSet I ℓ C.t1 lam).max' hne = k)) :
    ContinuousWithinAt
      ((canonicalPath I (le_of_lt hγ) hγhi).value ℓ)
      (Set.Icc (0 : ℝ) 1)
      lam := by
  rcases hcases with hsmallLeft | ⟨h0lt, hbelowEmpty, hleftJump⟩ | hbarStrict | hpred
  · exact canonicalPath_continuousWithinAt_case1_2_b_ii_of_run_some
      (I := I) (le_of_lt hγ) hγhi hlam hrun hsmallLeft
  · exact canonicalPath_continuousWithinAt_case1_2_b_ii_of_run_some_leftJump_empty
      (I := I) hγ hγhi hlam h0lt hrun
      hbelowEmpty hleftJump
  · exact canonicalPath_continuousWithinAt_of_run_some_barTau_strict_full
      (I := I) hγ hγhi hlam hrun hbarStrict
  · exact canonicalPath_continuousWithinAt_of_run_some_theta_strict_cases
      (I := I) hγ hγhi hlam hrun hpred

theorem canonicalPath_continuousWithinAt_of_run_some
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {C : ProcedureRun I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩)}
    (hrun :
      ((canonicalPath I (le_of_lt hγ) hγhi).output ℓ ⟨lam, hlam⟩).run? = some C) :
    ContinuousWithinAt
      ((canonicalPath I (le_of_lt hγ) hγhi).value ℓ)
      (Set.Icc (0 : ℝ) 1)
      lam := by
  by_cases hsmallLeft :
      Advice.sectionPhaseTwoBudgetValue I ℓ (firstIdx n) lam < I.program.barTau
  · exact canonicalPath_continuousWithinAt_case1_2_b_ii_of_run_some
      (I := I) (le_of_lt hγ) hγhi hlam hrun hsmallLeft
  · by_cases hbarStrict :
        I.program.barTau < Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam
    · exact canonicalPath_continuousWithinAt_of_run_some_barTau_strict_full
        (I := I) hγ hγhi hlam hrun hbarStrict
    · have hbarAtT1 :
          I.program.barTau ≤ Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam := by
        simpa [Advice.PhaseTwoData.beforeBudget_eq_sectionPhaseTwoBudgetValue_of_sectionAdvice
          (Ξ := C.phaseTwo) C.t1] using C.t1_beforeBudget_ge_barTau
      have hbarEq :
          Advice.sectionPhaseTwoBudgetValue I ℓ C.t1 lam = I.program.barTau :=
        le_antisymm (le_of_not_gt hbarStrict) hbarAtT1
      rcases sectionPhaseTwoBudgetValue_leftStable_or_leftJump_of_eq_barTau
          (I := I) (le_of_lt hγ) hlam hbarEq with hstable | ⟨h0lt, hleftJump⟩
      · exact canonicalPath_continuousWithinAt_of_run_some_leftStable
          (I := I) hγ hγhi hlam hrun hstable
      · by_cases hempty : Advice.belowThresholdNononeSet I ℓ C.t1 lam = ∅
        · exact canonicalPath_continuousWithinAt_case1_2_b_ii_of_run_some_leftJump_empty
            (I := I) hγ hγhi hlam h0lt hrun hempty hleftJump
        · have hne : (Advice.belowThresholdNononeSet I ℓ C.t1 lam).Nonempty := by
            exact Finset.nonempty_iff_ne_empty.mpr hempty
          exact canonicalPath_continuousWithinAt_case1_2_b_i_of_run_some_leftJump
            (I := I) hγ hγhi hlam h0lt hrun
            (k := (Advice.belowThresholdNononeSet I ℓ C.t1 lam).max' hne)
            (hne := hne) rfl hleftJump

theorem canonicalPath_continuousWithinAt
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousWithinAt
      ((canonicalPath I (le_of_lt hγ) hγhi).value ℓ)
      (Set.Icc (0 : ℝ) 1)
      lam := by
  let O : RawProcedureOutput I (Advice.sectionAdvice I ℓ lam ⟨hlam.1, hlam.2⟩) :=
    (canonicalPath I (le_of_lt hγ) hγhi).output ℓ ⟨lam, hlam⟩
  by_cases ht1none : O.phaseTwo.t1? = none
  · exact canonicalPath_continuousWithinAt_of_t1_none
      (I := I) (le_of_lt hγ) hγhi hlam ht1none
  · obtain ⟨t1, ht1some⟩ : ∃ t1 : Idx n, O.phaseTwo.t1? = some t1 := by
      cases ht1 : O.phaseTwo.t1? with
      | none => exact False.elim (ht1none ht1)
      | some t1 => exact ⟨t1, rfl⟩
    have hrunne : O.run? ≠ none :=
      RawProcedureOutput.run_ne_none_of_t1_some (I := I) (O := O) ht1some
    rcases O.exists_run_of_ne_none I hrunne with ⟨C, hrun⟩
    exact canonicalPath_continuousWithinAt_of_run_some
      (I := I) hγ hγhi hlam hrun

@[simp] theorem canonicalPath_firstOutput_run_eq_none
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    (canonicalPath I hγlo hγhi).firstOutput.run? = none := by
  apply RawProcedureOutput.run_eq_none_of_t1_none
  have hphase :
      ((canonicalPath I hγlo hγhi).firstOutput).phaseTwo =
        Advice.sectionPhaseTwoData (I := I) hγlo (firstIdx n) 0 (by constructor <;> norm_num) := by
    simpa [SectionRawOutputPath.firstOutput, canonicalPath, Advice.gammaZero] using
      (PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice
        (I := I)
        (Ξ := ((canonicalPath I hγlo hγhi).firstOutput).phaseTwo)
        (ℓ := firstIdx n)
        (lam := 0)
        (hlam := by constructor <;> norm_num)
        hγlo)
  rw [hphase]
  exact sectionPhaseTwoData_t1_eq_none_at_gammaZero I hγlo hγhi

theorem canonicalPath_firstOutput_R0_le_one
    [NeZero n] {I : ProcedureInput n}
    (hγ : 1 < I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    (canonicalPath I (le_of_lt hγ) hγhi).firstOutput.R0 ≤ 1 := by
  have hnone :
      (canonicalPath I (le_of_lt hγ) hγhi).firstOutput.run? = none :=
    canonicalPath_firstOutput_run_eq_none (I := I) (le_of_lt hγ) hγhi
  have hlt :
      (canonicalPath I (le_of_lt hγ) hγhi).firstOutput.R0 < 1 :=
    RawProcedureOutput.R0_lt_one_of_none
      (I := I)
      ((canonicalPath I (le_of_lt hγ) hγhi).firstOutput)
      (barTau_lt_one_of_one_lt_Mcoeff I hγ)
      hnone
  linarith

theorem canonicalPath_lastOutput_R0_ge_one
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    1 ≤ (canonicalPath I hγlo hγhi).lastOutput.R0 := by
  exact gammaOneOutput_R0_ge_one I ((canonicalPath I hγlo hγhi).lastOutput) hγlo hγhi

@[simp] theorem canonicalSectionOutput_phaseTwo_eq
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    (ℓ : Idx n) (x : Set.Icc (0 : ℝ) 1) :
    (canonicalSectionOutput I hγlo hγhi ℓ x).phaseTwo =
      Advice.sectionPhaseTwoData (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩ := by
  simpa using!
    (PhaseTwoData.eq_sectionPhaseTwoData_of_sectionAdvice
      (Ξ := (canonicalSectionOutput I hγlo hγhi ℓ x).phaseTwo) hγlo)

theorem canonicalSectionOutput_run_eq_none_of_t1_none
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {x : Set.Icc (0 : ℝ) 1}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩).t1? = none) :
    (canonicalSectionOutput I hγlo hγhi ℓ x).run? = none := by
  apply RawProcedureOutput.run_eq_none_of_t1_none
  simpa [canonicalSectionOutput_phaseTwo_eq (I := I) hγlo hγhi ℓ x] using ht1

theorem canonicalSectionOutput_run_ne_none_of_t1_some
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {x : Set.Icc (0 : ℝ) 1} {t1 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩).t1? = some t1) :
    (canonicalSectionOutput I hγlo hγhi ℓ x).run? ≠ none := by
  apply RawProcedureOutput.run_ne_none_of_t1_some
  simpa [canonicalSectionOutput_phaseTwo_eq (I := I) hγlo hγhi ℓ x] using ht1

theorem canonicalSectionOutput_run_eq_some_of_t1_t2
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} {x : Set.Icc (0 : ℝ) 1} {t1 t2 : Idx n}
    (ht1 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩).t1? = some t1)
    (ht2 :
      (Advice.sectionPhaseTwoData (I := I) hγlo ℓ x.1 ⟨x.2.1, x.2.2⟩).t2? = some t2) :
    (canonicalSectionOutput I hγlo hγhi ℓ x).run? =
      some
        (sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi ℓ x.1
          ⟨x.2.1, x.2.2⟩ ht1 ht2) := by
  classical
  have hne :
      (canonicalSectionOutput I hγlo hγhi ℓ x).run? ≠ none :=
    canonicalSectionOutput_run_ne_none_of_t1_some (I := I) hγlo hγhi ht1
  have ht1phase :
      (canonicalSectionOutput I hγlo hγhi ℓ x).phaseTwo.t1? = some t1 := by
    simpa [canonicalSectionOutput_phaseTwo_eq (I := I) hγlo hγhi ℓ x] using ht1
  have ht2phase :
      (canonicalSectionOutput I hγlo hγhi ℓ x).phaseTwo.t2? = some t2 := by
    simpa [canonicalSectionOutput_phaseTwo_eq (I := I) hγlo hγhi ℓ x] using ht2
  rcases (canonicalSectionOutput I hγlo hγhi ℓ x).exists_run_eq_thresholds_of_phaseTwo
      (I := I) (t1 := t1) (t2 := t2) ht1phase ht2phase hne with
    ⟨C, hC, hCt1, hCt2⟩
  rw [hC]
  cases hCt1
  cases hCt2
  simpa using congrArg some (C.eq_sectionProcedureRunOfPhaseTwoThresholds hγlo hγhi)

theorem canonicalSectionOutput_toNextSectionLeft_eq
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff)
    (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125)
    {ℓ : Idx n} (hℓ : ℓ < lastIdx n) :
    (canonicalSectionOutput I hγlo hγhi ℓ
      ⟨1, by constructor <;> norm_num⟩).toNextSectionLeft hℓ =
      canonicalSectionOutput I hγlo hγhi (succIdx ℓ hℓ)
        ⟨0, by constructor <;> norm_num⟩ := by
  classical
  let xR : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  let xL : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  change (canonicalSectionOutput I hγlo hγhi ℓ xR).toNextSectionLeft hℓ =
    canonicalSectionOutput I hγlo hγhi (succIdx ℓ hℓ) xL
  apply RawProcedureOutput.ext
  · erw [RawProcedureOutput.toNextSectionLeft_phaseTwo]
    simpa [canonicalSectionOutput_phaseTwo_eq (I := I) hγlo hγhi] using
      (sectionPhaseTwoData_toNextSectionLeft_eq (I := I) hℓ hγlo)
  · by_cases ht1none :
        (Advice.sectionPhaseTwoData (I := I) hγlo ℓ 1
          (by constructor <;> norm_num)).t1? = none
    · have hright_none :
          (canonicalSectionOutput I hγlo hγhi ℓ xR).run? = none :=
        canonicalSectionOutput_run_eq_none_of_t1_none (I := I) hγlo hγhi ht1none
      have ht1' :
          (Advice.sectionPhaseTwoData (I := I) hγlo (succIdx ℓ hℓ) 0
            (by constructor <;> norm_num)).t1? = none := by
        rw [← sectionPhaseTwoData_toNextSectionLeft_eq (I := I) hℓ hγlo]
        simpa using! ht1none
      have hleft_none :
          (canonicalSectionOutput I hγlo hγhi (succIdx ℓ hℓ) xL).run? =
            none :=
        canonicalSectionOutput_run_eq_none_of_t1_none (I := I) hγlo hγhi ht1'
      rw [RawProcedureOutput.toNextSectionLeft_run_eq_none
        (hℓ := hℓ)
        (O := canonicalSectionOutput I hγlo hγhi ℓ xR)
        hright_none]
      exact hleft_none.symm
    · obtain ⟨t1, ht1some⟩ :
          ∃ t1 : Idx n,
            (Advice.sectionPhaseTwoData (I := I) hγlo ℓ 1
              (by constructor <;> norm_num)).t1? = some t1 := by
        cases ht1' : (Advice.sectionPhaseTwoData (I := I) hγlo ℓ 1
            (by constructor <;> norm_num)).t1? with
        | none =>
            exact False.elim (ht1none ht1')
        | some t1' =>
            exact ⟨t1', rfl⟩
      obtain ⟨t2, ht2⟩ :=
        sectionPhaseTwoData_exists_t2_of_t1_spec I hγlo hγhi ℓ 1
          (by constructor <;> norm_num) ht1some
      have ht1' :
          (Advice.sectionPhaseTwoData (I := I) hγlo (succIdx ℓ hℓ) 0
            (by constructor <;> norm_num)).t1? = some t1 := by
        rw [← sectionPhaseTwoData_toNextSectionLeft_eq (I := I) hℓ hγlo]
        simpa using! ht1some
      have ht2' :
          (Advice.sectionPhaseTwoData (I := I) hγlo (succIdx ℓ hℓ) 0
            (by constructor <;> norm_num)).t2? = some t2 := by
        rw [← sectionPhaseTwoData_toNextSectionLeft_eq (I := I) hℓ hγlo]
        simpa using! ht2
      have hright_some :
          (canonicalSectionOutput I hγlo hγhi ℓ xR).run? =
            some
              (sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi ℓ 1
                (by constructor <;> norm_num) ht1some ht2) :=
        canonicalSectionOutput_run_eq_some_of_t1_t2
          (I := I) (ℓ := ℓ) (x := xR) (t1 := t1) (t2 := t2) hγlo hγhi ht1some ht2
      have hleft_some :
          (canonicalSectionOutput I hγlo hγhi (succIdx ℓ hℓ) xL).run? =
            some
              (sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi (succIdx ℓ hℓ) 0
                (by constructor <;> norm_num) ht1' ht2') :=
        canonicalSectionOutput_run_eq_some_of_t1_t2
          (I := I) (ℓ := succIdx ℓ hℓ) (x := xL) (t1 := t1) (t2 := t2) hγlo hγhi ht1' ht2'
      have hrun_transport :
          (sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi ℓ 1
            (by constructor <;> norm_num) ht1some ht2).toNextSectionLeft hℓ =
            sectionProcedureRunOfPhaseTwoThresholds I hγlo hγhi (succIdx ℓ hℓ) 0
              (by constructor <;> norm_num) ht1' ht2' :=
        ProcedureRun.sectionProcedureRunOfPhaseTwoThresholds_toNextSectionLeft_eq
          (I := I) (hℓ := hℓ) hγlo hγhi ht1some ht2 ht1' ht2'
      rw [RawProcedureOutput.toNextSectionLeft_run_eq_some
        (hℓ := hℓ)
        (O := canonicalSectionOutput I hγlo hγhi ℓ xR)
        hright_some]
      rw [hrun_transport, hleft_some]
      rfl

theorem canonicalPath_compatible
    [NeZero n] {I : ProcedureInput n}
    (hγlo : 1 ≤ I.program.Mcoeff) (hγhi : I.program.Mcoeff ≤ (153 : ℝ) / 125) :
    SectionRawOutputPath.EndpointCompatible (canonicalPath I hγlo hγhi) := by
  intro ℓ hℓ
  simpa [SectionRawOutputPath.nextLeftOutput, SectionRawOutputPath.rightOutput, canonicalPath,
    Advice.nextSectionLeft, Advice.sectionRight] using
    (canonicalSectionOutput_toNextSectionLeft_eq (I := I) hγlo hγhi hℓ).symm

end KMedian195


