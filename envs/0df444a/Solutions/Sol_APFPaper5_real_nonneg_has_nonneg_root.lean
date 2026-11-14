-- Prove2me | solution 1 for APFPaper5.real_nonneg_has_nonneg_root
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:50:18.088647+00:00
-- url     : https://prove2.me/submissions/ba2969eb-4a94-403e-8823-db3b7acfbd07

/-
DRAFT (Claude seat, phone session 2026-11-13; not gated, not reviewed, not released, not built on the build box).
name: APFPaper5_real_nonneg_has_root
title: Every nonnegative real number has a nonnegative square root
ordinary mathematics; consumes no APF input. Discharges the binder `hroot` in both forms in which the K1 and
K3 reference theorems carry it. Proved from order completeness of the reals (supremum of the set of
nonnegative s with s * s ≤ t), so that the only Mathlib modules imported are ones the frozen v15 ledger
already imports. The one-line alternative through `Real.sqrt` needs Mathlib.Analysis.Real.Sqrt, which pulls
in topology.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

theorem APFPaper5.real_nonneg_has_nonneg_root :
    ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t := by
  intro t ht
  have h0 : (0 : ℝ) ∈ {s : ℝ | 0 ≤ s ∧ s * s ≤ t} := ⟨le_refl 0, by simpa using ht⟩
  have hbdd : BddAbove {s : ℝ | 0 ≤ s ∧ s * s ≤ t} := by
    refine ⟨t + 1, ?_⟩
    rintro s ⟨hs0, hs⟩
    by_contra hlt
    have hlt' : t + 1 < s := not_le.mp hlt
    nlinarith
  have hr0 : 0 ≤ sSup {s : ℝ | 0 ≤ s ∧ s * s ≤ t} := le_csSup hbdd h0
  refine ⟨sSup {s : ℝ | 0 ≤ s ∧ s * s ≤ t}, hr0, ?_⟩
  generalize hr : sSup {s : ℝ | 0 ≤ s ∧ s * s ≤ t} = r at hr0
  rcases lt_trichotomy (r * r) t with hlt | heq | hgt
  · exfalso
    have hden : 0 < 2 * r + 1 := by linarith
    have hεpos : 0 < min 1 ((t - r * r) / (2 * r + 1)) :=
      lt_min one_pos (div_pos (by linarith) hden)
    have hε1 : min 1 ((t - r * r) / (2 * r + 1)) ≤ 1 := min_le_left _ _
    have hε2 : min 1 ((t - r * r) / (2 * r + 1)) ≤ (t - r * r) / (2 * r + 1) := min_le_right _ _
    generalize min 1 ((t - r * r) / (2 * r + 1)) = ε at hεpos hε1 hε2
    have hε3 : ε * (2 * r + 1) ≤ t - r * r := (le_div_iff₀ hden).mp hε2
    have hmem : r + ε ∈ {s : ℝ | 0 ≤ s ∧ s * s ≤ t} :=
      ⟨by linarith, by nlinarith [mul_le_mul_of_nonneg_left hε1 hεpos.le]⟩
    have hle : r + ε ≤ r := by
      have h := le_csSup hbdd hmem
      rw [hr] at h
      exact h
    linarith
  · exact heq
  · exfalso
    have hrpos : 0 < r := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hgt
        simp at hgt
        linarith
    have hεpos : 0 < (r * r - t) / (2 * r) := div_pos (by linarith) (by linarith)
    have hεeq : (r * r - t) / (2 * r) * (2 * r) = r * r - t := by field_simp
    generalize (r * r - t) / (2 * r) = ε at hεpos hεeq
    have hre : 0 ≤ r - ε := by nlinarith [mul_pos hrpos hrpos]
    have hub : ∀ s ∈ {s : ℝ | 0 ≤ s ∧ s * s ≤ t}, s ≤ r - ε := by
      rintro s ⟨hs0, hs⟩
      by_contra hlt
      have hlt' : r - ε < s := not_le.mp hlt
      nlinarith [mul_pos (sub_pos.mpr hlt') (by linarith : 0 < s + (r - ε)), sq_nonneg ε]
    have hle : r ≤ r - ε := by
      have h := csSup_le ⟨0, h0⟩ hub
      rw [hr] at h
      exact h
    linarith

theorem APFPaper5.real_nonneg_has_root :
    ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, r * r = t :=
  fun t ht => (APFPaper5.real_nonneg_has_nonneg_root t ht).imp fun _ h => h.2

#print axioms APFPaper5.real_nonneg_has_nonneg_root
#print axioms APFPaper5.real_nonneg_has_root


theorem solution :
∀ (t : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
    @Exists.{1} Real fun (r : Real) =>
      And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
        (@Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r r) t) := by
  exact @APFPaper5.real_nonneg_has_nonneg_root
