-- Prove2me | solution 1 for ArapostathisAC.SennottACOI.acoi_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:25:00.910502+00:00
-- url     : https://prove2.me/submissions/7a9ea3dd-ab34-4abe-97da-adf4cf6ffbe5

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions
import Theorems.Thm_ArapostathisAC_SennottACOI_eq_5_15

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.SennottACOI

lemma sennott_prob_hasSum {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (i : ℕ) (a : A) :
    HasSum (fun j => ArapostathisAC.VanishingDiscount.prob M i a j) 1 := by
  have h1 : ∑' j, M.P (i, a) {j} = 1 := by
    have := Measure.tsum_indicator_apply_singleton (M.P (i, a)) Set.univ MeasurableSet.univ
    simpa [Set.indicator_univ] using this
  have h2 := ENNReal.hasSum_toReal (f := fun j => M.P (i, a) {j}) (by rw [h1]; simp)
  rw [← ENNReal.tsum_toReal_eq (fun j => measure_ne_top _ _), h1] at h2
  simpa [ArapostathisAC.VanishingDiscount.prob] using h2

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (h14 : Assumption5_14 M) (L : ℕ)
    (hL : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, -(L : ℝ) ≤ ArapostathisAC.VanishingDiscount.hRel M β i) (h16 : Assumption5_16 M)
    (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1))
    (fβ : ℕ → StationaryPolicy M) (hfβ : ∀ n, ArapostathisAC.VanishingDiscount.IsDiscOptimal M (β n) (fβ n))
    (f : StationaryPolicy M) (h : ℕ → ℝ) (ρ : ℝ)
    (hf : ∀ i, Tendsto (fun n => (fβ n).1 i) atTop (𝓝 (f.1 i)))
    (hh : ∀ i, Tendsto (fun n => ArapostathisAC.VanishingDiscount.hRel M (β n) i) atTop (𝓝 (h i)))
    (hρ : Tendsto (fun n => (1 - β n) * (ArapostathisAC.VanishingDiscount.discValue M (β n) 0).toReal) atTop (𝓝 ρ))
    (i : ℕ) :
    Summable (fun j => ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * h j) ∧
    M.c i (f.1 i) + ∑' j, ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * h j ≤ ρ + h i := by
  set p : ℕ → ℕ → ℝ := fun n j => ArapostathisAC.VanishingDiscount.prob M i ((fβ n).1 i) j with hp
  set q : ℕ → ℝ := fun j => ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j with hq
  set g : ℕ → ℕ → ℝ := fun n j => ArapostathisAC.VanishingDiscount.hRel M (β n) j with hg
  have hp0 : ∀ n j, 0 ≤ p n j := fun n j => ENNReal.toReal_nonneg
  have hq0 : ∀ j, 0 ≤ q j := fun j => ENNReal.toReal_nonneg
  -- convergence of the actions inside `U i`
  have hfw : Tendsto (fun n => (fβ n).1 i) atTop (𝓝[M.U i] (f.1 i)) :=
    tendsto_nhdsWithin_iff.2 ⟨hf i, Eventually.of_forall (fun n => (fβ n).2 i)⟩
  have hpq : ∀ j, Tendsto (fun n => p n j) atTop (𝓝 (q j)) := fun j =>
    ((M.P_cont i j) (f.1 i) (f.2 i)).tendsto.comp hfw
  have hc : Tendsto (fun n => M.c i ((fβ n).1 i)) atTop (𝓝 (M.c i (f.1 i))) :=
    ((M.c_cont i) (f.1 i) (f.2 i)).tendsto.comp hfw
  -- the identity (5.15)
  have E := fun n => eq_5_15 M (β n) (hβ n) (h14 (β n) (hβ n)) (fβ n) (hfβ n) i
  -- shifted nonnegative terms
  have hsumL : ∀ n, HasSum (fun j => p n j * (g n j + L))
      ((∑' j, p n j * g n j) + L) := by
    intro n
    have h1 : HasSum (fun j => p n j * g n j) (∑' j, p n j * g n j) := (E n).1.hasSum
    have h2 : HasSum (fun j => p n j * (L : ℝ)) (1 * L) :=
      (sennott_prob_hasSum M i ((fβ n).1 i)).mul_right _
    have := h1.add h2
    simpa [mul_add, one_mul] using this
  set R : ℝ := ρ + h i - M.c i (f.1 i) + L with hR
  have hRn : Tendsto (fun n => β n * ((∑' j, p n j * g n j) + L)) atTop (𝓝 R) := by
    have heq : ∀ n, β n * ((∑' j, p n j * g n j) + L) =
        (1 - β n) * (ArapostathisAC.VanishingDiscount.discValue M (β n) 0).toReal + g n i
          - M.c i ((fβ n).1 i) + β n * L := by
      intro n; have := (E n).2; simp only [hp, hg] at this ⊢; linarith
    simp_rw [heq]
    have := ((hρ.add (hh i)).sub hc).add (hβ1.mul_const (L : ℝ))
    simpa [hR, one_mul] using this
  -- finite partial sums of the limit terms
  have hF : ∀ F : Finset ℕ, ∑ j ∈ F, q j * (h j + L) ≤ R := by
    intro F
    have hlim : Tendsto (fun n => β n * ∑ j ∈ F, p n j * (g n j + L)) atTop
        (𝓝 (1 * ∑ j ∈ F, q j * (h j + L))) :=
      hβ1.mul (tendsto_finset_sum _ (fun j _ => (hpq j).mul ((hh j).add_const _)))
    rw [one_mul] at hlim
    refine le_of_tendsto_of_tendsto' hlim hRn (fun n => ?_)
    apply mul_le_mul_of_nonneg_left _ (hβ n).1.le
    rw [← (hsumL n).tsum_eq]
    refine Summable.sum_le_tsum F (fun j _ => ?_) (hsumL n).summable
    exact mul_nonneg (hp0 n j) (by linarith [hL (β n) (hβ n) j])
  have hhL : ∀ j, -(L : ℝ) ≤ h j := fun j =>
    ge_of_tendsto (hh j) (Eventually.of_forall (fun n => hL (β n) (hβ n) j))
  have hnn : 0 ≤ fun j => q j * (h j + L) := fun j =>
    mul_nonneg (hq0 j) (by linarith [hhL j])
  have hsum : Summable (fun j => q j * (h j + L)) := summable_of_sum_le hnn hF
  have htle : ∑' j, q j * (h j + L) ≤ R := Real.tsum_le_of_sum_le hnn hF
  have hqL : HasSum (fun j => q j * (L : ℝ)) (1 * L) :=
    (sennott_prob_hasSum M i (f.1 i)).mul_right _
  have hsub : HasSum (fun j => q j * h j) (∑' j, q j * (h j + L) - 1 * L) := by
    have := hsum.hasSum.sub hqL
    refine this.congr_fun (fun j => ?_)
    ring
  refine ⟨hsub.summable, ?_⟩
  show M.c i (f.1 i) + ∑' j, q j * h j ≤ ρ + h i
  rw [hsub.tsum_eq]
  linarith
