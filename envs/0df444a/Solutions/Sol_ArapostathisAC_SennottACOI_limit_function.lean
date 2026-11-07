-- Prove2me | solution 1 for ArapostathisAC.SennottACOI.limit_function
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:27:35.742812+00:00
-- url     : https://prove2.me/submissions/ac347b53-8ac1-4bf9-af4f-cbbf5b5679c0

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions
import Theorems.Thm_ArapostathisAC_SennottACOI_theorem_2_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.SennottACOI

lemma sennott_tsum_meas_singleton {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (i : ℕ) (a : A) :
    ∑' j, M.P (i, a) {j} = 1 := by
  have := Measure.tsum_indicator_apply_singleton (M.P (i, a)) Set.univ MeasurableSet.univ
  simpa [Set.indicator_univ] using this

/-- The bound `(1 - β) J*_β(0) ≤ c(0, a₀) + Σ_j P(j | 0, a₀) Mf(j)` from the DCOE at state `0`. -/
lemma sennott_disc_bound {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hfin : ∀ i, ArapostathisAC.VanishingDiscount.discValue M β i ≠ ⊤)
    (Mf : ℕ → ℝ) (hM0 : ∀ i, 0 ≤ Mf i)
    (hMle : ∀ i, ArapostathisAC.VanishingDiscount.hRel M β i ≤ Mf i)
    (a0 : A) (ha0 : a0 ∈ M.U 0)
    (hs : Summable (fun j => ArapostathisAC.VanishingDiscount.prob M 0 a0 j * Mf j)) :
    (1 - β) * (ArapostathisAC.VanishingDiscount.discValue M β 0).toReal ≤
      M.c 0 a0 + ∑' j, ArapostathisAC.VanishingDiscount.prob M 0 a0 j * Mf j := by
  set J := ArapostathisAC.VanishingDiscount.discValue M β with hJ
  set S := ∑' j, ArapostathisAC.VanishingDiscount.prob M 0 a0 j * Mf j with hS
  have hS0 : 0 ≤ S := tsum_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg (hM0 j))
  have hc0 : 0 ≤ M.c 0 a0 := M.c_nonneg 0 a0 ha0
  have hJ0 : 0 ≤ (J 0).toReal := ENNReal.toReal_nonneg
  have hdcoe := (theorem_2_1 M β hβ).1 0
  have h1 : J 0 ≤ ENNReal.ofReal (M.c 0 a0) +
      ENNReal.ofReal β * ∑' j, M.P (0, a0) {j} * J j := by
    rw [← hJ] at hdcoe
    rw [hdcoe]
    exact iInf₂_le a0 ha0
  -- J j ≤ J 0 + Mf j
  have h2 : ∀ j, J j ≤ J 0 + ENNReal.ofReal (Mf j) := by
    intro j
    have hj : (J j).toReal ≤ (J 0).toReal + Mf j := by
      have := hMle j
      simp only [ArapostathisAC.VanishingDiscount.hRel] at this
      linarith
    rw [← ENNReal.ofReal_toReal (hfin j), ← ENNReal.ofReal_toReal (hfin 0),
      ← ENNReal.ofReal_add hJ0 (hM0 j)]
    exact ENNReal.ofReal_le_ofReal hj
  have h3 : ∑' j, M.P (0, a0) {j} * J j ≤ J 0 + ENNReal.ofReal S := by
    calc ∑' j, M.P (0, a0) {j} * J j
        ≤ ∑' j, M.P (0, a0) {j} * (J 0 + ENNReal.ofReal (Mf j)) :=
          ENNReal.tsum_le_tsum (fun j => mul_le_mul_right (h2 j) _)
      _ = ∑' j, (M.P (0, a0) {j} * J 0 + M.P (0, a0) {j} * ENNReal.ofReal (Mf j)) := by
          congr 1; ext j; rw [mul_add]
      _ = (∑' j, M.P (0, a0) {j}) * J 0 + ∑' j, M.P (0, a0) {j} * ENNReal.ofReal (Mf j) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      _ = J 0 + ENNReal.ofReal S := by
          rw [sennott_tsum_meas_singleton, one_mul, hS,
            ENNReal.ofReal_tsum_of_nonneg (f := fun j => ArapostathisAC.VanishingDiscount.prob M 0 a0 j * Mf j) (fun j => mul_nonneg ENNReal.toReal_nonneg (hM0 j)) hs]
          congr 1; congr 1; ext j
          simp only [ArapostathisAC.VanishingDiscount.prob]
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have h4 : J 0 ≤ ENNReal.ofReal (M.c 0 a0 + β * ((J 0).toReal + S)) := by
    refine h1.trans ?_
    calc ENNReal.ofReal (M.c 0 a0) + ENNReal.ofReal β * ∑' j, M.P (0, a0) {j} * J j
        ≤ ENNReal.ofReal (M.c 0 a0) + ENNReal.ofReal β * (J 0 + ENNReal.ofReal S) := by
          gcongr
      _ = ENNReal.ofReal (M.c 0 a0 + β * ((J 0).toReal + S)) := by
          rw [ENNReal.ofReal_add hc0 (mul_nonneg hβ.1.le (add_nonneg hJ0 hS0)),
            ENNReal.ofReal_mul hβ.1.le, ENNReal.ofReal_add hJ0 hS0,
            ENNReal.ofReal_toReal (hfin 0)]
  have h5 : (J 0).toReal ≤ M.c 0 a0 + β * ((J 0).toReal + S) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h4
    rwa [ENNReal.toReal_ofReal (add_nonneg hc0 (mul_nonneg hβ.1.le (add_nonneg hJ0 hS0)))]
      at this
  have : β * S ≤ S := by nlinarith [hβ.2]
  nlinarith

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (h14 : Assumption5_14 M) (L : ℕ)
    (hL : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, -(L : ℝ) ≤ ArapostathisAC.VanishingDiscount.hRel M β i) (h16 : Assumption5_16 M)
    (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1))
    (fβ : ℕ → StationaryPolicy M) (hfβ : ∀ n, ArapostathisAC.VanishingDiscount.IsDiscOptimal M (β n) (fβ n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : StationaryPolicy M, ∃ h : ℕ → ℝ, ∃ ρ : ℝ, 0 ≤ ρ ∧
      (∀ i, Tendsto (fun n => (fβ (φ n)).1 i) atTop (𝓝 (f.1 i))) ∧
      (∀ i, Tendsto (fun n => ArapostathisAC.VanishingDiscount.hRel M (β (φ n)) i) atTop (𝓝 (h i))) ∧
      (∀ i, -(L : ℝ) ≤ h i) ∧
      ∀ i, Tendsto (fun n => (1 - β (φ n)) * (ArapostathisAC.VanishingDiscount.discValue M (β (φ n)) i).toReal) atTop
        (𝓝 ρ) := by
  obtain ⟨Mf, hM0, hMle, ha⟩ := h16
  obtain ⟨a0, ha0, hs⟩ := ha 0
  set B : ℝ := M.c 0 a0 + ∑' j, ArapostathisAC.VanishingDiscount.prob M 0 a0 j * Mf j with hB
  set x : ℕ → ℝ := fun n =>
    (1 - β n) * (ArapostathisAC.VanishingDiscount.discValue M (β n) 0).toReal with hx
  have hxB : ∀ n, x n ∈ Set.Icc 0 B := fun n =>
    ⟨mul_nonneg (by linarith [(hβ n).2]) ENNReal.toReal_nonneg,
      sennott_disc_bound M (β n) (hβ n) (h14 (β n) (hβ n)) Mf hM0 (hMle (β n) (hβ n)) a0 ha0 hs⟩
  set K := (Set.univ.pi M.U) ×ˢ
    (Set.univ.pi (fun i => Set.Icc (-(L : ℝ)) (Mf i))) ×ˢ Set.Icc 0 B with hKdef
  have hK : IsCompact K :=
    (isCompact_univ_pi M.U_compact).prod ((isCompact_univ_pi (fun i => isCompact_Icc)).prod
      isCompact_Icc)
  set u : ℕ → (ℕ → A) × (ℕ → ℝ) × ℝ := fun n =>
    ((fβ n).1, fun i => ArapostathisAC.VanishingDiscount.hRel M (β n) i, x n) with hu
  have huK : ∀ n, u n ∈ K := by
    intro n
    refine ⟨fun i _ => (fβ n).2 i, fun i _ => ⟨hL (β n) (hβ n) i, hMle (β n) (hβ n) i⟩, hxB n⟩
  obtain ⟨⟨f0, h, ρ⟩, ⟨hf0, hhK, hρK⟩, φ, hφ, hlim⟩ := hK.tendsto_subseq huK
  have hl1 : Tendsto (fun n => (fβ (φ n)).1) atTop (𝓝 f0) := by
    have := (continuous_fst.tendsto _).comp hlim; exact this
  have hl2 : Tendsto (fun n => fun i => ArapostathisAC.VanishingDiscount.hRel M (β (φ n)) i)
      atTop (𝓝 h) := by
    have := ((continuous_fst.comp continuous_snd).tendsto _).comp hlim; exact this
  have hl3 : Tendsto (fun n => x (φ n)) atTop (𝓝 ρ) := by
    have := ((continuous_snd.comp continuous_snd).tendsto _).comp hlim; exact this
  have hhconv : ∀ i, Tendsto (fun n => ArapostathisAC.VanishingDiscount.hRel M (β (φ n)) i)
      atTop (𝓝 (h i)) := tendsto_pi_nhds.1 hl2
  refine ⟨φ, hφ, ⟨f0, fun i => hf0 i (Set.mem_univ i)⟩, h, ρ, hρK.1,
    tendsto_pi_nhds.1 hl1, hhconv, fun i => (hhK i (Set.mem_univ i)).1, fun i => ?_⟩
  have hβφ : Tendsto (fun n => 1 - β (φ n)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub (hβ1.comp hφ.tendsto_atTop)
    simpa using this
  have hsplit : ∀ n, (1 - β (φ n)) *
      (ArapostathisAC.VanishingDiscount.discValue M (β (φ n)) i).toReal =
      x (φ n) + (1 - β (φ n)) * ArapostathisAC.VanishingDiscount.hRel M (β (φ n)) i := by
    intro n
    simp only [hx, ArapostathisAC.VanishingDiscount.hRel]
    ring
  simp_rw [hsplit]
  have := hl3.add (hβφ.mul (hhconv i))
  simpa using this
