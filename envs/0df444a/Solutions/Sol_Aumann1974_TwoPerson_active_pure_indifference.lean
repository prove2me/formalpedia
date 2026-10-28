-- Prove2me | solution 1 for Aumann1974.TwoPerson.active_pure_indifference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:03:02.384902+00:00
-- url     : https://prove2.me/submissions/751db56b-4c7c-439f-bd79-df206bad324e

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure
import Definitions.Def_Aumann1974_TwoPerson_Payoffs

namespace AK2a6b4c82

open MeasureTheory

theorem integral_fin_valued {Ω T : Type*} [MeasurableSpace Ω] [Fintype T]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → T) (F : T → ℝ)
    (hf : ∀ t, MeasurableSet {ω | f ω = t}) :
    ∫ ω, F (f ω) ∂μ = ∑ t, μ.real {ω | f ω = t} * F t := by
  classical
  have : (fun ω => F (f ω)) = fun ω => ∑ t, Set.indicator {ω | f ω = t} (fun _ => F t) ω := by
    funext ω
    rw [Finset.sum_eq_single (f ω)]
    · simp
    · intro b _ hb
      simp [Set.indicator, Ne.symm hb]
    · simp
  rw [this, integral_finsetSum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_indicator_const _ (hf t), smul_eq_mul]
  · intro t _
    exact (integrable_const (F t)).indicator (hf t)

end AK2a6b4c82

open MeasureTheory in
theorem solution {Ω X : Type*} {mΩ : MeasurableSpace Ω}
    {S : Fin 2 → Type*} [∀ i, Fintype (S i)] [Fintype X]
    (R : Aumann1974.TwoPerson.RandomizingStructure (Fin 2) Ω mΩ)
    (hII : Aumann1974.TwoPerson.AssumptionII R)
    (g : (∀ i, S i) → X) (u : Fin 2 → X → ℝ)
    (s : ∀ i, Ω → S i) (hs : Aumann1974.TwoPerson.IsEquilibrium R u g s)
    (hmix : ∀ i, Aumann1974.TwoPerson.IsMixed R i (s i))
    (i : Fin 2) (a : S i) (hpos : R.p i {ω | s i ω = a} ≠ 0) :
    Aumann1974.TwoPerson.H R u g (Function.update s i (fun _ => a)) i
      = Aumann1974.TwoPerson.H R u g s i := by
  classical

  obtain ⟨j, hji, hall⟩ : ∃ j : Fin 2, j ≠ i ∧ ∀ k, k = i ∨ k = j := by
    fin_cases i
    · exact ⟨1, by decide, by intro k; fin_cases k <;> simp⟩
    · exact ⟨0, by decide, by intro k; fin_cases k <;> simp⟩
  set μ := R.p i with hμ
  have hmeas : ∀ k (b : S k), MeasurableSet {ω | s k ω = b} :=
    fun k b => R.J_le k _ (hs.1 k b)
  -- weights
  set w : S i → ℝ := fun c => μ.real {ω | s i ω = c} with hw
  set q : S j → ℝ := fun d => μ.real {ω | s j ω = d} with hq
  -- independence
  have hind : ∀ (c : S i) (d : S j),
      μ.real ({ω | s i ω = c} ∩ {ω | s j ω = d}) = w c * q d := by
    intro c d
    have h1 := (hmix j d).2 i hji.symm {ω | s i ω = c}
      ((le_iSup₂ (f := fun (k : Fin 2) (_ : k ≠ j) => R.J k) i hji.symm) _ (hs.1 i c))
    simp only [Measure.real, hw, hq]
    rw [Set.inter_comm, h1, ENNReal.toReal_mul, mul_comm]
  -- profile integral as sum
  have hprof : ∀ t : ∀ k, Ω → S k, (∀ k b, MeasurableSet {ω | t k ω = b}) →
      Aumann1974.TwoPerson.H R u g t i
        = ∑ x : (∀ k, S k), μ.real {ω | (fun k => t k ω) = x}
            * Aumann1974.TwoPerson.payoffFn u g i x := by
    intro t ht
    unfold Aumann1974.TwoPerson.H
    apply AK2a6b4c82.integral_fin_valued
    intro x
    have : {ω | (fun k => t k ω) = x} = ⋂ k, {ω | t k ω = x k} := by
      ext ω; simp [funext_iff]
    rw [this]; exact MeasurableSet.iInter fun k => ht k (x k)
  set h := Aumann1974.TwoPerson.payoffFn u g i
  have hHs : Aumann1974.TwoPerson.H R u g s i = ∑ x : (∀ k, S k), w (x i) * q (x j) * h x := by
    rw [hprof s hmeas]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    rw [← hind]
    congr 1
    ext ω
    simp only [funext_iff, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · intro hh; exact ⟨hh i, hh j⟩
    · intro hh k; rcases hall k with rfl | rfl
      · exact hh.1
      · exact hh.2
  have hupd_meas : ∀ c : S i, ∀ k b,
      MeasurableSet {ω | Function.update s i (fun _ => c) k ω = b} := by
    intro c k b
    by_cases hk : k = i
    · subst hk; simp only [Function.update_self]; exact MeasurableSet.const _
    · simp only [Function.update_of_ne hk]; exact hmeas k b
  have hHc : ∀ c : S i, Aumann1974.TwoPerson.H R u g (Function.update s i (fun _ => c)) i
      = ∑ x : (∀ k, S k), (if c = x i then q (x j) else 0) * h x := by
    intro c
    rw [hprof _ (hupd_meas c)]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    have hset : {ω | (fun k => Function.update s i (fun _ => c) k ω) = x}
        = {ω | c = x i ∧ s j ω = x j} := by
      ext ω
      simp only [funext_iff, Set.mem_ofPred_eq]
      constructor
      · intro hh
        refine ⟨by simpa using hh i, by simpa [Function.update_of_ne hji] using hh j⟩
      · intro hh k; rcases hall k with rfl | rfl
        · simpa using hh.1
        · simpa [Function.update_of_ne hji] using hh.2
    rw [hset]
    split_ifs with hc
    · simp [hc, hq]
    · simp [hc]
  -- weights sum to one
  have hwsum : ∑ c, w c = 1 := by
    have := AK2a6b4c82.integral_fin_valued μ (s i) (fun _ => (1 : ℝ)) (hmeas i)
    simpa using this.symm
  have hw0 : ∀ c, 0 ≤ w c := fun c => measureReal_nonneg
  have hkey : Aumann1974.TwoPerson.H R u g s i
      = ∑ c, w c * Aumann1974.TwoPerson.H R u g (Function.update s i (fun _ => c)) i := by
    simp_rw [hHc, Finset.mul_sum]
    rw [Finset.sum_comm, hHs]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp_rw [← mul_assoc, mul_ite, mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp
  have hle : ∀ c : S i, Aumann1974.TwoPerson.H R u g (Function.update s i (fun _ => c)) i
      ≤ Aumann1974.TwoPerson.H R u g s i := by
    intro c
    refine hs.2 i _ ?_
    intro b
    exact MeasurableSet.const _
  refine le_antisymm (hle a) ?_
  by_contra hlt
  rw [not_le] at hlt
  have hwa : 0 < w a := by
    simp only [hw, Measure.real]
    exact ENNReal.toReal_pos hpos (measure_ne_top _ _)
  have : ∑ c, w c * Aumann1974.TwoPerson.H R u g (Function.update s i (fun _ => c)) i
      < ∑ c, w c * Aumann1974.TwoPerson.H R u g s i := by
    apply Finset.sum_lt_sum
    · intro c _; exact mul_le_mul_of_nonneg_left (hle c) (hw0 c)
    · exact ⟨a, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt hwa⟩
  rw [← Finset.sum_mul, hwsum, one_mul, ← hkey] at this
  exact lt_irrefl _ this
