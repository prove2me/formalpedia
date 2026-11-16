-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_maruyama_scheme_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T22:51:08.158044+00:00
-- url     : https://prove2.me/submissions/172609b6-239b-4483-90b0-1e9ecd25002d

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

/-- A globally Lipschitz map is continuous. -/
theorem em_lipschitz_continuous {b : ℝ → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hbL : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) : Continuous b := by
  have hl : LipschitzWith (Real.toNNReal L) b := LipschitzWith.of_dist_le_mul (fun x y => by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0]; exact hbL x y)
  exact hl.continuous

/-- A globally Lipschitz map preserves square integrability on a probability space. -/
theorem em_lipschitz_comp_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) {b : ℝ → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hbL : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) :
    MemLp (fun ω => b (f ω)) 2 P := by
  have hbc : Continuous b := em_lipschitz_continuous hL0 hbL
  have h1 : MemLp (fun ω => b (f ω) - b 0) 2 P := by
    refine MemLp.of_le_mul (c := L) hf
      ((hbc.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub aestronglyMeasurable_const)
      (ae_of_all _ (fun ω => ?_))
    have := hbL (f ω) 0
    rw [sub_zero] at this
    simpa [Real.norm_eq_abs] using this
  have h2 : MemLp (fun ω => (b (f ω) - b 0) + b 0) 2 P := h1.add (memLp_const (b 0))
  have hfun : (fun ω => (b (f ω) - b 0) + b 0) = fun ω => b (f ω) := by
    funext ω; ring
  rwa [hfun] at h2

/-- The product of two independent square-integrable real random variables is square
integrable. -/
theorem em_indep_mul_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U V : Ω → ℝ} (hU : MemLp U 2 P) (hV : MemLp V 2 P)
    (hind : IndepFun U V P) : MemLp (fun ω => U ω * V ω) 2 P := by
  have hae : AEStronglyMeasurable (fun ω => U ω * V ω) P :=
    hU.aestronglyMeasurable.mul hV.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hae]
  have hind2 : IndepFun (fun ω => U ω ^ 2) (fun ω => V ω ^ 2) P :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hprod := hind2.integrable_mul hU.integrable_sq hV.integrable_sq
  have hfun : (fun ω => (U ω * V ω) ^ 2) = (fun ω => U ω ^ 2) * (fun ω => V ω ^ 2) := by
    funext ω; simp only [Pi.mul_apply]; ring
  rw [hfun]; exact hprod

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (E : (n : ℕ) → Fin (n + 1) → Ω → ℝ)
    (hE0 : ∀ (n : ℕ) (ω : Ω), E n 0 ω = x₀)
    (hErec : ∀ (n : ℕ), 0 < n →
      ∀ (k : Fin n) (ω : Ω),
        E n k.succ ω = E n k.castSucc ω +
          b (E n k.castSucc ω) * (T / n) +
          σ (E n k.castSucc ω) *
          (W.W ((((k.val + 1 : ℕ) : ℝ) * T / n)) ω -
            W.W (((k.val : ℝ) * T / n)) ω)) :
    ∀ (n : ℕ), 0 < n → ∀ k : Fin (n + 1), MemLp (E n k) 2 P := by
  intro n hn
  obtain ⟨L, hL0, hbL, hσL⟩ := hLip
  have hbc : Continuous b := em_lipschitz_continuous hL0 hbL
  have hσc : Continuous σ := em_lipschitz_continuous hL0 hσL
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ (j : ℕ) (hj : j ≤ n),
      MemLp (E n ⟨j, Nat.lt_succ_of_le hj⟩) 2 P ∧
        Measurable[ℱ ((j : ℝ) * T / n)] (E n ⟨j, Nat.lt_succ_of_le hj⟩) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h0 : E n ⟨0, Nat.lt_succ_of_le hj⟩ = fun _ => x₀ := funext (fun ω => hE0 n ω)
      rw [h0]
      exact ⟨memLp_const x₀, measurable_const⟩
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      obtain ⟨hmem, hmeas⟩ := ih (Nat.le_of_lt hjn)
      set t0 : ℝ := (j : ℝ) * T / n with ht0
      set t1 : ℝ := ((j + 1 : ℕ) : ℝ) * T / n with ht1
      have ht0nn : 0 ≤ t0 := by positivity
      have ht01 : t0 < t1 := by
        rw [ht0, ht1]; push_cast
        have : (j : ℝ) * T < ((j : ℝ) + 1) * T := by nlinarith
        exact div_lt_div_of_pos_right this hnR
      have hrec : E n ⟨j + 1, Nat.lt_succ_of_le hj⟩ = fun ω =>
          E n ⟨j, Nat.lt_succ_of_le (Nat.le_of_lt hjn)⟩ ω +
            b (E n ⟨j, Nat.lt_succ_of_le (Nat.le_of_lt hjn)⟩ ω) * (T / n) +
            σ (E n ⟨j, Nat.lt_succ_of_le (Nat.le_of_lt hjn)⟩ ω) * (W.W t1 ω - W.W t0 ω) :=
        funext (fun ω => hErec n hn ⟨j, hjn⟩ ω)
      set Ej : Ω → ℝ := E n ⟨j, Nat.lt_succ_of_le (Nat.le_of_lt hjn)⟩ with hEj
      -- the Brownian increment is square integrable
      have hΔmeas : Measurable (fun ω => W.W t1 ω - W.W t0 ω) :=
        (W.measurable_eval t1).sub (W.measurable_eval t0)
      have hΔ : MemLp (fun ω => W.W t1 ω - W.W t0 ω) 2 P := by
        have hlaw := W.increment_gaussian ht0nn ht01
        have hid : MemLp (id : ℝ → ℝ) 2 (P.map (fun ω => W.W t1 ω - W.W t0 ω)) := by
          rw [hlaw]; exact memLp_id_gaussianReal 2
        exact (memLp_map_measure_iff aestronglyMeasurable_id hΔmeas.aemeasurable).mp hid
      -- independence of the frozen coefficient and the increment
      have hσmeas : Measurable[ℱ t0] (fun ω => σ (Ej ω)) := hσc.measurable.comp hmeas
      have hind : IndepFun (fun ω => σ (Ej ω)) (fun ω => W.W t1 ω - W.W t0 ω) P := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_left (hW.indep ht0nn ht01) hσmeas.comap_le
      have hσΔ : MemLp (fun ω => σ (Ej ω) * (W.W t1 ω - W.W t0 ω)) 2 P :=
        em_indep_mul_memLp (em_lipschitz_comp_memLp hmem hL0 hσL) hΔ hind
      have hbEj : MemLp (fun ω => b (Ej ω) * (T / n)) 2 P :=
        (em_lipschitz_comp_memLp hmem hL0 hbL).mul_const (T / n)
      rw [hrec]
      refine ⟨(hmem.add hbEj).add hσΔ, ?_⟩
      have hle : ℱ t0 ≤ ℱ t1 := ℱ.mono ht01.le
      have hEj1 : Measurable[ℱ t1] Ej := hmeas.mono hle le_rfl
      exact (hEj1.add ((hbc.measurable.comp hEj1).mul measurable_const)).add
        ((hσc.measurable.comp hEj1).mul ((hW.measurable t1).sub ((hW.measurable t0).mono hle le_rfl)))
  intro k
  exact (key k.val (Nat.le_of_lt_succ k.isLt)).1
