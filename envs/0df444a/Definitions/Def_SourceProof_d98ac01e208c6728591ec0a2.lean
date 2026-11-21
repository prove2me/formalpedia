-- Prove2me | Definitions.Def_SourceProof_d98ac01e208c6728591ec0a2
-- name    : SourceProof_d98ac01e208c6728591ec0a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:20:45.913716+00:00
-- url     : https://prove2.me/theorems/574c7c2e-5522-4485-8cc3-7c3ae098f0e1
-- title:
--   LevyStochCalc source module: SourceProof_d98ac01e208c6728591ec0a2
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped_general` comes from the `LevyStochCalc.Ito.ItoFormulaStoppedLimit` module. The staged Lean declaration includes its source proof and dependency references. Some theorem-statement references have been redirected to generated helpers; formal type equivalence still requires certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStoppedLimit_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStoppedLimit_F001
import Definitions.Def_LevyStochCalc_Ito_VectorItoProcessDiff_F000
import Definitions.Def_SourceProof_7c1e051c1c1f9aebd6c80fa9
import Definitions.Def_SourceProof_c420c5d06462fb990bdab16f
import Definitions.Def_SourceProof_ec9b353ac49d35cb2a8d9aa5
import Definitions.Def_SourceProof_f726d8526913cd14b0792e3b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a path stopped at an arbitrary stopping time

A stopping time is approximated from above by the stopping times that stop at the first point of
a uniform grid strictly beyond it, which take finitely many values. The horizons clipped at the
approximations converge to the horizon clipped at the stopping time, the integrands cut off at the
approximations converge in the energy of a window to the integrand cut off at the stopping time,
and Itô's formula along the finite-range stopped paths passes to the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop` — the clipped horizons converge.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_gridStop` — the cut-off integrands converge
  in the energy of the window.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped_general` — the process stopped at a
  stopping time is the vector Itô process of the stopped coefficients.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general` — Itô's formula along the stopped path.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section ClipLimit

variable {Ω : Type u}

end ClipLimit

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Energy

section StoppedGeneral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

include hcoord in

theorem _root_.Prove2MeSourceProof.h_d98ac01e208c6728591ec0a2
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω) :
    IsVectorItoVersion W ℱ' hcoord (fun p k => Probability.stopped τ (H p k))
      (fun p k => Probability.measurable_uncurry_stopped hτ (hHm p k))
      (fun p k => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ (hHp p k))
      (fun p k => energy_lt_top_of_abs_le
        (fun ω s => Probability.abs_stopped_le τ (H p k) ω s) (hHs p k))
      X₀ (fun p => Probability.stopped τ (bdrift p))
      (fun t ω => X (clipTime τ t ω) ω) := by
  classical
  refine ⟨fun ω => (h.continuous_path ω).comp (LevyStochCalc.Brownian.Ito.continuous_clipTime τ ω), ?_, ?_⟩
  · intro t
    rcases le_or_gt t 0 with ht | ht
    · have hEq : (fun ω => X (LevyStochCalc.Brownian.Ito.clipTime τ t ω) ω) = X t := by
        funext ω
        refine congrArg (fun u => X u ω) ?_
        exact LevyStochCalc.Brownian.Ito.clipTime_of_le (le_trans (by exact_mod_cast ht) (hτ0 ω))
      rw [hEq]
      exact h.adapted t
    · refine LevyStochCalc.Brownian.Ito.stronglyMeasurable_of_tendsto_pi
        (F := fun m ω => X (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Brownian.Ito.gridStop τ t m) t ω) ω) (fun m => ?_) (fun ω => ?_)
      · exact _root_.Prove2MeSourceProof.h_12c97cbc46c921129491cc08 ℱ' (LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t m) h.adapted
          ((Finset.range (m + 1)).image (LevyStochCalc.Brownian.Ito.gridPt t m)) (LevyStochCalc.Brownian.Ito.gridStop_eq_or_top τ t m) t
      · exact ((h.continuous_path ω).tendsto _).comp (_root_.Prove2MeSourceProof.h_ec9b353ac49d35cb2a8d9aa5 τ hτ0 ht ω)
  · intro t ht
    rcases eq_or_lt_of_le ht with rfl | ht'
    · have hclip : ∀ ω, LevyStochCalc.Brownian.Ito.clipTime τ (0 : ℝ) ω = 0 := fun ω => LevyStochCalc.Brownian.Ito.clipTime_of_le (hτ0 ω)
      filter_upwards [h.ae_eq 0 le_rfl,
        _root_.Prove2MeSourceProof.h_284ef0277f5e06a285dc439e W ℱ' hcoord H hHm hHp hHs X₀ bdrift,
        _root_.Prove2MeSourceProof.h_284ef0277f5e06a285dc439e W ℱ' hcoord (fun p k => LevyStochCalc.Probability.stopped τ (H p k))
          (fun p k => LevyStochCalc.Probability.measurable_uncurry_stopped hτ (hHm p k))
          (fun p k => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ (hHp p k))
          (fun p k => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le
            (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ (H p k) ω s) (hHs p k))
          X₀ (fun p => LevyStochCalc.Probability.stopped τ (bdrift p))] with ω e1 e2 e3
      simp only [hclip ω]
      rw [e1, e2, e3]
    · have hσ : ∀ m : ℕ, MeasureTheory.IsStoppingTime ℱ' (LevyStochCalc.Brownian.Ito.gridStop τ t m) :=
        fun m => LevyStochCalc.Brownian.Ito.isStoppingTime_gridStop τ hτ t m
      have hσ0 : ∀ (m : ℕ) (ω : Ω), ((0 : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t m ω :=
        fun m ω => le_trans (hτ0 ω) (LevyStochCalc.Brownian.Ito.le_gridStop τ t m ω)
      have hmG : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
          (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) (H p k))) :=
        fun m p k => LevyStochCalc.Probability.measurable_uncurry_stopped (hσ m) (hHm p k)
      have hpG : ∀ (m : ℕ) (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
          (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) (H p k)) :=
        fun m p k => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e (hσ m) (hHp p k)
      have hqG : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) (H p k) ω s‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P < ⊤ :=
        fun m p k => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le
          (fun ω s => LevyStochCalc.Probability.abs_stopped_le (LevyStochCalc.Brownian.Ito.gridStop τ t m) (H p k) ω s) (hHs p k)
      have hmS : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
          (LevyStochCalc.Probability.stopped τ (H p k))) :=
        fun p k => LevyStochCalc.Probability.measurable_uncurry_stopped hτ (hHm p k)
      have hpS : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
          (LevyStochCalc.Probability.stopped τ (H p k)) :=
        fun p k => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ (hHp p k)
      have hqS : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖LevyStochCalc.Probability.stopped τ (H p k) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
        fun p k => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le
          (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ (H p k) ω s) (hHs p k)
      have hgrid : ∀ m : ℕ, (fun ω => X (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Brownian.Ito.gridStop τ t m) t ω) ω)
          =ᵐ[P] LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ' hcoord
            (fun p k => LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) (H p k)) (hmG m) (hpG m) (hqG m)
            X₀ (fun p => LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) (bdrift p)) t := by
        intro m
        exact (_root_.Prove2MeSourceProof.h_8cfa002050fede424ae29a90 W ℱ' hcoord h (hσ m) (hσ0 m)
          ((Finset.range (m + 1)).image (LevyStochCalc.Brownian.Ito.gridPt t m))
          (fun c hc => by
            obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
            exact LevyStochCalc.Brownian.Ito.gridPt_nonneg ht'.le m j)
          (LevyStochCalc.Brownian.Ito.gridStop_eq_or_top τ t m)).ae_eq t ht
      obtain ⟨ms, hmsge, hSI⟩ := _root_.Prove2MeSourceProof.h_7c1e051c1c1f9aebd6c80fa9 (μ := P)
        (ι := Fin n × Fin d)
        (u := fun m c ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
          (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) (H c.1 c.2)) (hmG m c.1 c.2) (hpG m c.1 c.2)
          (hqG m c.1 c.2) t ω)
        (v := fun c ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
          (LevyStochCalc.Probability.stopped τ (H c.1 c.2)) (hmS c.1 c.2) (hpS c.1 c.2) (hqS c.1 c.2) t ω)
        (fun m c => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
          (hmG m c.1 c.2) (hpG m c.1 c.2) (hqG m c.1 c.2) t).mono (ℱ'.le t)).measurable)
        (fun c => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
          (hmS c.1 c.2) (hpS c.1 c.2) (hqS c.1 c.2) t).mono (ℱ'.le t)).measurable)
        (fun c => by
          refine Filter.Tendsto.congr (fun m => ?_)
            (_root_.Prove2MeSourceProof.h_f726d8526913cd14b0792e3b hτ (hHm c.1 c.2) ht' (hHs c.1 c.2 t ht'))
          exact (_root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 (W.W c.2) ℱ' (hcoord c.2)
            (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) (H c.1 c.2))
            (LevyStochCalc.Probability.stopped τ (H c.1 c.2))
            (hmG m c.1 c.2) (hmS c.1 c.2) (hpG m c.1 c.2) (hpS c.1 c.2)
            (hqG m c.1 c.2) (hqS c.1 c.2) ht').symm)
      have hdrift : ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto
          (fun m : ℕ => ∫ s in Set.Icc (0 : ℝ) t,
            LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t m) (bdrift p) ω s ∂volume) Filter.atTop
          (𝓝 (∫ s in Set.Icc (0 : ℝ) t, LevyStochCalc.Probability.stopped τ (bdrift p) ω s ∂volume)) := by
        have hint : ∀ᵐ ω ∂P, ∀ p : Fin n,
            MeasureTheory.IntegrableOn (bdrift p ω) (Set.Icc (0 : ℝ) t) volume := by
          rw [MeasureTheory.ae_all_iff]
          exact fun p => LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm p) (hbq p t ht')
        filter_upwards [hint] with ω hω
        intro p
        refine MeasureTheory.tendsto_integral_of_dominated_convergence
          (fun s => |bdrift p ω s|) (fun m => ?_) (hω p).abs (fun m => ?_) ?_
        · exact (Measurable.of_uncurry_left
            (LevyStochCalc.Probability.measurable_uncurry_stopped (hσ m) (hbm p))).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun s => ?_
          rw [Real.norm_eq_abs]
          exact LevyStochCalc.Probability.abs_stopped_le (LevyStochCalc.Brownian.Ito.gridStop τ t m) (bdrift p) ω s
        · have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by simp
          filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull,
            MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs0 hsmem
          have hsne : s ≠ 0 := by simpa using hs0
          have hs : 0 < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
          by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
          · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun m _ => ?_
            have h1 : ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t m ω :=
              le_trans hτs (LevyStochCalc.Brownian.Ito.le_gridStop τ t m ω)
            simp [LevyStochCalc.Probability.stopped, h1, hτs]
          · rw [not_le] at hτs
            obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
              (_root_.Prove2MeSourceProof.h_c420c5d06462fb990bdab16f τ ht' ω hs hsmem.2 hτs)
            refine tendsto_atTop_of_eventually_const (i₀ := N) fun m hmN => ?_
            have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Brownian.Ito.gridStop τ t m ω := not_le.mpr (hN m hmN)
            have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := not_le.mpr hτs
            simp [LevyStochCalc.Probability.stopped, h1, h2]
      have hmsTop : Filter.Tendsto ms Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono hmsge Filter.tendsto_id
      filter_upwards [MeasureTheory.ae_all_iff.mpr hgrid, hSI, hdrift] with ω h1 h2 h3
      funext p
      have hB : Filter.Tendsto (fun i : ℕ => X₀ ω p
          + (∫ s in Set.Icc (0 : ℝ) t,
              LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t (ms i)) (bdrift p) ω s ∂volume)
          + ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (LevyStochCalc.Probability.stopped (LevyStochCalc.Brownian.Ito.gridStop τ t (ms i)) (H p k))
              (hmG (ms i) p k) (hpG (ms i) p k) (hqG (ms i) p k) t ω) Filter.atTop
          (𝓝 (X₀ ω p
            + (∫ s in Set.Icc (0 : ℝ) t, LevyStochCalc.Probability.stopped τ (bdrift p) ω s ∂volume)
            + ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (LevyStochCalc.Probability.stopped τ (H p k)) (hmS p k) (hpS p k) (hqS p k) t ω)) :=
        (tendsto_const_nhds.add ((h3 p).comp hmsTop)).add
          (tendsto_finsetSum _ fun k _ => h2 (p, k))
      have hA : Filter.Tendsto (fun i : ℕ => X (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Brownian.Ito.gridStop τ t (ms i)) t ω) ω p)
          Filter.atTop (𝓝 (X (LevyStochCalc.Brownian.Ito.clipTime τ t ω) ω p)) :=
        (((continuous_apply p).comp (h.continuous_path ω)).tendsto _).comp
          ((_root_.Prove2MeSourceProof.h_ec9b353ac49d35cb2a8d9aa5 τ hτ0 ht' ω).comp hmsTop)
      exact tendsto_nhds_unique hA
        (Filter.Tendsto.congr (fun i => (congrFun (h1 (ms i)) p).symm) hB)
end StoppedGeneral

end LevyStochCalc.Brownian.Ito


