-- Prove2me | Definitions.Def_SourceProof_ad87eebc265310df7bf2d34e
-- name    : SourceProof_ad87eebc265310df7bf2d34e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:09:32.550185+00:00
-- url     : https://prove2.me/theorems/6b9efebf-4d9b-4ccb-9f44-f6822ce16655
-- title:
--   LevyStochCalc source module: SourceProof_ad87eebc265310df7bf2d34e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_sq_sub_compensator` comes from the `LevyStochCalc.Brownian.ItoL2CompletionCompensator` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003
import Definitions.Def_SourceProof_4067b19605ae30f4039a5e7e
import Definitions.Def_SourceProof_bb0b34113d40cb04820c2414
import Definitions.Def_SourceProof_c343f3fddeb9bb9bc3b8ffc2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the compensated square of a simple integral

Weighted off-diagonal vanishing for products of Brownian increments, the clamped
expansion of the square of a difference of simple integrals, and the martingale
property of the compensated square
`(simpleIntegral W H t)² − ∫_{[0, t]} (H.eval u)² du` with respect to the
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_ad87eebc265310df7bf2d34e
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    MeasureTheory.Martingale
      (fun t ω => (simpleIntegral W G t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
      ℱ P := by
  have hImart : MeasureTheory.Martingale (fun u => LevyStochCalc.Brownian.Ito.simpleIntegral W G u) ℱ P :=
    _root_.Prove2MeSourceProof.h_79c2c57f6aeff6dbd6853f31 W ℱ hℱ G h_adapt
  -- `I_u ∈ L²(P)` at every time.
  have hIL2 : ∀ u, MeasureTheory.MemLp (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W G u ω) 2 P := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · have heq : (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W G u ω) = fun _ => (0 : ℝ) :=
        funext (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W G hu ω)
      rw [heq]; exact MeasureTheory.memLp_const 0
    · rcases le_or_gt u T with huT | huT
      · exact _root_.Prove2MeSourceProof.h_f748d28952e895ba511897bd W ℱ hℱ hT G h_adapt (le_of_lt hu) huT
      · have heq : (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W G u ω) = (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω) := by
          funext ω; unfold LevyStochCalc.Brownian.Ito.simpleIntegral
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hps : G.partition i.succ ≤ T :=
            le_trans (G.partition_strictMono.monotone (Fin.le_last _)) G.partition_le_T
          have hpc : G.partition i.castSucc ≤ T :=
            le_trans (G.partition_strictMono.monotone (Fin.le_last _)) G.partition_le_T
          rw [min_eq_left (le_trans hps (le_of_lt huT)),
            min_eq_left (le_trans hpc (le_of_lt huT)), min_eq_left hps, min_eq_left hpc]
        rw [heq]
        exact _root_.Prove2MeSourceProof.h_f748d28952e895ba511897bd W ℱ hℱ hT G h_adapt (le_of_lt hT)
          (le_refl T)
  -- `ξᵢ²` integrable.
  have hξ2int : ∀ i : Fin G.N, MeasureTheory.Integrable (fun ω => (G.ξ i ω) ^ 2) P := fun i => by
    obtain ⟨M, hM⟩ := G.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (M ^ 2))
      ((G.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  -- The compensator `A_u = ∫₀ᵘ G²` is integrable …
  have hAint : ∀ u, MeasureTheory.Integrable
      (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume) P := by
    intro u
    rcases le_or_gt 0 u with _ | hu
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun ω => ∑ i : Fin G.N,
              (min (G.partition i.succ) u - min (G.partition i.castSucc) u) * (G.ξ i ω) ^ 2 :=
        funext (fun ω => _root_.Prove2MeSourceProof.h_c343f3fddeb9bb9bc3b8ffc2 G ω)
      rw [heq]
      exact MeasureTheory.integrable_finsetSum _ (fun i _ => (hξ2int i).const_mul _)
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr hu)]; simp
      rw [heq]; exact MeasureTheory.integrable_const 0
  -- … and `ℱ_u`-adapted.
  have hA_adapt : ∀ u, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u)
      (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume) := by
    intro u
    rcases le_or_gt 0 u with _ | hu
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun ω => ∑ i : Fin G.N,
              (min (G.partition i.succ) u - min (G.partition i.castSucc) u) * (G.ξ i ω) ^ 2 :=
        funext (fun ω => _root_.Prove2MeSourceProof.h_c343f3fddeb9bb9bc3b8ffc2 G ω)
      rw [heq]
      refine Finset.stronglyMeasurable_fun_sum _ (fun i _ => ?_)
      by_cases hc : G.partition i.castSucc < u
      · have hle : ℱ.seq (G.partition i.castSucc) ≤ ℱ.seq u := ℱ.mono (le_of_lt hc)
        have hξ2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u) (fun ω => (G.ξ i ω) ^ 2) := by
          simpa [pow_two, Pi.mul_def] using ((h_adapt i).mono hle).mul ((h_adapt i).mono hle)
        exact hξ2.const_mul _
      · push Not at hc
        have hcoef : min (G.partition i.succ) u - min (G.partition i.castSucc) u = 0 := by
          rw [min_eq_right hc, min_eq_right
            (le_trans hc (le_of_lt (G.partition_strictMono Fin.castSucc_lt_succ)))]; ring
        rw [show (fun ω => (min (G.partition i.succ) u - min (G.partition i.castSucc) u)
              * (G.ξ i ω) ^ 2) = fun _ => (0 : ℝ) from by funext ω; rw [hcoef, zero_mul]]
        exact stronglyMeasurable_const
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr hu)]; simp
      rw [heq]; exact stronglyMeasurable_const
  -- the per-point clamp identity `(Δᵗ − Δˢ) = max s (min p t) − …`.
  have hclamp : ∀ (s t : ℝ), s ≤ t → ∀ p : ℝ,
      max s (min p t) = s + min p t - min p s := by
    intro s t hst p
    have h1 : min s (min p t) = min p s := by
      rw [min_comm s (min p t), min_assoc, min_eq_right hst]
    have h2 := max_add_min s (min p t)
    rw [h1] at h2; linarith
  -- conditional martingale identity for `0 ≤ s ≤ t`, via set integrals.
  have hcond : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      P[(fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s]
        =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume := by
    intro s t hs hst
    have hm : ℱ.seq s ≤ ‹MeasurableSpace Ω› := ℱ.le s
    have hIt2 : MeasureTheory.Integrable (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2) P :=
      (hIL2 t).integrable_sq
    have hIs2 : MeasureTheory.Integrable (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2) P :=
      (hIL2 s).integrable_sq
    have hIinc_int : MeasureTheory.Integrable
        (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2) P := by
      simpa [pow_two] using ((hIL2 t).sub (hIL2 s)).integrable_sq
    have hNs_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
        (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) := by
      have hIs2m : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
          (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2) := by
        simpa [pow_two, Pi.mul_def] using (hImart.stronglyAdapted s).mul (hImart.stronglyAdapted s)
      exact hIs2m.sub (hA_adapt s)
    refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm (hIt2.sub (hAint t))
      (fun B _ _ => (hIs2.sub (hAint s)).integrableOn) (fun B hB _ => ?_)
      hNs_meas.aestronglyMeasurable).symm
    -- goal: `∫_B N_s = ∫_B N_t`. Split both via term-mode `integral_sub`.
    simp only [Pi.sub_apply]
    have hsplitN_s : ∫ ω in B, ((LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P
        = (∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2 ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P :=
      MeasureTheory.integral_sub hIs2.integrableOn (hAint s).integrableOn
    have hsplitN_t : ∫ ω in B, ((LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) ∂P
        = (∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2 ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) ∂P :=
      MeasureTheory.integral_sub hIt2.integrableOn (hAint t).integrableOn
    have hsplitA : ∫ ω in B, ((∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P
        = (∫ ω in B, (∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P :=
      MeasureTheory.integral_sub (hAint t).integrableOn (hAint s).integrableOn
    -- set Pythagoras: `∫_B (I_t−I_s)² = ∫_B I_t² − ∫_B I_s²`.
    have hsetpyth : ∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2 ∂P
        = (∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2 ∂P)
          - ∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2 ∂P := by
      have hpyth := _root_.Prove2MeSourceProof.h_bb0b34113d40cb04820c2414 hImart (hIL2 s) (hIL2 t) hst
      calc ∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2 ∂P
          = ∫ ω in B, (P[(fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2)
              | ℱ.seq s]) ω ∂P := (MeasureTheory.setIntegral_condExp hm hIinc_int hB).symm
        _ = ∫ ω in B, ((P[(fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2) | ℱ.seq s]) ω
              - (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2) ∂P :=
            MeasureTheory.setIntegral_congr_ae (hm B hB) (hpyth.mono (fun ω hω _ => hω))
        _ = (∫ ω in B, (P[(fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2) | ℱ.seq s]) ω ∂P)
              - ∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2 ∂P :=
            MeasureTheory.integral_sub MeasureTheory.integrable_condExp.integrableOn
              hIs2.integrableOn
        _ = (∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2 ∂P)
              - ∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2 ∂P := by
            rw [MeasureTheory.setIntegral_condExp hm hIt2 hB]
    -- set isometry: `∫_B (I_t−I_s)² = ∫_B (A_t − A_s)`.
    have hgmeas : Measurable (Set.indicator B (fun _ => (1 : ℝ))) :=
      (measurable_const).indicator (hm B hB)
    have hg_bdd : ∀ ω, |Set.indicator B (fun _ => (1 : ℝ)) ω| ≤ 1 := fun ω => by
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω]; norm_num
      · rw [Set.indicator_of_notMem hω]; norm_num
    have hind : ∀ (F : Ω → ℝ), ∫ ω in B, F ω ∂P
        = ∫ ω, Set.indicator B (fun _ => (1 : ℝ)) ω * F ω ∂P := by
      intro F
      have heqf : (fun ω => Set.indicator B (fun _ => (1 : ℝ)) ω * F ω) = Set.indicator B F := by
        funext ω
        by_cases hω : ω ∈ B <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      rw [heqf, MeasureTheory.integral_indicator (hm B hB)]
    have hiso_set : ∫ ω in B, (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2 ∂P
        = ∫ ω in B, ((∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P := by
      rw [hind, _root_.Prove2MeSourceProof.h_4067b19605ae30f4039a5e7e W ℱ hℱ G h_adapt hs hst
        (stronglyMeasurable_const.indicator hB) hg_bdd]
      have hAdiff : ∀ ω, (∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume
          = ∑ i : Fin G.N, (max s (min (G.partition i.succ) t)
              - max s (min (G.partition i.castSucc) t)) * (G.ξ i ω) ^ 2 := by
        intro ω
        rw [_root_.Prove2MeSourceProof.h_c343f3fddeb9bb9bc3b8ffc2 G ω,
          _root_.Prove2MeSourceProof.h_c343f3fddeb9bb9bc3b8ffc2 G ω, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← sub_mul]; congr 1
        rw [hclamp s t hst (G.partition i.succ), hclamp s t hst (G.partition i.castSucc)]; ring
      rw [MeasureTheory.setIntegral_congr_fun (hm B hB) (fun ω _ => hAdiff ω), hind,
        show (fun ω => Set.indicator B (fun _ => (1 : ℝ)) ω
              * ∑ i : Fin G.N, (max s (min (G.partition i.succ) t)
                - max s (min (G.partition i.castSucc) t)) * (G.ξ i ω) ^ 2)
            = fun ω => ∑ i : Fin G.N, (max s (min (G.partition i.succ) t)
                - max s (min (G.partition i.castSucc) t))
                  * (Set.indicator B (fun _ => (1 : ℝ)) ω * (G.ξ i ω) ^ 2) from by
          funext ω; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
      rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
        (((hξ2int i).bdd_mul (c := 1) hgmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall
            (fun ω => (Real.norm_eq_abs _).le.trans (hg_bdd ω)))).const_mul _))]
      exact Finset.sum_congr rfl (fun i _ => by rw [MeasureTheory.integral_const_mul])
    -- combine: `∫_B N_s = ∫_B N_t`.
    rw [hsetpyth] at hiso_set
    linarith [hiso_set, hsplitN_s, hsplitN_t, hsplitA]
  -- assemble the full martingale (handle `s < 0` by the tower property).
  refine ⟨?_, fun s t hst => ?_⟩
  · intro u
    have hI2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u)
        (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G u ω) ^ 2) := by
      simpa [pow_two, Pi.mul_def] using (hImart.stronglyAdapted u).mul (hImart.stronglyAdapted u)
    exact hI2.sub (hA_adapt u)
  · rcases le_or_gt 0 s with hs | hs
    · exact hcond s t hs hst
    · have hN0 : (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G 0 ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), (G.eval u ω) ^ 2 ∂volume) =ᵐ[P] 0 := by
        filter_upwards with ω
        rw [LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W G (le_refl 0) ω,
          _root_.Prove2MeSourceProof.h_c343f3fddeb9bb9bc3b8ffc2 G ω]
        have : ∀ i : Fin G.N, (min (G.partition i.succ) (0 : ℝ)
            - min (G.partition i.castSucc) (0 : ℝ)) * (G.ξ i ω) ^ 2 = 0 := by
          intro i
          have hp1 : (0 : ℝ) ≤ G.partition i.succ := by
            have := G.partition_strictMono.monotone (Fin.zero_le i.succ)
            rwa [G.partition_zero] at this
          have hp2 : (0 : ℝ) ≤ G.partition i.castSucc := by
            have := G.partition_strictMono.monotone (Fin.zero_le i.castSucc)
            rwa [G.partition_zero] at this
          rw [min_eq_right hp1, min_eq_right hp2, sub_self, zero_mul]
        rw [Finset.sum_eq_zero (fun i _ => this i)]; simp
      have hle0 : ℱ.seq s ≤ ℱ.seq 0 := ℱ.mono (le_of_lt hs)
      rcases le_or_gt 0 t with ht | ht
      · have h0 := hcond 0 t (le_refl 0) ht
        calc P[(fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s]
            =ᵐ[P] P[P[(fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq 0] | ℱ.seq s] :=
              (MeasureTheory.condExp_condExp_of_le hle0 (ℱ.le 0)).symm
          _ =ᵐ[P] P[(fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G 0 ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s] :=
              MeasureTheory.condExp_congr_ae h0
          _ =ᵐ[P] P[(0 : Ω → ℝ) | ℱ.seq s] := MeasureTheory.condExp_congr_ae hN0
          _ =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume := by
              rw [MeasureTheory.condExp_zero]
              filter_upwards with ω
              rw [LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W G (le_of_lt hs) ω,
                Set.Icc_eq_empty (not_le.mpr hs)]
              simp
      · -- `t < 0`: both sides are a.e. `0`.
        have hNt : (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2
            - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) =ᵐ[P] 0 := by
          filter_upwards with ω
          rw [LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W G (le_of_lt ht) ω,
            Set.Icc_eq_empty (not_le.mpr ht)]; simp
        calc P[(fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s]
            =ᵐ[P] P[(0 : Ω → ℝ) | ℱ.seq s] := MeasureTheory.condExp_congr_ae hNt
          _ =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G s ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume := by
              rw [MeasureTheory.condExp_zero]
              filter_upwards with ω
              rw [LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W G (le_of_lt hs) ω,
                Set.Icc_eq_empty (not_le.mpr hs)]; simp
end LevyStochCalc.Brownian.Ito


