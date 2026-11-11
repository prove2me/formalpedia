-- Prove2me | Definitions.Def_Q220Uk004
-- name    : Q220Uk004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:41:50.144325+00:00
-- url     : https://prove2.me/theorems/af213e58-8b62-4391-beba-73866d05a8ad
-- title:
--   Definitions bundle Q220Uk004 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 245 declarations of OpenAI's Lean: 23 definitions and 222 theorems. The definitions and types are `OAI.UniformKServer.ActualRoster.retires`, `OAI.UniformKServer.GeometricMass.logarithm`, `OAI.UniformKServer.GeometricMass.nonheavy`, `OAI.UniformKServer.LevelMap.Data.heavyStationaryBudget`, `OAI.UniformKServer.LevelMap.Data.moverAllowance`, `OAI.UniformKServer.LevelMap.Data.stationaryAllowance`, `OAI.UniformKServer.LevelMap.Data.stationaryBudget`, `OAI.UniformKServer.PartitionLevel.Input.localLog`, `OAI.UniformKServer.PartitionLevel.Input.nonheavyMotion`, `OAI.UniformKServer.PartitionLevel.Input.smallError`, `OAI.UniformKServer.PartitionLevel.Input.unqualifiedMotion`, `OAI.UniformKServer.PartitionScales.Input.coefficient`, `OAI.UniformKServer.PartitionScales.Input.editCoefficient`, `OAI.UniformKServer.PartitionScales.Input.isNonheavy`, `OAI.UniformKServer.PilotCompact.coarseConstant`, `OAI.UniformKServer.PilotCompact.momentRatio`, `OAI.UniformKServer.PilotCompact.shellRatio`, `OAI.UniformKServer.PilotEdits.moverCost`, `OAI.UniformKServer.PilotEdits.potential`, `OAI.UniformKServer.PilotFamily.template`, `OAI.UniformKServer.PilotFamily.weight`, `OAI.UniformKServer.ShortRoster.State.Valid`, `OAI.UniformKServer.ShortRoster.editedValue`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_ActualEditCosts`, `UniformKServer_ActualLevelPilot`, `UniformKServer_ActualPartitions`, `UniformKServer_ActualPilot`, `UniformKServer_ActualRoster`, `UniformKServer_CausalShort`, `UniformKServer_ChronologicalRoster`, `UniformKServer_CooldownLabels`, `UniformKServer_DyadicTiers`, `UniformKServer_FiniteProbability`, `UniformKServer_FlowAuxiliary`, `UniformKServer_GeometricMass`, `UniformKServer_HeavyEditPayment`, `UniformKServer_HeavyEditRamp`, `UniformKServer_HeavyPilot`, `UniformKServer_HeavyProcessEdits`, `UniformKServer_HeavyRadius`, `UniformKServer_HeavyRecordGeometry`, `UniformKServer_HeavyRecords`, `UniformKServer_KeyEdits`, `UniformKServer_LevelAllowances`, `UniformKServer_LevelErrorMass`, `UniformKServer_LevelHeavyEdits`, `UniformKServer_LevelKeyLedger`, `UniformKServer_LevelMassLedger`, `UniformKServer_LevelMoverBudget`, `UniformKServer_LevelSerial`, `UniformKServer_LevelTierEdits`, `UniformKServer_LevelTierLedger`, `UniformKServer_PartitionCausal`, `UniformKServer_PartitionLevel`, `UniformKServer_PartitionScales`, `UniformKServer_PilotCapacity`, `UniformKServer_PilotCompact`, `UniformKServer_PilotConcentration`, `UniformKServer_PilotCredits`, `UniformKServer_PilotDeletion`, `UniformKServer_PilotEdits`, `UniformKServer_PilotExtension`, `UniformKServer_PilotFamily`, `UniformKServer_PilotRelocation`, `UniformKServer_PilotSlope`, `UniformKServer_PilotStability`, `UniformKServer_ReverseScales`, `UniformKServer_ScaleAllowances`, `UniformKServer_ShortRoster`, `UniformKServer_ShortRosterValidity`, `UniformKServer_SmallScales`, `UniformKServer_TierInner`, `UniformKServer_TierInsertion`, `UniformKServer_TierKeyEdits`, `UniformKServer_TierKeyProcess`, `UniformKServer_TierKeys`, `UniformKServer_TierLabeledEdits`, `UniformKServer_TierParameters`, `UniformKServer_TierPilot`, `UniformKServer_TierRadius`, `UniformKServer_TierRetirement`, `UniformKServer_TierShortSchedule`.
--
--   **Imports.** It imports the bundles `Q220Uk000` and `Q220Uk001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q220Uk007` and `Q220Uk008`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_Q220Uk000
import Definitions.Def_Q220Uk001

section
-- module Solutions.Q220_UK.UniformKServer_PilotCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

                                                                               
                                                                            
namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem bumpA_zero (σ R v : ℝ) (hR : 0 < R) (hv : 2*R ≤ v) : bumpA σ R v = 0 := by
  unfold bumpA
  have hnot : ¬v ≤ R := by linarith
  rw [ite_eq_right hnot]
  split_ifs with hv'
  · have he : v = 2*R := by linarith
    rw [he]
    field_simp
    ring
  · rfl

theorem weighted_bumpA (σ R v z : ℝ) (hR : 0 < R) (hz : 0 ≤ z) :
    z*bumpA σ R v ≤ max (z-gate R v) 0 := by
  by_cases hv : v ≤ 2*R
  · have hg : gate R v = 0 := gate_eq_zero R v hR (by linarith)
    rw [hg, sub_zero, max_eq_left hz]
    nlinarith [mul_le_mul_of_nonneg_left (bumpA_bounds σ R v hR).2 hz]
  · rw [bumpA_zero σ R v hR (by linarith), mul_zero]
    exact le_max_right _ _

theorem surcharge_sum (r σ R : ℝ) (hR : 0 < R) (g z : X → ℝ)
    (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z) (p : X) :
    (∑ s, z s*(1+g s)*bumpA σ R (dist s p/r)) ∈ Set.Icc (0:ℝ) 2 := by
  have hsum : (∑ s, z s*bumpA σ R (dist s p/r)) ≤ 1 :=
    (Finset.sum_le_sum fun s _ => weighted_bumpA σ R _ _ hR (hz.1 s)).trans (hz.2.1 p)
  constructor
  · apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (mul_nonneg (hz.1 s) (by linarith [(hg s).1])) (bumpA_bounds σ R _ hR).1
  · calc
      _ ≤ ∑ s, 2*(z s*bumpA σ R (dist s p/r)) := by
        apply Finset.sum_le_sum
        intro s hs
        have hnn := mul_nonneg (hz.1 s) (bumpA_bounds σ R (dist s p/r) hR).1
        have hm := mul_le_mul_of_nonneg_left (show 1+g s ≤ 2 by linarith [(hg s).2]) hnn
        first | (convert hm using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))
      _ = 2*∑ s, z s*bumpA σ R (dist s p/r) := (Finset.mul_sum ..).symm
      _ ≤ 2 := by linarith

theorem integrand_bounds (r σ R : ℝ) (_hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (g z : X → ℝ)
    (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z) (p : X) :
    integrand r σ R g z p ∈ Set.Icc (0:ℝ) 514 := by
  have hB := weighted_bumpB_sum r σ R hσ hσ1 hR z hz p
  have hA := surcharge_sum r σ R (by linarith) g z hg hz p
  have hn : 0 ≤ (1+g p)*(1-∑ s, z s*bumpB σ (dist s p/r)) :=
    mul_nonneg (by linarith [(hg p).1]) (by linarith [hB.2])
  have hu : (1+g p)*(1-∑ s, z s*bumpB σ (dist s p/r)) ≤ 2 := by
    have hh := mul_le_mul (show 1+g p ≤ 2 by linarith [(hg p).2])
      (show 1-∑ s, z s*bumpB σ (dist s p/r) ≤ 1 by linarith [hB.1])
      (show 0 ≤ 1-∑ s, z s*bumpB σ (dist s p/r) by linarith [hB.2]) (by norm_num : (0:ℝ) ≤ 2)
    simpa using hh
  unfold integrand
  constructor <;> linarith [hA.1, hA.2]

theorem value_bounds (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (μ g : X → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ value r σ R μ g ∧ value r σ R μ g ≤ 2*r*∑ p, μ p := by
  obtain ⟨z, hz, he, hmin⟩ := minimum_exists r σ R μ g
  constructor
  · rw [← he]
    apply mul_nonneg hr.le
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (hμ p) (integrand_bounds r σ R hr hσ hσ1 hR g z hg hz p).1
  · have h0 := value_le r σ R μ g (fun _ => 0) (zero_feasible r σ R)
    have hb : objective r σ R μ g (fun _ => 0) ≤ 2*r*∑ p, μ p := by
      simp only [objective, integrand, zero_mul, Finset.sum_const_zero, sub_zero, mul_one, mul_zero,
        add_zero]
      calc
        _ ≤ r*∑ p, 2*μ p := by
          apply mul_le_mul_of_nonneg_left _ hr.le
          apply Finset.sum_le_sum
          intro p hp
          nlinarith [mul_le_mul_of_nonneg_left (hg p).2 (hμ p)]
        _ = _ := by rw [← Finset.mul_sum]; ring
    exact h0.trans hb


/-! Local optimality construction. -/


end
end UniformKServer.PilotCompact
end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

omit [Fintype X] in
theorem bumpA_inner_lower (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (x s p : X) (hnear : σ/4 ≤ dist s x/r) (hfar : dist s x/r ≤ R/2)
    (hp : dist x p ≤ γ*r) : (225:ℝ)/4096 ≤ bumpA σ R (dist s p/r) := by
  have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hp
  have ht := normalized_triangle r hr s x p
  have ht' := normalized_triangle r hr s p x
  rw [dist_comm p x] at ht'
  have hu : dist s p/r ≤ R := by linarith
  have hl : (15:ℝ)/64*σ ≤ dist s p/r := by linarith
  have hnon : 0 ≤ dist s p/r := div_nonneg dist_nonneg hr.le
  have hsq : (225:ℝ)/4096 ≤ (dist s p/r)^2/σ^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
    nlinarith [sq_nonneg (dist s p/r-(15:ℝ)/64*σ)]
  unfold bumpA
  rw [ite_eq_left hu]
  exact le_min hsq (by norm_num)

omit [Fintype X] in
theorem coefficient_lower (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (g : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x s p : X) (hnear : σ/4 ≤ dist s x/r) (hfar : dist s x/r ≤ R/2) :
    (225:ℝ)/16*(if dist x p ≤ γ*r then 1 else 0) -
        2*(if dist x p ≤ (100*R)*r then 1 else 0) ≤ coefficient r σ R g s p := by
  have ha := bumpA_bounds σ R (dist s p/r) (show 0<R by linarith)
  have hb := bumpB_bounds σ (dist s p/r)
  have hlo : (225:ℝ)/4096*(if dist x p ≤ γ*r then 1 else 0) ≤ bumpA σ R (dist s p/r) := by
    split_ifs with hp
    · simpa using bumpA_inner_lower r σ R γ hr hσ hσ1 hR hγσ x s p hnear hfar hp
    · simpa using ha.1
  have hhi := bumpB_outer_bound r σ R hr hσ hσ1 hR x s p hfar
  have hterm : 256*bumpA σ R (dist s p/r)-2*bumpB σ (dist s p/r) ≤
      coefficient r σ R g s p := by
    unfold coefficient
    nlinarith [mul_nonneg (hg s).1 ha.1,
      mul_nonneg (show 0 ≤ 1-g p by linarith [(hg p).2]) hb.1]
  linarith

theorem middle_site_zero [DecidableEq X] (r σ R γ δ : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (_hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g)
    (s : X) (hnear : σ/4 ≤ dist s x/r) (hfar : dist s x/r ≤ R/2) :
    z s = 0 := by
  have hc : (225:ℝ)/16 * ballMass r γ μ x - 2*ballMass r (100*R) μ x ≤
      ∑ p, μ p*coefficient r σ R g s p := by
    have he : (225:ℝ)/16 * ballMass r γ μ x - 2*ballMass r (100*R) μ x =
        ∑ p, μ p*((225:ℝ)/16*(if dist x p ≤ γ*r then 1 else 0) -
          2*(if dist x p ≤ (100*R)*r then 1 else 0)) := by
      unfold ballMass
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring
    rw [he]
    exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
      (coefficient_lower r σ R γ hr hσ hσ1 hR hγσ g hg x s p hnear hfar) (hμ p)
  have hδle : δ ≤ 1 := by linarith
  have hout : ballMass r (100*R) μ x ≤ 2*ballMass r γ μ x := by
    exact hconc.trans (by nlinarith [mul_nonneg (show 0≤1-δ by linarith) hM.le])
  have hpos : 0 < ∑ p, μ p*coefficient r σ R g s p := by linarith
  have hdel := value_le r σ R μ g (Function.update z s 0) (erase_feasible r σ R z hz s)
  rw [← hmin] at hdel
  have he := objective_erase r σ R μ g z s
  rcases (hz.1 s).eq_or_lt with hzero | hposz
  · exact hzero.symm
  · have hprod := mul_pos (mul_pos hr hposz) hpos
    linarith

omit [Fintype X] in
theorem insertUnit_le [DecidableEq X] (r R : ℝ) (z : X → ℝ)
    (hz : ∀ s, 0 ≤ z s) (x s : X) (hne : s ≠ x) : insertUnit r R z x s ≤ z s := by
  unfold insertUnit
  rw [ite_eq_right hne]
  split_ifs <;> first | exact hz s | rfl

omit [Fintype X] in
theorem insertUnit_positive [DecidableEq X] (r R : ℝ) (z : X → ℝ)
    (x s : X) (hne : s ≠ x) (hp : 0 < insertUnit r R z x s) :
    (50*R)*r < dist s x ∧ 0 < z s := by
  unfold insertUnit at hp
  rw [ite_eq_right hne] at hp
  split_ifs at hp with h
  · linarith
  · exact ⟨lt_of_not_ge h, hp⟩

theorem insertUnit_feasible [DecidableEq X] (r σ R : ℝ)
    (hr : 0 < r) (_hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (z : X → ℝ) (hz : feasible r σ R z) (x : X) :
    feasible r σ R (insertUnit r R z x) := by
  refine ⟨insertUnit_nonneg r R z hz.1 x, ?_, ?_⟩
  · intro p
    by_cases hfar : 20*R ≤ dist x p/r
    · have hg := gate_one R (dist x p/r) (by linarith) hfar
      apply le_trans (Finset.sum_le_sum ?_) (hz.2.1 p)
      intro s hs
      by_cases heq : s=x
      · subst s
        rw [insertUnit_at, hg]
        norm_num
      · exact max_le_max (sub_le_sub_right (insertUnit_le r R z hz.1 x s heq) _) le_rfl
    · have hother : ∀ s : X, s ≠ x →
          max (insertUnit r R z x s-gate R (dist s p/r)) 0 = 0 := by
        intro s hne
        by_cases hcut : dist s x ≤ (50*R)*r
        · simp only [insertUnit, ite_eq_right hne, ite_eq_left hcut]
          exact max_eq_right (by linarith [gate_nonneg R (dist s p/r)])
        · have hsx : 50*R < dist s x/r := (lt_div_iff₀ hr).mpr (lt_of_not_ge hcut)
          have ht := normalized_triangle r hr s p x
          rw [dist_comm p x] at ht
          have hsp : 20*R ≤ dist s p/r := by linarith
          rw [gate_one R _ (by linarith) hsp]
          apply max_eq_right
          exact sub_nonpos.mpr ((insertUnit_le r R z hz.1 x s hne).trans (feasible_upper r σ R z hz s))
      have he : (∑ s, max (insertUnit r R z x s-gate R (dist s p/r)) 0) =
          max (1-gate R (dist x p/r)) 0 := by
        rw [Finset.sum_eq_single x]
        · rw [insertUnit_at]
        · intro s hs hne
          exact hother s hne
        · simp
      rw [he]
      exact max_le (by linarith [gate_nonneg R (dist x p/r)]) (by norm_num)
  · intro s s' hne hs hs'
    have hsep : 5*σ*r ≤ 50*R*r := by nlinarith
    by_cases hx : s=x
    · subst s
      have hp := insertUnit_positive r R z x s' (Ne.symm hne) hs'
      rw [dist_comm]
      exact hsep.trans hp.1.le
    by_cases hx' : s'=x
    · subst s'
      exact hsep.trans (insertUnit_positive r R z x s hx hs).1.le
    exact hz.2.2 s s' hne (insertUnit_positive r R z x s hx hs).2
      (insertUnit_positive r R z x s' hx' hs').2

theorem old_inner_lower (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγ : 0 < γ) (hγσ : γ ≤ σ/64)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z)
    (x p : X) (hp : dist x p ≤ γ*r)
    (hmid : ∀ s, σ/4 ≤ dist s x/r → dist s x/r ≤ R/2 → z s = 0) :
    1-nearWeight r σ z x ≤ integrand r σ R g z p := by
  have hB := nearWeight_bounds r σ R γ hr hσ hσ1 hR hγ hγσ z hz x hmid
  have hA := surcharge_sum r σ R (show 0<R by linarith) g z hg hz p
  unfold integrand
  rw [inner_bump_sum r σ R γ hr hσ hσ1 hR hγσ z x p hp hmid]
  nlinarith [mul_nonneg (hg p).1 (show 0≤1-nearWeight r σ z x by linarith [hB.2]), hA.1]

theorem new_inner_upper [DecidableEq X] (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x p : X) (hp : dist x p ≤ γ*r) :
    integrand r σ R g (insertUnit r R z x) p ≤ 512/σ^2*(dist x p/r)^2 := by
  have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hp
  have hzero : ∀ s : X, s ≠ x →
      insertUnit r R z x s*bumpB σ (dist s p/r) = 0 ∧
      insertUnit r R z x s*(1+g s)*bumpA σ R (dist s p/r) = 0 := by
    intro s hne
    by_cases hc : dist s x ≤ (50*R)*r
    · simp [insertUnit, hne, hc]
    · have hsx : 50*R < dist s x/r := (lt_div_iff₀ hr).mpr (lt_of_not_ge hc)
      have ht := normalized_triangle r hr s p x
      rw [dist_comm p x] at ht
      rw [bumpB_zero σ _ hσ (by linarith), bumpA_zero σ R _ (by linarith) (by linarith)]
      simp
  have hB : (∑ s, insertUnit r R z x s*bumpB σ (dist s p/r)) = 1 := by
    rw [Finset.sum_eq_single x]
    · rw [insertUnit_at, one_mul, bumpB_one σ _ hσ (by linarith)]
    · intro s hs hne
      exact (hzero s hne).1
    · simp
  have hA : (∑ s, insertUnit r R z x s*(1+g s)*bumpA σ R (dist s p/r)) =
      (1+g x)*bumpA σ R (dist x p/r) := by
    rw [Finset.sum_eq_single x]
    · rw [insertUnit_at, one_mul]
    · intro s hs hne
      exact (hzero s hne).2
    · simp
  have ha : bumpA σ R (dist x p/r) ≤ (dist x p/r)^2/σ^2 := by
    unfold bumpA
    rw [ite_eq_left (by linarith : dist x p/r ≤ R)]
    exact min_le_left _ _
  have haa := (bumpA_bounds σ R (dist x p/r) (show 0<R by linarith)).1
  unfold integrand
  rw [hB, hA]
  have hh := mul_le_mul_of_nonneg_right (show 1+g x ≤ 2 by linarith [(hg x).2]) haa
  have he : 512/σ^2*(dist x p/r)^2 = 512*((dist x p/r)^2/σ^2) := by ring
  rw [he]
  nlinarith

theorem unchanged_outside [DecidableEq X] (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (g z : X → ℝ) (x p : X)
    (hp : (100*R)*r < dist x p) :
    integrand r σ R g (insertUnit r R z x) p = integrand r σ R g z p := by
  have hv : 100*R < dist x p/r := (lt_div_iff₀ hr).mpr hp
  have hterm : ∀ s : X,
      insertUnit r R z x s*bumpB σ (dist s p/r) = z s*bumpB σ (dist s p/r) ∧
      insertUnit r R z x s*(1+g s)*bumpA σ R (dist s p/r) =
        z s*(1+g s)*bumpA σ R (dist s p/r) := by
    intro s
    by_cases hc : dist s x ≤ (50*R)*r
    · have hsx : dist s x/r ≤ 50*R := (div_le_iff₀ hr).mpr hc
      have ht := normalized_triangle r hr x s p
      rw [dist_comm x s] at ht
      rw [bumpB_zero σ _ hσ (by linarith), bumpA_zero σ R _ (by linarith) (by linarith)]
      simp
    · have hne : s ≠ x := by
        intro he
        subst s
        simp only [dist_self, not_le] at hc
        have : 0 ≤ 50*R*r := by positivity
        linarith
      simp [insertUnit, hne, hc]
  have hB := Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => (hterm s).1)
  have hA := Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => (hterm s).2)
  unfold integrand
  rw [hB, hA]

theorem innerMoment_bounds (r γ : ℝ) (hr : 0 < r) (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X) :
    0 ≤ innerMoment r γ μ x ∧ innerMoment r γ μ x ≤ γ*ballMass r γ μ x := by
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    split_ifs
    · exact mul_nonneg (hμ p) (div_nonneg dist_nonneg hr.le)
    · rfl
  · unfold innerMoment ballMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    split_ifs with hd
    · have hv := (div_le_iff₀ hr).mpr hd
      nlinarith [mul_le_mul_of_nonneg_left hv (hμ p)]
    · simp


end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
theorem near_deficit [DecidableEq X] (r σ R γ δ : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g) :
    (1-nearWeight r σ z x)*ballMass r γ μ x ≤
      (512*γ/σ^2)*innerMoment r γ μ x +
        514*(ballMass r (100*R) μ x-ballMass r γ μ x) := by
  have hmid := middle_site_zero r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
    μ g z hμ hg x hM hconc hz hmin
  let w := insertUnit r R z x
  have hw : feasible r σ R w := insertUnit_feasible r σ R hr hσ hσ1 hR z hz x
  have hpoint : ∀ p : X,
      integrand r σ R g w p - integrand r σ R g z p ≤
        (if dist x p ≤ γ*r then (512*γ/σ^2)*(dist x p/r)-(1-nearWeight r σ z x) else 0) +
        514*((if dist x p ≤ (100*R)*r then 1 else 0)-(if dist x p ≤ γ*r then 1 else 0)) := by
    intro p
    by_cases hi : dist x p ≤ γ*r
    · have ho : dist x p ≤ (100*R)*r := hi.trans (by nlinarith)
      simp only [ite_eq_left hi, ite_eq_left ho]
      have hu := new_inner_upper r σ R γ hr hσ hσ1 hR hγσ g z hg x p hi
      have hl := old_inner_lower r σ R γ hr hσ hσ1 hR hγ hγσ g z hg hz x p hi hmid
      have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hi
      have hsq : (dist x p/r)^2 ≤ γ*(dist x p/r) := by
        nlinarith [mul_nonneg (div_nonneg (dist_nonneg (x := x) (y := p)) hr.le) (sub_nonneg.mpr hv)]
      have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 512/σ^2 by positivity)
      have hm' : 512/σ^2*(dist x p/r)^2 ≤ (512*γ/σ^2)*(dist x p/r) := by
        calc
          _ ≤ (512/σ^2)*(γ*(dist x p/r)) := hm
          _ = _ := by ring
      change integrand r σ R g (insertUnit r R z x) p - integrand r σ R g z p ≤ _
      linarith only [hu, hl, hm']
    · by_cases ho : dist x p ≤ (100*R)*r
      · simp only [ite_eq_right hi, ite_eq_left ho]
        have hu := (integrand_bounds r σ R hr hσ hσ1 hR g w hg hw p).2
        have hl := (integrand_bounds r σ R hr hσ hσ1 hR g z hg hz p).1
        linarith
      · simp only [ite_eq_right hi, ite_eq_right ho]
        change integrand r σ R g (insertUnit r R z x) p - integrand r σ R g z p ≤ _
        rw [unchanged_outside r σ R hr hσ hσ1 hR g z x p (lt_of_not_ge ho)]
        norm_num
  have hs := Finset.sum_le_sum (fun (p : X) (_ : p ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint p) (hμ p))
  have he : (∑ p, μ p*((if dist x p ≤ γ*r then (512*γ/σ^2)*(dist x p/r)-
        (1-nearWeight r σ z x) else 0) +
        514*((if dist x p ≤ (100*R)*r then 1 else 0)-(if dist x p ≤ γ*r then 1 else 0)))) =
      (512*γ/σ^2)*innerMoment r γ μ x - (1-nearWeight r σ z x)*ballMass r γ μ x +
        514*(ballMass r (100*R) μ x-ballMass r γ μ x) := by
    unfold innerMoment ballMass
    simp only [Finset.mul_sum, mul_sub]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> ring
  rw [he] at hs
  have hmin' := value_le r σ R μ g w hw
  rw [← hmin] at hmin'
  have hcost : 0 ≤ ∑ p, μ p*(integrand r σ R g w p-integrand r σ R g z p) := by
    unfold objective at hmin'
    have hh : (∑ p, μ p*integrand r σ R g z p) ≤ ∑ p, μ p*integrand r σ R g w p :=
      (mul_le_mul_iff_right₀ hr).mp hmin'
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    linarith
  linarith

theorem nearWeight_large [DecidableEq X] (r σ R γ δ : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g) :
    (3:ℝ)/4 ≤ nearWeight r σ z x := by
  have hd := near_deficit r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
    μ g z hμ hg x hM hconc hz hmin
  have hm := (innerMoment_bounds r γ hr μ hμ x).2
  have hsq : 512*γ^2/σ^2 ≤ (1:ℝ)/8 := by
    apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
    nlinarith [sq_nonneg (σ-64*γ), mul_nonneg (sub_nonneg.mpr hγσ) hγ.le]
  have hc : 0 ≤ 512*γ/σ^2 := by positivity
  have hmoment : (512*γ/σ^2)*innerMoment r γ μ x ≤ (1:ℝ)/8*ballMass r γ μ x := by
    calc
      _ ≤ (512*γ/σ^2)*(γ*ballMass r γ μ x) := mul_le_mul_of_nonneg_left hm hc
      _ = (512*γ^2/σ^2)*ballMass r γ μ x := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq hM.le
  have hshell : 514*(ballMass r (100*R) μ x-ballMass r γ μ x) ≤
      (1:ℝ)/8*ballMass r γ μ x := by
    have hh := mul_le_mul_of_nonneg_right (show 514*δ ≤ (1:ℝ)/8 by linarith) hM.le
    nlinarith
  have hprod : (3/4-nearWeight r σ z x)*ballMass r γ μ x ≤ 0 := by nlinarith
  by_contra hh
  have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hM
  linarith

theorem nearWeight_eq_site (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (z : X → ℝ) (hz : feasible r σ R z) (x s : X)
    (hs : 0 < z s) (hn : dist s x/r < σ/4) : nearWeight r σ z x = z s := by
  classical
  unfold nearWeight
  rw [Finset.sum_eq_single s]
  · rw [ite_eq_left hn]
  · intro t ht hne
    split_ifs with htnear
    · have hnpos : ¬0<z t := by
        intro htp
        exact hne (near_positive_unique r σ R hr hσ z hz x s t hs htp hn htnear)
      linarith [hz.1 t]
    · rfl
  · simp

theorem near_site_exists [DecidableEq X] (r σ R γ δ : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hγ : 0 < γ) (hγσ : γ ≤ σ/64) (hδ : 0 < δ) (hδbound : δ ≤ 1/4112)
    (μ g z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (x : X) (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*R) μ x ≤ (1+δ)*ballMass r γ μ x)
    (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g) :
    ∃ s, dist s x/r < σ/4 ∧ (3:ℝ)/4 ≤ z s ∧
      (∀ s', 0 < z s' → dist s' x/r < σ/4 → s'=s) ∧
      1-z s ≤ (512*γ/σ^2)*(innerMoment r γ μ x/ballMass r γ μ x) +
        514*((ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x) := by
  have hl := nearWeight_large r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
    μ g z hμ hg x hM hconc hz hmin
  have hp : 0 < ∑ s, if dist s x/r < σ/4 then z s else 0 := lt_of_lt_of_le (by norm_num) hl
  have hn : ∀ s ∈ (Finset.univ : Finset X), 0 ≤ (if dist s x/r < σ/4 then z s else 0) := by
    intro s hs
    split_ifs <;> first | exact hz.1 s | rfl
  obtain ⟨s, hs, hspos⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp hp
  have hnear : dist s x/r < σ/4 := by
    by_contra hn
    rw [ite_eq_right hn] at hspos
    linarith
  rw [ite_eq_left hnear] at hspos
  have he := nearWeight_eq_site r σ R hr hσ z hz x s hspos hnear
  rw [he] at hl
  refine ⟨s, hnear, hl, ?_, ?_⟩
  · intro t ht hn
    exact near_positive_unique r σ R hr hσ z hz x s t hspos ht hnear hn
  · have hd := near_deficit r σ R γ δ hr hσ hσ1 hR hγ hγσ hδ hδbound
      μ g z hμ hg x hM hconc hz hmin
    rw [he] at hd
    have heq : (512*γ/σ^2)*(innerMoment r γ μ x/ballMass r γ μ x) +
        514*((ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x) =
        ((512*γ/σ^2)*innerMoment r γ μ x +
          514*(ballMass r (100*R) μ x-ballMass r γ μ x))/ballMass r γ μ x := by ring
    rw [heq]
    exact (le_div_iff₀ hM).mpr hd

/-! Scalar slope proofs for exact compact pilot. -/

theorem bumpA_tail (σ R u : ℝ) (hR : 0 < R) (hu : R < u) :
    bumpA σ R u = max (2-u/R) 0 := by
  unfold bumpA
  rw [ite_eq_right (not_le_of_gt hu)]
  split_ifs with h2
  · exact (max_eq_left (by have hh := (div_le_iff₀ hR).mpr h2; linarith)).symm
  · have hh : 2 < u/R := (lt_div_iff₀ hR).mpr (lt_of_not_ge h2)
    exact (max_eq_right (by linarith)).symm

theorem bumpA_at_R (σ R : ℝ) (hσ : 0 < σ) (hRσ : σ ≤ R) : bumpA σ R R = 1 := by
  unfold bumpA
  rw [ite_eq_left le_rfl]
  apply min_eq_right
  apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
  have hR : 0 ≤ R := hσ.le.trans hRσ
  nlinarith

theorem bumpA_cross (σ R u v : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hR : 256 ≤ R) (hu : 0 ≤ u) (huR : u ≤ R) (hRv : R < v) :
    |bumpA σ R u-bumpA σ R v| ≤ (2/σ)*(v-u) := by
  have hRpos : 0 < R := by linarith
  have hf : min (R^2/σ^2) 1 = 1 := by
    have he := bumpA_at_R σ R hσ (by linarith)
    simpa only [bumpA, ite_eq_left le_rfl] using he
  have hg : max (2-R/R) 0 = 1 := by norm_num [ne_of_gt hRpos]
  have hqi := quadratic_abs σ u R hσ hu hRpos.le
  rw [hf, abs_of_nonpos (sub_nonpos.mpr huR)] at hqi
  have hti := tail_abs R R v hRpos
  rw [hg, abs_of_nonpos (sub_nonpos.mpr hRv.le)] at hti
  have hC : 1/R ≤ 2/σ := by
    apply (div_le_div_iff₀ hRpos hσ).mpr
    linarith
  have hlo : |bumpA σ R u-1| ≤ (2/σ)*(R-u) := by
    simpa only [bumpA, ite_eq_left huR, neg_sub] using hqi
  have hhi : |1-bumpA σ R v| ≤ (2/σ)*(v-R) := by
    rw [bumpA_tail σ R v hRpos hRv]
    have ht' : |1-max (2-v/R) 0| ≤ (1/R)*(v-R) := by
      simpa only [neg_sub] using hti
    exact ht'.trans (mul_le_mul_of_nonneg_right hC (by linarith))
  calc
    _ ≤ |bumpA σ R u-1|+|1-bumpA σ R v| := abs_sub_le _ _ _
    _ ≤ (2/σ)*(R-u)+(2/σ)*(v-R) := add_le_add hlo hhi
    _ = _ := by ring

theorem bumpA_lipschitz (σ R u v : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hR : 256 ≤ R) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |bumpA σ R u-bumpA σ R v| ≤ (2/σ)*|u-v| := by
  have hRpos : 0 < R := by linarith
  by_cases huR : u ≤ R
  · by_cases hvR : v ≤ R
    · simpa only [bumpA, ite_eq_left huR, ite_eq_left hvR] using quadratic_abs σ u v hσ hu hv
    · have hh := bumpA_cross σ R u v hσ hσ1 hR hu huR (lt_of_not_ge hvR)
      rw [abs_of_nonpos (by linarith : u-v≤0), neg_sub]
      exact hh
  · by_cases hvR : v ≤ R
    · have hh := bumpA_cross σ R v u hσ hσ1 hR hv hvR (lt_of_not_ge huR)
      rw [abs_sub_comm, abs_of_nonneg (by linarith : 0≤u-v)]
      exact hh
    · rw [bumpA_tail σ R u hRpos (lt_of_not_ge huR), bumpA_tail σ R v hRpos (lt_of_not_ge hvR)]
      have hC : 1/R ≤ 2/σ := by
        apply (div_le_div_iff₀ hRpos hσ).mpr
        linarith
      exact (tail_abs R u v hRpos).trans (mul_le_mul_of_nonneg_right hC (abs_nonneg _))


end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem integrand_global_lipschitz (r σ R L : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hL : 0 ≤ L)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r))
    (hz : feasible r σ R z) (x y : X) :
    |integrand r σ R g z x-integrand r σ R g z y| ≤ (L+1026/σ)*(dist x y/r) := by
  have hd : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  by_cases hxy : dist x y/r ≤ 1
  · have hA := weighted_radial_lipschitz r R (2*R) (2/σ) 2 hr hR le_rfl
      (by positivity) (by norm_num) (bumpA σ R)
      (fun u hu => bumpA_zero σ R u (by linarith) hu)
      (fun u v hu hv => bumpA_lipschitz σ R u v hσ hσ1 hR hu hv)
      z (fun s => 1+g s) hz.1 (fun s => ⟨by linarith [(hg s).1], by linarith [(hg s).2]⟩)
      x y (hz.2.1 x) hxy
    have hB := weighted_radial_lipschitz r R (2*σ) (1/σ) 1 hr hR (by linarith)
      (by positivity) (by norm_num) (bumpB σ)
      (fun u hu => bumpB_zero σ u hσ hu)
      (fun u v _ _ => by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using bumpB_lipschitz σ u v hσ)
      z (fun _ => 1) hz.1 (fun _ => ⟨by norm_num, le_rfl⟩) x y (hz.2.1 x) hxy
    simp only [mul_one, one_mul] at hB
    let bx := ∑ s, z s*bumpB σ (dist s x/r)
    let by' := ∑ s, z s*bumpB σ (dist s y/r)
    have hbx := weighted_bumpB_sum r σ R hσ hσ1 hR z hz x
    change bx ∈ Set.Icc (0:ℝ) 1 at hbx
    have hres : |(1+g x)*(1-bx)-(1+g y)*(1-by')| ≤ (L+2/σ)*(dist x y/r) := by
      have he : (1+g x)*(1-bx)-(1+g y)*(1-by') =
          (g x-g y)*(1-bx)+(1+g y)*(by'-bx) := by ring
      rw [he]
      calc
        _ ≤ |(g x-g y)*(1-bx)|+|(1+g y)*(by'-bx)| := abs_add_le _ _
        _ = |g x-g y| *(1-bx)+(1+g y)*|bx-by'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hbx.2] : 0 ≤ 1-bx),
            abs_of_nonneg (by linarith [(hg y).1] : 0 ≤ 1+g y), abs_sub_comm by' bx]
        _ ≤ L*(dist x y/r)*1+2*((1/σ)*(dist x y/r)) := by
          apply add_le_add
          · exact mul_le_mul (hgLip x y) (by linarith [hbx.1]) (by linarith [hbx.2]) (mul_nonneg hL hd)
          · exact mul_le_mul (by linarith [(hg y).2]) hB (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    have he : integrand r σ R g z x-integrand r σ R g z y =
        ((1+g x)*(1-bx)-(1+g y)*(1-by')) +
          256*((∑ s, z s*(1+g s)*bumpA σ R (dist s x/r))-
            (∑ s, z s*(1+g s)*bumpA σ R (dist s y/r))) := by
      unfold integrand bx by'
      ring
    rw [he]
    calc
      _ ≤ |(1+g x)*(1-bx)-(1+g y)*(1-by')| +
          |256*((∑ s, z s*(1+g s)*bumpA σ R (dist s x/r))-
            (∑ s, z s*(1+g s)*bumpA σ R (dist s y/r)))| := abs_add_le _ _
      _ ≤ (L+2/σ)*(dist x y/r)+256*(2*(2/σ)*(dist x y/r)) := by
        apply add_le_add hres
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 256)]
        exact mul_le_mul_of_nonneg_left hA (by norm_num)
      _ = _ := by ring
  · have hx := integrand_bounds r σ R hr hσ hσ1 hR g z hg hz x
    have hy := integrand_bounds r σ R hr hσ hσ1 hR g z hg hz y
    have hb : |integrand r σ R g z x-integrand r σ R g z y| ≤ 514 :=
      abs_le.mpr ⟨by linarith [hx.1,hy.2], by linarith [hx.2,hy.1]⟩
    have hc : 1026 ≤ 1026/σ := (le_div_iff₀ hσ).mpr (by nlinarith)
    exact hb.trans (by nlinarith)


theorem drift_lipschitz [DecidableEq X] (r σ R L : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hL : 0 ≤ L) (μ ν g : X → ℝ)
    (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1) (x : X)
    (hg : ∀ y, g y ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ y z, |g y-g z| ≤ L*(dist y z/r)) :
    max (value r σ R (fun y => μ y-ν y+if y=x then 1 else 0) g-value r σ R μ g) 0 ≤
      (L+1026/σ)*(∑ y, ν y*dist x y) := by
  obtain ⟨z, hz, hmin, _⟩ := minimum_exists r σ R μ g
  calc
    _ ≤ r*∑ y, ν y*max (integrand r σ R g z x-integrand r σ R g z y) 0 :=
      drift_nonneg_bound r σ R hr μ ν g z hν hν1 x hz hmin
    _ ≤ r*∑ y, ν y*((L+1026/σ)*(dist x y/r)) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hν y)
      exact (max_le (le_abs_self _) (abs_nonneg _)).trans
        (integrand_global_lipschitz r σ R L hr hσ hσ1 hR hL g z hg hgLip hz x y)
    _ = _ := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      field_simp


end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

omit [Fintype X] in
theorem relocate_other_le [DecidableEq X] (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (z : X → ℝ) (hz : ∀ t, 0 ≤ z t) (s x t : X) (htx : t ≠ x) :
    relocate r R z s x t ≤ z t := by
  unfold relocate
  rw [ite_eq_right htx]
  split_ifs
  · exact hz t
  · have hq : 0 ≤ (dist s x/r)/(10*R) := by positivity
    exact max_le (by linarith) (hz t)
  · rfl

theorem relocated_capacity [DecidableEq X] (r σ R : ℝ) (hr : 0 < r) (hR : 256 ≤ R)
    (z : X → ℝ) (hz : feasible r σ R z) (s x : X) (hsx : s ≠ x) (hzx : z x=0)
    (p : X) : (∑ t, max (relocate r R z s x t-gate R (dist t p/r)) 0) ≤ 1 := by
  let q := (dist s x/r)/(10*R)
  let A := max (z s-gate R (dist s p/r)) 0
  let A' := max (z s-gate R (dist x p/r)) 0
  let a : X → ℝ := fun t => if t=s ∨ t=x then 0 else max (z t-gate R (dist t p/r)) 0
  let b : X → ℝ := fun t => if t=s ∨ t=x then 0 else max (relocate r R z s x t-gate R (dist t p/r)) 0
  have hRpos : 0 < R := by linarith
  have hq : 0 ≤ q := by dsimp [q] <;> positivity
  have hnegative : ∀ t : X, max (0-gate R (dist t p/r)) 0 = 0 := by
    intro t
    exact max_eq_right (by linarith [gate_nonneg R (dist t p/r)])
  have hold : (∑ t, max (z t-gate R (dist t p/r)) 0) = A+∑ t, a t := by
    rw [sum_split_pair _ s x hsx, hzx, hnegative]
    simp only [add_zero]
    rfl
  have hnew : (∑ t, max (relocate r R z s x t-gate R (dist t p/r)) 0) = A'+∑ t, b t := by
    rw [sum_split_pair _ s x hsx, relocate_at_site r R z s x hsx, hnegative, relocate_at_target]
    simp only [zero_add]
    rfl
  rw [hnew]
  apply capacity_patch a b A A' q
  · intro t
    dsimp [a]
    split_ifs <;> first | rfl | exact le_max_right _ _
  · exact hq
  · rw [← hold]
    exact hz.2.1 p
  · dsimp [A']
    exact max_le (by linarith [feasible_upper r σ R z hz s, gate_nonneg R (dist x p/r)]) (by norm_num)
  · have hg := gate_lipschitz R (dist s p/r) (dist x p/r) hRpos
    have hdist : |dist s p/r-dist x p/r| ≤ dist s x/r := by
      rw [← sub_div, abs_div, abs_of_pos hr]
      exact div_le_div_of_nonneg_right (abs_dist_sub_le s x p) hr.le
    have hgp : |gate R (dist s p/r)-gate R (dist x p/r)| ≤ q :=
      hg.trans (div_le_div_of_nonneg_right hdist (by positivity))
    have hm := abs_max_sub_max_le_abs (z s-gate R (dist x p/r)) (z s-gate R (dist s p/r)) 0
    have he : (z s-gate R (dist x p/r))-(z s-gate R (dist s p/r)) =
        gate R (dist s p/r)-gate R (dist x p/r) := by ring
    rw [he] at hm
    have hi : A'-A ≤ q := (le_abs_self _).trans (hm.trans hgp)
    linarith
  · intro t
    dsimp [a, b]
    split_ifs with ht
    · rfl
    · exact max_le_max (sub_le_sub_right
        (relocate_other_le r R hr hRpos z hz.1 s x t (fun h => ht (Or.inr h))) _) le_rfl
  · intro hA t
    by_cases hts : t=s ∨ t=x
    · simp [a, b, hts]
    have hts' : t ≠ s := fun h => hts (Or.inl h)
    have htx : t ≠ x := fun h => hts (Or.inr h)
    dsimp [a, b]
    rw [ite_eq_right hts, ite_eq_right hts]
    by_cases hc : dist t x ≤ (50*R)*r
    · simp only [relocate, ite_eq_right htx, ite_eq_right hts', ite_eq_left hc]
      exact le_of_eq (trim_contribution _ _ _ (gate_nonneg _ _) hq)
    · have hAp : 0 < A' := (le_max_right _ _).trans_lt hA
      have hxp : dist x p/r < 20*R :=
        gate_positive_near R _ _ hRpos (feasible_upper r σ R z hz s) hAp
      have hat : max (z t-gate R (dist t p/r)) 0 = 0 := by
        apply le_antisymm _ (le_max_right _ _)
        by_contra hn
        have htp := gate_positive_near R _ _ hRpos (feasible_upper r σ R z hz t) (lt_of_not_ge hn)
        have htri := normalized_triangle r hr t p x
        rw [dist_comm p x] at htri
        have hfar : 50*R < dist t x/r := (lt_div_iff₀ hr).mpr (lt_of_not_ge hc)
        linarith
      simp only [relocate, ite_eq_right htx, ite_eq_right hts', ite_eq_right hc, hat]
      exact le_max_right _ _

theorem relocate_feasible [DecidableEq X] (r σ R : ℝ)
    (hr : 0 < r) (_hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (z : X → ℝ) (hz : feasible r σ R z) (s x : X)
    (hsx : s ≠ x) (_hs : 0 < z s) (_hnear : dist s x/r < σ/4)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r) :
    feasible r σ R (relocate r R z s x) := by
  have hRpos : 0 < R := by linarith
  have hzx := zero_at_relocation_target r σ R hr hR z hz s x hsx hother
  refine ⟨relocate_nonneg r R z hz.1 s x, relocated_capacity r σ R hr hR z hz s x hsx hzx, ?_⟩
  intro u v huv hu hv
  have hne : ∀ t, 0 < relocate r R z s x t → t ≠ s := by
    intro t ht he
    subst t
    rw [relocate_at_site r R z s x hsx] at ht
    linarith
  have hfar : ∀ t, t ≠ x → 0 < relocate r R z s x t → 5*σ*r ≤ dist t x := by
    intro t htx ht
    have htz : 0 < z t := ht.trans_le (relocate_other_le r R hr hRpos z hz.1 s x t htx)
    have hf := hother t (hne t ht) htz
    have hh : 5*σ ≤ dist t x/r := by linarith
    exact (le_div_iff₀ hr).mp hh
  by_cases hux : u=x
  · subst u
    rw [dist_comm]
    exact hfar v huv.symm hv
  by_cases hvx : v=x
  · subst v
    exact hfar u hux hu
  exact hz.2.2 u v huv
    (hu.trans_le (relocate_other_le r R hr hRpos z hz.1 s x u hux))
    (hv.trans_le (relocate_other_le r R hr hRpos z hz.1 s x v hvx))

omit [MetricSpace X] in
theorem sum_le_unique (f : X → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hbound : ∀ t, f t ≤ q) (huniq : ∀ u v, 0 < f u → 0 < f v → u=v) :
    (∑ t, f t) ≤ q := by
  classical
  by_cases hp : ∃ t, 0 < f t
  · obtain ⟨t, ht⟩ := hp
    have hh : ∀ u, f u ≤ if u=t then q else 0 := by
      intro u
      by_cases he : u=t
      · simpa [he] using hbound t
      · rw [ite_eq_right he]
        by_contra h
        exact he (huniq u t (lt_of_not_ge h) ht)
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hh u)
    simpa using hh'
  · have hh : ∀ t, f t ≤ 0 := fun t => le_of_not_gt (fun h => hp ⟨t,h⟩)
    exact (Finset.sum_nonpos fun t ht => hh t).trans hq

omit [Fintype X] in
theorem relocate_reduction [DecidableEq X] (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (z : X → ℝ) (hz : ∀ t, 0 ≤ z t) (s x t : X) (hts : t ≠ s) (htx : t ≠ x) :
    z t-relocate r R z s x t ∈ Set.Icc (0:ℝ) ((dist s x/r)/(10*R)) := by
  have hq : 0 ≤ (dist s x/r)/(10*R) := by positivity
  refine ⟨sub_nonneg.mpr (relocate_other_le r R hr hR z hz s x t htx), ?_⟩
  unfold relocate
  rw [ite_eq_right htx, ite_eq_right hts]
  split_ifs
  · linarith [le_max_left (z t-dist s x/r/(10*R)) 0]
  · simpa using hq


end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotRelocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem bumpA_quadratic (σ R u : ℝ) (hσ : 0 < σ) (hσR : σ ≤ R)
    (hu : 0 ≤ u) (huσ : u ≤ σ) : bumpA σ R u = u^2/σ^2 := by
  unfold bumpA
  rw [ite_eq_left (huσ.trans hσR)]
  apply min_eq_left
  apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
  nlinarith

theorem other_inner_nonpos [DecidableEq X] (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1) (hz : feasible r σ R z)
    (s x p : X) (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r)
    (hinner : dist x p ≤ γ*r) :
    (∑ t, if t=s ∨ t=x then 0 else
      (relocate r R z s x t-z t)*coefficient r σ R g t p) ≤ 0 := by
  have hRpos : 0 < R := by linarith
  apply Finset.sum_nonpos
  intro t ht
  split_ifs with hts
  · rfl
  · have hts' : t ≠ s := fun h => hts (Or.inl h)
    have htx : t ≠ x := fun h => hts (Or.inr h)
    have hle := relocate_other_le r R hr hRpos z hz.1 s x t htx
    by_cases hpos : 0 < z t
    · have hB := other_inner_zero r σ R γ hr hσ hσ1 hR hγσ z hz s x p t hother hinner hts' hpos
      have hc : 0 ≤ coefficient r σ R g t p := by
        unfold coefficient
        rw [hB, mul_zero, sub_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [(hg t).1]))
          (bumpA_bounds σ R _ hRpos).1
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) hc
    · have he : z t=0 := le_antisymm (le_of_not_gt hpos) (hz.1 t)
      have he' : relocate r R z s x t=0 := le_antisymm (he ▸ hle) (relocate_nonneg r R z hz.1 s x t)
      simp [he,he']

theorem relocated_inner_gain [DecidableEq X] (r σ R γ L : ℝ)
    (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (hL : 0 ≤ L) (hγσ : γ ≤ σ/64) (hLγ : L*γ ≤ 1)
    (g z : X → ℝ) (hg : ∀ p, g p ∈ Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q| ≤ L*(dist p q/r)) (hz : feasible r σ R z)
    (s x p : X) (hsx : s ≠ x) (hzx : z x=0) (hnear : dist s x/r < σ/4)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r)
    (hinner : dist x p ≤ γ*r) :
    integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p ≤
      -(256*z s/σ^2)*((dist s x/r)^2-5*(dist s x/r)*(dist x p/r)) := by
  let u := dist s p/r
  let v := dist x p/r
  let w := dist s x/r
  have hu : 0 ≤ u := by dsimp [u] <;> positivity
  have hv : 0 ≤ v := by dsimp [v] <;> positivity
  have hw : 0 ≤ w := by dsimp [w] <;> positivity
  have hvγ : v ≤ γ := (div_le_iff₀ hr).mpr hinner
  have htv := normalized_triangle r hr s x p
  have hus : u ≤ σ := by dsimp [u] at * <;> linarith
  have hvs : v ≤ σ := by linarith
  have hb1 := bumpB_one σ u hσ hus
  have hb2 := bumpB_one σ v hσ hvs
  have ha1 := bumpA_quadratic σ R u hσ (by linarith) hu hus
  have ha2 := bumpA_quadratic σ R v hσ (by linarith) hv hvs
  have hlip : g x-g s ≤ L*w := by
    exact (le_abs_self _).trans (by simpa only [abs_sub_comm] using hgLip s x)
  have ht1 : w ≤ u+v := by
    have hh := normalized_triangle r hr s p x
    simpa only [dist_comm p x] using hh
  have ht2 : v ≤ u+w := by
    have hh := normalized_triangle r hr x s p
    rw [dist_comm x s] at hh
    dsimp [u,v,w]
    linarith
  have hLv : L*v ≤ 1 := (mul_le_mul_of_nonneg_left hvγ hL).trans hLγ
  have hquad := quadratic_gain (g s) (g x) u v w L (hg s) hlip hu hv hw ht1 ht2 hLv
  have hc : coefficient r σ R g x p-coefficient r σ R g s p ≤
      -(256/σ^2)*(w^2-5*w*v) := by
    change 256*(1+g x)*bumpA σ R v-(1+g p)*bumpB σ v -
      (256*(1+g s)*bumpA σ R u-(1+g p)*bumpB σ u) ≤ _
    rw [hb1,hb2,ha1,ha2]
    have hm := mul_le_mul_of_nonneg_left hquad (show 0≤256/σ^2 by positivity)
    calc
      _ = -(256/σ^2)*((1+g s)*u^2-(1+g x)*v^2) := by ring
      _ ≤ _ := by linarith
  rw [integrand_relocate r σ R g z s x p hsx hzx]
  have ho := other_inner_nonpos r σ R γ hr hσ hσ1 hR hγσ g z hg hz s x p hother hinner
  calc
    _ ≤ z s*(-(256/σ^2)*(w^2-5*w*v))+0 :=
      add_le_add (mul_le_mul_of_nonneg_left hc (hz.1 s)) ho
    _ = _ := by dsimp [w,v] <;> ring

omit [Fintype X] in
theorem coefficient_far (r σ R : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hR : 256 ≤ R)
    (g : X → ℝ) (t p : X) (hfar : 2*R ≤ dist t p/r) : coefficient r σ R g t p = 0 := by
  have hRpos : 0<R := by linarith
  unfold coefficient
  rw [bumpA_zero σ R _ hRpos hfar, bumpB_zero σ _ hσ (by linarith)]
  ring

theorem relocate_unchanged_outside [DecidableEq X] (r σ R : ℝ) (hr : 0 < r)
    (hσ : 0<σ) (hσ1 : σ≤1) (hR : 256≤R)
    (g z : X → ℝ) (s x p : X) (hsx : s≠x) (hzx : z x=0)
    (hnear : dist s x/r < σ/4) (hfar : (100*R)*r < dist x p) :
    integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p = 0 := by
  have hxp : 100*R < dist x p/r := (lt_div_iff₀ hr).mpr hfar
  have hzero : ∀ t, dist t x/r ≤ 50*R → coefficient r σ R g t p=0 := by
    intro t ht
    have hh := normalized_triangle r hr x t p
    rw [dist_comm x t] at hh
    exact coefficient_far r σ R hσ hσ1 hR g t p (by linarith)
  have hs0 := hzero s (by linarith)
  have hx0 := coefficient_far r σ R hσ hσ1 hR g x p (by linarith)
  rw [integrand_relocate r σ R g z s x p hsx hzx, hs0, hx0]
  simp only [sub_self, mul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro t ht
  split_ifs with htsx
  · rfl
  · have hts : t≠s := fun h => htsx (Or.inl h)
    have htx : t≠x := fun h => htsx (Or.inr h)
    by_cases hc : dist t x ≤ (50*R)*r
    · rw [hzero t ((div_le_iff₀ hr).mpr hc), mul_zero]
    · simp [relocate, htx, hts, hc]

theorem ballMass_mono (r a b : ℝ) (hr : 0 ≤ r) (hab : a ≤ b)
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X) : ballMass r a μ x ≤ ballMass r b μ x := by
  unfold ballMass
  apply Finset.sum_le_sum
  intro p hp
  have hi : dist x p ≤ a*r → dist x p ≤ b*r := fun h => h.trans (mul_le_mul_of_nonneg_right hab hr)
  split_ifs <;> first | linarith [hμ p] | exact False.elim (by aesop)



end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem capacity_other [DecidableEq X] (r σ R : ℝ) (hR : 0<R) (z : X → ℝ)
    (hz : feasible r σ R z) (s x : X) (hs : dist s x/r ≤ 10*R)
    (P : X → Prop) [DecidablePred P] (hP : ∀ t, P t → dist t x/r ≤ 10*R) :
    (∑ t, if t=s then 0 else if P t then z t else 0) ≤ 1-z s := by
  classical
  have hcap := hz.2.1 x
  rw [sum_split_single _ s, gate_eq_zero R _ hR hs, sub_zero, max_eq_left (hz.1 s)] at hcap
  have hh : (∑ t, if t=s then 0 else if P t then z t else 0) ≤
      ∑ t, if t=s then 0 else max (z t-gate R (dist t x/r)) 0 := by
    apply Finset.sum_le_sum
    intro t ht
    by_cases he : t=s
    · simp [he]
    · rw [ite_eq_right he,ite_eq_right he]
      by_cases hp : P t
      · rw [ite_eq_left hp,gate_eq_zero R _ hR (hP t hp),sub_zero,max_eq_left (hz.1 t)]
      · rw [ite_eq_right hp]
        exact le_max_right _ _
  linarith

theorem other_surcharge_slope [DecidableEq X] (r σ R : ℝ) (hr : 0 < r) (hσ : 0<σ)
    (hσ1 : σ≤1) (hR : 256≤R) (g z : X → ℝ) (hg : ∀ p,g p∈Set.Icc (0:ℝ) 1)
    (hz : feasible r σ R z) (s x y : X)
    (hnear : dist s x/r < σ/4) (hxy : dist x y/r < σ/8) :
    (∑ t, if t=s then 0 else z t*(1+g t)*(bumpA σ R (dist t x/r)-bumpA σ R (dist t y/r))) ≤
      (4/σ)*(1-z s)*(dist x y/r) := by
  classical
  let P : X → Prop := fun t => bumpA σ R (dist t x/r)≠0 ∨ bumpA σ R (dist t y/r)≠0
  let W : X → ℝ := fun t => if t=s then 0 else if P t then z t else 0
  have hRpos : 0<R := by linarith
  have hv : 0≤dist x y/r := by positivity
  have hP : ∀ t, P t → dist t x/r≤10*R := by
    intro t ht
    have hn : ∀ q, bumpA σ R (dist t q/r)≠0 → dist t q/r<2*R := by
      intro q ha
      by_contra hh
      exact ha (bumpA_zero σ R _ hRpos (le_of_not_gt hh))
    rcases ht with hx | hy
    · linarith [hn x hx]
    · have hh := normalized_triangle r hr t y x
      rw [dist_comm y x] at hh
      linarith [hn y hy]
  have hW : (∑ t, W t)≤1-z s := capacity_other r σ R hRpos z hz s x (by linarith) P hP
  have hterm : ∀ t, (if t=s then 0 else z t*(1+g t)*(bumpA σ R (dist t x/r)-bumpA σ R (dist t y/r))) ≤
      ((4/σ)*(dist x y/r))*W t := by
    intro t
    by_cases hts : t=s
    · simp [W,hts]
    rw [ite_eq_right hts]
    by_cases hp : P t
    · dsimp [W]
      rw [ite_eq_right hts,ite_eq_left hp]
      have hd : |dist t x/r-dist t y/r| ≤ dist x y/r := by
        simpa only [dist_comm t x,dist_comm t y] using normalized_dist_difference r hr x y t
      have ha := (bumpA_lipschitz σ R _ _ hσ hσ1 hR (by positivity) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hd (by positivity : 0≤2/σ))
      have hg0 : 0≤1+g t := by linarith [(hg t).1]
      have hg2 : 1+g t≤2 := by linarith [(hg t).2]
      calc
        _ ≤ z t*(1+g t)*|bumpA σ R (dist t x/r)-bumpA σ R (dist t y/r)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (hz.1 t) hg0)
        _ ≤ z t*2*((2/σ)*(dist x y/r)) := mul_le_mul
          (mul_le_mul_of_nonneg_left hg2 (hz.1 t)) ha (abs_nonneg _) (mul_nonneg (hz.1 t) (by norm_num))
        _ = _ := by ring
    · have hx : bumpA σ R (dist t x/r)=0 := by by_contra hh; exact hp (Or.inl hh)
      have hy : bumpA σ R (dist t y/r)=0 := by by_contra hh; exact hp (Or.inr hh)
      simp [W,hts,hp,hx,hy]
  calc
    _ ≤ ∑ t, ((4/σ)*(dist x y/r))*W t := Finset.sum_le_sum fun t _ => hterm t
    _ = ((4/σ)*(dist x y/r))*(∑ t,W t) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((4/σ)*(dist x y/r))*(1-z s) := mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by ring

theorem near_surcharge_slope (r σ R : ℝ) (hr : 0 < r) (hσ : 0<σ)
    (hσ1 : σ≤1) (hR : 256≤R) (g z : X → ℝ) (hg : ∀ p,g p∈Set.Icc (0:ℝ) 1)
    (hz : feasible r σ R z) (s x y : X)
    (hnear : dist s x/r < σ/4) (hxy : dist x y/r < σ/8) :
    256*z s*(1+g s)*(bumpA σ R (dist s x/r)-bumpA σ R (dist s y/r)) ≤
      (1024*(dist s x/r)/σ^2)*(dist x y/r) := by
  let w := dist s x/r
  let u := dist s y/r
  let v := dist x y/r
  have hw : 0≤w := by dsimp [w] <;> positivity
  have hu : 0≤u := by dsimp [u] <;> positivity
  have hv : 0≤v := by dsimp [v] <;> positivity
  have htri := normalized_triangle r hr s x y
  have htri' := normalized_triangle r hr s y x
  rw [dist_comm y x] at htri'
  have huσ : u≤σ := by dsimp [u] <;> linarith
  have hwσ : w≤σ := by dsimp [w] <;> linarith
  have hd := square_difference u w v hu hw hv (by dsimp [u,w,v] <;> linarith)
  have hgain : w^2/σ^2-u^2/σ^2≤2*w*v/σ^2 := by
    rw [←sub_div]
    exact div_le_div_of_nonneg_right hd (sq_nonneg σ)
  have hzs : z s≤1 := feasible_upper r σ R z hz s
  have hg0 : 0≤1+g s := by linarith [(hg s).1]
  have hg2 : 1+g s≤2 := by linarith [(hg s).2]
  change 256*z s*(1+g s)*(bumpA σ R w-bumpA σ R u) ≤ _
  rw [bumpA_quadratic σ R w hσ (by linarith) hw hwσ,bumpA_quadratic σ R u hσ (by linarith) hu huσ]
  calc
    _ ≤ 256*z s*(1+g s)*(2*w*v/σ^2) := mul_le_mul_of_nonneg_left hgain (mul_nonneg (mul_nonneg (by norm_num) (hz.1 s)) hg0)
    _ ≤ 512*(2*w*v/σ^2) := mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (hz.1 s) (sub_nonneg.mpr hg2)]) (by positivity)
    _ = _ := by dsimp [w,v] <;> ring

theorem local_slope_raw (r σ R L : ℝ) (hr : 0 < r) (hσ : 0<σ)
    (hσ1 : σ≤1) (hR : 256≤R) (_hL : 0≤L)
    (g z : X → ℝ) (hg : ∀ p,g p∈Set.Icc (0:ℝ) 1)
    (hgLip : ∀ p q, |g p-g q|≤L*(dist p q/r))
    (hz : feasible r σ R z) (s x y : X)
    (hnear : dist s x/r<σ/4) (hother : ∀ t,t≠s → 0<z t → R/2<dist t x/r)
    (hxy : dist x y/r<σ/8) :
    integrand r σ R g z x-integrand r σ R g z y ≤
      ((L+1024/σ)*(1-z s)+1024*(dist s x/r)/σ^2)*(dist x y/r) := by
  classical
  have hb1 := local_bump_sum r σ R hr hσ hσ1 hR z hz s x x hnear hother (by simp <;> positivity)
  have hb2 := local_bump_sum r σ R hr hσ hσ1 hR z hz s x y hnear hother hxy
  have hs := other_surcharge_slope r σ R hr hσ hσ1 hR g z hg hz s x y hnear hxy
  have hn := near_surcharge_slope r σ R hr hσ hσ1 hR g z hg hz s x y hnear hxy
  have hz1 : 0≤1-z s := sub_nonneg.mpr (feasible_upper r σ R z hz s)
  have hres : (1-z s)*(g x-g y)≤(1-z s)*(L*(dist x y/r)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hgLip x y)) hz1
  have hsum : (∑ t,z t*(1+g t)*bumpA σ R (dist t x/r)) -
      (∑ t,z t*(1+g t)*bumpA σ R (dist t y/r)) =
      z s*(1+g s)*(bumpA σ R (dist s x/r)-bumpA σ R (dist s y/r))+
      ∑ t,if t=s then 0 else z t*(1+g t)*(bumpA σ R (dist t x/r)-bumpA σ R (dist t y/r)) := by
    rw [←Finset.sum_sub_distrib]
    simp_rw [←mul_sub]
    exact sum_split_single _ s
  unfold integrand
  rw [hb1,hb2]
  ring_nf at hres hs hn hsum ⊢
  linarith only [hres,hs,hn,hsum]

end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

def shellRatio (r γ R : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  (ballMass r (100*R) μ x-ballMass r γ μ x)/ballMass r γ μ x

def momentRatio (r γ : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  innerMoment r γ μ x/ballMass r γ μ x

theorem ballMass_extent_mono (r s a b : ℝ) (hab : a*r ≤ b*s)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) :
    ballMass r a μ x ≤ ballMass s b μ x :=
  PilotScales.mass_mono μ (dist x) hμ hab

theorem ballMass_total (r a : ℝ) (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) :
    ballMass r a μ x ≤ ∑ y, μ y := by
  apply Finset.sum_le_sum
  intro y _
  split_ifs <;> first | rfl | exact hμ y

theorem shellRatio_nonneg (r γ R : ℝ) (hr : 0 ≤ r) (hγR : γ ≤ 100*R)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) :
    0 ≤ shellRatio r γ R μ x := by
  apply div_nonneg
  · exact sub_nonneg.mpr (ballMass_mono r γ (100*R) hr hγR μ hμ x)
  · exact PilotScales.mass_nonneg μ (dist x) hμ _

theorem momentRatio_nonneg (r γ : ℝ) (hr : 0 < r)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) :
    0 ≤ momentRatio r γ μ x :=
  div_nonneg (innerMoment_bounds r γ hr μ hμ x).1
    (PilotScales.mass_nonneg μ (dist x) hμ _)

end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotCredits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

def coarseConstant (σ γ δ L : ℝ) (p : ℕ) (k : ℝ) : ℝ :=
  (L+1026/σ)/δ*((p:ℝ)/Real.log 2*Real.log (2*k)) +
    localSlopeConstant σ L*((p:ℝ)/Real.log 2*Real.log (2*k) +
      2*γ*(1+Real.log (2*k))) + 8224/σ

theorem coarseConstant_nonneg (σ γ δ L : ℝ) (p : ℕ) (k : ℝ)
    (hσ : 0 < σ) (hγ : 0 < γ) (hδ : 0 < δ) (hL : 0 ≤ L) (hk : 1/2 ≤ k) :
    0 ≤ coarseConstant σ γ δ L p k := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlk : 0 ≤ Real.log (2*k) := Real.log_nonneg (by linarith)
  unfold coarseConstant localSlopeConstant
  positivity

end
end UniformKServer.PilotCompact



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.PilotEdits

section
open PilotCompact
attribute [local instance] Classical.propDecidable

variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

def potential (T : I → Template) (a : I → ℝ) (r τ : ℝ) (N : ℕ)
    (μ : X → ℝ) (g : I → ℕ → X → ℝ) : ℝ :=
  ∑ i, a i * ∑ j ∈ Finset.range N, value (r*τ^j) (T i).sigma (T i).R μ (g i j)

def moverCost {k : ℕ} (F : Flow X Ω k) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ y, F.mover t ω y*dist (F.request t ω) y

end

section
open PilotCompact
attribute [local instance] Classical.propDecidable
variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

lemma potential_bounds (T : I → Template) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r τ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ) (N k : ℕ)
    (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμk : ∑ y, μ y = k)
    (g : I → ℕ → X → ℝ) (hg : ∀ i j y, g i j y ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ potential T a r τ N μ g ∧
      potential T a r τ N μ g ≤ 2*k*(∑ i, a i)*(∑ j ∈ Finset.range N, r*τ^j) := by
  have hτ0 : 0 < τ := by linarith
  have hval : ∀ i j, 0 ≤ value (r*τ^j) (T i).sigma (T i).R μ (g i j) ∧
      value (r*τ^j) (T i).sigma (T i).R μ (g i j) ≤ 2*(r*τ^j)*k := by
    intro i j
    simpa only [hμk] using value_bounds (r*τ^j) (T i).sigma (T i).R (by positivity)
      (T i).sigma_pos (T i).sigma_le_one (T i).R_large μ (g i j) hμ (hg i j)
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (ha i)
      (Finset.sum_nonneg fun j _ => (hval i j).1)
  · calc
      _ ≤ ∑ i, a i * ∑ j ∈ Finset.range N, 2*(r*τ^j)*k :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ => (hval i j).2) (ha i)
      _ = _ := by
        have he : ∀ j, 2*(r*τ^j)*(k:ℝ) = (2*k)*(r*τ^j) := by intro j; ring
        simp_rw [he,←Finset.mul_sum,←Finset.sum_mul]
        ring

end

end UniformKServer.PilotEdits

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Fixed-slot implementation of disjoint heavy balls, including the literal
finite-metric intersection test for label reuse. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset
open scoped Classical
variable {X Λ : Type*} [MetricSpace X] [Fintype Λ]

variable {r : ℝ}

theorem key_none (S : State X Λ r) (p : X) : key S p=none ↔ ¬∃ l, covers S l p := by
  unfold key
  split_ifs <;> simp_all

theorem covers_insert_iff (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) (l : Λ) (p : X) :
    covers (insert S hr x R hR fresh hf) l p ↔
      (l=chosen S x R fresh ∧ dist x p ≤ R) ∨ (l ∈ survivors S x ∧ covers S l p) := by
  by_cases hl : l=chosen S x R fresh
  · subst l
    have hn := chosen_not_survivor S hr x R hR.2 fresh hf
    simp only [covers,insert,mem_insert_self,true_and,Function.update_self,hn,false_and,or_false]
  · simp only [covers,insert,mem_insert,hl,false_or,Function.update_of_ne hl,false_and,false_or]
    constructor
    · intro h; exact ⟨h.1,(mem_filter.mp h.1).1,h.2⟩
    · intro h; exact ⟨h.1,h.2.2⟩

end UniformKServer.HeavyRecords

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyPilot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.HeavyPilot

section
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem ramp_bounds (v : ℝ) : ramp v ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

omit [MetricSpace X] in
theorem ramp_zero {v : ℝ} (h : v ≤ 3) : ramp v = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [MetricSpace X] in
theorem ramp_one {v : ℝ} (h : 4 ≤ v) : ramp v = 1 := by
  unfold ramp
  rw [min_eq_left (by linarith)]
  norm_num

omit [MetricSpace X] in
theorem ramp_lip (v w : ℝ) : |ramp v-ramp w| ≤ |v-w| := by
  have h₁ := abs_max_sub_max_le_max (0:ℝ) (min 1 (v-3)) 0 (min 1 (w-3))
  have h₂ := abs_min_sub_min_le_max (1:ℝ) (v-3) 1 (w-3)
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (min 1 (v-3)-min 1 (w-3)))] at h₁
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (v-3-(w-3)))] at h₂
  simpa only [sub_sub_sub_cancel_right,ramp] using h₁.trans h₂

theorem parameter_bounds (r : ℝ) (H : Finset X) (p : X) :
    parameter r H p ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply Finset.le_min'
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · norm_num
    · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ha
      exact (ramp_bounds _).1
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem parameter_le_center (r : ℝ) (H : Finset X) (p c : X) (hc : c ∈ H) :
    parameter r H p ≤ ramp (dist p c/r) :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c,hc,rfl⟩))

theorem le_parameter (r : ℝ) (H : Finset X) (p : X) (a : ℝ) (h1 : a ≤ 1)
    (hc : ∀ c ∈ H, a ≤ ramp (dist p c/r)) : a ≤ parameter r H p := by
  apply Finset.le_min'
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact h1
  · obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hb
    exact hc c hc'

theorem parameter_lip (r : ℝ) (hr : 0 < r) (H : Finset X) (p q : X) :
    |parameter r H p-parameter r H q| ≤ dist p q/r := by
  suffices h : ∀ p q : X, parameter r H p-parameter r H q ≤ dist p q/r by
    apply abs_le.mpr
    constructor
    · have hh := h q p
      rw [dist_comm q p] at hh
      linarith
    · exact h p q
  intro p q
  have hm := Finset.min'_mem (insert 1 (H.image (fun c => ramp (dist q c/r)))) (by simp)
  change parameter r H q ∈ insert 1 (H.image (fun c => ramp (dist q c/r))) at hm
  rcases Finset.mem_insert.mp hm with hq | hq
  · rw [hq]
    have := (parameter_bounds r H p).2
    exact (sub_nonpos.mpr this).trans (div_nonneg dist_nonneg hr.le)
  · obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hq
    have h₁ := parameter_le_center r H p c hc
    have h₂ := (le_abs_self (ramp (dist p c/r)-ramp (dist q c/r))).trans (ramp_lip _ _)
    have h₃ : |dist p c/r-dist q c/r| ≤ dist p q/r := by
      rw [←sub_div,abs_div,abs_of_pos hr]
      exact div_le_div_of_nonneg_right (abs_dist_sub_le p q c) hr.le
    rw [he] at h₂
    linarith

theorem update_zero (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hp : dist p x ≤ 3*r) : parameter r (updateCenters r H x) p = 0 := by
  have hc := parameter_le_center r (updateCenters r H x) p x (by simp [updateCenters])
  rw [ramp_zero ((div_le_iff₀ hr).mpr hp)] at hc
  linarith [(parameter_bounds r (updateCenters r H x) p).1]

theorem update_far (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hp : 104*r < dist p x) : parameter r (updateCenters r H x) p ≤ parameter r H p := by
  apply le_parameter r H p _ (parameter_bounds r (updateCenters r H x) p).2
  intro c hc
  by_cases hfar : 100*r < dist x c
  · exact parameter_le_center r (updateCenters r H x) p c (by simp [updateCenters,hc,hfar])
  · have hpc : 4 ≤ dist p c/r := by
      have ht := dist_triangle p c x
      rw [dist_comm c x] at ht
      apply (le_div_iff₀ hr).mpr
      push Not at hfar
      linarith
    rw [ramp_one hpc]
    exact (parameter_bounds r (updateCenters r H x) p).2

theorem increase_support (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hinc : parameter r H p < parameter r (updateCenters r H x) p) :
    3*r < dist p x ∧ dist p x ≤ 104*r := by
  constructor
  · by_contra h
    have he := update_zero r hr H x p (le_of_not_gt h)
    rw [he] at hinc
    linarith [(parameter_bounds r H p).1]
  · by_contra h
    exact (not_lt_of_ge (update_far r hr H x p (lt_of_not_ge h))) hinc

theorem near_old_one (r : ℝ) (hr : 0 < r) (H : Finset X) (x s : X)
    (hfar : ∀ c ∈ H, 8*r < dist x c) (hs : dist s x/r < 1/4) :
    parameter r H s = 1 := by
  apply le_antisymm (parameter_bounds r H s).2
  apply le_parameter r H s 1 le_rfl
  intro c hc
  have hsc : 4 ≤ dist s c/r := by
    have ht := dist_triangle x s c
    rw [dist_comm x s] at ht
    have hds := (div_lt_iff₀ hr).mp hs
    apply (le_div_iff₀ hr).mpr
    linarith [hfar c hc]
  rw [ramp_one hsc]

theorem near_new_zero (r : ℝ) (hr : 0 < r) (H : Finset X) (x s : X)
    (hs : dist s x/r < 1/4) : parameter r (updateCenters r H x) s = 0 := by
  apply update_zero r hr H x s
  have hds := (div_lt_iff₀ hr).mp hs
  linarith

theorem annulus_surcharge (r : ℝ) (hr : 0 < r) (x s p : X)
    (hs : dist s x/r < 1/4) (hp : 3*r < dist p x ∧ dist p x ≤ 120*r) :
    PilotCompact.bumpA 1 512 (dist s p/r) = 1 := by
  have hds := (div_lt_iff₀ hr).mp hs
  have hlow : 1 ≤ dist s p/r := by
    apply (le_div_iff₀ hr).mpr
    have ht := dist_triangle p s x
    rw [dist_comm p s] at ht
    linarith [hp.1]
  have hhigh : dist s p/r ≤ 512 := by
    apply (div_le_iff₀ hr).mpr
    have ht := dist_triangle s x p
    rw [dist_comm x p] at ht
    linarith [hp.2]
  simp only [PilotCompact.bumpA,ite_eq_left hhigh,one_pow,div_one]
  exact min_eq_right (by nlinarith)

end

section
attribute [local instance] Classical.propDecidable
open PilotCompact
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem integrand_gain (r : ℝ) (hr : 0 < r) (H : Finset X) (x s : X)
    (hfar : ∀ c ∈ H, 8*r < dist x c) (hs : dist s x/r < 1/4)
    (z : X → ℝ) (hz : feasible r 1 512 z) (hweight : (1:ℝ)/2 ≤ z s)
    (hzero : ∀ c, 1/4 ≤ dist c x/r → dist c x/r ≤ 256 → z c = 0) (p : X) :
    (if 3*r < dist p x ∧ dist p x ≤ 120*r then 127 else 0) ≤
      integrand r 1 512 (parameter r H) z p -
        integrand r 1 512 (parameter r (updateCenters r H x)) z p := by
  let go := parameter r H
  let gn := parameter r (updateCenters r H x)
  let B := 1-∑ c, z c*bumpB 1 (dist c p/r)
  let A := fun c => z c*(go c-gn c)*bumpA 1 512 (dist c p/r)
  have hB : B ∈ Set.Icc (0:ℝ) 1 := by
    have h := weighted_bumpB_sum r 1 512 (by norm_num) (by norm_num) (by norm_num) z hz p
    dsimp [B]
    constructor <;> linarith [h.1,h.2]
  have hA : ∀ c, 0 ≤ A c := by
    intro c
    by_cases hc : go c < gn c
    · have hsup := increase_support r hr H x c hc
      have he : z c = 0 := hzero c (by
          apply (le_div_iff₀ hr).mpr
          linarith [hsup.1]) (by
          apply (div_le_iff₀ hr).mpr
          linarith [hsup.2])
      simp [A,he]
    · exact mul_nonneg (mul_nonneg (hz.1 c) (sub_nonneg.mpr (le_of_not_gt hc)))
        (bumpA_bounds 1 512 _ (by norm_num)).1
  have hid : integrand r 1 512 go z p-integrand r 1 512 gn z p =
      (go p-gn p)*B+256*∑ c, A c := by
    simp only [integrand,A,B,mul_add,add_mul,mul_sub,sub_mul,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]
    ring
  change _ ≤ integrand r 1 512 go z p-integrand r 1 512 gn z p
  rw [hid]
  by_cases hp : 3*r < dist p x ∧ dist p x ≤ 120*r
  · rw [ite_eq_left hp]
    have hsingle : z s ≤ ∑ c, A c := by
      have hh := Finset.single_le_sum (f := A) (fun c _ => hA c) (Finset.mem_univ s)
      have hsA : A s = z s := by
        dsimp [A,go,gn]
        rw [near_old_one r hr H x s hfar hs,near_new_zero r hr H x s hs,
          annulus_surcharge r hr x s p hs hp]
        ring
      rw [hsA] at hh
      exact hh
    have hres : -1 ≤ (go p-gn p)*B := by
      have hg : -1 ≤ go p-gn p := by
        dsimp [go,gn]
        linarith [(parameter_bounds r H p).1,(parameter_bounds r (updateCenters r H x) p).2]
      have hh := mul_le_mul_of_nonneg_right hg hB.1
      nlinarith [hB.2]
    linarith
  · rw [ite_eq_right hp]
    have hgn : gn p ≤ go p := by
      by_contra h
      have hsup := increase_support r hr H x p (lt_of_not_ge h)
      exact hp ⟨hsup.1,by linarith [hsup.2]⟩
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hgn) hB.1)
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun c _ => hA c)))

end
open PilotCompact
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- Exact heavy-center pilot gain, companion §07 heavy annulus budget. -/
theorem heavy_gain (r γ δ : ℝ) (hr : 0 < r)
    (hγ : 0 < γ) (hγsmall : γ ≤ 1/64) (hδ : 0 < δ) (hδsmall : δ ≤ 1/4112)
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (H : Finset X) (x : X)
    (hfar : ∀ c ∈ H, 8*r < dist x c)
    (hM : 0 < ballMass r γ μ x)
    (hconc : ballMass r (100*512) μ x ≤ (1+δ)*ballMass r γ μ x) :
    127*r*annulusMass r μ x ≤
      value r 1 512 μ (parameter r H) -
        value r 1 512 μ (parameter r (updateCenters r H x))
 := by
  classical
  obtain ⟨z,hz,hmin,_⟩ := minimum_exists r 1 512 μ (parameter r H)
  obtain ⟨s,hs,hw,_,_⟩ := near_site_exists r 1 512 γ δ hr (by norm_num) (by norm_num)
    (by norm_num) hγ (by simpa using hγsmall) hδ hδsmall μ (parameter r H) z hμ
    (parameter_bounds r H) x hM hconc hz hmin
  have hzero : ∀ c, 1/4 ≤ dist c x/r → dist c x/r ≤ 256 → z c = 0 := by
    intro c hnear hfar
    exact middle_site_zero r 1 512 γ δ hr (by norm_num) (by norm_num) (by norm_num)
      hγ (by simpa using hγsmall) hδ hδsmall μ (parameter r H) z hμ (parameter_bounds r H)
      x hM hconc hz hmin c (by simpa using hnear) (by norm_num; exact hfar)
  have hg : ∀ p, (if 3*r < dist p x ∧ dist p x ≤ 120*r then 127 else 0) ≤
      integrand r 1 512 (parameter r H) z p -
        integrand r 1 512 (parameter r (updateCenters r H x)) z p :=
    fun p => integrand_gain r hr H x s hfar hs z hz (by linarith) hzero p
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    mul_le_mul_of_nonneg_left (hg p) (hμ p))
  have hh := mul_le_mul_of_nonneg_left hsum hr.le
  have hleft : r*(∑ p, μ p*(if 3*r < dist p x ∧ dist p x ≤ 120*r then 127 else 0)) =
      127*r*annulusMass r μ x := by
    unfold annulusMass
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  have hright : r*(∑ p, μ p*(integrand r 1 512 (parameter r H) z p -
        integrand r 1 512 (parameter r (updateCenters r H x)) z p)) =
      objective r 1 512 μ (parameter r H) z -
        objective r 1 512 μ (parameter r (updateCenters r H x)) z := by
    simp only [objective,mul_sub,Finset.sum_sub_distrib]
  rw [hleft,hright,hmin] at hh
  have hv := value_le r 1 512 μ (parameter r (updateCenters r H x)) z hz
  linarith

end UniformKServer.HeavyPilot

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyRecordGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! The actual center-set projection and common-label properties of the
finite-slot heavy-ball update. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset
open scoped Classical
variable {X Λ : Type*} [MetricSpace X] {r : ℝ}

variable [Fintype Λ]

theorem unchanged_far (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present)
    (p : X) (hd : 120*r < dist x p) : key (insert S hr x R hR fresh hf) p=key S p := by
  have hnew : ¬ dist x p ≤ R := by linarith [hR.2]
  have hsurv (l : Λ) (hl : covers S l p) : l ∈ survivors S x := by
    refine mem_filter.mpr ⟨hl.1,?_⟩
    have ht := dist_triangle x (S.center l) p
    linarith [hl.2,(S.radius_bounds l hl.1).2]
  by_cases he : ∃ l, covers S l p
  · obtain ⟨l,hl⟩ := he
    rw [(key_some S hr p l).mpr hl]
    apply (key_some _ hr p l).mpr
    exact (covers_insert_iff S hr x R hR fresh hf l p).mpr (Or.inr ⟨hsurv l hl,hl⟩)
  · rw [(key_none S p).mpr he]
    apply (key_none _ p).mpr
    rintro ⟨l,hl⟩
    rcases (covers_insert_iff S hr x R hR fresh hf l p).mp hl with hh|hh
    · exact hnew hh.2
    · exact he ⟨l,hh.2⟩

end UniformKServer.HeavyRecords

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.FiniteProbability

variable {Ω I : Type*} [Fintype Ω]

theorem Law.expect_close (P : Law Ω) (f g : Ω → ℝ) (d : ℝ)
    (h : ∀ ω, |f ω-g ω| ≤ d) : |P.expect f-P.expect g| ≤ d := by
  apply abs_le.mpr
  have hlo := P.expect_mono (fun _ => -d) (fun ω => f ω-g ω) (fun ω => (abs_le.mp (h ω)).1)
  have hhi := P.expect_mono (fun ω => f ω-g ω) (fun _ => d) (fun ω => (abs_le.mp (h ω)).2)
  rw [P.expect_const,P.expect_sub] at hlo
  rw [P.expect_const,P.expect_sub] at hhi
  exact ⟨hlo,hhi⟩

end UniformKServer.FiniteProbability

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! A finite exact realization of the uniform heavy-ball radius.  The same
finite signature records membership for every possible center. Thus selecting
a center by the input-driven schedule does not alter the radius distribution. -/
noncomputable section
namespace UniformKServer.HeavyRadius
open FiniteProbability
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

attribute [local instance] OAI.UniformKServer.HeavyRadius.pairDecEq
omit [Fintype X] in
theorem probability_bounds (r : ℝ) (a : X × X) : probability r a ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

end UniformKServer.HeavyRadius

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ChronologicalRoster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ChronologicalRoster

variable {I X : Type*} [LinearOrder I] [MetricSpace X]

theorem ball_young_count (S : Finset I) (c : I → X) (r d : ℝ) (A : ℕ) (p : X)
    (hd : 2*d ≤ 20*r) :
    ((young S c r A).filter fun i => dist p (c i) ≤ d).card ≤ A := by
  apply local_age_count S _ c r A
  · intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  · intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  · intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have ht := dist_triangle (c i) p (c j)
    rw [dist_comm (c i) p] at ht
    linarith

end UniformKServer.ChronologicalRoster

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! One universal finite radius seed covers every possible input-driven
center, so the seed law is independent of the hidden input. -/
noncomputable section
namespace UniformKServer.TierRadius
open FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X]

attribute [local instance] OAI.UniformKServer.TierRadius.pairDecEq
omit [Fintype X] in
theorem cover_outer (lam r : ℝ) (hr : 0 < r) (ω : Sample (X:=X) lam r)
    (c p : X) (hc : ω.val (c,p)=true) : dist c p < 2*r := by
  by_contra hd
  have hd' : 2 ≤ dist c p/r := (le_div_iff₀ hr).mpr (le_of_not_gt hd)
  obtain ⟨u,hu,he⟩ := ω.property
  rw [he] at hc
  simp only [FiniteThreshold.threshold,decide_eq_true_eq,probability,RadiusTail.tail_eq_zero lam _ hd'] at hc
  exact (not_le_of_gt hu.1) hc

end UniformKServer.TierRadius

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section

/-! The actual persistent-radius tape controls all roster keys at once;
conditioning on arbitrary independent lifetimes leaves these estimates valid. -/
noncomputable section
namespace UniformKServer.TierKeys
open FiniteProbability Finset
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I] [LinearOrder I] {X : Type} [Fintype X] [MetricSpace X]

attribute [local instance] OAI.UniformKServer.TierKeys.pairDecEq
omit [Fintype I] [LinearOrder I] [Fintype X] in
theorem key_covers (lam r : ℝ) (is : List I) (c : I → X) (ω : I → TierRadius.Sample (X:=X) lam r)
    (p : X) (i : I) (hi : key lam r is c ω p=some i) : (ω i).val (c i,p)=true := by
  exact List.find?_some (p:=fun j => (ω j).val (c j,p)) hi

end UniformKServer.TierKeys

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierPilot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TierPilot

section
attribute [local instance] Classical.propDecidable
open PilotCompact

variable {X : Type*} [Fintype X] [MetricSpace X]

theorem ballMass_nonneg (r a : ℝ) (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X) :
    0 ≤ ballMass r a μ x := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> first | exact hμ p | rfl

theorem annulus_identity (r a b : ℝ) (hr : 0 ≤ r) (hab : a ≤ b) (μ : X → ℝ) (x : X) :
    ballMass r b μ x-ballMass r a μ x =
      ∑ p, if a*r < dist x p ∧ dist x p ≤ b*r then μ p else 0 := by
  simp only [ballMass,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hm := mul_le_mul_of_nonneg_right hab hr
  by_cases ha : dist x p ≤ a*r
  · have hb : dist x p ≤ b*r := ha.trans hm
    simp [ha,hb,not_lt.mpr ha]
  · have ha' : a*r < dist x p := lt_of_not_ge ha
    simp [ha,ha']

theorem insertionMass_bounds (P : Parameters) (r : ℝ) (hr : 0 ≤ r)
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X) :
    0 ≤ insertionMass P r μ x ∧ insertionMass P r μ x ≤ ballMass r 20480000 μ x := by
  have hm := ballMass_mono r P.gammaH 51200 hr (by linarith [P.gammaH_small]) μ hμ x
  have hbig := ballMass_mono r 51200 20480000 hr (by norm_num) μ hμ x
  have hn := ballMass_nonneg r P.gammaH μ hμ x
  unfold insertionMass
  split_ifs
  · constructor <;> linarith
  · exact ⟨ballMass_nonneg r 20480000 μ hμ x,le_rfl⟩

theorem residual_bounds (P : Parameters) (r : ℝ) (z : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (p : X) :
    (1-∑ s, z s*bumpB P.sigma (dist s p/r)) ∈ Set.Icc (0:ℝ) 1 := by
  have h := weighted_bumpB_sum r P.sigma 204800 P.sigma_pos P.sigma_le_one
    (by norm_num) z hz p
  constructor <;> linarith [h.1,h.2]

theorem variation_nonneg (P : Parameters) (r : ℝ) (z f : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (hf : ∀ p, 0 ≤ f p) (p : X) :
    0 ≤ variation r P.sigma z f p := by
  apply add_nonneg
  · exact mul_nonneg (hf p) (residual_bounds P r z hz p).1
  · apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hz.1 s) (hf s))
      (bumpA_bounds P.sigma 204800 _ (by norm_num)).1

theorem variation_mono (P : Parameters) (r : ℝ) (z f g : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (hfg : ∀ p, f p ≤ g p) (p : X) :
    variation r P.sigma z f p ≤ variation r P.sigma z g p := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (hfg p) (residual_bounds P r z hz p).1
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hfg s) (hz.1 s)) (bumpA_bounds P.sigma 204800 _ (by norm_num)).1

theorem variation_constant_bound (P : Parameters) (r ε : ℝ) (hε : 0 ≤ ε) (z : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (p : X) : variation r P.sigma z (fun _ => ε) p ≤ 257*ε := by
  have hB := (residual_bounds P r z hz p).2
  have hA : (∑ s, z s*bumpA P.sigma 204800 (dist s p/r)) ≤ 1 :=
    (Finset.sum_le_sum fun s _ => weighted_bumpA P.sigma 204800 _ _ (by norm_num) (hz.1 s)).trans (hz.2.1 p)
  have heq : (∑ s, z s*ε*bumpA P.sigma 204800 (dist s p/r)) =
      ε*∑ s, z s*bumpA P.sigma 204800 (dist s p/r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  unfold variation
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hB hε, mul_le_mul_of_nonneg_left hA hε]

omit [Fintype X] [MetricSpace X] in
theorem plateau (σ R v : ℝ) (hσ : 0 < σ) (hlo : σ ≤ v) (hhi : v ≤ R) :
    bumpA σ R v = 1 := by
  simp only [bumpA,ite_eq_left hhi]
  apply min_eq_right
  apply (le_div_iff₀ (sq_pos_of_pos hσ)).mpr
  nlinarith

omit [Fintype X] in
theorem heavy_coefficient_lower (P : Parameters) (r : ℝ) (hr : 0 < r)
    (go : X → ℝ) (hg : ∀ p, go p ∈ Set.Icc (0:ℝ) 1) (x c p : X)
    (hc : r/8 < dist x c ∧ dist x c ≤ 21*r) :
    256*(if dist x p ≤ P.gammaH*r then 1 else 0) -
      2*(if dist x p ≤ 51200*r then 1 else 0) ≤
        coefficient r P.sigma 204800 go c p := by
  have hcx : 1/8 < dist c x/r ∧ dist c x/r ≤ 21 := by
    rw [dist_comm c x]
    constructor
    · apply (lt_div_iff₀ hr).mpr
      linarith [hc.1]
    · exact (div_le_iff₀ hr).mpr hc.2
  have hA : (if dist x p ≤ P.gammaH*r then 1 else 0) ≤
      bumpA P.sigma 204800 (dist c p/r) := by
    split_ifs with hp
    · have hpx := (div_le_iff₀ hr).mpr hp
      have ht := normalized_triangle r hr c p x
      have ht' := normalized_triangle r hr c x p
      rw [dist_comm p x] at ht
      rw [plateau P.sigma 204800 _ P.sigma_pos
        (by linarith [P.sigma_small,P.gammaH_small,hcx.1])
        (by linarith [P.gammaH_small,hcx.2])]
    · exact (bumpA_bounds _ _ _ (by norm_num)).1
  have hB : bumpB P.sigma (dist c p/r) ≤ (if dist x p ≤ 51200*r then 1 else 0) := by
    split_ifs with hp
    · exact (bumpB_bounds _ _).2
    · have hpx := (lt_div_iff₀ hr).mpr (lt_of_not_ge hp)
      have ht := normalized_triangle r hr x c p
      rw [dist_comm x c] at ht
      rw [bumpB_zero P.sigma _ P.sigma_pos (by linarith [hcx.2,P.sigma_le_one])]
  have hcoeff : 256*bumpA P.sigma 204800 (dist c p/r)-2*bumpB P.sigma (dist c p/r) ≤
      coefficient r P.sigma 204800 go c p := by
    unfold coefficient
    nlinarith [mul_nonneg (hg c).1 (bumpA_bounds P.sigma 204800 (dist c p/r) (by norm_num)).1,
      mul_nonneg (show 0 ≤ 1-go p by linarith [(hg p).2]) (bumpB_bounds P.sigma (dist c p/r)).1]
  linarith

theorem increasing_site_zero (P : Parameters) (r ε : ℝ) (hr : 0 < r)
    (μ go gn z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hM : 0 < ballMass r P.gammaH μ x) (hh : heavy P r μ x)
    (he : Edit r ε x go gn) (hz : feasible r P.sigma 204800 z)
    (hmin : objective r P.sigma 204800 μ go z = value r P.sigma 204800 μ go)
    (c : X) (hc : go c < gn c) : z c = 0 := by
  classical
  have hcoef : 256*ballMass r P.gammaH μ x-2*ballMass r 51200 μ x ≤
      ∑ p, μ p*coefficient r P.sigma 204800 go c p := by
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left
        (heavy_coefficient_lower P r hr go he.old_range x c p (he.support c hc)) (hμ p))
    have hid : (∑ p, μ p*(256*(if dist x p ≤ P.gammaH*r then 1 else 0)-
        2*(if dist x p ≤ 51200*r then 1 else 0))) =
        256*ballMass r P.gammaH μ x-2*ballMass r 51200 μ x := by
      simp only [ballMass,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rwa [hid] at hi
  have hmass : ballMass r 51200 μ x ≤ 2*ballMass r P.gammaH μ x := by
    have hd : P.deltaH*ballMass r P.gammaH μ x ≤ ballMass r P.gammaH μ x := by
      have := mul_le_mul_of_nonneg_right
        (show P.deltaH ≤ 1 by linarith [P.deltaH_small]) hM.le
      simpa using this
    dsimp [heavy] at hh
    nlinarith
  have hpos : 0 < ∑ p, μ p*coefficient r P.sigma 204800 go c p := by linarith
  have hval := value_le r P.sigma 204800 μ go (Function.update z c 0) (erase_feasible r P.sigma 204800 z hz c)
  have hdiff := objective_erase r P.sigma 204800 μ go z c
  rw [hmin] at hdiff
  by_contra hn
  have hzc : 0 < z c := lt_of_le_of_ne (hz.1 c) (Ne.symm hn)
  have hmul := mul_pos (mul_pos hr hzc) hpos
  linarith

theorem rise_nonheavy_point (P : Parameters) (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε)
    (x : X) (go gn z : X → ℝ) (he : Edit r ε x go gn)
    (hz : feasible r P.sigma 204800 z) (p : X) :
    variation r P.sigma z (rise go gn) p ≤
      257*ε*(if dist x p ≤ 20480000*r then 1 else 0) := by
  by_cases hp : dist x p ≤ 20480000*r
  · rw [ite_eq_left hp,mul_one]
    exact (variation_mono P r z _ _ hz (rise_bound r ε hε x go gn he) p).trans
      (variation_constant_bound P r ε hε z hz p)
  · rw [ite_eq_right hp,mul_zero]
    have hzero : rise go gn p = 0 := by
      by_contra hn
      have h := (rise_support r ε x go gn he p hn).2
      linarith [lt_of_not_ge hp]
    have hsum : (∑ s, z s*rise go gn s*bumpA P.sigma 204800 (dist s p/r)) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      by_cases hs : rise go gn s = 0
      · simp [hs]
      · have hxs := (rise_support r ε x go gn he s hs).2
        have ht := dist_triangle x s p
        have hd : 2*(204800:ℝ) ≤ dist s p/r := by
          apply (le_div_iff₀ hr).mpr
          linarith [lt_of_not_ge hp]
        rw [bumpA_zero P.sigma 204800 _ (by norm_num) hd,mul_zero]
    simp [variation,hzero,hsum]

theorem rise_heavy_point (P : Parameters) (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε)
    (μ go gn z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hM : 0 < ballMass r P.gammaH μ x) (hh : heavy P r μ x)
    (he : Edit r ε x go gn) (hz : feasible r P.sigma 204800 z)
    (hmin : objective r P.sigma 204800 μ go z = value r P.sigma 204800 μ go)
    (p : X) : variation r P.sigma z (rise go gn) p ≤
      ε*(if P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r then 1 else 0) := by
  have hsum : (∑ s, z s*rise go gn s*bumpA P.sigma 204800 (dist s p/r)) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : go s < gn s
    · rw [increasing_site_zero P r ε hr μ go gn z hμ x hM hh he hz hmin s hs]
      ring
    · rw [rise_zero go gn s (le_of_not_gt hs)]
      ring
  simp only [variation,hsum,mul_zero,add_zero]
  have hbound := mul_le_mul_of_nonneg_left (residual_bounds P r z hz p).2 (rise_nonneg go gn p)
  by_cases hp : P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r
  · rw [ite_eq_left hp,mul_one]
    exact (by simpa using hbound : rise go gn p*(1-∑ s, z s*bumpB P.sigma (dist s p/r)) ≤ rise go gn p).trans
      (rise_bound r ε hε x go gn he p)
  · have hn : rise go gn p = 0 := by
      by_contra hne
      have hd := rise_support r ε x go gn he p hne
      apply hp
      constructor
      · nlinarith [P.gammaH_small]
      · linarith [hd.2]
    simp [hn,hp]

theorem rise_integral_bound (P : Parameters) (r ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε)
    (μ go gn z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hM : 0 < ballMass r P.gammaH μ x)
    (he : Edit r ε x go gn) (hz : feasible r P.sigma 204800 z)
    (hmin : objective r P.sigma 204800 μ go z = value r P.sigma 204800 μ go) :
    (∑ p, μ p*variation r P.sigma z (rise go gn) p) ≤
      257*ε*insertionMass P r μ x := by
  by_cases hh : heavy P r μ x
  · have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left (rise_heavy_point P r ε hr hε μ go gn z hμ x hM hh he hz hmin p) (hμ p))
    have hid : (∑ p, μ p*(ε*(if P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r then 1 else 0))) =
        ε*insertionMass P r μ x := by
      rw [insertionMass,ite_eq_left hh,annulus_identity r P.gammaH 51200 hr.le (by linarith [P.gammaH_small]),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rw [hid] at hi
    have hn := (insertionMass_bounds P r hr.le μ hμ x).1
    nlinarith [mul_nonneg hε hn]
  · have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left (rise_nonheavy_point P r ε hr hε x go gn z he hz p) (hμ p))
    have hid : (∑ p, μ p*(257*ε*(if dist x p ≤ 20480000*r then 1 else 0))) =
        257*ε*insertionMass P r μ x := by
      simp only [insertionMass,ite_eq_right hh,ballMass,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rwa [hid] at hi

theorem fall_near_point (P : Parameters) (r ε : ℝ) (hr : 0 < r)
    (x : X) (go gn z : X → ℝ) (he : Edit r ε x go gn)
    (hz : feasible r P.sigma 204800 z) (s : X)
    (hxs : dist x s ≤ 3*P.sigma*r) (hzs : 1/2 ≤ z s) (p : X) :
    128*(if P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r then 1 else 0) ≤
      variation r P.sigma z (fall go gn) p := by
  have hn := variation_nonneg P r z (fall go gn) hz (fall_nonneg go gn) p
  by_cases hp : P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r
  · rw [ite_eq_left hp,mul_one]
    have hfs := fall_unit r ε x go gn he s (by nlinarith [P.sigma_small])
    have hA : bumpA P.sigma 204800 (dist s p/r) = 1 := by
      apply plateau P.sigma 204800 _ P.sigma_pos
      · apply (le_div_iff₀ hr).mpr
        have := dist_triangle x s p
        nlinarith [P.sigma_gamma,P.sigma_pos]
      · apply (div_le_iff₀ hr).mpr
        have := dist_triangle s x p
        rw [dist_comm s x] at this
        nlinarith [P.sigma_le_one,hp.2]
    have hs := Finset.single_le_sum (s := Finset.univ) (a := s)
      (fun t _ => mul_nonneg (mul_nonneg (hz.1 t) (fall_nonneg go gn t))
        (bumpA_bounds P.sigma 204800 (dist t p/r) (by norm_num)).1) (Finset.mem_univ s)
    rw [hfs,hA,mul_one,mul_one] at hs
    have hres := mul_nonneg (fall_nonneg go gn p) (residual_bounds P r z hz p).1
    unfold variation
    linarith
  · rw [ite_eq_right hp,mul_zero]
    exact hn

theorem residual_half (P : Parameters) (r : ℝ) (hr : 0 < r) (z : X → ℝ)
    (hz : feasible r P.sigma 204800 z) (x : X)
    (hnear : ¬∃ s, dist x s ≤ 3*P.sigma*r ∧ 1/2 ≤ z s)
    (p : X) (hp : dist x p ≤ P.gammaL*r) :
    1/2 ≤ 1-∑ s, z s*bumpB P.sigma (dist s p/r) := by
  have hsum : (∑ s, z s*bumpB P.sigma (dist s p/r)) ≤ 1/2 := by
    apply sum_le_unique _ _ (by norm_num)
    · intro s
      by_cases hb : 0 < bumpB P.sigma (dist s p/r)
      · have hd : dist s p/r < 2*P.sigma := by
          by_contra hn
          rw [bumpB_zero P.sigma _ P.sigma_pos (le_of_not_gt hn)] at hb
          linarith
        have hxs : dist x s ≤ 3*P.sigma*r := by
          have ht := dist_triangle x p s
          rw [dist_comm p s] at ht
          have := (div_lt_iff₀ hr).mp hd
          nlinarith [P.gammaL_small]
        have hzs : z s < 1/2 := lt_of_not_ge (fun hs => hnear ⟨s,hxs,hs⟩)
        calc
          z s*bumpB P.sigma (dist s p/r) ≤ z s*1 :=
            mul_le_mul_of_nonneg_left (bumpB_bounds _ _).2 (hz.1 s)
          _ ≤ 1/2 := by linarith
      · have hzero : bumpB P.sigma (dist s p/r) = 0 :=
          le_antisymm (le_of_not_gt hb) (bumpB_bounds _ _).1
        norm_num [hzero]
    · exact positive_bump_unique r P.sigma 204800 hr P.sigma_pos z hz p
  linarith

theorem fall_far_point (P : Parameters) (r ε : ℝ) (hr : 0 < r)
    (x : X) (go gn z : X → ℝ) (he : Edit r ε x go gn)
    (hz : feasible r P.sigma 204800 z)
    (hnear : ¬∃ s, dist x s ≤ 3*P.sigma*r ∧ 1/2 ≤ z s) (p : X) :
    (1/2)*(if dist x p ≤ P.gammaL*r then 1 else 0) ≤
      variation r P.sigma z (fall go gn) p := by
  by_cases hp : dist x p ≤ P.gammaL*r
  · rw [ite_eq_left hp,mul_one]
    have hfp := fall_unit r ε x go gn he p (by nlinarith [P.gammaL_small,P.sigma_small])
    have hres := residual_half P r hr z hz x hnear p hp
    have hs : 0 ≤ ∑ s, z s*fall go gn s*bumpA P.sigma 204800 (dist s p/r) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hz.1 s) (fall_nonneg go gn s))
        (bumpA_bounds P.sigma 204800 _ (by norm_num)).1
    unfold variation
    rw [hfp,one_mul]
    linarith
  · rw [ite_eq_right hp,mul_zero]
    exact variation_nonneg P r z _ hz (fall_nonneg go gn) p

theorem qualification_inner (P : Parameters) (r h : ℝ) (hr : 0 ≤ r)
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hqual : ballMass r 20480000 μ x ≤ Real.exp h*ballMass r P.gammaL μ x) :
    Real.exp (-h)*insertionMass P r μ x ≤ ballMass r P.gammaL μ x := by
  have hi := mul_le_mul_of_nonneg_left
    ((insertionMass_bounds P r hr μ hμ x).2.trans hqual) (Real.exp_pos (-h)).le
  have he : Real.exp (-h)*Real.exp h = 1 := by rw [←Real.exp_add]; simp
  simpa only [←mul_assoc,he,one_mul] using hi

theorem fall_integral_bound (P : Parameters) (r ε h : ℝ) (hr : 0 < r) (hh : 0 ≤ h)
    (μ go gn z : X → ℝ) (hμ : ∀ p, 0 ≤ μ p) (x : X)
    (hqual : ballMass r 20480000 μ x ≤ Real.exp h*ballMass r P.gammaL μ x)
    (he : Edit r ε x go gn) (hz : feasible r P.sigma 204800 z) :
    min (1/2) (128*P.deltaH)*Real.exp (-h)*insertionMass P r μ x ≤
      ∑ p, μ p*variation r P.sigma z (fall go gn) p := by
  have hinner := qualification_inner P r h hr.le μ hμ x hqual
  have hW := (insertionMass_bounds P r hr.le μ hμ x).1
  have hc : 0 ≤ min (1/2:ℝ) (128*P.deltaH) := le_min (by norm_num) (mul_nonneg (by norm_num) P.deltaH_pos.le)
  by_cases hnear : ∃ s, dist x s ≤ 3*P.sigma*r ∧ 1/2 ≤ z s
  · obtain ⟨s,hxs,hzs⟩ := hnear
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left (fall_near_point P r ε hr x go gn z he hz s hxs hzs p) (hμ p))
    have hid : (∑ p, μ p*(128*(if P.gammaH*r < dist x p ∧ dist x p ≤ 51200*r then 1 else 0))) =
        128*(ballMass r 51200 μ x-ballMass r P.gammaH μ x) := by
      rw [annulus_identity r P.gammaH 51200 hr.le (by linarith [P.gammaH_small]),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rw [hid] at hi
    by_cases hheavy : heavy P r μ x
    · have hidW : insertionMass P r μ x = ballMass r 51200 μ x-ballMass r P.gammaH μ x := ite_eq_left hheavy
      have he1 : Real.exp (-h) ≤ 1 := by simpa using Real.exp_le_exp.mpr (show -h ≤ 0 by linarith)
      have hce : min (1/2:ℝ) (128*P.deltaH)*Real.exp (-h) ≤ 128 := by
        have := mul_le_mul_of_nonneg_left he1 hc
        linarith [min_le_left (1/2:ℝ) (128*P.deltaH)]
      have hm := mul_le_mul_of_nonneg_right hce hW
      rw [hidW] at hm
      simpa only [hidW] using hm.trans hi
    · have hann : P.deltaH*ballMass r P.gammaL μ x ≤
          ballMass r 51200 μ x-ballMass r P.gammaH μ x := by
        have hLH := ballMass_mono r P.gammaL P.gammaH hr.le
          (by linarith [P.gammaL_small,P.sigma_gamma,P.sigma_pos]) μ hμ x
        have hh' := lt_of_not_ge hheavy
        change (1+P.deltaH)*ballMass r P.gammaH μ x < ballMass r 51200 μ x at hh'
        nlinarith [mul_le_mul_of_nonneg_left hLH P.deltaH_pos.le]
      have hci := mul_le_mul_of_nonneg_left hinner hc
      have hcM := mul_le_mul_of_nonneg_right (min_le_right (1/2:ℝ) (128*P.deltaH))
        (ballMass_nonneg r P.gammaL μ hμ x)
      nlinarith
  · have hi := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      mul_le_mul_of_nonneg_left (fall_far_point P r ε hr x go gn z he hz hnear p) (hμ p))
    have hid : (∑ p, μ p*((1/2)*(if dist x p ≤ P.gammaL*r then 1 else 0))) =
        (1/2)*ballMass r P.gammaL μ x := by
      simp only [ballMass,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rw [hid] at hi
    have hci := mul_le_mul_of_nonneg_left hinner hc
    have hcM := mul_le_mul_of_nonneg_right (min_le_left (1/2:ℝ) (128*P.deltaH))
      (ballMass_nonneg r P.gammaL μ hμ x)
    nlinarith

end
open PilotCompact
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- Source tier-pilot drop with explicit absolute constants. The later
short-roster bound substitutes ε ≤ C/√K. -/
theorem insertion_gain (P : Parameters) (r ε h : ℝ) (hr : 0 < r)
    (hε : 0 ≤ ε) (hh : 1 ≤ h) (μ go gn : X → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    (x : X) (hM : 0 < ballMass r P.gammaH μ x)
    (hqual : ballMass r 20480000 μ x ≤ Real.exp h*ballMass r P.gammaL μ x)
    (he : Edit r ε x go gn) :
    r*insertionMass P r μ x*
      (min (1/2) (128*P.deltaH)*Real.exp (-h)-257*ε) ≤
        value r P.sigma 204800 μ go-value r P.sigma 204800 μ gn
 := by
  classical
  obtain ⟨z,hz,hmin,_⟩ := minimum_exists r P.sigma 204800 μ go
  have hrise := rise_integral_bound P r ε hr hε μ go gn z hμ x hM he hz hmin
  have hfall := fall_integral_bound P r ε h hr (by linarith) μ go gn z hμ x hqual he hz
  have hsplit : (fun p => go p-gn p) = (fun p => fall go gn p-rise go gn p) := by
    funext p
    simp only [fall,rise]
    by_cases hp : go p ≤ gn p
    · rw [max_eq_right (sub_nonpos.mpr hp),max_eq_left (sub_nonneg.mpr hp)]
      ring
    · have hp' := le_of_not_ge hp
      rw [max_eq_left (sub_nonneg.mpr hp'),max_eq_right (sub_nonpos.mpr hp')]
      ring
  have hid : objective r P.sigma 204800 μ go z-objective r P.sigma 204800 μ gn z =
      r*((∑ p, μ p*variation r P.sigma z (fall go gn) p)-
        ∑ p, μ p*variation r P.sigma z (rise go gn) p) := by
    simp only [objective,←mul_sub,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [integrand_variation,hsplit,variation_sub]
  have hv := value_le r P.sigma 204800 μ gn z hz
  rw [hmin] at hid
  have hi := mul_le_mul_of_nonneg_left (sub_le_sub hfall hrise) hr.le
  nlinarith

end UniformKServer.TierPilot

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ShortRoster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ShortRoster

section
open FiniteProbability
variable {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable

def editedValue (a : I → ℝ) (b : ℝ) (inc kill : I → Prop)
    (H : Finset I) (τ : I → Bool) : ℝ := min b (costValue a (retained inc kill H τ))

omit [Fintype I] in
theorem cost_bounds (a : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) (H : Finset I) :
    costValue a H ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · apply Finset.le_min'
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact (ha i).1
  · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

omit [Fintype I] in
theorem cost_le (a : I → ℝ) (H : Finset I) (i : I) (hi : i ∈ H) : costValue a H ≤ a i :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,hi,rfl⟩))

omit [Fintype I] in
theorem le_cost (a : I → ℝ) (H : Finset I) (v : ℝ) (h1 : v ≤ 1)
    (h : ∀ i ∈ H, v ≤ a i) : v ≤ costValue a H := by
  apply Finset.le_min'
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact h1
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact h i hi

omit [Fintype I] in
theorem cost_witness (a : I → ℝ) (H : Finset I) (h : costValue a H < 1) :
    ∃ i ∈ H, a i = costValue a H := by
  have hm := Finset.min'_mem (insert 1 (H.image a)) (by simp)
  change costValue a H ∈ insert 1 (H.image a) at hm
  rcases Finset.mem_insert.mp hm with he | hm
  · linarith
  · exact Finset.mem_image.mp hm

omit [Fintype I] in
theorem cost_close (a b : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (hb : ∀ i, b i ∈ Set.Icc (0:ℝ) 1) (d : ℝ) (hd : 0 ≤ d)
    (hab : ∀ i, |a i-b i| ≤ d) (H : Finset I) :
    |costValue a H-costValue b H| ≤ d := by
  suffices hh : ∀ a b : I → ℝ, (∀ i, a i ∈ Set.Icc (0:ℝ) 1) →
      (∀ i, b i ∈ Set.Icc (0:ℝ) 1) → (∀ i, a i-b i ≤ d) →
      costValue a H-costValue b H ≤ d by
    apply abs_le.mpr
    constructor
    · have hi := hh b a hb ha (fun i => by have := (abs_le.mp (hab i)).1; linarith)
      linarith
    · exact hh a b ha hb (fun i => (le_abs_self _).trans (hab i))
  intro a b ha hb hab
  by_cases hm : costValue b H < 1
  · obtain ⟨i,hi,he⟩ := cost_witness b H hm
    linarith [cost_le a H i hi,hab i]
  · have he : costValue b H = 1 := le_antisymm (cost_bounds b hb H).2 (le_of_not_gt hm)
    rw [he]
    linarith [(cost_bounds a ha H).2]

omit [Fintype I] in
theorem edited_bounds (a : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Icc (0:ℝ) 1) (inc kill : I → Prop)
    (H : Finset I) (τ : I → Bool) : editedValue a b inc kill H τ ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min hb.1 (cost_bounds a ha _).1,(min_le_left _ _).trans hb.2⟩

omit [Fintype I] in
theorem edited_le_retained (a : I → ℝ) (b : ℝ) (inc kill : I → Prop)
    (H : Finset I) (τ : I → Bool) (i : I) (hi : i ∈ H)
    (hkeep : ¬inc i ∨ (¬kill i ∧ τ i = true)) : editedValue a b inc kill H τ ≤ a i :=
  (min_le_right _ _).trans (cost_le a _ i (Finset.mem_filter.mpr ⟨hi,hkeep⟩))

theorem conditional_increase (a : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Icc (0:ℝ) 1) (inc kill : I → Prop)
    (H : Finset I) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    (fresh (I := I) q hq).expect (fun τ => editedValue a b inc kill H τ-costValue a H) ≤
      q+∑ i, if i ∈ H ∧ inc i ∧ kill i ∧ a i < 1 then 1 else 0 := by
  classical
  let Q := fresh (I := I) q hq
  have hs : 0 ≤ ∑ i : I, if i ∈ H ∧ inc i ∧ kill i ∧ a i < 1 then (1:ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have trivialBound (τ : I → Bool) : editedValue a b inc kill H τ-costValue a H ≤ 1 := by
    linarith [(edited_bounds a ha b hb inc kill H τ).2,(cost_bounds a ha H).1]
  by_cases hm : costValue a H < 1
  · obtain ⟨i,hi,he⟩ := cost_witness a H hm
    by_cases hinc : inc i
    · by_cases hkill : kill i
      · have hsite : (1:ℝ) ≤ ∑ j : I, if j ∈ H ∧ inc j ∧ kill j ∧ a j < 1 then 1 else 0 := by
          have hi' : a i < 1 := by linarith
          have hx := Finset.single_le_sum (s := Finset.univ) (a := i)
            (f := fun j : I => if j ∈ H ∧ inc j ∧ kill j ∧ a j < 1 then (1:ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
          simpa only [ite_eq_left (show i ∈ H ∧ inc i ∧ kill i ∧ a i < 1 from ⟨hi,hinc,hkill,hi'⟩)] using hx
        have hv := Q.expect_mono _ _ trivialBound
        rw [Q.expect_const] at hv
        exact hv.trans (by linarith [hq.1])
      · have hp : ∀ τ, editedValue a b inc kill H τ-costValue a H ≤ if τ i then 0 else 1 := by
          intro τ
          cases ht : τ i
          · simpa [ht] using trivialBound τ
          · have hh := edited_le_retained a b inc kill H τ i hi (Or.inr ⟨hkill,ht⟩)
            simpa only [ht,Bool.true_eq,ite_true, if_true] using (show editedValue a b inc kill H τ-costValue a H ≤ 0 by linarith)
        have hv := Q.expect_mono _ _ hp
        have hQ : Q.expect (fun τ => if τ i then 0 else 1) = q := by
          calc
            _ = 1-(1-q) := coins_false (fun _ : I => 1-q)
              (fun _ => ⟨by linarith [hq.2],by linarith [hq.1]⟩) i
            _ = q := by ring
        rw [hQ] at hv
        exact hv.trans (by linarith)
    · have hp : ∀ τ, editedValue a b inc kill H τ-costValue a H ≤ 0 := by
        intro τ
        have hh := edited_le_retained a b inc kill H τ i hi (Or.inl hinc)
        linarith
      have hv := Q.expect_mono _ _ hp
      rw [Q.expect_const] at hv
      exact hv.trans (by linarith [hq.1])
  · have he : costValue a H = 1 := le_antisymm (cost_bounds a ha H).2 (le_of_not_gt hm)
    have hp : ∀ τ, editedValue a b inc kill H τ-costValue a H ≤ 0 := by
      intro τ
      rw [he]
      exact sub_nonpos.mpr (edited_bounds a ha b hb inc kill H τ).2
    have hv := Q.expect_mono _ _ hp
    rw [Q.expect_const] at hv
    exact hv.trans (by linarith [hq.1])

end

section
open FiniteProbability
attribute [local instance] Classical.propDecidable

variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]

def State.Valid (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ) (q : ℝ) : Prop :=
  (∀ ω, D.live ω ⊆ ChronologicalRoster.young S c r K) ∧
  (∀ i, D.law.expect (fun ω => if i ∈ D.live ω then 1 else 0) =
    if i ∈ S ∧ ChronologicalRoster.age S c r i < K then
      (1-q)^ChronologicalRoster.age S c r i else 0)

end

section
attribute [local instance] Classical.propDecidable
open FiniteProbability
variable {I Ω : Type*} [Fintype I] [Fintype Ω]

theorem mean_increase (P : Law Ω) (H : Ω → Finset I)
    (a : I → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Icc (0:ℝ) 1) (inc kill : I → Prop)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (C : Finset I)
    (s : ℝ) (hs : 0 ≤ s) (A : ℕ) (hcard : C.card ≤ A)
    (hcover : ∀ ω i, i ∈ H ω → inc i → kill i → a i < 1 → i ∈ C)
    (hmarg : ∀ i ∈ C, P.expect (fun ω => if i ∈ H ω then 1 else 0) ≤ s) :
    P.expect (fun ω => (fresh (I := I) q hq).expect
      (fun τ => editedValue a b inc kill (H ω) τ)) - P.expect (fun ω => costValue a (H ω)) ≤
      q+(A:ℝ)*s := by
  classical
  let Q := fresh (I := I) q hq
  have hpoint (ω : Ω) : Q.expect (fun τ => editedValue a b inc kill (H ω) τ-costValue a (H ω)) ≤
      q+∑ i ∈ C, if i ∈ H ω then (1:ℝ) else 0 := by
    have h := conditional_increase a ha b hb inc kill (H ω) q hq
    have heq : (∑ i : I, if i ∈ H ω ∧ inc i ∧ kill i ∧ a i < 1 then (1:ℝ) else 0) =
        ∑ i ∈ C, if i ∈ H ω ∧ inc i ∧ kill i ∧ a i < 1 then (1:ℝ) else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      intro i _ hi
      split_ifs with hp
      · exact (hi (hcover ω i hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)).elim
      · rfl
    have hle : (∑ i ∈ C, if i ∈ H ω ∧ inc i ∧ kill i ∧ a i < 1 then (1:ℝ) else 0) ≤
        ∑ i ∈ C, if i ∈ H ω then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ H ω
      · simp only [ite_eq_left hi]
        split_ifs <;> norm_num
      · simp only [hi,false_and,ite_false, if_false,le_refl]
    rw [heq] at h
    exact h.trans (add_le_add le_rfl hle)
  have hmean := P.expect_mono _ _ hpoint
  have hleft : P.expect (fun ω => Q.expect (fun τ => editedValue a b inc kill (H ω) τ-costValue a (H ω))) =
      P.expect (fun ω => Q.expect (fun τ => editedValue a b inc kill (H ω) τ)) -
      P.expect (fun ω => costValue a (H ω)) := by
    simp only [Q.expect_sub,Q.expect_const,P.expect_sub]
  rw [hleft,P.expect_add,P.expect_const,P.expect_finset_sum] at hmean
  have hsum := Finset.sum_le_sum (s := C) (fun i hi => hmarg i hi)
  have hsum' : (∑ i ∈ C, P.expect (fun ω => if i ∈ H ω then (1:ℝ) else 0)) ≤ (A:ℝ)*s := by
    calc
      _ ≤ ∑ _i ∈ C, s := hsum
      _ = (C.card:ℝ)*s := by simp
      _ ≤ (A:ℝ)*s := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hs
  exact hmean.trans (add_le_add le_rfl hsum')

end

attribute [local instance] Classical.propDecidable
open FiniteProbability ChronologicalRoster
variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem ramp_bounds (v : ℝ) : ramp v ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem ramp_zero (v : ℝ) (hv : v ≤ 1/8) : ramp v = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem ramp_one (v : ℝ) (hv : 1/4 ≤ v) : ramp v = 1 := by
  unfold ramp
  rw [min_eq_left (by linarith)]
  norm_num

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem ramp_lip (v w : ℝ) : |ramp v-ramp w| ≤ 8*|v-w| := by
  have h₁ := abs_max_sub_max_le_max (0:ℝ) (min 1 (8*v-1)) 0 (min 1 (8*w-1))
  have h₂ := abs_min_sub_min_le_max (1:ℝ) (8*v-1) 1 (8*w-1)
  simp only [sub_self,abs_zero] at h₁ h₂
  rw [max_eq_right (abs_nonneg (min 1 (8*v-1)-min 1 (8*w-1)))] at h₁
  rw [max_eq_right (abs_nonneg (8*v-1-(8*w-1)))] at h₂
  have he : |8*v-1-(8*w-1)| = 8*|v-w| := by
    rw [show 8*v-1-(8*w-1)=8*(v-w) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<8)]
  exact h₁.trans (he ▸ h₂)

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem cost_insert (a : I → ℝ) (H : Finset I) (n : I) :
    costValue a (insert n H) = min (a n) (costValue a H) := by
  classical
  unfold costValue
  simp only [Finset.image_insert, Finset.insert_comm (1:ℝ) (a n)]
  exact Finset.min'_insert (a n) (insert 1 (H.image a)) (by simp)

omit [Fintype I] [LinearOrder I] in
theorem parameter_bounds (D : State I) (c : I → X) (r : ℝ) (p : X) :
    D.parameter c r p ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact D.law.expect_nonneg _ (fun ω => (cost_bounds _ (fun _ => ramp_bounds _) (D.live ω)).1)
  · have hi := D.law.expect_mono (fun ω => costValue (fun i => ramp (dist p (c i)/r)) (D.live ω))
      (fun _ => 1) (fun ω => (cost_bounds _ (fun _ => ramp_bounds _) (D.live ω)).2)
    simpa only [State.parameter,D.law.expect_const] using hi

omit [Fintype I] [LinearOrder I] in
theorem parameter_lip (D : State I) (c : I → X) (r : ℝ) (hr : 0 < r) (p y : X) :
    |D.parameter c r p-D.parameter c r y| ≤ 8*dist p y/r := by
  apply D.law.expect_close
  intro ω
  apply cost_close _ _ (fun _ => ramp_bounds _) (fun _ => ramp_bounds _) _ (by positivity)
  intro i
  have hi := ramp_lip (dist p (c i)/r) (dist y (c i)/r)
  have hd : |dist p (c i)/r-dist y (c i)/r| ≤ dist p y/r := by
    rw [←sub_div,abs_div,abs_of_pos hr]
    exact div_le_div_of_nonneg_right (abs_dist_sub_le p y (c i)) hr.le
  have := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 8)
  exact hi.trans (by simpa only [mul_div_assoc] using this)

theorem next_parameter (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I) (p : X) :
    (D.next S c r K q hq n).parameter c r p =
      D.law.expect (fun ω => (fresh (I := I) q hq).expect (fun τ =>
        editedValue (fun i => ramp (dist p (c i)/r)) (ramp (dist p (c n)/r))
          (fun i => dist (c i) (c n) ≤ 20*r)
          (fun i => K ≤ age S c r i+1) (D.live ω) τ)) := by
  change (D.law.prod (fresh q hq)).expect (fun ω =>
    costValue (fun i => ramp (dist p (c i)/r))
      (insert n (retained (fun i => dist (c i) (c n) ≤ 20*r)
        (fun i => K ≤ age S c r i+1) (D.live ω.1) ω.2))) = _
  rw [D.law.expect_prod (fresh q hq) (fun ω τ =>
    costValue (fun i => ramp (dist p (c i)/r))
      (insert n (retained (fun i => dist (c i) (c n) ≤ 20*r)
        (fun i => K ≤ age S c r i+1) (D.live ω) τ)))]
  apply D.law.expect_congr
  intro ω
  apply Law.expect_congr
  intro τ
  exact cost_insert _ _ _

theorem parameter_unit_drop (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : D.Valid S c r K q)
    (htest : ∀ i ∈ young S c r K, r/2 < dist (c n) (c i))
    (p : X) (hp : dist (c n) p ≤ r/8) :
    D.parameter c r p = 1 ∧ (D.next S c r K q hq n).parameter c r p = 0 := by
  constructor
  · have hpoint (ω : D.Sample) : costValue (fun i => ramp (dist p (c i)/r)) (D.live ω) = 1 := by
      apply le_antisymm (cost_bounds _ (fun _ => ramp_bounds _) _).2
      apply le_cost _ _ 1 le_rfl
      intro i hi
      have hd := htest i (hD.1 ω hi)
      have ht := dist_triangle (c n) p (c i)
      rw [ramp_one _ ((le_div_iff₀ hr).mpr (by linarith))]
    unfold State.parameter
    rw [D.law.expect_congr _ _ hpoint,D.law.expect_const]
  · apply le_antisymm _ (parameter_bounds _ _ _ _).1
    rw [next_parameter]
    have hp' : ramp (dist p (c n)/r) = 0 := by
      rw [dist_comm p (c n)]
      exact ramp_zero _ ((div_le_iff₀ hr).mpr (by linarith))
    have hpoint (ω : D.Sample) : (fresh (I := I) q hq).expect (fun τ =>
        editedValue (fun i => ramp (dist p (c i)/r)) (ramp (dist p (c n)/r))
          (fun i => dist (c i) (c n) ≤ 20*r) (fun i => K ≤ age S c r i+1) (D.live ω) τ) ≤ 0 := by
      have hi := (fresh (I := I) q hq).expect_mono
        (fun τ => editedValue (fun i => ramp (dist p (c i)/r)) (ramp (dist p (c n)/r))
          (fun i => dist (c i) (c n) ≤ 20*r) (fun i => K ≤ age S c r i+1) (D.live ω) τ)
        (fun _ => 0) (fun τ => by
        unfold editedValue
        rw [hp']
        exact min_le_left _ _)
      simpa only [Law.expect_const] using hi
    have hi := D.law.expect_mono _ _ hpoint
    simpa only [Law.expect_const] using hi

theorem parameter_far (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (p : X) (hp : 21*r < dist (c n) p) :
    (D.next S c r K q hq n).parameter c r p ≤ D.parameter c r p := by
  rw [next_parameter]
  apply D.law.expect_mono
  intro ω
  have hpoint (τ : I → Bool) :
      editedValue (fun i => ramp (dist p (c i)/r)) (ramp (dist p (c n)/r))
        (fun i => dist (c i) (c n) ≤ 20*r) (fun i => K ≤ age S c r i+1) (D.live ω) τ ≤
      costValue (fun i => ramp (dist p (c i)/r)) (D.live ω) := by
    apply le_cost _ _ _ (edited_bounds _ (fun _ => ramp_bounds _) _ (ramp_bounds _) _ _ _ _).2
    intro i hi
    by_cases hinc : dist (c i) (c n) ≤ 20*r
    · have hd : 1/4 ≤ dist p (c i)/r := by
        apply (le_div_iff₀ hr).mpr
        have ht := dist_triangle (c n) (c i) p
        rw [dist_comm (c n) (c i),dist_comm (c i) p] at ht
        linarith
      rw [ramp_one _ hd]
      exact (edited_bounds _ (fun _ => ramp_bounds _) _ (ramp_bounds _) _ _ _ _).2
    · exact edited_le_retained _ _ _ _ _ _ i hi (Or.inl hinc)
  have hi := (fresh (I := I) q hq).expect_mono _ _ hpoint
  simpa only [Law.expect_const] using hi

theorem parameter_increase (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : D.Valid S c r K q) (p : X) :
    (D.next S c r K q hq n).parameter c r p-D.parameter c r p ≤
      q+(K:ℝ)*(1-q)^(K-1) := by
  classical
  let a : I → ℝ := fun i => ramp (dist p (c i)/r)
  let C := (young S c r K).filter fun i => K ≤ age S c r i+1 ∧ a i < 1
  have hC : C ⊆ (young S c r K).filter (fun i => dist p (c i) ≤ r/4) := by
    intro i hi
    obtain ⟨hy,_,ha⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hy,?_⟩
    by_contra hn
    have hh : 1/4 ≤ dist p (c i)/r :=
      (le_div_iff₀ hr).mpr (by linarith [lt_of_not_ge hn])
    have he : a i = 1 := ramp_one _ hh
    linarith
  have hcard : C.card ≤ K := (Finset.card_le_card hC).trans
    (ball_young_count S c r (r/4) K p (by linarith))
  rw [next_parameter]
  apply mean_increase D.law D.live a (fun _ => ramp_bounds _)
    (ramp (dist p (c n)/r)) (ramp_bounds _) _ _ q hq C
    ((1-q)^(K-1)) (pow_nonneg (by linarith [hq.2]) _) K hcard
  · intro ω i hi _ hk ha
    exact Finset.mem_filter.mpr ⟨hD.1 ω hi,hk,ha⟩
  · intro i hi
    obtain ⟨hy,hkill,_⟩ := Finset.mem_filter.mp hi
    obtain ⟨hiS,hage⟩ := Finset.mem_filter.mp hy
    rw [hD.2 i,ite_eq_left ⟨hiS,hage⟩]
    have he : age S c r i = K-1 := by omega
    rw [he]

/-- Exact source short-roster edit, with the finite lifetime experiment
constructed by `State.next`. No drift or gain hypothesis is present. -/
theorem short_edit (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (_hK : 0 < K) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : D.Valid S c r K q) (_hn : ∀ i ∈ S, i < n)
    (htest : ∀ i ∈ young S c r K, r/2 < dist (c n) (c i)) :
    TierPilot.Edit r (q+(K:ℝ)*(1-q)^(K-1)) (c n)
      (D.parameter c r) ((D.next S c r K q hq n).parameter c r) := by
  refine ⟨parameter_bounds D c r,parameter_bounds _ c r,
    parameter_unit_drop D S c r hr K q hq n hD htest,
    parameter_increase D S c r hr K q hq n hD,?_⟩
  intro p hp
  constructor
  · by_contra hdist
    have he := parameter_unit_drop D S c r hr K q hq n hD htest p (le_of_not_gt hdist)
    rw [he.1,he.2] at hp
    norm_num at hp
  · by_contra hdist
    exact (not_lt_of_ge (parameter_far D S c r hr K q hq n p (lt_of_not_ge hdist))) hp

end UniformKServer.ShortRoster

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ShortRosterValidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section
namespace UniformKServer.ShortRoster
noncomputable section
attribute [local instance] Classical.propDecidable
open FiniteProbability ChronologicalRoster
variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]

attribute [local instance] OAI.UniformKServer.ShortRoster.rosterDecEq
omit [Fintype I] in
theorem State.empty_valid (c : I → X) (r : ℝ) (K : ℕ) (q : ℝ) :
    (State.empty (I := I)).Valid ∅ c r K q := by
  constructor
  · intro ω
    exact Finset.empty_subset _
  · intro i
    change (State.empty (I := I)).law.expect (fun _ => if i ∈ (∅ : Finset I) then 1 else 0) = _
    simp only [Finset.notMem_empty,ite_false, if_false,false_and,Law.expect_const]

theorem next_marginal (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n i : I) (hi : i ≠ n) :
    (D.next S c r K q hq n).law.expect (fun ω =>
      if i ∈ (D.next S c r K q hq n).live ω then 1 else 0) =
    (if dist (c i) (c n) ≤ 20*r then (if K ≤ age S c r i+1 then 0 else 1-q) else 1)*
      D.law.expect (fun ω => if i ∈ D.live ω then 1 else 0) := by
  change (D.law.prod (fresh q hq)).expect (fun ω =>
    if i ∈ insert n (retained (fun j => dist (c j) (c n) ≤ 20*r)
      (fun j => K ≤ age S c r j+1) (D.live ω.1) ω.2) then 1 else 0) = _
  rw [D.law.expect_prod (fresh q hq) (fun ω τ =>
    if i ∈ insert n (retained (fun j => dist (c j) (c n) ≤ 20*r)
      (fun j => K ≤ age S c r j+1) (D.live ω) τ) then 1 else 0)]
  simp only [Finset.mem_insert,hi,false_or,retained_marginal]
  conv_rhs => rw [←D.law.expect_mul]
  apply D.law.expect_congr
  intro ω
  by_cases hmem : i ∈ D.live ω
  · simp only [ite_eq_left hmem,one_mul,mul_one]
    split_ifs <;> rfl
  · simp only [ite_eq_right hmem,zero_mul,mul_zero]

theorem State.next_valid (D : State I) (S : Finset I) (c : I → X) (r : ℝ)
    (K : ℕ) (hK : 0 < K) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : D.Valid S c r K q) (hn : ∀ i ∈ S, i < n) :
    (D.next S c r K q hq n).Valid (insert n S) c r K q := by
  classical
  rw [insert_linear S n]
  constructor
  · intro ω i hi
    simp only [State.next,Finset.mem_insert] at hi
    obtain hei | hi := hi
    · subst i
      simp only [young,Finset.mem_filter,Finset.mem_insert_self,true_and]
      rw [new_age_zero S c r n hn]
      exact hK
    · have hi' : i ∈ D.live ω.1 ∧
          (¬dist (c i) (c n) ≤ 20*r ∨ (¬K ≤ age S c r i+1 ∧ ω.2 i = true)) := by
        simpa only [retained,Finset.mem_filter] using hi
      obtain ⟨hi,hstay⟩ := hi'
      obtain ⟨hiS,hage⟩ := Finset.mem_filter.mp (hD.1 ω.1 hi)
      simp only [young,Finset.mem_filter,Finset.mem_insert,hiS,or_true,true_and]
      rw [age_insert S c r n i hn hiS]
      by_cases hd : dist (c i) (c n) ≤ 20*r
      · rw [ite_eq_left hd]
        exact lt_of_not_ge ((hstay.resolve_left (not_not.mpr hd)).1)
      · simpa only [ite_eq_right hd,add_zero] using hage
  · intro i
    by_cases hi : i = n
    · subst i
      have he : ∀ ω, (if n ∈ (D.next S c r K q hq n).live ω then (1:ℝ) else 0) = 1 := by
        intro ω
        simp only [State.next,Finset.mem_insert_self,ite_true, if_true]
      rw [Law.expect_congr _ _ _ he,Law.expect_const,new_age_zero S c r n hn]
      simp only [Finset.mem_insert_self,hK,and_self,ite_true, if_true,pow_zero]
    · rw [next_marginal D S c r K q hq n i hi,hD.2]
      by_cases hiS : i ∈ S
      · rw [age_insert S c r n i hn hiS]
        simp only [Finset.mem_insert,hiS,or_true,true_and]
        by_cases hd : dist (c i) (c n) ≤ 20*r
        · rw [ite_eq_left hd,ite_eq_left hd]
          by_cases hk : K ≤ age S c r i+1
          · rw [ite_eq_left hk,ite_eq_right (not_lt.mpr hk),zero_mul]
          · have ha : age S c r i < K := by omega
            rw [ite_eq_right hk,ite_eq_left ha,ite_eq_left (lt_of_not_ge hk),pow_succ]
            exact mul_comm _ _
        · rw [ite_eq_right hd,ite_eq_right hd,add_zero,one_mul]
      · simp only [hiS,hi,Finset.mem_insert,false_or,false_and,ite_false, if_false,mul_zero]

end
end UniformKServer.ShortRoster

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualRoster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section
namespace UniformKServer.ActualRoster
noncomputable section
attribute [local instance] Classical.propDecidable
open FiniteProbability ChronologicalRoster ShortRoster
variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]

attribute [local instance] OAI.UniformKServer.ActualRoster.rosterDecEq
/-- Only an old selected covering record can trigger this event. The selector
may depend on the entire old roster and its persistent radii, but not on the
fresh lifetime trials. -/
def retires (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (n : I) (select : D.Sample → Option I) (ω : D.Sample) (τ : I → Bool) : Prop :=
  ∃ i, select ω = some i ∧ i ∈ D.live ω ∧
    i ∉ retained (active S c r K n) (compulsory S c r K) (D.live ω) τ
theorem conditional_retirement (D : State I) (S : Finset I) (c : I → X) (r : ℝ)
    (K : ℕ) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (n : I) (p : X)
    (select : D.Sample → Option I)
    (hcover : ∀ ω i, select ω = some i → dist p (c i) ≤ 2*r) (ω : D.Sample) :
    (fresh (I := I) (1/(K:ℝ)) hq).expect (fun τ =>
      if retires D S c r K n select ω τ then 1 else 0) ≤
    1/(K:ℝ)+∑ i : I, if i ∈ D.live ω ∧ compulsory S c r K i ∧ dist p (c i) ≤ 2*r
      then 1 else 0 := by
  classical
  have hsum : 0 ≤ ∑ i : I, if i ∈ D.live ω ∧ compulsory S c r K i ∧ dist p (c i) ≤ 2*r
      then (1:ℝ) else 0 := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  cases hsel : select ω with
  | none =>
    have he : ∀ τ, (if retires D S c r K n select ω τ then (1:ℝ) else 0) = 0 := by
      intro τ
      simp [retires,hsel]
    rw [Law.expect_congr _ _ _ he,Law.expect_const]
    linarith [hq.1]
  | some i =>
    have hd := hcover ω i hsel
    have he : ∀ τ, retires D S c r K n select ω τ ↔
        i ∈ D.live ω ∧ i ∉ retained (active S c r K n) (compulsory S c r K) (D.live ω) τ := by
      intro τ
      simp only [retires,hsel,Option.some.injEq,exists_eq_left']
    simp only [he]
    by_cases hi : i ∈ D.live ω
    · by_cases hcp : compulsory S c r K i
      · have hiTerm : (1:ℝ) ≤ ∑ j : I,
            if j ∈ D.live ω ∧ compulsory S c r K j ∧ dist p (c j) ≤ 2*r then 1 else 0 := by
          have hs := Finset.single_le_sum (f := fun j : I =>
            if j ∈ D.live ω ∧ compulsory S c r K j ∧ dist p (c j) ≤ 2*r then (1:ℝ) else 0)
            (s := Finset.univ) (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
          simpa only [hi,hcp,hd,and_self,ite_true, if_true] using hs
        have hb := (fresh (I := I) (1/(K:ℝ)) hq).expect_mono
          (fun τ => if i ∈ D.live ω ∧ i ∉ retained (active S c r K n) (compulsory S c r K) (D.live ω) τ then 1 else 0)
          (fun _ => 1) (fun τ => by split_ifs <;> norm_num)
        rw [Law.expect_const] at hb
        linarith [hq.1]
      · by_cases ha : active S c r K n i
        · have hind : ∀ τ, (if i ∈ D.live ω ∧ i ∉ retained (active S c r K n)
              (compulsory S c r K) (D.live ω) τ then (1:ℝ) else 0) = if τ i then 0 else 1 := by
            intro τ
            simp only [retained,Finset.mem_filter,hi,ha,hcp,not_true_eq_false,
              not_false_eq_true,true_and,false_or]
            cases τ i <;> norm_num
          rw [Law.expect_congr _ _ _ hind]
          have hc : (fresh (I := I) (1/(K:ℝ)) hq).expect
              (fun τ => if τ i then 0 else 1) = 1-(1-1/(K:ℝ)) := coins_false _ _ i
          rw [hc]
          linarith
        · have hind : ∀ τ, (if i ∈ D.live ω ∧ i ∉ retained (active S c r K n)
              (compulsory S c r K) (D.live ω) τ then (1:ℝ) else 0) = 0 := by
            intro τ
            simp [retained,hi,ha]
          rw [Law.expect_congr _ _ _ hind,Law.expect_const]
          linarith [hq.1]
    · simp only [hi,false_and,ite_false, if_false,Law.expect_const]
      linarith [hq.1]
/-- Source actual-retirement-bound, including arbitrary data-dependent first
coverer and the exact locality cutoff. Survival is averaged over the old law,
not falsely conditioned on a realized surviving old roster. -/
theorem first_retirement (D : State I) (S : Finset I) (c : I → X) (r : ℝ)
    (hr : 0 < r) (K : ℕ) (hK : 2 ≤ K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (n : I) (hD : valid D S c r K) (p : X) (select : D.Sample → Option I)
    (hcover : ∀ ω i, select ω = some i → dist p (c i) ≤ 2*r) :
    (D.law.prod (fresh (I := I) (1/(K:ℝ)) hq)).expect (fun ω =>
      if retires D S c r K n select ω.1 ω.2 then 1 else 0) ≤
        if dist (c n) p ≤ 22*r then 49/(K:ℝ) else 0
 := by
  classical
  by_cases hnear : dist (c n) p ≤ 22*r
  · rw [ite_eq_left hnear]
    let C := (young S c r (K^2)).filter fun i => compulsory S c r K i ∧ dist p (c i) ≤ 2*r
    have hC : C ⊆ (young S c r (K^2)).filter fun i => dist p (c i) ≤ 2*r := by
      intro i hi
      obtain ⟨hy,_,hd⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hy,hd⟩
    have hcard : C.card ≤ K^2 := (Finset.card_le_card hC).trans
      (ball_young_count S c r (2*r) (K^2) p (by linarith))
    have hpoint (ω : D.Sample) :
        (fresh (I := I) (1/(K:ℝ)) hq).expect (fun τ =>
          if retires D S c r K n select ω τ then 1 else 0) ≤
        1/(K:ℝ)+∑ i ∈ C, if i ∈ D.live ω then (1:ℝ) else 0 := by
      have hh := conditional_retirement D S c r K hq n p select hcover ω
      have heq : (∑ i : I, if i ∈ D.live ω ∧ compulsory S c r K i ∧ dist p (c i) ≤ 2*r
            then (1:ℝ) else 0) =
          ∑ i ∈ C, if i ∈ D.live ω ∧ compulsory S c r K i ∧ dist p (c i) ≤ 2*r then 1 else 0 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ C)
        intro i _ hi
        split_ifs with hp
        · exact (hi (Finset.mem_filter.mpr ⟨hD.1 ω hp.1,hp.2⟩)).elim
        · rfl
      rw [heq] at hh
      apply hh.trans
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ D.live ω
      · simp only [ite_eq_left hi]
        split_ifs <;> norm_num
      · simp only [hi,false_and,ite_false, if_false,le_refl]
    rw [D.law.expect_prod (fresh (1/(K:ℝ)) hq)
      (fun ω τ => if retires D S c r K n select ω τ then 1 else 0)]
    have hmean := D.law.expect_mono _ _ hpoint
    rw [D.law.expect_add,D.law.expect_const,D.law.expect_finset_sum] at hmean
    have hmarg : ∀ i ∈ C, D.law.expect (fun ω => if i ∈ D.live ω then (1:ℝ) else 0) =
        (1-1/(K:ℝ))^(K^2-K) := by
      intro i hi
      obtain ⟨hy,hcp,_⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiS,hage⟩ := Finset.mem_filter.mp hy
      rw [hD.2 i,ite_eq_left hiS]
      unfold survival
      rw [ite_eq_left hage]
      change K^2 ≤ age S c r i+1 at hcp
      congr 1
      omega
    have hsum : (∑ i ∈ C, D.law.expect (fun ω => if i ∈ D.live ω then (1:ℝ) else 0)) ≤
        (K:ℝ)^2*(1-1/(K:ℝ))^(K^2-K) := by
      rw [Finset.sum_congr rfl hmarg,Finset.sum_const,←Nat.cast_smul_eq_nsmul ℝ]
      simp only [smul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact pow_nonneg (by linarith [hq.2]) _
    exact (hmean.trans (add_le_add le_rfl hsum)).trans (RosterTails.actual_tail K hK)
  · rw [ite_eq_right hnear]
    have he : ∀ ω : D.Sample × (I → Bool),
        (if retires D S c r K n select ω.1 ω.2 then (1:ℝ) else 0) = 0 := by
      intro ω
      apply ite_eq_right
      rintro ⟨i,hsel,hi,hret⟩
      have ha : active S c r K n i := by
        by_contra hn
        exact hret (Finset.mem_filter.mpr ⟨hi,Or.inl hn⟩)
      have hd := hcover ω.1 i hsel
      have ht := dist_triangle (c n) (c i) p
      rw [dist_comm (c n) (c i),dist_comm (c i) p] at ht
      exact hnear (by linarith [ha.1])
    rw [Law.expect_congr _ _ _ he,Law.expect_const]
end
end UniformKServer.ActualRoster

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierKeyProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

noncomputable section
namespace UniformKServer.TierKeyProcess
open FiniteProbability Finset ChronologicalRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

attribute [local instance] OAI.UniformKServer.TierKeyProcess.pairDecEq
attribute [local instance] OAI.UniformKServer.TierKeyProcess.indexDecEq
omit [Fintype X] in
theorem covers (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K) (q : Fin N → Prop) (c : Fin N → X)
    (t : ℕ) (τ : TierLifetimes.Tape N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r)
    (p : X) (i : Fin N) (hi : key r K q c t τ ω p=some i) : dist p (c i)≤2*r := by
  have hc := TierKeys.key_covers _ _ _ c ω p i hi
  have hKr : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hlam : 0<Real.log (1+(K:ℝ)^2) := Real.log_pos (by nlinarith [sq_pos_of_pos hKr])
  have hd := TierRadius.cover_outer _ r hr (ω i) (c i) p hc
  simpa only [dist_comm] using hd.le

end UniformKServer.TierKeyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CooldownLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Fixed finite label pools with a full preceding-step cooldown. No historical
label is globally reserved: only current and preceding record sets are excluded. -/
noncomputable section
namespace UniformKServer.CooldownLabels
open Finset
open scoped Classical
variable {I : Type*} [DecidableEq I]

theorem label_old (M : ℕ) (S : ℕ → Finset I) (birth : ℕ → Option I)
    (t : ℕ) (n i : I) (hb : birth t=some n) (hi : i≠n) :
    (run M S birth (t+1)).label i=(run M S birth t).label i := by
  simp only [run,step,hb,Function.update_of_ne hi]

end UniformKServer.CooldownLabels

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Quantitative radius parameter used by the chronological tiers in §07.
Constants are explicit and independent of the metric and the horizon. -/
namespace UniformKServer.TierParameters
noncomputable section

/-- The cutoff can be exponentially large in the tier, but the radius slope
is linear in that tier. No dependence on the number of records is introduced. -/
theorem radius_parameter (C h : ℝ) (hC : 1 ≤ C) (hh : 1 ≤ h) :
    Real.log (1+(cutoff C h:ℝ)^2) ≤ (2*C+4)*h := by
  have ha : 0 ≤ C*h := mul_nonneg (by linarith) (by linarith)
  have he : 1 ≤ Real.exp (C*h) := Real.one_le_exp_iff.mpr ha
  have hk0 : (0:ℝ) ≤ cutoff C h := Nat.cast_nonneg _
  have hk : (cutoff C h:ℝ) ≤ 2*Real.exp (C*h) := by
    have hc := Nat.ceil_lt_add_one (Real.exp_pos (C*h)).le
    unfold cutoff
    linarith
  have hs : (cutoff C h:ℝ)^2 ≤ (2*Real.exp (C*h))^2 :=
    pow_le_pow_left₀ hk0 hk 2
  have he2 : 1 ≤ (Real.exp (C*h))^2 := one_le_pow₀ he
  have harg : 1+(cutoff C h:ℝ)^2 ≤ 5*(Real.exp (C*h))^2 := by nlinarith
  have hl := Real.log_le_log (by positivity : 0 < 1+(cutoff C h:ℝ)^2) harg
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_exp] at hl
  have h5 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5)
    linarith
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith

end
end UniformKServer.TierParameters

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_DyadicTiers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! The source's dyadic tiers, including the minimal last tier and the sharp
prefix/unqualified sums. These coefficients are summed before summing scales. -/
noncomputable section
namespace UniformKServer.DyadicTiers
open Finset
open scoped Classical

theorem value_pos (i : ℕ) : 0<value i := lt_of_lt_of_le (by norm_num) (one_le_value i)

theorem sum_exact (n : ℕ) : ∑ i∈range n, value i=2^n-1 := by
  have h := geom_sum_mul (2:ℝ) n
  norm_num only [show (2:ℝ)-1=1 by norm_num,mul_one] at h
  exact h

theorem value_mono : Monotone value := by
  intro i j hij
  exact pow_le_pow_right₀ (by norm_num) hij

theorem unqualified_sum (L : ℝ) (hL : 0≤L) (n : ℕ) :
    (∑ i∈range n, if value i<L then value i else 0)≤2*L := by
  induction n with
  | zero => simp only [sum_range_zero] <;> linarith
  | succ n ih =>
    by_cases hn : value n<L
    · have hall : (∑ i∈range (n+1), if value i<L then value i else 0)=
          ∑ i∈range (n+1), value i := by
        apply sum_congr rfl
        intro i hi
        exact ite_eq_left ((value_mono (by have := mem_range.mp hi; omega)).trans_lt hn)
      rw [hall,sum_exact,pow_succ]
      dsimp only [value] at hn
      linarith
    · rw [sum_range_succ,ite_eq_right hn,add_zero]
      exact ih

theorem inverse_cutoff (C : ℝ) (hC : 1≤C) (i : ℕ) :
    1/(TierParameters.cutoff C (value i):ℝ)≤(1/2:ℝ)^i := by
  have hv := value_pos i
  have hc : value i≤(TierParameters.cutoff C (value i):ℝ) := by
    have he := Real.add_one_le_exp (C*value i)
    have hh := Nat.le_ceil (Real.exp (C*value i))
    change _≤(⌈Real.exp (C*value i)⌉₊:ℝ)
    nlinarith
  have hinv := one_div_le_one_div_of_le hv hc
  simpa only [one_div_pow,value] using hinv

theorem inverse_sum (C : ℝ) (hC : 1≤C) (n : ℕ) :
    (∑ i∈range n, 1/(TierParameters.cutoff C (value i):ℝ))≤2 := by
  exact (sum_le_sum (fun i _ => inverse_cutoff C hC i)).trans (sum_geometric_two_le n)

end UniformKServer.DyadicTiers

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_GeometricMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The actual geometric scales and the posterior ball masses at a request.
The shift comparison is proved from metric ball inclusion, rather than assumed
as an abstract scalar inequality. The scale count is independent of aspect. -/
noncomputable section
namespace UniformKServer.GeometricMass
open Finset
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem mass_mono (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) {a b : ℝ} (hab : a ≤ b) :
    mass μ x a ≤ mass μ x b := by
  apply sum_le_sum
  intro y _
  by_cases hy : dist x y ≤ a
  · simp only [ite_eq_left hy,ite_eq_left (hy.trans hab),le_refl]
  · simp only [ite_eq_right hy]
    split_ifs <;> [exact hμ y; exact le_rfl]

theorem mass_total (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (a : ℝ) :
    mass μ x a ≤ ∑ y, μ y := by
  apply sum_le_sum
  intro y _
  split_ifs <;> [exact le_rfl; exact hμ y]

theorem mass_center (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (a : ℝ) (ha : 0 ≤ a) :
    μ x ≤ mass μ x a := by
  have hs := single_le_sum (s:=univ) (f:=fun y => if dist x y ≤ a then μ y else 0)
    (fun y _ => by split_ifs <;> [exact hμ y; exact le_rfl]) (mem_univ x)
  simpa only [mass,dist_self,ite_eq_left ha] using hs

theorem radius_shift (R q : ℝ) (j p : ℕ) (hp : p ≤ j) :
    radius R q j=radius R q (j-p)*q^p := by
  unfold radius
  rw [mul_assoc,←pow_add]
  congr 2
  omega

theorem mass_shift (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (R q γ D : ℝ)
    (hR : 0< R) (hq : 0< q) (p j : ℕ) (hp : p ≤ j) (hs : D*q^p ≤ γ) :
    mass μ x (D*radius R q j) ≤ mass μ x (γ*radius R q (j-p)) := by
  apply mass_mono μ hμ x
  rw [radius_shift R q j p hp]
  have h := mul_le_mul_of_nonneg_right hs (radius_pos R q hR hq (j-p)).le
  nlinarith only [h]

def logarithm (μ : X → ℝ) (x : X) (R q γ D : ℝ) (j : ℕ) : ℝ :=
  Real.log (mass μ x (D*radius R q j)/mass μ x (γ*radius R q j))

theorem logarithm_nonneg (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (hx : 1 ≤ μ x)
    (R q γ D : ℝ) (hR : 0< R) (hq : 0< q) (hγ : 0 ≤ γ) (hD : γ ≤ D) (j : ℕ) :
    0 ≤ logarithm μ x R q γ D j := by
  have hr := radius_pos R q hR hq j
  have ha := hx.trans (mass_center μ hμ x _ (mul_nonneg hγ hr.le))
  apply Real.log_nonneg
  apply (le_div_iff₀ (by linarith : 0< mass μ x (γ*radius R q j))).mpr
  simpa only [one_mul] using mass_mono μ hμ x (mul_le_mul_of_nonneg_right hD hr.le)

theorem log_sum (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (hx : 1 ≤ μ x)
    (k R q γ D : ℝ) (hk : ∑ y, μ y ≤ k) (hR : 0< R) (hq : 0< q) (hγ : 0 ≤ γ)
    (hD : γ ≤ D) (p J : ℕ) (hs : D*q^p ≤ γ) :
    (∑ j∈range J, logarithm μ x R q γ D j) ≤ (p:ℝ)*Real.log k := by
  have hk1 : 1 ≤ k := hx.trans ((single_le_sum (fun y _ => hμ y) (mem_univ x)).trans hk)
  have ha (j : ℕ) : 1 ≤ mass μ x (γ*radius R q j) :=
    hx.trans (mass_center μ hμ x _ (mul_nonneg hγ (radius_pos R q hR hq j).le))
  have hb (j : ℕ) : mass μ x (γ*radius R q j) ≤ mass μ x (D*radius R q j) :=
    mass_mono μ hμ x (mul_le_mul_of_nonneg_right hD (radius_pos R q hR hq j).le)
  have ht (j : ℕ) : mass μ x (D*radius R q j) ≤ if j< p then k else mass μ x (γ*radius R q (j-p)) := by
    split_ifs with hj
    · exact (mass_total μ hμ x _).trans hk
    · exact mass_shift μ hμ x R q γ D hR hq p j (by omega) hs
  simpa only [div_one,logarithm] using PilotScales.scale_logarithms
    (fun j => mass μ x (γ*radius R q j)) (fun j => mass μ x (D*radius R q j)) J p 1 k
    (by norm_num) hk1 (fun j _ => ha j) (fun j _ => hb j) (fun j _ => ht j)

def nonheavy (μ : X → ℝ) (x : X) (R q γ D δ : ℝ) (j : ℕ) : Prop :=
  (1+δ)*mass μ x (γ*radius R q j)< mass μ x (D*radius R q j)

theorem nonheavy_log (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (hx : 1 ≤ μ x)
    (R q γ D δ : ℝ) (hR : 0< R) (hq : 0< q) (hγ : 0 ≤ γ) (hδ : 0< δ)
    (j : ℕ) (hj : nonheavy μ x R q γ D δ j) :
    Real.log (1+δ)< logarithm μ x R q γ D j := by
  have ha := hx.trans (mass_center μ hμ x _ (mul_nonneg hγ (radius_pos R q hR hq j).le))
  apply Real.log_lt_log (by linarith : 0< 1+δ)
  exact (lt_div_iff₀ (by linarith : 0< mass μ x (γ*radius R q j))).mpr hj

theorem nonheavy_count (μ : X → ℝ) (hμ : ∀ y, 0 ≤ μ y) (x : X) (hx : 1 ≤ μ x)
    (k R q γ D δ : ℝ) (hk : ∑ y, μ y ≤ k) (hR : 0< R) (hq : 0< q) (hγ : 0 ≤ γ)
    (hD : γ ≤ D) (hδ : 0< δ) (p J : ℕ) (hs : D*q^p ≤ γ) :
    ((range J).filter (nonheavy μ x R q γ D δ)).card ≤ 
      (p:ℝ)*Real.log k/Real.log (1+δ) := by
  have hl : 0< Real.log (1+δ) := Real.log_pos (by linarith)
  apply (le_div_iff₀ hl).mpr
  calc
    _ = ∑ j∈range J, if nonheavy μ x R q γ D δ j then Real.log (1+δ) else 0 := by
      rw [←sum_filter,sum_const,nsmul_eq_mul]
    _  ≤  ∑ j∈range J, logarithm μ x R q γ D j := by
      apply sum_le_sum
      intro j _
      split_ifs with hj
      · exact (nonheavy_log μ hμ x hx R q γ D δ hR hq hγ hδ j hj).le
      · exact logarithm_nonneg μ hμ x hx R q γ D hR hq hγ hD j
    _  ≤  _ := log_sum μ hμ x hx k R q γ D hk hR hq hγ hD p J hs

end UniformKServer.GeometricMass

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Instantiation of the level construction from the true post-request GeometricMass.mass.
Tier qualifications are precisely the source exponential GeometricMass.mass test. -/
noncomputable section
namespace UniformKServer.PartitionLevel
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

namespace Input

local instance pairDecEq_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
def localLog (I : Input X N) (n : Fin N) : ℝ :=
  Real.log (GeometricMass.mass (I.μ n) (I.center n) (20480000*I.r)/GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r))

theorem inner_one (I : Input X N) (n : Fin N) :
    1 ≤ GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r) :=
  (I.served n).trans (mass_center _ (I.μ_nonneg n) _ _ (mul_pos I.P.gammaL_pos I.r_pos).le)

theorem outer_pos (I : Input X N) (n : Fin N) :
    0< GeometricMass.mass (I.μ n) (I.center n) (20480000*I.r) := by
  have h := (I.served n).trans (mass_center (I.μ n) (I.μ_nonneg n) (I.center n) (20480000*I.r) (mul_nonneg (by norm_num) I.r_pos.le))
  linarith

theorem localLog_nonneg (I : Input X N) (n : Fin N) : 0 ≤ I.localLog n := by
  have hi := I.inner_one n
  have ho : I.P.gammaL ≤ 20480000 := by linarith [I.P.gammaL_small,I.P.sigma_small]
  apply Real.log_nonneg
  apply (le_div_iff₀ (by linarith : 0< GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r))).mpr
  simpa only [one_mul] using mass_mono (I.μ n) (I.μ_nonneg n) (I.center n) (mul_le_mul_of_nonneg_right ho I.r_pos.le)

theorem qualification (I : Input X N) (n : Fin N) (i : Fin I.height) :
    I.data.qualify i n ↔ I.localLog n ≤ DyadicTiers.value i.val := by
  have hi := I.inner_one n
  have hip : 0< GeometricMass.mass (I.μ n) (I.center n) (I.P.gammaL*I.r) := by linarith
  have hratio := div_pos (I.outer_pos n) hip
  change _ ↔ Real.log _ ≤ _
  rw [←Real.exp_le_exp,Real.exp_log hratio,div_le_iff₀ hip]
  rfl

end Input
end UniformKServer.PartitionLevel

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SmallScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! A thresholded geometric scale sum with no dependence on the number of
scales. Used for designated-mover errors, not a per-level additive error. -/
noncomputable section
namespace UniformKServer.SmallScales
open Finset
open scoped Classical

theorem small (R q a : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q) (hq1 : q<1) (ha : 0 ≤ a) (n : ℕ) :
    (∑ j∈range n, if R*q^j ≤ a then R*q^j else 0) ≤ a/(1-q) := by
  induction n generalizing R with
  | zero => simp only [sum_range_zero] <;> positivity
  | succ n ih =>
    by_cases hRa : R ≤ a
    · apply le_trans (sum_le_sum (fun j _ => ?_))
        ((geometric R q hR hq hq1 (n+1)).trans (div_le_div_of_nonneg_right hRa (by linarith)))
      split_ifs <;> [exact le_rfl; exact mul_nonneg hR (pow_nonneg hq j)]
    · rw [sum_range_succ']
      have he (j : ℕ) : R*q^(j+1)=(R*q)*q^j := by rw [pow_succ]; ring
      simp only [he,pow_zero,mul_one,ite_eq_right hRa,add_zero]
      exact ih (R*q) (mul_nonneg hR hq)

end UniformKServer.SmallScales

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Final-map separation summed over geometric scales. The additive one in
the level estimate is charged only at nonheavy scales, not at every scale. -/
noncomputable section
namespace UniformKServer.PartitionScales
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N J : ℕ}

namespace Input

def isNonheavy (I : Input X N J) (n : Fin N) (j : ℕ) : Prop :=
  nonheavy (I.μ n) (I.center n) I.R I.q I.P.gammaH 51200 I.P.deltaH j

theorem not_heavy (I : Input X N J) (n : Fin N) (j : ℕ) :
    I.isNonheavy n j ↔ ¬(I.level j).data.heavy n := by
  exact lt_iff_not_ge

theorem log_sum (I : Input X N J) (n : Fin N) :
    (∑ j∈range J, (I.level j).localLog n) ≤ Real.log I.k := by
  have hg : I.P.gammaL ≤ 20480000 := by linarith [I.P.gammaL_small,I.P.sigma_small]
  have h := GeometricMass.log_sum (I.μ n) (I.μ_nonneg n) (I.center n) (I.served n)
    I.k I.R I.q I.P.gammaL 20480000 (I.μ_total n) I.R_pos I.q_pos I.P.gammaL_pos.le hg 1 J
    (by simpa only [pow_one] using I.shiftL)
  simpa only [Nat.cast_one,one_mul,level,PartitionLevel.Input.localLog,logarithm] using h

theorem nonheavy_count (I : Input X N J) (n : Fin N) :
    ((range J).filter (I.isNonheavy n)).card ≤ Real.log I.k/Real.log (1+I.P.deltaH) := by
  have hg : I.P.gammaH ≤ 51200 := by linarith [I.P.gammaH_small]
  have h := GeometricMass.nonheavy_count (I.μ n) (I.μ_nonneg n) (I.center n) (I.served n)
    I.k I.R I.q I.P.gammaH 51200 I.P.deltaH (I.μ_total n) I.R_pos I.q_pos
    I.P.gammaH_pos.le hg I.P.deltaH_pos 1 J (by simpa only [pow_one] using I.shiftH)
  change (((range J).filter (nonheavy (I.μ n) (I.center n) I.R I.q I.P.gammaH 51200 I.P.deltaH)).card : ℝ) ≤ _
  simpa only [Nat.cast_one,one_mul] using h

def coefficient (I : Input X N J) : ℝ := 8+(16*I.C+33)*(1+1/Real.log (1+I.P.deltaH))

end Input
end UniformKServer.PartitionScales

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section
namespace UniformKServer.TierInsertion
noncomputable section
open PilotCompact TierPilot ShortRoster ChronologicalRoster

variable {I X : Type} [Fintype I] [LinearOrder I] [Fintype X] [MetricSpace X]
omit [Fintype I] [LinearOrder I] [Fintype X] [MetricSpace X] in
theorem coefficient_bounds (P : Parameters) : 0 < gainCoefficient P ∧ gainCoefficient P ≤ 1/2 := by
  exact ⟨lt_min (by norm_num) (mul_pos (by norm_num) P.deltaH_pos),min_le_left _ _⟩

omit [Fintype I] [LinearOrder I] [Fintype X] [MetricSpace X] in
theorem exponent_bounds (P : Parameters) (h : ℝ) (hh : 1 ≤ h) (K : ℕ)
    (hlarge : Real.exp (lifetimeExponent P*h) ≤ K) :
    257*(49/Real.sqrt (K:ℝ)) ≤ gainCoefficient P/2*Real.exp (-h) ∧
      1/(K:ℝ) ≤ gainCoefficient P/2*Real.exp (-2*h) := by
  let c := gainCoefficient P
  let A := 2*257*49/c
  have hc : 0 < c := (coefficient_bounds P).1
  have hcBound : c ≤ 1/2 := (coefficient_bounds P).2
  have hApos : 0 < A := by dsimp [A] <;> positivity
  have hA1 : 1 ≤ A := by
    dsimp [A]
    apply (le_div_iff₀ hc).mpr
    linarith
  have hlog : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hk : 0 < (K:ℝ) := (Real.exp_pos _).trans_le hlarge
  have hs := Real.sqrt_pos.mpr hk
  have he : h+Real.log A ≤ lifetimeExponent P*h/2 := by
    change h+Real.log A ≤ (2*(Real.log A+3))*h/2
    nlinarith [mul_nonneg hlog (show 0 ≤ h-1 by linarith)]
  have hroot : Real.exp (lifetimeExponent P*h/2) ≤ Real.sqrt (K:ℝ) := by
    apply (Real.le_sqrt (Real.exp_nonneg _) hk.le).mpr
    rw [←Real.exp_nat_mul]
    convert hlarge using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hAs : A*Real.exp h ≤ Real.sqrt (K:ℝ) := by
    have := (Real.exp_le_exp.mpr he).trans hroot
    simpa [Real.exp_add,Real.exp_log hApos,mul_comm] using this
  have hinv : 257*(49/Real.sqrt (K:ℝ)) ≤ c/2*Real.exp (-h) := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hs).mpr
    have hAs' := mul_le_mul_of_nonneg_left hAs
      (show 0 ≤ c/2*Real.exp (-h) by positivity)
    have hid : c/2*Real.exp (-h)*(A*Real.exp h) = 257*49 := by
      have hex : Real.exp (-h)*Real.exp h=1 := by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
      calc
        _ = (c/2*A)*(Real.exp (-h)*Real.exp h) := by ring
        _ = 257*49 := by rw [hex]; dsimp [A]; field_simp
    rw [hid] at hAs'
    exact hAs'
  have hpay : 1/(K:ℝ) ≤ c/2*Real.exp (-2*h) := by
    have hsq := mul_self_le_mul_self (show 0 ≤ A*Real.exp h by positivity) hAs
    rw [Real.mul_self_sqrt hk.le] at hsq
    have ha2 : 2/c ≤ A^2 := by
      have hAc : A*c=2*257*49 := by dsimp [A]; field_simp
      apply (div_le_iff₀ hc).mpr
      nlinarith [mul_le_mul_of_nonneg_right hA1 hc.le]
    have hb := mul_le_mul_of_nonneg_right ha2 (sq_nonneg (Real.exp h))
    have he2 : Real.exp (2*h) = (Real.exp h)^2 := by rw [show 2*h=h+h by ring,Real.exp_add,pow_two]
    have hmain : (2/c)*Real.exp (2*h) ≤ K := by rw [he2]; nlinarith
    apply (div_le_iff₀ hk).mpr
    have hm := mul_le_mul_of_nonneg_left hmain (show 0 ≤ c/2*Real.exp (-2*h) by positivity)
    have hid : c/2*Real.exp (-2*h)*((2/c)*Real.exp (2*h)) = 1 := by
      have hex : Real.exp (-2*h)*Real.exp (2*h)=1 := by
        rw [←Real.exp_add,show -2*h+2*h=0 by ring,Real.exp_zero]
      calc
        _ = (c/2*(2/c))*(Real.exp (-2*h)*Real.exp (2*h)) := by ring
        _ = 1 := by rw [hex]; field_simp
    rw [hid] at hm
    exact hm
  exact ⟨hinv,hpay⟩
/-- The literal weighted insertion payment, with the auxiliary roster built
by independent lifetime experiments and a single fixed lifetime exponent. -/
theorem weighted_short_gain (P : Parameters) (D : State I) (S : Finset I)
    (c : I → X) (r h : ℝ) (hr : 0 < r) (hh : 1 ≤ h) (K : ℕ) (hK : 2 ≤ K)
    (hlarge : Real.exp (lifetimeExponent P*h) ≤ K)
    (hq : 1/Real.sqrt (K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (n : I) (hD : D.Valid S c r K (1/Real.sqrt (K:ℝ)))
    (hn : ∀ i ∈ S, i < n)
    (htest : ∀ i ∈ young S c r K, r/2 < dist (c n) (c i))
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    (hM : 0 < ballMass r P.gammaH μ (c n))
    (hqual : ballMass r 20480000 μ (c n) ≤ Real.exp h*ballMass r P.gammaL μ (c n)) :
    r*insertionMass P r μ (c n)/(K:ℝ) ≤
      Real.exp (-h)*(value r P.sigma 204800 μ (D.parameter c r)-
        value r P.sigma 204800 μ
          ((D.next S c r K (1/Real.sqrt (K:ℝ)) hq n).parameter c r))
 := by
  let q := 1/Real.sqrt (K:ℝ)
  let ε := q+(K:ℝ)*(1-q)^(K-1)
  have hε : 0 ≤ ε := by
    dsimp only [ε]
    exact add_nonneg hq.1 (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith [hq.2]) _))
  have he := short_edit D S c r hr K (by omega) q hq n hD hn htest
  have hg := insertion_gain P r ε h hr hε hh μ (D.parameter c r)
    ((D.next S c r K q hq n).parameter c r) hμ (c n) hM hqual he
  have ht : ε ≤ 49/Real.sqrt (K:ℝ) := RosterTails.short_tail K hK
  obtain ⟨herr,hpay⟩ := exponent_bounds P h hh K hlarge
  have herr' : 257*ε ≤ gainCoefficient P/2*Real.exp (-h) :=
    (mul_le_mul_of_nonneg_left ht (by norm_num)).trans herr
  have hW := (insertionMass_bounds P r hr.le μ hμ (c n)).1
  have hrW : 0 ≤ r*insertionMass P r μ (c n) := mul_nonneg hr.le hW
  have hdrop : r*insertionMass P r μ (c n)*(gainCoefficient P/2*Real.exp (-h)) ≤
      value r P.sigma 204800 μ (D.parameter c r)-
        value r P.sigma 204800 μ ((D.next S c r K q hq n).parameter c r) := by
    apply le_trans _ hg
    apply mul_le_mul_of_nonneg_left _ hrW
    change _ ≤ gainCoefficient P*Real.exp (-h)-257*ε
    linarith
  have hw := mul_le_mul_of_nonneg_left hdrop (Real.exp_nonneg (-h))
  have heq : Real.exp (-h)*Real.exp (-h)=Real.exp (-2*h) := by
    rw [←Real.exp_add]; congr 1; ring
  have hpayment := mul_le_mul_of_nonneg_left hpay hrW
  calc
    _ = (r*insertionMass P r μ (c n))*(1/(K:ℝ)) := by ring
    _ ≤ (r*insertionMass P r μ (c n))*(gainCoefficient P/2*Real.exp (-2*h)) := hpayment
    _ = Real.exp (-h)*(r*insertionMass P r μ (c n)*(gainCoefficient P/2*Real.exp (-h))) := by
      rw [←heq]; ring
    _ ≤ _ := hw
end
end UniformKServer.TierInsertion

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The actual true-posterior partition, on every positive finite hidden law.
All inputs are the real post-request counts, not a fitted proxy mass. -/
noncomputable section
namespace UniformKServer.ActualPartitions
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

namespace Config

theorem lifetime_large (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (j : ℕ) (i : Fin ((A.input (N:=N) (J:=J) D hk ω).level j).height) :
    Real.exp (TierInsertion.lifetimeExponent A.P*DyadicTiers.value i.val)≤
      (((A.input (N:=N) (J:=J) D hk ω).level j).data.K i:ℝ) := by
  change _≤(TierParameters.cutoff A.C (DyadicTiers.value i.val):ℝ)
  calc
    _ ≤ Real.exp (A.C*DyadicTiers.value i.val) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right A.C_large (by linarith [DyadicTiers.one_le_value i.val]))
    _ ≤ _ := Nat.le_ceil _

end Config
end UniformKServer.ActualPartitions

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_KeyEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                               
section
namespace UniformKServer.KeyEdits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I J : Type*}

theorem none_charge (earlier : Option J) (label : I → J) (later : J) (new : Option I) :
    changed earlier label later none new+uncovered new-uncovered (none : Option I) ≤ 0 := by
  cases new with
  | none => simp [uncovered]
  | some i =>
    have h := (changed_bounds earlier label later none (some i)).2
    simp only [uncovered,Option.isNone_some,Bool.false_eq_true,ite_false, if_false,Option.isNone_none,ite_true, if_true] at *
    linarith
/-- All three rows of the source noncoverage table, including changes hidden
by higher-priority structures. Covers/radii are persistent for old records. -/
theorem insertion_stationary (old : List I) (keep cover : I → Bool) (n : I)
    (earlier : Option J) (label : I → J) (later : J) :
    changed earlier label later (old.find? cover) ((next old keep n).find? cover) +
      uncovered ((next old keep n).find? cover)-uncovered (old.find? cover) ≤
        2*retirement (old.find? cover) keep
 := by
  cases hfirst : old.find? cover with
  | none =>
    simpa only [retirement,mul_zero] using
      none_charge earlier label later ((next old keep n).find? cover)
  | some i =>
    by_cases hk : keep i = true
    · rw [first_persists old keep cover n i hfirst hk,changed_self]
      simp [retirement,hk]
    · have hc := (changed_bounds earlier label later (some i) ((next old keep n).find? cover)).2
      have hu := (uncovered_bounds ((next old keep n).find? cover)).2
      simp only [uncovered,Option.isNone_some,Bool.false_eq_true,ite_false, if_false,retirement,ite_eq_right hk] at *
      linarith

end
end UniformKServer.KeyEdits

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyEditRamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.HeavyEditRamp

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X]

theorem update_far (r : ℝ) (hr : 0 < r) (H : Finset X) (x p : X)
    (hp : 110*r < dist p x) : parameter r (HeavyPilot.updateCenters r H x) p ≤ parameter r H p := by
  apply le_parameter r H p _ (parameter_bounds r (HeavyPilot.updateCenters r H x) p).2
  intro c hc
  by_cases hfar : 100*r < dist x c
  · exact parameter_le_center r (HeavyPilot.updateCenters r H x) p c (by simp [HeavyPilot.updateCenters,hc,hfar])
  · have hpc : 10 ≤ dist p c/r := by
      have ht := dist_triangle p c x
      rw [dist_comm c x] at ht
      apply (le_div_iff₀ hr).mpr
      push Not at hfar
      linarith
    rw [ramp_one hpc]
    exact (parameter_bounds r (HeavyPilot.updateCenters r H x) p).2

end UniformKServer.HeavyEditRamp

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyEditPayment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The literal [9,10] auxiliary potential pays heavy-label edits (§07,
Heavy edits). These are pointwise inequalities before any posterior averaging. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset HeavyEditRamp
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

omit [Fintype X] in
theorem stationary_edit_payment (S : State X Λ r) (hr : 0 < r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) (p : X) :
    editCharge S (insert S hr.le x R hR fresh hf) p+
      r*(parameter r (centers (insert S hr.le x R hR fresh hf)) p-parameter r (centers S) p) ≤
      if 3*r < dist p x ∧ dist p x ≤ 120*r then 2*r else 0 := by
  by_cases hi : dist p x ≤ 3*r
  · rw [ite_eq_right (fun h => (not_lt_of_ge hi) h.1)]
    exact inner_edit_payment S hr x R hR fresh hf p hi
  · by_cases ho : dist p x ≤ 120*r
    · rw [ite_eq_left ⟨lt_of_not_ge hi,ho⟩]
      have hc := (editCharge_bounds S (insert S hr.le x R hR fresh hf) hr.le p).2
      have hp := parameter_bounds r (centers (insert S hr.le x R hR fresh hf)) p
      have hq := parameter_bounds r (centers S) p
      nlinarith [hp.1,hp.2,hq.1,hq.2]
    · rw [ite_eq_right (fun h => ho h.2)]
      have hd : 120*r < dist x p := by rw [dist_comm]; exact lt_of_not_ge ho
      have he := unchanged_far S hr.le x R hR fresh hf p hd
      rw [editCharge,ite_eq_right (not_not.mpr he.symm),centers_insert]
      have hm := HeavyEditRamp.update_far r hr (centers S) x p (by rw [dist_comm] at hd; linarith)
      nlinarith

end UniformKServer.HeavyRecords

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyProcessEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! End-to-end heavy edits and physical movement, including all no-insertion
cases. The auxiliary potential is the literal [9,10] distance ramp. -/
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords HeavyEditRamp
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

theorem step_stationary_payment (S T : State X Λ r) (hr : 0 < r)
    (hΛ : 2*Fintype.card X<Fintype.card Λ) (h : Prop) (x : X) (R : ℝ)
    (hR : R∈Set.Icc (16*r) (20*r)) (p : X) :
    editCharge S (step S T hr.le hΛ h x R hR) p+
      r*(parameter r (centers (step S T hr.le hΛ h x R hR)) p-parameter r (centers S) p)≤
      if HeavySchedule.trigger r h (centers S) x ∧ 3*r<dist p x ∧ dist p x≤120*r then 2*r else 0 := by
  by_cases hi : HeavySchedule.trigger r h (centers S) x
  · simp only [step,hi,ite_true, if_true,true_and]
    exact stationary_edit_payment S hr x R hR (fresh S T hr.le hΛ) (fresh_absent S T hr.le hΛ).1 p
  · simp only [step,hi,ite_false, if_false,false_and,editCharge,ne_eq,not_true_eq_false,ite_false,sub_self,mul_zero,add_zero,le_refl]

theorem run_stationary_payment (a : X) (hr : 0 < r)
    (hΛ : 2*Fintype.card X<Fintype.card Λ) (h : ℕ→Prop) (x : ℕ→X)
    (R : ℕ→ℝ) (hR : ∀ t, R t∈Set.Icc (16*r) (20*r)) (t : ℕ) (p : X) :
    editCharge (run a hr.le hΛ h x R hR t) (run a hr.le hΛ h x R hR (t+1)) p+
      r*(parameter r (HeavySchedule.centers r h x (t+1)) p-parameter r (HeavySchedule.centers r h x t) p)≤
      if HeavySchedule.trigger r (h t) (HeavySchedule.centers r h x t) (x t) ∧
        3*r<dist p (x t) ∧ dist p (x t)≤120*r then 2*r else 0 := by
  have hp := step_stationary_payment (run a hr.le hΛ h x R hR t)
    (runPair a hr.le hΛ h x R hR t).1 hr hΛ (h t) (x t) (R t) (hR t) p
  change editCharge (run a hr.le hΛ h x R hR t) (run a hr.le hΛ h x R hR (t+1)) p+
    r*(parameter r (centers (run a hr.le hΛ h x R hR (t+1))) p-
      parameter r (centers (run a hr.le hΛ h x R hR t)) p)≤_ at hp
  simpa only [run_centers] using hp

end UniformKServer.HeavyProcess

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelHeavyEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Heavy key edits on the actual tape, with a tape-independent auxiliary ramp. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqHeavyEdit_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.LevelMap.Data.tierDecEqHeavyEdit
local instance pairDecEqHeavyEdit_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem heavy_stationary (D : Data X N H) (n : Fin N) (p : X) (ω : Tape D) :
    D.r*(D.heavyEdit n p ω+D.heavyPotential (n.val+1) p-D.heavyPotential n.val p)≤
      if D.heavyTrigger n ∧ 3*D.r<dist (D.center n) p ∧ dist (D.center n) p≤120*D.r then 2*D.r else 0 := by
  have h := HeavyProcess.run_stationary_payment D.base D.positive
    (show 2*Fintype.card X<Fintype.card (HeavySlot X) by simp [HeavySlot])
    D.heavyFlag D.point (HeavyProcess.radiusStream D.r N ω.1)
    (HeavyProcess.radiusStream_bounds D.r D.positive.le N ω.1) n.val p
  change HeavyRecords.editCharge (D.heavyState ω.1 n.val) (D.heavyState ω.1 (n.val+1)) p+
    D.r*(D.heavyPotential (n.val+1) p-D.heavyPotential n.val p)≤
      (if D.heavyTrigger n ∧ 3*D.r<dist p (D.point n.val) ∧ dist p (D.point n.val)≤120*D.r then 2*D.r else 0) at h
  rw [point_at,dist_comm p] at h
  nlinarith only [h,D.heavyEdit_le n p ω]

end UniformKServer.LevelMap.Data

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierRetirement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

noncomputable section
namespace UniformKServer.TierRetirement
open FiniteProbability Finset ChronologicalRoster ShortRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [MetricSpace X] {N : ℕ}

local instance pairDecEq_r5f289f_2 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.TierRetirement.indexDecEq
/-- Averaged under the true old survivor distribution. Conditioning on a
realized surviving old record (which would invalidate this bound) is not used. -/
theorem probability_bound (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (ω : Fin N → TierRadius.Sample (X:=X) (Real.log (1+(K:ℝ)^2)) r) (p : X) :
    (TierLifetimes.law (N:=N) K hq).expect (fun τ => if event r K q c n τ ω p then (1:ℝ) else 0)≤
      if dist (c n) p≤22*r then 49/(K:ℝ) else 0 := by
  let S := TierSchedule.run r K q c n.val
  let D := TierLifetimes.state r K hq q c n.val
  let select := fun τ : TierLifetimes.Tape N => TierKeyProcess.key r K q c n.val τ ω p
  have hb := ActualRoster.first_retirement D S c r hr K hK hq n
    (TierLifetimes.valid r K hK hq q c n.val) p select
    (fun τ i hi => TierKeyProcess.covers r hr K hK q c n.val τ ω p i hi)
  let g := fun H : Finset (Fin N) => fun τ' : Fin N → Bool =>
    if ∃ i, TierKeys.key (Real.log (1+(K:ℝ)^2)) r (H.sort (·≤·)) c ω p=some i ∧ i∈H ∧
      i∉retained (ActualRoster.active S c r K n) (ActualRoster.compulsory S c r K) H τ' then (1:ℝ) else 0
  have he : (fun τ => if event r K q c n τ ω p then (1:ℝ) else 0)=
      (fun τ => g (TierLifetimes.live r K q c n.val τ) (τ n)) := by
    funext τ
    dsimp only [event,TierKeyProcess.key,g,S]
    congr 1
  rw [he]
  rw [TierLifetimes.fresh_step r K hq q c n g]
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  apply Law.expect_congr
  intro z
  dsimp only [g,D,S,select,TierLifetimes.state,ActualRoster.retires,TierKeyProcess.key]
  congr 1

end UniformKServer.TierRetirement

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierKeyEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Actual roster edits, including the noncoverage credit. The fixed-radius
values are persistent over an insertion, and retirements use the true law. -/
noncomputable section
namespace UniformKServer.TierKeyEdits
open Finset FiniteProbability ShortRoster ChronologicalRoster
attribute [local instance] Classical.propDecidable
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

local instance pairDecEq_r5f289f_3 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq_r5f289f_2 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
omit [Fintype X] in
theorem sorted_next (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (τ : TierLifetimes.Tape N) :
    (TierLifetimes.live r K q c (n.val+1) τ).sort (·≤·)=
      KeyEdits.next ((TierLifetimes.live r K q c n.val τ).sort (·≤·)) (keep r K q c n τ) n := by
  rw [TierLifetimes.live,dite_eq_left n.isLt,ite_eq_left hn]
  rw [ShortRoster.insert_linear]
  rw [SortedRoster.sort_insert_last]
  · unfold KeyEdits.next
    congr 1
    exact SortedRoster.sort_filter _ _
  · intro i hi
    exact TierSchedule.index_lt r K q c n.val i
      ((mem_filter.mp ((TierLifetimes.valid r K hK hq q c n.val).1 τ (mem_filter.mp hi).1)).1)

theorem retirement_eq (r : ℝ) (K : ℕ) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (τ : TierLifetimes.Tape N) (ω : RadiusTape X N K r) (p : X) :
    KeyEdits.retirement (TierKeyProcess.key r K q c n.val τ ω p) (keep r K q c n τ)=
      if TierRetirement.event r K q c n τ ω p then 1 else 0 := by
  cases hk : TierKeyProcess.key r K q c n.val τ ω p with
  | none => simp [KeyEdits.retirement,TierRetirement.event,hk]
  | some i =>
    have hi : i∈TierLifetimes.live r K q c n.val τ :=
      (mem_sort _).mp (TierKeys.key_mem _ _ _ c ω p i hk)
    have he : TierRetirement.event r K q c n τ ω p ↔ keep r K q c n τ i=false := by
      unfold TierRetirement.event
      simp only [hk,Option.some.injEq]
      constructor
      · rintro ⟨j, hij, hj, hret⟩
        subst j
        simpa only [keep, decide_eq_false_iff_not, retained, mem_filter, hi, true_and] using hret
      · intro hkf
        refine ⟨i,rfl,hi,?_⟩
        simpa only [keep, decide_eq_false_iff_not, retained, mem_filter, hi, true_and] using hkf
    simp only [KeyEdits.retirement,he]
    cases keep r K q c n τ i <;> rfl

theorem stationary (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : RadiusTape X N K r) (p : X) {J : Type*}
    (earlier : TierLifetimes.Tape N → Option J) (label : TierLifetimes.Tape N → Fin N → J)
    (later : TierLifetimes.Tape N → J) :
    (TierLifetimes.law K hq).expect (fun τ =>
      KeyEdits.changed (earlier τ) (label τ) (later τ)
        (TierKeyProcess.key r K q c n.val τ ω p) (TierKeyProcess.key r K q c (n.val+1) τ ω p)+
      KeyEdits.uncovered (TierKeyProcess.key r K q c (n.val+1) τ ω p)-
      KeyEdits.uncovered (TierKeyProcess.key r K q c n.val τ ω p)) ≤
      2*(if dist (c n) p≤22*r then 49/(K:ℝ) else 0) := by
  have hm := (TierLifetimes.law K hq).expect_mono _ _ (fun τ =>
    KeyEdits.insertion_stationary ((TierLifetimes.live r K q c n.val τ).sort (·≤·))
      (keep r K q c n τ) (fun i => (ω i).val (c i,p)) n (earlier τ) (label τ) (later τ))
  have he (τ : TierLifetimes.Tape N) :
      (KeyEdits.next ((TierLifetimes.live r K q c n.val τ).sort (·≤·)) (keep r K q c n τ) n).find?
        (fun i => (ω i).val (c i,p))=TierKeyProcess.key r K q c (n.val+1) τ ω p := by
    rw [←sorted_next r K hK hq q c n hn τ]; rfl
  simp_rw [he] at hm
  change _ ≤ (TierLifetimes.law K hq).expect (fun τ => 2*KeyEdits.retirement
    (TierKeyProcess.key r K q c n.val τ ω p) (keep r K q c n τ)) at hm
  simp_rw [retirement_eq] at hm
  rw [Law.expect_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left (TierRetirement.probability_bound r hr K hK hq q c n ω p) (by norm_num))

theorem mover (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : RadiusTape X N K r) (p : X) {J : Type*}
    (earlier : TierLifetimes.Tape N → Option J) (label : TierLifetimes.Tape N → Fin N → J)
    (later : TierLifetimes.Tape N → J) :
    (TierLifetimes.law K hq).expect (fun τ =>
      KeyEdits.changed (earlier τ) (label τ) (later τ)
        (TierKeyProcess.key r K q c n.val τ ω p) (TierKeyProcess.key r K q c (n.val+1) τ ω p)-
      KeyEdits.uncovered (TierKeyProcess.key r K q c n.val τ ω p)) ≤
      if dist (c n) p≤22*r then 49/(K:ℝ) else 0 := by
  have hm := (TierLifetimes.law K hq).expect_mono _ _ (fun τ =>
    KeyEdits.insertion_mover ((TierLifetimes.live r K q c n.val τ).sort (·≤·))
      (keep r K q c n τ) (fun i => (ω i).val (c i,p)) n (earlier τ) (label τ) (later τ))
  have he (τ : TierLifetimes.Tape N) :
      (KeyEdits.next ((TierLifetimes.live r K q c n.val τ).sort (·≤·)) (keep r K q c n τ) n).find?
        (fun i => (ω i).val (c i,p))=TierKeyProcess.key r K q c (n.val+1) τ ω p := by
    rw [←sorted_next r K hK hq q c n hn τ]; rfl
  simp_rw [he] at hm
  change _ ≤ (TierLifetimes.law K hq).expect (fun τ => KeyEdits.retirement
    (TierKeyProcess.key r K q c n.val τ ω p) (keep r K q c n τ)) at hm
  simp_rw [retirement_eq] at hm
  exact hm.trans (TierRetirement.probability_bound r hr K hK hq q c n ω p)

end UniformKServer.TierKeyEdits

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierLabeledEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The one-edit noncoverage ledger uses the actual recycled labels. Old
records preserve their labels; the proof does not assume eternal identifiers. -/
noncomputable section
namespace UniformKServer.TierLabeledKeys
open Finset FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ} {J : Type*}

local instance indexDecEq_r5f289f_3 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqEdit_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem old_map (r : ℝ) (K : ℕ) (hK : 2≤K) (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1)
    (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (τ : TierLifetimes.Tape N) (ω : TierKeyEdits.RadiusTape X N K r) (p : X) :
    key r K q c n.val τ ω p=(TierKeyProcess.key r K q c n.val τ ω p).map
      (TierLabels.labels r K q c (n.val+1)).label := by
  unfold key
  cases ho : TierKeyProcess.key r K q c n.val τ ω p with
  | none => rfl
  | some i =>
    have hi := (mem_sort _).mp (TierKeys.key_mem _ _ _ c ω p i ho)
    have hit := TierSchedule.index_lt r K q c n.val i
      ((mem_filter.mp ((TierLifetimes.valid r K hK hq q c n.val).1 τ hi)).1)
    have hin : i≠n := fun he => by have := congrArg Fin.val he; omega
    have hb : TierLabels.birth r K q c n.val=some n := by
      rw [TierLabels.birth,dite_eq_left n.isLt,ite_eq_left hn]
    simp only [Option.map_some]
    congr 1
    exact (@CooldownLabels.label_old (Fin N) (instDecidableEqFin N) (Fintype.card X*K^2) (TierLabels.reserved r K q c) (TierLabels.birth r K q c) n.val n i hb hin).symm

theorem uncovered_map {I L : Type*} (f : I→L) (o : Option I) :
    KeyEdits.uncovered (o.map f)=KeyEdits.uncovered o := by cases o <;> rfl

theorem changed_map {I L : Type*} (e : Option J) (l : L→J) (z : J)
    (f : I→L) (a b : Option I) :
    KeyEdits.changed e l z (a.map f) (b.map f)=KeyEdits.changed e (l∘f) z a b := by
  cases a <;> cases b <;> rfl

theorem stationary (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X)
    (earlier : TierLifetimes.Tape N→Option J) (label : TierLifetimes.Tape N→Slot X K→J)
    (later : TierLifetimes.Tape N→J) :
    (TierLifetimes.law K hq).expect (fun τ=>
      KeyEdits.changed (earlier τ) (label τ) (later τ) (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)+
        KeyEdits.uncovered (key r K q c (n.val+1) τ ω p)-KeyEdits.uncovered (key r K q c n.val τ ω p))≤
      2*(if dist (c n) p≤22*r then 49/(K:ℝ) else 0) := by
  have he (τ : TierLifetimes.Tape N) : KeyEdits.changed (earlier τ) (label τ) (later τ)
      (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)=
      KeyEdits.changed (earlier τ) (label τ∘(TierLabels.labels r K q c (n.val+1)).label) (later τ)
        (TierKeyProcess.key r K q c n.val τ ω p) (TierKeyProcess.key r K q c (n.val+1) τ ω p) := by
    rw [old_map r K hK hq q c n hn τ ω p]
    exact changed_map _ _ _ _ _ _
  simp_rw [he,key,uncovered_map]
  exact TierKeyEdits.stationary r hr K hK hq q c n hn ω p earlier _ later

theorem mover (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X)
    (earlier : TierLifetimes.Tape N→Option J) (label : TierLifetimes.Tape N→Slot X K→J)
    (later : TierLifetimes.Tape N→J) :
    (TierLifetimes.law K hq).expect (fun τ=>
      KeyEdits.changed (earlier τ) (label τ) (later τ) (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)-
        KeyEdits.uncovered (key r K q c n.val τ ω p))≤
      if dist (c n) p≤22*r then 49/(K:ℝ) else 0 := by
  have he (τ : TierLifetimes.Tape N) : KeyEdits.changed (earlier τ) (label τ) (later τ)
      (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)=
      KeyEdits.changed (earlier τ) (label τ∘(TierLabels.labels r K q c (n.val+1)).label) (later τ)
        (TierKeyProcess.key r K q c n.val τ ω p) (TierKeyProcess.key r K q c (n.val+1) τ ω p) := by
    rw [old_map r K hK hq q c n hn τ ω p]
    exact changed_map _ _ _ _ _ _
  simp_rw [he,key,uncovered_map]
  exact TierKeyEdits.mover r hr K hK hq q c n hn ω p earlier _ later

end UniformKServer.TierLabeledKeys

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! At a heavy request the inner ball has no short-edit error: the completed
heavy key shadows every short tier, while a qualifying tier covers that ball. -/
noncomputable section
namespace UniformKServer.TierLabeledKeys
open Finset FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ} {J : Type*}

local instance indexDecEqInner_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqInner_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem coverage_near (r : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K) (q : Fin N→Prop)
    (c : Fin N→X) (n : Fin N) (hn : q n) (τ : TierLifetimes.Tape N)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X) (hp : dist (c n) p ≤ r/2) :
    (key r K q c (n.val+1) τ ω p).isSome=true := by
  obtain ⟨i,hi,hd⟩ := TierLifetimes.coverage r hr.le K (by omega) q c n hn τ
  have hKr : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hlam : 0<Real.log (1+(K:ℝ)^2) := Real.log_pos (by nlinarith [sq_pos_of_pos hKr])
  have hcover : (ω i).val (c i,p)=true := by
    apply TierRadius.cover_inner _ r hlam hr (ω i) _ _
    have ht := dist_triangle (c i) (c n) p
    rw [dist_comm (c i) (c n)] at ht
    linarith
  have hsome : (TierKeyProcess.key r K q c (n.val+1) τ ω p).isSome=true := by
    change (List.find? (fun j => (ω j).val (c j,p))
      ((TierLifetimes.live r K q c (n.val+1) τ).sort (·≤·))).isSome=true
    rw [List.isSome_find?]
    exact List.any_eq_true.mpr ⟨i,(mem_sort _).mpr hi,hcover⟩
  simpa only [key,Option.isSome_map] using hsome

theorem annular_stationary (r γ : ℝ) (hr : 0 < r) (hγ : γ≤1/2) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X) (heavy : Prop)
    (earlier : TierLifetimes.Tape N→Option J) (label : TierLifetimes.Tape N→Slot X K→J)
    (later : TierLifetimes.Tape N→J)
    (he : heavy→dist (c n) p≤γ*r→∀ τ, (earlier τ).isSome=true) :
    (TierLifetimes.law K hq).expect (fun τ=>
      KeyEdits.changed (earlier τ) (label τ) (later τ) (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)+
        KeyEdits.uncovered (key r K q c (n.val+1) τ ω p)-KeyEdits.uncovered (key r K q c n.val τ ω p))≤
      98/(K:ℝ)*(if dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p) then 1 else 0) := by
  by_cases hh : heavy ∧ dist (c n) p≤γ*r
  · have hp : dist (c n) p ≤ r/2 := by nlinarith [mul_le_mul_of_nonneg_right hγ hr.le]
    have hz (τ : TierLifetimes.Tape N) := coverage_near r hr K hK q c n hn.1 τ ω p hp
    have hn' : ¬(dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p)) := by aesop
    simp only [ite_eq_right hn',mul_zero]
    calc
      _ ≤ (TierLifetimes.law K hq).expect (fun _ => 0) := by
        apply (TierLifetimes.law K hq).expect_mono
        intro τ
        cases heq : earlier τ with
        | none => have := he hh.1 hh.2 τ; simp [heq] at this
        | some j =>
          rw [KeyEdits.shadowed]
          cases hzkey : key r K q c (n.val+1) τ ω p with
          | none => have hzt := hz τ; simp [hzkey] at hzt
          | some i =>
            have hu := (KeyEdits.uncovered_bounds (key r K q c n.val τ ω p)).1
            simpa only [KeyEdits.uncovered,Option.isNone_some,Bool.false_eq_true,ite_false, if_false,
              zero_add,zero_sub,neg_nonpos] using hu
      _ = _ := Law.expect_const _ _
  · have hc : ¬heavy ∨ γ*r<dist (c n) p := by
      by_cases h : heavy
      · exact Or.inr (lt_of_not_ge (fun hp => hh ⟨h,hp⟩))
      · exact Or.inl h
    have h := stationary r hr K hK hq q c n hn ω p earlier label later
    by_cases hp : dist (c n) p≤22*r
    · have hcond : dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p) := ⟨hp,hc⟩
      simpa only [ite_eq_left hp,ite_eq_left hcond,mul_one,show (2:ℝ)*(49/(K:ℝ))=98/(K:ℝ) by ring] using h
    · simpa only [ite_eq_right hp,ite_eq_right (not_and_of_not_left _ hp),mul_zero] using h


theorem annular_mover (r γ : ℝ) (hr : 0 < r) (K : ℕ) (hK : 2≤K)
    (hq : 1/(K:ℝ)∈Set.Icc (0:ℝ) 1) (q : Fin N→Prop) (c : Fin N→X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (ω : TierKeyEdits.RadiusTape X N K r) (p : X) (heavy : Prop)
    (earlier : TierLifetimes.Tape N→Option J) (label : TierLifetimes.Tape N→Slot X K→J)
    (later : TierLifetimes.Tape N→J)
    (he : heavy→dist (c n) p≤γ*r→∀ τ, (earlier τ).isSome=true) :
    (TierLifetimes.law K hq).expect (fun τ=>
      KeyEdits.changed (earlier τ) (label τ) (later τ) (key r K q c n.val τ ω p) (key r K q c (n.val+1) τ ω p)-
        KeyEdits.uncovered (key r K q c n.val τ ω p))≤
      49/(K:ℝ)*(if dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p) then 1 else 0) := by
  by_cases hh : heavy ∧ dist (c n) p≤γ*r
  · have hn' : ¬(dist (c n) p≤22*r ∧ (¬heavy ∨ γ*r<dist (c n) p)) := by aesop
    simp only [ite_eq_right hn',mul_zero]
    calc
      _ ≤ (TierLifetimes.law K hq).expect (fun _ => 0) := by
        apply (TierLifetimes.law K hq).expect_mono
        intro τ
        cases heq : earlier τ with
        | none => have := he hh.1 hh.2 τ; simp [heq] at this
        | some j =>
          rw [KeyEdits.shadowed]
          simpa only [zero_sub,neg_nonpos] using
            (KeyEdits.uncovered_bounds (key r K q c n.val τ ω p)).1
      _ = _ := Law.expect_const _ _
  · have hc : ¬heavy ∨ γ*r<dist (c n) p := by
      by_cases h : heavy
      · exact Or.inr (lt_of_not_ge (fun hp => hh ⟨h,hp⟩))
      · exact Or.inl h
    have h := mover r hr K hK hq q c n hn ω p earlier label later
    by_cases hp : dist (c n) p≤22*r
    · simpa only [ite_eq_left hp,ite_eq_left (And.intro hp hc),mul_one] using h
    · simpa only [ite_eq_right hp,ite_eq_right (not_and_of_not_left _ hp),mul_zero] using h

end UniformKServer.TierLabeledKeys

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelTierEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Actual full-tape one-tier edit estimates. Prefix and suffix may depend
arbitrarily on the tape; the noncoverage ledger is not conditioned on either. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqEdit_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.LevelMap.Data.tierDecEqEdit
attribute [local instance] OAI.UniformKServer.LevelMap.Data.pairDecEqEdit
theorem tier_stationary (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (γ : ℝ) (hγ : γ≤1/2) (hn : D.tierTrigger n i)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω, (earlier ω).isSome=true) :
    D.law.expect (fun ω=>D.tierEdit n i p earlier later ω+
      D.tierUncovered ω (n.val+1) i p-D.tierUncovered ω n.val i p)≤
      98/(D.K i:ℝ)*(if dist (D.center n) p≤22*D.r ∧ (¬D.heavy n ∨ γ*D.r<dist (D.center n) p) then 1 else 0) := by
  apply tier_expect_bound D i
  intro heavy b rad
  let z := fun τ : TierLifetimes.Tape N =>
    (heavy,(Equiv.piSplitAt i (TierTape D)).symm ((τ,rad),b))
  have hz (τ : TierLifetimes.Tape N) : (z τ).2 i=(τ,rad) := by simp [z,Equiv.piSplitAt]
  have h := TierLabeledKeys.annular_stationary D.r γ D.positive hγ (D.K i) (D.two i)
    (D.quota i) (D.qualify i) D.center n hn rad p (D.heavy n)
    (fun τ=>earlier (z τ)) (fun _ l=>Sum.inr (Sum.inl ⟨i,l⟩)) (fun τ=>later (z τ))
    (fun hh hp τ=>he hh hp (z τ))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (TierLifetimes.law (D.K i) (D.quota i)).expect
  funext τ
  change D.tierEdit n i p earlier later (z τ)+D.tierUncovered (z τ) (n.val+1) i p-
    D.tierUncovered (z τ) n.val i p=_
  simp only [tierEdit,tierUncovered,tierKey,hz,TierLabeledKeys.changed_map,
    TierLabeledKeys.uncovered_map,Function.id_comp]

theorem tier_mover (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (γ : ℝ) (hn : D.tierTrigger n i)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω, (earlier ω).isSome=true) :
    D.law.expect (fun ω=>D.tierEdit n i p earlier later ω-
      D.tierUncovered ω n.val i p)≤
      49/(D.K i:ℝ)*(if dist (D.center n) p≤22*D.r ∧ (¬D.heavy n ∨ γ*D.r<dist (D.center n) p) then 1 else 0) := by
  apply tier_expect_bound D i
  intro heavy b rad
  let z := fun τ : TierLifetimes.Tape N =>
    (heavy,(Equiv.piSplitAt i (TierTape D)).symm ((τ,rad),b))
  have hz (τ : TierLifetimes.Tape N) : (z τ).2 i=(τ,rad) := by simp [z,Equiv.piSplitAt]
  have h := TierLabeledKeys.annular_mover D.r γ D.positive (D.K i) (D.two i)
    (D.quota i) (D.qualify i) D.center n hn rad p (D.heavy n)
    (fun τ=>earlier (z τ)) (fun _ l=>Sum.inr (Sum.inl ⟨i,l⟩)) (fun τ=>later (z τ))
    (fun hh hp τ=>he hh hp (z τ))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (TierLifetimes.law (D.K i) (D.quota i)).expect
  funext τ
  change D.tierEdit n i p earlier later (z τ)-D.tierUncovered (z τ) n.val i p=_
  simp only [tierEdit,tierUncovered,tierKey,hz,TierLabeledKeys.changed_map,
    TierLabeledKeys.uncovered_map,Function.id_comp]

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelTierLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! The complete one-tier end-to-end ledger; movement is included exactly once.
No-insertion qualified tiers contribute zero, not a spurious per-step cost. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqLedger_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqLedger_r5f289f_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqLedger_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def stationaryBudget (D : Data X N H) (γ : ℝ) (n : Fin N) (i : Fin H) (p : X) : ℝ :=
  if D.tierTrigger n i then 98*D.r/(D.K i:ℝ)*D.errorIndicator γ n p else 0

theorem stationary_ledger (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (γ : ℝ) (hγ : γ≤1/2)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω, (earlier ω).isSome=true) :
    D.r*D.law.expect (fun ω=>D.tierEdit n i p earlier later ω+
      D.tierUncovered ω (n.val+1) i p-D.tierUncovered ω n.val i p)≤D.stationaryBudget γ n i p := by
  by_cases hn : D.tierTrigger n i
  · have h := mul_le_mul_of_nonneg_left (D.tier_stationary n i p γ hγ hn earlier later he) D.positive.le
    rw [stationaryBudget,ite_eq_left hn]
    exact h.trans_eq (by change D.r*(98/(D.K i:ℝ)*D.errorIndicator γ n p)=_; ring)
  · have hz (ω : Tape D) := D.tierEdit_frozen n i p earlier later hn ω
    have h0 (ω : Tape D) := (hz ω).1
    have h1 (ω : Tape D) := (hz ω).2
    simp only [h0,h1,zero_add,sub_self,Law.expect_const,mul_zero,stationaryBudget,ite_eq_right hn,le_refl]

theorem mover_ledger (D : Data X N H) (n : Fin N) (i : Fin H) (p : X)
    (γ : ℝ)
    (earlier : Tape D→Option (Label D)) (later : Tape D→Label D)
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω, (earlier ω).isSome=true) :
    D.r*D.law.expect (fun ω=>D.tierEdit n i p earlier later ω+
      D.tierUncovered ω (n.val+1) i (D.center n)-D.tierUncovered ω n.val i p)≤D.moverBudget γ n i p := by
  by_cases hn : D.tierTrigger n i
  · have hz (ω : Tape D) : D.tierUncovered ω (n.val+1) i (D.center n)=0 :=
      D.tierUncovered_covered n i hn.1 ω
    simp only [hz,add_zero,moverBudget,ite_eq_left hn]
    have h := mul_le_mul_of_nonneg_left (D.tier_mover n i p γ hn earlier later he) D.positive.le
    exact h.trans_eq (by change D.r*(49/(D.K i:ℝ)*D.errorIndicator γ n p)=_; ring)
  · have hz (ω : Tape D) := D.tierEdit_frozen n i p earlier later hn ω
    have h0 (ω : Tape D) := (hz ω).1
    simp only [h0,zero_add,moverBudget,ite_eq_right hn]
    have heq (ω : Tape D) : D.tierUncovered ω n.val i p=D.tierUncovered ω (n.val+1) i p := (hz ω).2.symm
    simp_rw [heq]
    exact D.tierUncovered_motion n i p

end UniformKServer.LevelMap.Data

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelSerial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The source edit order: first heavy, then tiers in order. Each tier ledger
retains its higher-priority shadow and its old lower-priority suffix. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqSerial_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqSerial_r5f289f_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqSerial_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem serial_ledger (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p q : X)
    (e : Tape D→Option (Label D)) (shadow : Prop) (he : shadow→∀ ω,(e ω).isSome=true)
    (b : Fin H→ℝ)
    (h : ∀ i∈is, ∀ (earlier : Tape D→Option (Label D)) (later : Tape D→Label D),
      (shadow→∀ ω,(earlier ω).isSome=true)→
      D.r*D.law.expect (fun ω=>D.tierEdit n i p earlier later ω+
        D.tierUncovered ω (n.val+1) i q-D.tierUncovered ω n.val i p)≤b i) :
    D.r*D.law.expect (fun ω=> D.serialEdit n is p e ω+
      D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω)≤(is.map b).sum := by
  induction is generalizing e with
  | nil => simp only [serialEdit,editSum,tierPotential,List.map_nil,List.sum_nil,add_zero,sub_zero,Law.expect_const,mul_zero,le_refl]
  | cons i is ih =>
    let later : Tape D→Label D := fun ω=>
      (first is (fun j=>D.tierKey ω n.val j p)).getD (Sum.inr (Sum.inr p))
    let e' : Tape D→Option (Label D) := fun ω=>(e ω).or (D.tierKey ω (n.val+1) i p)
    have he' : shadow→∀ ω,(e' ω).isSome=true := by
      intro hs ω
      have ho := he hs ω
      cases hω : e ω with
      | none => simp [hω] at ho
      | some l => simp only [e',hω,Option.some_or,Option.isSome_some]
    have head := h i (List.mem_cons_self ..) e later he
    have tail := ih e' he' (fun j hj=>h j (List.mem_cons_of_mem _ hj))
    have heq (ω : Tape D) : D.serialEdit n (i::is) p e ω+
        D.tierPotential (i::is) (n.val+1) q ω-D.tierPotential (i::is) n.val p ω=
        (D.tierEdit n i p e later ω+D.tierUncovered ω (n.val+1) i q-D.tierUncovered ω n.val i p)+
        (D.serialEdit n is p e' ω+D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω) := by
      dsimp only [serialEdit,editSum,tierPotential,List.map_cons,List.sum_cons,tierEdit,e',later]
      simp only [List.map_cons,List.sum_cons]
      ring
    simp_rw [heq]
    rw [Law.expect_add,mul_add,List.map_cons,List.sum_cons]
    exact add_le_add head tail

theorem serial_stationary (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X)
    (γ : ℝ) (hγ : γ≤1/2) (e : Tape D→Option (Label D))
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω,(e ω).isSome=true) :
    D.r*D.law.expect (fun ω=>D.serialEdit n is p e ω+
      D.tierPotential is (n.val+1) p ω-D.tierPotential is n.val p ω)≤
        (is.map fun i=>D.stationaryBudget γ n i p).sum := by
  apply serial_ledger D n is p p e (D.heavy n ∧ dist (D.center n) p≤γ*D.r)
    (fun h=>he h.1 h.2)
  intro i _ earlier later he'
  exact D.stationary_ledger n i p γ hγ earlier later (fun hh hp=>he' ⟨hh,hp⟩)

theorem serial_mover (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X)
    (γ : ℝ) (e : Tape D→Option (Label D))
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω,(e ω).isSome=true) :
    D.r*D.law.expect (fun ω=>D.serialEdit n is p e ω+
      D.tierPotential is (n.val+1) (D.center n) ω-D.tierPotential is n.val p ω)≤
        (is.map fun i=>D.moverBudget γ n i p).sum := by
  apply serial_ledger D n is p (D.center n) e (D.heavy n ∧ dist (D.center n) p≤γ*D.r)
    (fun h=>he h.1 h.2)
  intro i _ earlier later he'
  exact D.mover_ledger n i p γ earlier later (fun hh hp=>he' ⟨hh,hp⟩)

end UniformKServer.LevelMap.Data

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelKeyLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Full level key edits with the genuine heavy-first serial auxiliary potential. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqKey_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqKey_r5f289f_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqKey_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def heavyStationaryBudget (D : Data X N H) (n : Fin N) (p : X) : ℝ :=
  if D.heavyTrigger n ∧ 3*D.r<dist (D.center n) p ∧ dist (D.center n) p≤120*D.r then 2*D.r else 0

theorem key_stationary (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (γ : ℝ) (hγ : γ≤1/2) :
    D.r*D.law.expect (fun ω=>indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p)+
      D.keyPotential is (n.val+1) p ω-D.keyPotential is n.val p ω)≤
    D.heavyStationaryBudget n p+(is.map fun i=>D.stationaryBudget γ n i p).sum := by
  exact D.key_ledger n is p p _ _ (D.heavy_stationary n p)
    (D.serial_stationary n is p γ hγ _ (fun hh hp=>D.actual_shadow n p γ hγ hh hp))

theorem key_mover (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (γ : ℝ) (hγ : γ≤1/2) :
    D.r*D.law.expect (fun ω=>indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p)+
      D.keyPotential is (n.val+1) (D.center n) ω-D.keyPotential is n.val p ω)≤
    D.heavyMoverBudget n p+(is.map fun i=>D.moverBudget γ n i p).sum := by
  exact D.key_ledger n is p (D.center n) _ _ (D.heavy_mover n p)
    (D.serial_mover n is p γ _ (fun hh hp=>D.actual_shadow n p γ hγ hh hp))

end UniformKServer.LevelMap.Data

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelMassLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Linear auxiliary-potential accounting for a stationary submass and one
unit designated mover. The mover is charged separately from post-request mass. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

local instance indexDecEqMassLedger_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqMassLedger_r5f289f_1 : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqMassLedger_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def stationaryAllowance (D : Data X N H) (is : List (Fin H)) (γ : ℝ) (n : Fin N) (p : X) : ℝ :=
  D.heavyStationaryBudget n p+(is.map fun i=>D.stationaryBudget γ n i p).sum

def moverAllowance (D : Data X N H) (is : List (Fin H)) (γ : ℝ) (n : Fin N) (p : X) : ℝ :=
  D.heavyMoverBudget n p+(is.map fun i=>D.moverBudget γ n i p).sum

theorem auxiliary_stationary (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (γ : ℝ) (hγ : γ≤1/2) :
    D.editCost n is p+D.auxiliary is (n.val+1) p-D.auxiliary is n.val p≤D.stationaryAllowance is γ n p := by
  have h := D.key_stationary n is p γ hγ
  rw [Law.expect_sub,Law.expect_add,mul_sub,mul_add] at h
  exact h

theorem auxiliary_mover (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (γ : ℝ) (hγ : γ≤1/2) :
    D.editCost n is p+D.auxiliary is (n.val+1) (D.center n)-D.auxiliary is n.val p≤D.moverAllowance is γ n p := by
  have h := D.key_mover n is p γ hγ
  rw [Law.expect_sub,Law.expect_add,mul_sub,mul_add] at h
  exact h

theorem mass_ledger (D : Data X N H) (n : Fin N) (is : List (Fin H)) (γ : ℝ) (hγ : γ≤1/2)
    (s ν : X→ℝ) (hs : ∀ p,0≤ s p) (hν : ∀ p,0≤ν p) (hνtotal : ∑ p,ν p=1) :
    (∑ p,(s p+ν p)*D.editCost n is p)+
      ((∑ p,s p*D.auxiliary is (n.val+1) p)+D.auxiliary is (n.val+1) (D.center n))-
      (∑ p,(s p+ν p)*D.auxiliary is n.val p)≤
    (∑ p,s p*D.stationaryAllowance is γ n p)+(∑ p,ν p*D.moverAllowance is γ n p) := by
  have hs' := sum_le_sum (fun p (_ : p∈(univ : Finset X))=>
    mul_le_mul_of_nonneg_left (D.auxiliary_stationary n is p γ hγ) (hs p))
  have hν' := sum_le_sum (fun p (_ : p∈(univ : Finset X))=>
    mul_le_mul_of_nonneg_left (D.auxiliary_mover n is p γ hγ) (hν p))
  have he : (∑ p,s p*(D.editCost n is p+D.auxiliary is (n.val+1) p-D.auxiliary is n.val p))+
      (∑ p,ν p*(D.editCost n is p+D.auxiliary is (n.val+1) (D.center n)-D.auxiliary is n.val p))=
    (∑ p,(s p+ν p)*D.editCost n is p)+
      ((∑ p,s p*D.auxiliary is (n.val+1) p)+D.auxiliary is (n.val+1) (D.center n))-
      (∑ p,(s p+ν p)*D.auxiliary is n.val p) := by
    simp only [mul_sub,mul_add,add_mul,sum_sub_distrib,sum_add_distrib,←sum_mul,hνtotal,one_mul]
    ring
  exact he ▸ add_le_add hs' hν'

end UniformKServer.LevelMap.Data

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FlowAuxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Linear adapted auxiliary potentials commute with posterior filtering. -/
namespace UniformKServer.PilotEdits
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [Fintype Ω] {k : ℕ}

theorem linear_bounds (F : Flow X Ω k) (t : ℕ) (ω : Ω) (b : X→ℝ) (M : ℝ)
    (hb : ∀ p,0≤b p ∧ b p≤M) :
    0≤linearPotential (F.post t ω) b ∧ linearPotential (F.post t ω) b≤k*M := by
  constructor
  · exact sum_nonneg (fun p _=>mul_nonneg (F.post_nonneg t ω p) (hb p).1)
  · calc
      _≤∑ p,F.post t ω p*M := sum_le_sum (fun p _=>mul_le_mul_of_nonneg_left (hb p).2 (F.post_nonneg t ω p))
      _=_ := by rw [←sum_mul,F.post_total]

end UniformKServer.PilotEdits

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierShortSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Deterministic expected short-roster functions on the actual chronological
insertion records. These auxiliary experiments never select actual keys. -/
noncomputable section
namespace UniformKServer.TierShortSchedule
open Finset ShortRoster ChronologicalRoster
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

omit [Fintype X] in
theorem valid (r : ℝ) (K : ℕ) (hK : 0<K) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (t : ℕ) :
    (run r K s hs q c t).Valid (TierSchedule.run r K q c t) c r K s := by
  induction t with
  | zero => exact State.empty_valid c r K s
  | succ t ih =>
    by_cases ht : t<N
    · let n : Fin N := ⟨t,ht⟩
      by_cases hn : TierSchedule.trigger r K (TierSchedule.run r K q c t) q c n
      · rw [run,dite_eq_left ht,ite_eq_left hn,TierSchedule.run,dite_eq_left ht,ite_eq_left hn]
        convert (run r K s hs q c t).next_valid _ c r K hK s hs n ih
          (fun i hi => TierSchedule.index_lt r K q c t i hi) using 1
        all_goals try with_reducible_and_instances rfl
        ext i
        simp only [mem_insert]
        rfl
      · have hn' : ¬TierSchedule.trigger r K (TierSchedule.run r K q c t) q c ⟨t,ht⟩ := hn
        simpa only [run,TierSchedule.run,dite_eq_left ht,ite_eq_right hn'] using ih
    · simpa only [run,TierSchedule.run,dite_eq_right ht] using ih

theorem insertion_payment (P : TierPilot.Parameters) (r h : ℝ) (hr : 0 < r) (hh : 1≤h)
    (K : ℕ) (hK : 2≤K) (hlarge : Real.exp (TierInsertion.lifetimeExponent P*h)≤K)
    (hs : 1/Real.sqrt (K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (q : Fin N → Prop) (c : Fin N → X) (n : Fin N)
    (hn : TierSchedule.trigger r K (TierSchedule.run r K q c n.val) q c n)
    (μ : X → ℝ) (hμ : ∀ p, 0≤μ p)
    (hM : 0<PilotCompact.ballMass r P.gammaH μ (c n))
    (hqual : PilotCompact.ballMass r 20480000 μ (c n)≤
      Real.exp h*PilotCompact.ballMass r P.gammaL μ (c n)) :
    r*TierPilot.insertionMass P r μ (c n)/(K:ℝ)≤
      Real.exp (-h)*(PilotCompact.value r P.sigma 204800 μ
        (parameter r K (1/Real.sqrt (K:ℝ)) hs q c n.val)-
        PilotCompact.value r P.sigma 204800 μ
        (parameter r K (1/Real.sqrt (K:ℝ)) hs q c (n.val+1))) := by
  have htest : ∀ i∈young (TierSchedule.run r K q c n.val) c r K,
      r/2<dist (c n) (c i) := by
    intro i hi
    exact lt_of_not_ge (fun hd => hn.2 ⟨i,hi,hd⟩)
  have hb := TierInsertion.weighted_short_gain P (run r K (1/Real.sqrt (K:ℝ)) hs q c n.val)
    (TierSchedule.run r K q c n.val) c r h hr hh K hK hlarge hs n
    (valid r K (by omega) _ hs q c n.val)
    (fun i hi => TierSchedule.index_lt r K q c n.val i hi) htest μ hμ hM hqual
  simpa only [parameter,run,dite_eq_left n.isLt,ite_eq_left hn] using hb

end UniformKServer.TierShortSchedule

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualLevelPilot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

                                                                         
                                                                 
noncomputable section
namespace UniformKServer.PartitionLevel.Input
open Finset PilotCompact
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

theorem long_bounds (I : PartitionLevel.Input X N) (t : ℕ) (p : X) :
    I.longParameter t p∈Set.Icc (0:ℝ) 1 := HeavyPilot.parameter_bounds _ _ _

theorem long_lip (I : PartitionLevel.Input X N) (t : ℕ) (p q : X) :
    |I.longParameter t p-I.longParameter t q|≤dist p q/I.r :=
  HeavyPilot.parameter_lip I.r I.r_pos _ p q

theorem short_bounds (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) (p : X) :
    I.shortParameter i t p∈Set.Icc (0:ℝ) 1 := ShortRoster.parameter_bounds _ _ _ _

theorem short_lip (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) (p q : X) :
    |I.shortParameter i t p-I.shortParameter i t q|≤8*(dist p q/I.r) := by
  simpa only [shortParameter,TierShortSchedule.parameter,mul_div_assoc] using ShortRoster.parameter_lip
    (TierShortSchedule.run I.r (I.data.K i) (I.shortProb i) (I.shortProb_bounds i)
      (I.data.qualify i) I.center t) I.center I.r I.r_pos p q

theorem mass_bridge (r a : ℝ) (μ : X→ℝ) (x : X) :
    ballMass r a μ x=GeometricMass.mass μ x (a*r) := by
  unfold ballMass GeometricMass.mass
  rfl

theorem positive_inner (I : PartitionLevel.Input X N) (n : Fin N) :
    0<ballMass I.r I.P.gammaH (I.μ n) (I.center n) := by
  rw [mass_bridge]
  have h := (I.served n).trans (GeometricMass.mass_center _ (I.μ_nonneg n) _ _ (mul_pos I.P.gammaH_pos I.r_pos).le)
  linarith

theorem long_charge_nonneg (I : PartitionLevel.Input X N) (t : ℕ) : 0≤I.longCharge t := by
  unfold longCharge
  split_ifs with ht hn
  · apply mul_nonneg (mul_nonneg (by norm_num) I.r_pos.le)
    unfold HeavyPilot.annulusMass
    apply sum_nonneg
    intro p _
    split_ifs <;> [exact I.μ_nonneg ⟨t,ht⟩ p; exact le_rfl]
  all_goals exact le_rfl

theorem short_charge_nonneg (I : PartitionLevel.Input X N) (i : Fin I.height) (t : ℕ) :
    0≤I.shortCharge i t := by
  unfold shortCharge
  split_ifs with ht hn
  · exact div_nonneg (mul_nonneg I.r_pos.le
      (TierPilot.insertionMass_bounds I.P I.r I.r_pos.le _ (I.μ_nonneg ⟨t,ht⟩) _).1) (Nat.cast_nonneg _)
  all_goals exact le_rfl

theorem long_payment (I : PartitionLevel.Input X N) (t : ℕ) (μ : X→ℝ)
    (hμ : ∀ ht : t<N, μ=I.μ ⟨t,ht⟩) :
    I.longCharge t≤value I.r 1 512 μ (I.longParameter t)-
      value I.r 1 512 μ (I.longParameter (t+1)) := by
  by_cases ht : t<N
  · rw [hμ ht]
    unfold longCharge longParameter
    rw [dite_eq_left ht,HeavySchedule.centers]
    by_cases hi : HeavySchedule.trigger I.r (I.data.heavyFlag t)
        (HeavySchedule.centers I.r I.data.heavyFlag I.data.point t) (I.data.point t)
    · rw [ite_eq_left hi,HeavySchedule.step,ite_eq_left hi]
      have hx : I.data.point t=I.center ⟨t,ht⟩ := by simp only [LevelMap.Data.point,data,dite_eq_left ht]
      have hh : I.data.heavy ⟨t,ht⟩ := by obtain ⟨_,hh⟩ := hi.1; exact hh
      have hconc : ballMass I.r (100*512) (I.μ ⟨t,ht⟩) (I.center ⟨t,ht⟩)≤
          (1+I.P.deltaH)*ballMass I.r I.P.gammaH (I.μ ⟨t,ht⟩) (I.center ⟨t,ht⟩) := by
        simpa only [data,mass_bridge,show (100:ℝ)*512=51200 by norm_num] using hh
      rw [hx]
      exact HeavyPilot.heavy_gain I.r I.P.gammaH I.P.deltaH I.r_pos I.P.gammaH_pos
        (by linarith [I.P.gammaH_small]) I.P.deltaH_pos I.P.deltaH_small _ (I.μ_nonneg ⟨t,ht⟩)
        _ _ (by simpa only [hx] using hi.2) (I.positive_inner ⟨t,ht⟩) hconc
    · simp only [ite_eq_right hi,HeavySchedule.step,sub_self,le_refl]
  · have hf : ¬I.data.heavyFlag t := by rintro ⟨hnt,_⟩; exact ht hnt
    have hn : ¬HeavySchedule.trigger I.r (I.data.heavyFlag t)
        (HeavySchedule.centers I.r I.data.heavyFlag I.data.point t) (I.data.point t) := fun h => hf h.1
    simp only [longCharge,dite_eq_right ht,longParameter,HeavySchedule.centers,HeavySchedule.step,ite_eq_right hn,sub_self,le_refl]

theorem short_payment (I : PartitionLevel.Input X N) (i : Fin I.height)
    (hlarge : Real.exp (TierInsertion.lifetimeExponent I.P*DyadicTiers.value i.val)≤I.data.K i)
    (t : ℕ) (μ : X→ℝ) (hμ : ∀ ht : t<N, μ=I.μ ⟨t,ht⟩) :
    I.shortCharge i t≤Real.exp (-DyadicTiers.value i.val)*
      (value I.r I.P.sigma 204800 μ (I.shortParameter i t)-
        value I.r I.P.sigma 204800 μ (I.shortParameter i (t+1))) := by
  by_cases ht : t<N
  · rw [hμ ht]
    unfold shortCharge
    rw [dite_eq_left ht]
    by_cases hi : TierSchedule.trigger I.r (I.data.K i)
        (TierSchedule.run I.r (I.data.K i) (I.data.qualify i) I.center t) (I.data.qualify i) I.center ⟨t,ht⟩
    · rw [ite_eq_left hi]
      apply TierShortSchedule.insertion_payment I.P I.r _ I.r_pos (DyadicTiers.one_le_value i.val)
        (I.data.K i) (I.data.two i) hlarge (I.shortProb_bounds i) (I.data.qualify i) I.center ⟨t,ht⟩ hi
        (I.μ ⟨t,ht⟩) (I.μ_nonneg ⟨t,ht⟩) (I.positive_inner ⟨t,ht⟩)
      simpa only [data,mass_bridge] using hi.1
    · simp only [ite_eq_right hi,shortParameter,TierShortSchedule.parameter,TierShortSchedule.run,dite_eq_left ht,sub_self,mul_zero,le_refl]
  · simp only [shortCharge,dite_eq_right ht,shortParameter,TierShortSchedule.parameter,TierShortSchedule.run,sub_self,mul_zero,le_refl]

end UniformKServer.PartitionLevel.Input

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CausalShort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! The deterministic short-roster pilot is measurable from the true past;
its auxiliary probability space is integrated out, not secretly observed. -/
noncomputable section
namespace UniformKServer.CausalRosters
open Finset ChronologicalRoster ShortRoster
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

omit [Fintype X] in
lemma short_next (D : State (Fin N)) (S : Finset (Fin N)) (c d : Fin N → X)
    (r : ℝ) (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (n : Fin N)
    (hn : c n=d n) (he : ∀ j∈S, c j=d j) (hD : ∀ ω, D.live ω ⊆ S) :
    D.next S c r K s hs n=D.next S d r K s hs n := by
  unfold State.next
  congr 1
  funext ω
  congr 1
  unfold retained
  ext i
  simp only [mem_filter]
  apply and_congr_right
  intro hi
  rw [he i (hD ω.1 hi),hn,age_congr S c d r i (he i (hD ω.1 hi)) he]

omit [Fintype X] in
lemma short_inputs (r : ℝ) (K : ℕ) (hK : 0<K) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierShortSchedule.run r K s hs q c t=TierShortSchedule.run r K s hs v d t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun i hi => hq i (by omega)) (fun i hi => hc i (by omega))
    simp only [TierShortSchedule.run]
    by_cases ht : t<N
    · simp only [dite_eq_left ht,schedule r K q v c d t (fun i hi => hq i (by omega))
        (fun i hi => hc i (by omega)),hh]
      let S := TierSchedule.run r K v d t
      have he : ∀ j∈S, c j=d j := fun j hj => hc j (Nat.lt_succ_of_lt (TierSchedule.index_lt r K v d t j hj))
      have hn := hc ⟨t,ht⟩ (by simp)
      rw [propext (trigger_congr S q v c d r K ⟨t,ht⟩ (hq _ (by simp)) hn he)]
      split_ifs
      · exact short_next _ S c d r K s hs ⟨t,ht⟩ hn he (fun ω i hi =>
          (mem_filter.mp ((TierShortSchedule.valid r K hK s hs v d t).1 ω hi)).1)
      · rfl
    · simp only [dite_eq_right ht,hh]

omit [Fintype X] in
lemma short_parameter (r : ℝ) (K : ℕ) (hK : 0<K) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1)
    (q v : Fin N → Prop) (c d : Fin N → X) (t : ℕ)
    (hq : ∀ i : Fin N, i.val<t → (q i ↔ v i)) (hc : ∀ i : Fin N, i.val<t → c i=d i) :
    TierShortSchedule.parameter r K s hs q c t=TierShortSchedule.parameter r K s hs v d t := by
  unfold TierShortSchedule.parameter
  rw [short_inputs r K hK s hs q v c d t hq hc]
  funext p
  unfold State.parameter FiniteProbability.Law.expect
  apply sum_congr rfl
  intro ω _
  congr 1
  have he : ((TierShortSchedule.run r K s hs v d t).live ω).image
      (fun i => ramp (dist p (c i)/r)) =
      ((TierShortSchedule.run r K s hs v d t).live ω).image (fun i => ramp (dist p (d i)/r)) := by
    apply image_congr
    intro i hi
    dsimp only
    rw [hc i (TierSchedule.index_lt r K v d t i
      (mem_filter.mp ((TierShortSchedule.valid r K hK s hs v d t).1 ω hi)).1)]
  dsimp only [costValue]
  simp only [he]

end UniformKServer.CausalRosters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionCausal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Filtration measurability of actual partition keys, anchors, and pilot
parameters, with a common initially sampled finite tape. -/
noncomputable section
namespace UniformKServer.ActualPartitions.Config
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem long_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).longParameter t=
      ((A.input (N:=N) (J:=J) D hk v).level j).longParameter t := by
  unfold PartitionLevel.Input.longParameter
  congr 1
  apply HeavyProcess.centers_inputs
  · intro s hs
    unfold LevelMap.Data.heavyFlag
    apply exists_congr
    intro hN
    exact A.past_heavy (J:=J) D hk ω v t j he ⟨s,hN⟩ hs
  · intro s hs
    unfold LevelMap.Data.point
    split_ifs with hN
    · exact A.past_centers (J:=J) D hk ω v t he ⟨s,hN⟩ hs
    · rfl

theorem short_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω v : Ω) (t j : ℕ) (he : (D.filtration t).r ω v)
    (i : Fin ((A.input (N:=N) (J:=J) D hk ω).level j).height) :
    ((A.input (N:=N) (J:=J) D hk ω).level j).shortParameter i t=
      ((A.input (N:=N) (J:=J) D hk v).level j).shortParameter i t := by
  unfold PartitionLevel.Input.shortParameter
  apply CausalRosters.short_parameter
  · have := ((A.input (N:=N) (J:=J) D hk ω).level j).data.two i
    omega
  · exact A.past_qualify (J:=J) D hk ω v t j he i
  · exact A.past_centers (J:=J) D hk ω v t he

end UniformKServer.ActualPartitions.Config

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Uniform finite pilot family constants: the tier weights sum independently
of the number of tiers and of k. -/
namespace UniformKServer.PilotFamily
open Finset PilotEdits

def template (P : TierPilot.Parameters) {k : ℕ} : Index k→Template
  | none => heavyTemplate
  | some _ => shortTemplate P

def weight {k : ℕ} : Index k→ℝ
  | none => 1
  | some i => Real.exp (-DyadicTiers.value i.val)

theorem weight_nonneg {k : ℕ} (i : Index k) : 0≤weight i := by
  cases i <;> simp only [weight] <;> positivity

end UniformKServer.PilotFamily

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ReverseScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                    
section

/-! Finite geometric scale reversal for the pilot finance theorem. -/
namespace UniformKServer.GeometricMass
open Finset

theorem radius_reverse (R q : ℝ) (hq : q≠0) (J j : ℕ) (hj : j<J) :
    radius R q (J-1-j)=(R*q^J)*(q⁻¹)^j := by
  have he : J-1-j+1+j=J := by omega
  unfold radius
  have hp : q^J=q^(J-1-j+1)*q^j := by rw [←pow_add,he]
  rw [hp,inv_pow]
  have hqj : q^j≠0 := pow_ne_zero _ hq
  field_simp

end UniformKServer.GeometricMass

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualPilot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The global pilot finance ledger for the literal partition. Constants do not
 depend on the input law, time horizon, or the number of scales. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits PilotCompact
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem pilot_bounds (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) (p : X) :
    A.pilotParameter (N:=N) (J:=J) D hk t ω i j p∈Set.Icc (0:ℝ) 1 := by
  unfold pilotParameter
  split_ifs with hj
  · cases i with
    | none => exact PartitionLevel.Input.long_bounds _ _ _
    | some a => exact PartitionLevel.Input.short_bounds _ _ _ _
  · constructor <;> norm_num

theorem pilot_lip (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) (p q : X) :
    |A.pilotParameter (N:=N) (J:=J) D hk t ω i j p-A.pilotParameter (N:=N) (J:=J) D hk t ω i j q|≤
      (PilotFamily.template A.P i).L*(dist p q/((A.R*A.q^J)*(A.q⁻¹)^j)) := by
  by_cases hj : j<J
  · have hr := GeometricMass.radius_reverse A.R A.q A.q_pos.ne' J j hj
    simp only [pilotParameter,ite_eq_left hj]
    cases i with
    | none =>
      change _≤1*(dist p q/((A.R*A.q^J)*(A.q⁻¹)^j))
      rw [one_mul,←hr]
      exact PartitionLevel.Input.long_lip _ _ _ _
    | some a =>
      change _≤8*(dist p q/((A.R*A.q^J)*(A.q⁻¹)^j))
      rw [←hr]
      exact PartitionLevel.Input.short_lip _ _ _ _ _
  · simp only [pilotParameter,ite_eq_right hj,sub_self,abs_zero]
    exact mul_nonneg (PilotFamily.template A.P i).L_nonneg
      (div_nonneg dist_nonneg (mul_nonneg (mul_nonneg A.R_pos.le (pow_nonneg A.q_pos.le _))
        (pow_nonneg (inv_nonneg.mpr A.q_pos.le) _)))

theorem pilot_measurable (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω v : Ω) (he : (D.filtration t).r ω v) (i : PilotFamily.Index k) (j : ℕ) :
    A.pilotParameter (N:=N) (J:=J) D hk t ω i j=A.pilotParameter (N:=N) (J:=J) D hk t v i j := by
  unfold pilotParameter
  split_ifs with hj
  · cases i with
    | none => exact A.long_measurable D hk ω v t (J-1-j) he
    | some a => exact A.short_measurable D hk ω v t (J-1-j) he a
  · rfl

theorem pilot_charge_nonneg (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) :
    0≤A.pilotCharge (N:=N) (J:=J) D hk t ω i j := by
  cases i with
  | none => exact PartitionLevel.Input.long_charge_nonneg _ _
  | some a => exact PartitionLevel.Input.short_charge_nonneg _ _ _

theorem pilot_payment (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) (i : PilotFamily.Index k) (j : ℕ) (hj : j<J) :
    A.pilotCharge (N:=N) (J:=J) D hk t ω i (J-1-j)≤
      PilotFamily.weight i*(
        value ((A.R*A.q^J)*(A.q⁻¹)^j) (PilotFamily.template A.P i).sigma (PilotFamily.template A.P i).R
          (HiddenFlow.current D (t+1) ω) (A.pilotParameter (N:=N) (J:=J) D hk t ω i j)-
        value ((A.R*A.q^J)*(A.q⁻¹)^j) (PilotFamily.template A.P i).sigma (PilotFamily.template A.P i).R
          (HiddenFlow.current D (t+1) ω) (A.pilotParameter (N:=N) (J:=J) D hk (t+1) ω i j)) := by
  rw [←GeometricMass.radius_reverse A.R A.q A.q_pos.ne' J j hj]
  simp only [pilotParameter,ite_eq_left hj]
  cases i with
  | none =>
    change _≤1*(_-_)
    rw [one_mul]
    exact PartitionLevel.Input.long_payment _ t _ (fun _ => rfl)
  | some a =>
    exact PartitionLevel.Input.short_payment ((A.input (N:=N) (J:=J) D hk ω).level (J-1-j)) a
      (A.lifetime_large D hk ω (J-1-j) a) t _ (fun _ => rfl)

theorem total_pilot_payment (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (t : ℕ) (ω : Ω) :
    A.totalPilotCharge (N:=N) (J:=J) D hk t ω≤
      potential (PilotFamily.template A.P) PilotFamily.weight (A.R*A.q^J) A.q⁻¹ J
        (HiddenFlow.current D (t+1) ω) (A.pilotParameter (N:=N) (J:=J) D hk t ω)-
      potential (PilotFamily.template A.P) PilotFamily.weight (A.R*A.q^J) A.q⁻¹ J
        (HiddenFlow.current D (t+1) ω) (A.pilotParameter (N:=N) (J:=J) D hk (t+1) ω) := by
  simp only [potential,totalPilotCharge,←sum_sub_distrib,←mul_sub,Finset.mul_sum]
  apply sum_le_sum
  intro i _
  rw [←GeometricMass.reverse_sum (fun j => A.pilotCharge (N:=N) (J:=J) D hk t ω i j) J]
  exact sum_le_sum fun j hj => A.pilot_payment D hk t ω i j (mem_range.mp hj)

end UniformKServer.ActualPartitions.Config

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelErrorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual stationary posterior errors are charged to the insertion masses.
The designated mover is not incorrectly treated as post-request mass. -/
namespace UniformKServer.PartitionLevel.Input
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

theorem heavy_bridge (I : Input X N) (n : Fin N) :
    I.data.heavy n↔TierPilot.heavy I.P I.r (I.μ n) (I.center n) := by
  simp only [data,TierPilot.heavy,mass_bridge]

local instance indexDecEqMass_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqMass_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
theorem error_mass_bound (I : Input X N) (n : Fin N) (s : X→ℝ)
    (hs : ∀ p, 0≤ s p) (hsμ : ∀ p, s p≤I.μ n p) :
    (∑ p, s p*I.data.errorIndicator I.P.gammaH n p)≤
      TierPilot.insertionMass I.P I.r (I.μ n) (I.center n) := by
  by_cases hh : I.data.heavy n
  · rw [TierPilot.insertionMass,ite_eq_left ((I.heavy_bridge n).mp hh),
      TierPilot.annulus_identity I.r I.P.gammaH 51200 I.r_pos.le (by linarith [I.P.gammaH_small])]
    apply sum_le_sum
    intro p _
    change s p*(if dist (I.center n) p≤22*I.r ∧ (¬I.data.heavy n ∨ I.P.gammaH*I.r<dist (I.center n) p) then 1 else 0)≤_
    by_cases h : dist (I.center n) p≤22*I.r ∧ I.P.gammaH*I.r<dist (I.center n) p
    · have hp : dist (I.center n) p≤51200*I.r := by nlinarith [I.r_pos]
      simp only [hh,not_true_eq_false,false_or,ite_eq_left h,ite_eq_left (show I.P.gammaH*I.r<dist (I.center n) p ∧ dist (I.center n) p≤51200*I.r from ⟨h.2,hp⟩),mul_one]
      exact hsμ p
    · simp only [hh,not_true_eq_false,false_or,ite_eq_right h,mul_zero]
      split_ifs <;> [exact (hs p).trans (hsμ p); exact le_rfl]
  · rw [TierPilot.insertionMass,ite_eq_right (fun h=>hh ((I.heavy_bridge n).mpr h))]
    apply sum_le_sum
    intro p _
    change s p*(if dist (I.center n) p≤22*I.r ∧ (¬I.data.heavy n ∨ I.P.gammaH*I.r<dist (I.center n) p) then 1 else 0)≤_
    by_cases h : dist (I.center n) p≤22*I.r
    · have hp : dist (I.center n) p≤20480000*I.r := by nlinarith [I.r_pos]
      simp only [hh,not_false_eq_true,true_or,and_true,ite_eq_left h,mul_one,ite_eq_left hp]
      exact hsμ p
    · simp only [hh,not_false_eq_true,true_or,and_true,ite_eq_right h,mul_zero]
      split_ifs <;> [exact (hs p).trans (hsμ p); exact le_rfl]

theorem stationary_tier_charge (I : Input X N) (n : Fin N) (i : Fin I.height)
    (s : X→ℝ) (hs : ∀ p, 0≤ s p) (hsμ : ∀ p, s p≤I.μ n p) :
    (∑ p, s p*I.data.stationaryBudget I.P.gammaH n i p)≤98*I.shortCharge i n.val := by
  unfold LevelMap.Data.stationaryBudget shortCharge
  rw [dite_eq_left n.isLt]
  change (∑ p, s p*(if I.data.tierTrigger n i then _ else _))≤98*(if I.data.tierTrigger n i then _ else _)
  by_cases ht : I.data.tierTrigger n i
  · simp only [ite_eq_left ht]
    change (∑ p, s p*(98*I.r/(I.data.K i:ℝ)*I.data.errorIndicator I.P.gammaH n p))≤98*(I.r*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n)/(I.data.K i:ℝ))
    have he : (∑ p, s p*(98*I.r/(I.data.K i:ℝ)*I.data.errorIndicator I.P.gammaH n p))=
        (98*I.r/(I.data.K i:ℝ))*(∑ p, s p*I.data.errorIndicator I.P.gammaH n p) := by
      rw [mul_sum]; apply sum_congr rfl; intro p _; ring
    rw [he]
    have h := mul_le_mul_of_nonneg_left (I.error_mass_bound n s hs hsμ)
      (show 0≤98*I.r/(I.data.K i:ℝ) from div_nonneg (mul_nonneg (by norm_num) I.r_pos.le) (Nat.cast_nonneg _))
    exact h.trans_eq (by ring)
  · simp only [ite_eq_right ht,mul_zero,sum_const_zero,le_refl]

theorem stationary_heavy_charge (I : Input X N) (n : Fin N)
    (s : X→ℝ) (hs : ∀ p, 0≤ s p) (hsμ : ∀ p, s p≤I.μ n p) :
    (∑ p, s p*I.data.heavyStationaryBudget n p)≤I.longCharge n.val := by
  unfold LevelMap.Data.heavyStationaryBudget longCharge
  rw [dite_eq_left n.isLt]
  change (∑ p, s p*(if I.data.heavyTrigger n ∧ 3*I.r<dist (I.center n) p ∧ dist (I.center n) p≤120*I.r then 2*I.r else 0))≤
    (if I.data.heavyTrigger n then 127*I.r*HeavyPilot.annulusMass I.r (I.μ n) (I.center n) else 0)
  by_cases ht : I.data.heavyTrigger n
  · simp only [ht,true_and,ite_true, if_true,HeavyPilot.annulusMass,mul_sum]
    apply sum_le_sum
    intro p _
    rw [dist_comm p]
    split_ifs with hp
    · have hm := mul_le_mul_of_nonneg_left (hsμ p) I.r_pos.le
      have hn := mul_nonneg I.r_pos.le ((hs p).trans (hsμ p))
      nlinarith
    · simp only [mul_zero,le_refl]
  · simp only [ht,false_and,ite_false, if_false,mul_zero,sum_const_zero,le_refl]

end UniformKServer.PartitionLevel.Input

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelMoverBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Designated-mover error: nonheavy insertions are financed by positive
post-request mass; heavy insertions are a geometric small-scale error. -/
namespace UniformKServer.PartitionLevel.Input
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

local instance indexDecEqMover_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqMover_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def smallError (I : Input X N) (n : Fin N) (p : X) : ℝ :=
  if I.P.gammaH*I.r<dist (I.center n) p then I.r else 0

def unqualifiedMotion (I : Input X N) (n : Fin N) (i : Fin I.height) (p : X) : ℝ :=
  if I.data.qualify i n then 0 else (4+2*Real.log (1+(I.data.K i:ℝ)^2))*dist (I.center n) p

theorem smallError_nonneg (I : Input X N) (n : Fin N) (p : X) : 0≤I.smallError n p := by
  unfold smallError; split_ifs <;> [exact I.r_pos.le; exact le_rfl]

theorem unqualified_nonneg (I : Input X N) (n : Fin N) (i : Fin I.height) (p : X) :
    0≤I.unqualifiedMotion n i p := by
  unfold unqualifiedMotion
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by linarith [Real.log_nonneg (show (1:ℝ)≤1+(I.data.K i:ℝ)^2 by linarith [sq_nonneg (I.data.K i:ℝ)])]) dist_nonneg

theorem insertion_mass_one (I : Input X N) (n : Fin N) (hh : ¬I.data.heavy n) :
    1≤TierPilot.insertionMass I.P I.r (I.μ n) (I.center n) := by
  rw [TierPilot.insertionMass,ite_eq_right (fun h=>hh ((I.heavy_bridge n).mpr h)),mass_bridge]
  exact (I.served n).trans (GeometricMass.mass_center _ (I.μ_nonneg n) _ _ (mul_nonneg (by norm_num) I.r_pos.le))

theorem shortCharge_at (I : Input X N) (n : Fin N) (i : Fin I.height) :
    I.shortCharge i n.val=if I.data.tierTrigger n i then
      I.r*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n)/(I.data.K i:ℝ) else 0 := by
  unfold shortCharge
  rw [dite_eq_left n.isLt]
  rfl

theorem mover_budget_bound (I : Input X N) (n : Fin N) (i : Fin I.height) (p : X) :
    I.data.moverBudget I.P.gammaH n i p≤49*I.shortCharge i n.val+
      (49/(I.data.K i:ℝ))*I.smallError n p+I.unqualifiedMotion n i p := by
  have hr := I.r_pos
  have hK : (0:ℝ)<I.data.K i := by exact_mod_cast (show 0<I.data.K i by have := I.data.two i; omega)
  have hsmall := mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤49) hK.le) (I.smallError_nonneg n p)
  have hu := I.unqualified_nonneg n i p
  rw [shortCharge_at]
  unfold LevelMap.Data.moverBudget
  by_cases ht : I.data.tierTrigger n i
  · simp only [ite_eq_left ht]
    change 49*I.r/(I.data.K i:ℝ)*I.data.errorIndicator I.P.gammaH n p≤_
    by_cases hh : I.data.heavy n
    · have herr : 49*I.r/(I.data.K i:ℝ)*I.data.errorIndicator I.P.gammaH n p≤
          (49/(I.data.K i:ℝ))*I.smallError n p := by
        unfold LevelMap.Data.errorIndicator smallError
        change 49*I.r/(I.data.K i:ℝ)*(if dist (I.center n) p≤22*I.r ∧ (¬I.data.heavy n ∨ I.P.gammaH*I.r<dist (I.center n) p) then 1 else 0)≤_
        simp only [hh,not_true_eq_false,false_or]
        by_cases hp : I.P.gammaH*I.r<dist (I.center n) p
        · rw [ite_eq_left hp]
          by_cases hn : dist (I.center n) p≤22*I.r
          · rw [ite_eq_left ⟨hn,hp⟩,mul_one]
            exact le_of_eq (by ring)
          · rw [ite_eq_right (fun h=>hn h.1),mul_zero]
            exact mul_nonneg (div_nonneg (by norm_num) hK.le) hr.le
        · have hnot : ¬(dist (I.center n) p≤22*I.r ∧ I.P.gammaH*I.r<dist (I.center n) p) := fun h=>hp h.2
          rw [ite_eq_right hnot,ite_eq_right hp,mul_zero,mul_zero]
      have hc := TierPilot.insertionMass_bounds I.P I.r I.r_pos.le (I.μ n) (I.μ_nonneg n) (I.center n)
      have hcn : 0≤49*(I.r*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n)/(I.data.K i:ℝ)) :=
        mul_nonneg (by norm_num) (div_nonneg (mul_nonneg hr.le hc.1) hK.le)
      linarith
    · have he : I.data.errorIndicator I.P.gammaH n p≤1 := by
        unfold LevelMap.Data.errorIndicator; split_ifs <;> norm_num
      have hm := mul_le_mul_of_nonneg_left (I.insertion_mass_one n hh)
        (show 0≤49*I.r/(I.data.K i:ℝ) by positivity)
      have he' := mul_le_mul_of_nonneg_left he (show 0≤49*I.r/(I.data.K i:ℝ) by positivity)
      have heq : 49*(I.r*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n)/(I.data.K i:ℝ))=
          (49*I.r/(I.data.K i:ℝ))*TierPilot.insertionMass I.P I.r (I.μ n) (I.center n) := by ring
      rw [heq]
      linarith
  · simp only [ite_eq_right ht,mul_zero,zero_add]
    change I.unqualifiedMotion n i p≤49/(I.data.K i:ℝ)*I.smallError n p+I.unqualifiedMotion n i p
    linarith

theorem unqualified_sum (I : Input X N) (n : Fin N) (p : X) :
    (I.order.map fun i=>I.unqualifiedMotion n i p).sum≤(8*I.C+24)*I.localLog n*dist (I.center n) p := by
  have hcoef : 0≤4*I.C+12 := by linarith [I.C_one]
  have hlocal := DyadicTiers.unqualified_sum (I.localLog n) (I.localLog_nonneg n) I.height
  have hp (i : Fin I.height) : I.unqualifiedMotion n i p≤
      (4*I.C+12)*dist (I.center n) p*(if DyadicTiers.value i.val<I.localLog n then DyadicTiers.value i.val else 0) := by
    unfold unqualifiedMotion
    by_cases hq : I.data.qualify i n
    · rw [ite_eq_left hq,ite_eq_right (not_lt.mpr ((I.qualification n i).mp hq)),mul_zero]
    · have hlt : DyadicTiers.value i.val<I.localLog n := lt_of_not_ge (fun h=>hq ((I.qualification n i).mpr h))
      rw [ite_eq_right hq,ite_eq_left hlt]
      have hlog := TierParameters.radius_parameter I.C (DyadicTiers.value i.val) I.C_one (DyadicTiers.one_le_value i.val)
      change Real.log (1+(I.data.K i:ℝ)^2)≤_ at hlog
      have h := mul_le_mul_of_nonneg_right (show 4+2*Real.log (1+(I.data.K i:ℝ)^2)≤(4*I.C+12)*DyadicTiers.value i.val by nlinarith [DyadicTiers.one_le_value i.val]) (dist_nonneg (x:=I.center n) (y:=p))
      nlinarith only [h]
  rw [order,List.map_ofFn,List.sum_ofFn]
  have hsum := sum_le_sum (fun i (_ : i∈(univ : Finset (Fin I.height)))=>hp i)
  rw [←mul_sum] at hsum
  have hconvert : (∑ i : Fin I.height,if DyadicTiers.value i.val<I.localLog n then DyadicTiers.value i.val else 0)=
      ∑ i∈range I.height,if DyadicTiers.value i<I.localLog n then DyadicTiers.value i else 0 := Fin.sum_univ_eq_sum_range (fun j=>if DyadicTiers.value j<I.localLog n then DyadicTiers.value j else 0) I.height
  rw [hconvert] at hsum
  have h := mul_le_mul_of_nonneg_left hlocal (mul_nonneg hcoef (dist_nonneg (x:=I.center n) (y:=p)))
  simp only [Function.comp_apply,id_eq]
  nlinarith only [hsum,h]

theorem mover_tiers (I : Input X N) (n : Fin N) (p : X) :
    (I.order.map fun i=>I.data.moverBudget I.P.gammaH n i p).sum≤
      49*(I.order.map fun i=>I.shortCharge i n.val).sum+98*I.smallError n p+
        (8*I.C+24)*I.localLog n*dist (I.center n) p := by
  have hsum : (I.order.map fun i=>I.data.moverBudget I.P.gammaH n i p).sum≤
      (I.order.map fun i=>49*I.shortCharge i n.val+(49/(I.data.K i:ℝ))*I.smallError n p+I.unqualifiedMotion n i p).sum :=
    List.sum_le_sum (fun i _=>I.mover_budget_bound n i p)
  have hi : (I.order.map fun i=>1/(I.data.K i:ℝ)).sum≤2 := by
    rw [order,List.map_ofFn,List.sum_ofFn]
    change (∑ i : Fin I.height,1/(TierParameters.cutoff I.C (DyadicTiers.value i.val):ℝ))≤2
    change (∑ i : Fin I.height,(fun j=>1/(TierParameters.cutoff I.C (DyadicTiers.value j):ℝ)) i.val)≤2
    rw [Fin.sum_univ_eq_sum_range (fun j=>1/(TierParameters.cutoff I.C (DyadicTiers.value j):ℝ)) I.height]
    exact DyadicTiers.inverse_sum I.C I.C_one I.height
  have hid := mul_le_mul_of_nonneg_right hi (mul_nonneg (by norm_num : (0:ℝ)≤49) (I.smallError_nonneg n p))
  have hu := I.unqualified_sum n p
  have he : (I.order.map fun i=>49*I.shortCharge i n.val+(49/(I.data.K i:ℝ))*I.smallError n p+I.unqualifiedMotion n i p).sum=
      49*(I.order.map fun i=>I.shortCharge i n.val).sum+
      (I.order.map fun i=>1/(I.data.K i:ℝ)).sum*(49*I.smallError n p)+(I.order.map fun i=>I.unqualifiedMotion n i p).sum := by
    simp only [order,List.map_ofFn,List.sum_ofFn,Function.comp_apply,id_eq,mul_sum,sum_mul,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [he] at hsum
  linarith

end UniformKServer.PartitionLevel.Input

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LevelAllowances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual insertion charges and local logarithmic motion pay the level ledger. -/
namespace UniformKServer.PartitionLevel.Input
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}

local instance ixAllow_r5f289f_1 : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance pairAllow_r5f289f_1 : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
def nonheavyMotion (I : Input X N) (n : Fin N) (p : X) : ℝ :=
  if I.data.heavy n then 0 else dist (I.center n) p

theorem heavy_mover_bound (I : Input X N) (n : Fin N) (p : X) :
    I.data.heavyMoverBudget n p≤I.smallError n p+I.nonheavyMotion n p := by
  unfold LevelMap.Data.heavyMoverBudget nonheavyMotion
  apply add_le_add _ (le_refl (if I.data.heavy n then (0:ℝ) else dist (I.center n) p))
  change (if I.data.heavyTrigger n ∧ 3*I.r<dist (I.center n) p then I.r else 0)≤_
  split_ifs with ht
  · have gamma_bound : I.P.gammaH ≤ 3 := I.P.gammaH_small.trans (by norm_num)
    have hp : I.P.gammaH*I.r<dist (I.center n) p :=
      (mul_le_mul_of_nonneg_right gamma_bound I.r_pos.le).trans_lt ht.2
    rw [smallError,ite_eq_left hp]
  · exact I.smallError_nonneg n p

theorem stationary_allowance (I : Input X N) (n : Fin N) (s : X→ℝ)
    (hs : ∀ p, 0≤ s p) (hsμ : ∀ p, s p≤I.μ n p) :
    (∑ p,s p*I.data.stationaryAllowance I.order I.P.gammaH n p)≤98*I.charges n := by
  have ht (is : List (Fin I.height)) :
      (∑ p,s p*(is.map fun i=>I.data.stationaryBudget I.P.gammaH n i p).sum)≤
        98*(is.map fun i=>I.shortCharge i n.val).sum := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons,List.sum_cons,mul_add,sum_add_distrib]
      exact add_le_add (I.stationary_tier_charge n i s hs hsμ) ih
  unfold LevelMap.Data.stationaryAllowance charges
  simp only [mul_add,sum_add_distrib]
  have hh := I.stationary_heavy_charge n s hs hsμ
  have hn := I.long_charge_nonneg n.val
  have h := ht I.order
  linarith

theorem mover_allowance (I : Input X N) (n : Fin N) (p : X) :
    I.data.moverAllowance I.order I.P.gammaH n p≤49*I.charges n+
      99*I.smallError n p+I.nonheavyMotion n p+(8*I.C+24)*I.localLog n*dist (I.center n) p := by
  have hh := I.heavy_mover_bound n p
  have ht := I.mover_tiers n p
  have hn := I.long_charge_nonneg n.val
  unfold LevelMap.Data.moverAllowance charges
  linarith

end UniformKServer.PartitionLevel.Input

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ScaleAllowances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Height-free sum of the designated-mover auxiliary errors. -/
namespace UniformKServer.PartitionScales.Input
open Finset GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N J : ℕ}

def editCoefficient (I : Input X N J) : ℝ :=
  198/I.P.gammaH+1/Real.log (1+I.P.deltaH)+(8*I.C+24)

theorem small_sum (I : Input X N J) (n : Fin N) (p : X) :
    (∑ j∈range J,(I.level j).smallError n p)≤(2/I.P.gammaH)*dist (I.center n) p := by
  let d := dist (I.center n) p
  have hd : 0≤ d := dist_nonneg
  have hγ := I.P.gammaH_pos
  have hc := SmallScales.small (I.R*I.q) I.q (d/I.P.gammaH) (mul_pos I.R_pos I.q_pos).le I.q_pos.le
    (by linarith [I.q_small]) (div_nonneg hd hγ.le) J
  have he (j : ℕ) : (I.level j).r=(I.R*I.q)*I.q^j := by dsimp [level,radius]; rw [pow_succ]; ring
  have hbound (j : ℕ) : (I.level j).smallError n p≤
      (if (I.R*I.q)*I.q^j≤d/I.P.gammaH then (I.R*I.q)*I.q^j else 0) := by
    unfold PartitionLevel.Input.smallError
    change (if I.P.gammaH*(I.level j).r<d then (I.level j).r else 0)≤_
    rw [he]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso
      apply h2
      exact (le_div_iff₀ hγ).mpr (by linarith only [h1])
    · exact (mul_nonneg (mul_pos I.R_pos I.q_pos).le (pow_nonneg I.q_pos.le _))
    · exact le_rfl
  calc
    _≤∑ j∈range J,if (I.R*I.q)*I.q^j≤d/I.P.gammaH then (I.R*I.q)*I.q^j else 0 := sum_le_sum (fun j _=>hbound j)
    _≤(d/I.P.gammaH)/(1-I.q) := hc
    _≤(2/I.P.gammaH)*d := by
      apply (div_le_iff₀ (by linarith [I.q_small] : 0<1-I.q)).mpr
      have hz : 0≤d/I.P.gammaH := div_nonneg hd hγ.le
      have heq : (2/I.P.gammaH)*d*(1-I.q)=2*(d/I.P.gammaH)*(1-I.q) := by ring
      rw [heq]
      nlinarith [I.q_small]

theorem nonheavy_motion_sum (I : Input X N J) (n : Fin N) (p : X) :
    (∑ j∈range J,(I.level j).nonheavyMotion n p)≤
      (Real.log I.k/Real.log (1+I.P.deltaH))*dist (I.center n) p := by
  have he (j : ℕ) : (I.level j).nonheavyMotion n p=
      (if I.isNonheavy n j then (1:ℝ) else 0)*dist (I.center n) p := by
    unfold PartitionLevel.Input.nonheavyMotion
    by_cases hh : (I.level j).data.heavy n
    · simp only [hh,ite_true, if_true,ite_eq_right (fun hn=>((I.not_heavy n j).mp hn) hh),zero_mul]
    · rw [ite_eq_right hh,ite_eq_left ((I.not_heavy n j).mpr hh),one_mul]
      rfl
  simp_rw [he]
  rw [←sum_mul,←sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  exact mul_le_mul_of_nonneg_right (I.nonheavy_count n) dist_nonneg

theorem mover_allowance_sum (I : Input X N J) (n : Fin N) (p : X) :
    (∑ j∈range J,(I.level j).data.moverAllowance (I.level j).order I.P.gammaH n p)≤
      49*(∑ j∈range J,(I.level j).charges n)+I.editCoefficient*(1+Real.log I.k)*dist (I.center n) p := by
  have hb := sum_le_sum (s:=range J) (fun j _=>(I.level j).mover_allowance n p)
  have he : (∑ j∈range J,(49*(I.level j).charges n+99*(I.level j).smallError n p+
      (I.level j).nonheavyMotion n p+(8*(I.level j).C+24)*(I.level j).localLog n*dist ((I.level j).center n) p))=
      49*(∑ j∈range J,(I.level j).charges n)+99*(∑ j∈range J,(I.level j).smallError n p)+
      (∑ j∈range J,(I.level j).nonheavyMotion n p)+(8*I.C+24)*(∑ j∈range J,(I.level j).localLog n)*dist (I.center n) p := by
    simp only [sum_add_distrib,←mul_sum,←sum_mul,level]
  rw [he] at hb
  have hs := mul_le_mul_of_nonneg_left (I.small_sum n p) (by norm_num : (0:ℝ)≤99)
  have hn := I.nonheavy_motion_sum n p
  have hl := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (I.log_sum n)
    (show 0≤8*I.C+24 by linarith [I.C_one])) (dist_nonneg (x:=I.center n) (y:=p))
  have hlog : 0≤Real.log I.k := Real.log_nonneg (by exact_mod_cast (show 1≤I.k by have := I.two; omega))
  have hdelta : 0<Real.log (1+I.P.deltaH) := Real.log_pos (by linarith [I.P.deltaH_pos])
  have hγ := I.P.gammaH_pos
  have hd : 0≤dist (I.center n) p := dist_nonneg
  have hC : 0≤8*I.C+24 := by linarith [I.C_one]
  have hec : (198/I.P.gammaH+1/Real.log (1+I.P.deltaH)+(8*I.C+24))*(1+Real.log I.k)*dist (I.center n) p-
      (99*((2/I.P.gammaH)*dist (I.center n) p)+(Real.log I.k/Real.log (1+I.P.deltaH))*dist (I.center n) p+
      (8*I.C+24)*Real.log I.k*dist (I.center n) p)=
      ((198/I.P.gammaH)*Real.log I.k+1/Real.log (1+I.P.deltaH)+(8*I.C+24))*dist (I.center n) p := by ring
  have hp : 0≤((198/I.P.gammaH)*Real.log I.k+1/Real.log (1+I.P.deltaH)+(8*I.C+24))*dist (I.center n) p := by positivity
  change (∑ j∈range J,(I.level j).data.moverAllowance (I.level j).order I.P.gammaH n p)≤_ at hb
  unfold editCoefficient
  linarith only [hb,hs,hn,hl,hec,hp]

end UniformKServer.PartitionScales.Input

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ActualEditCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Full expected key-edit charge, including the actual posterior unit mover. -/
namespace UniformKServer.ActualPartitions.Config
open Finset PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem level_mass_step (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) (j : ℕ) :
    let I := ((A.input (N:=N) (J:=J) D hk ω).level j)
    (∑ p,HiddenFlow.filtered D n.val ω p*I.data.editCost n I.order p)+
      linearPotential (HiddenFlow.current D (n.val+1) ω) (I.data.auxiliary I.order (n.val+1))-
      linearPotential (HiddenFlow.filtered D n.val ω) (I.data.auxiliary I.order n.val)≤
    98*I.charges n+∑ p,HiddenFlow.mover D n.val ω p*I.data.moverAllowance I.order A.P.gammaH n p := by
  let F := HiddenFlow.flow D
  let I := ((A.input (N:=N) (J:=J) D hk ω).level j)
  let s : X→ℝ := fun p=>F.filtered n.val ω p-F.mover n.val ω p
  have hs (p : X) : 0≤ s p := sub_nonneg.mpr (F.mover_le n.val ω p)
  have hs' (p : X) : s p≤I.μ n p := by
    have he := F.update n.val ω p
    change I.μ n p= s p + (if p=I.center n then 1 else 0) at he
    rw [he]
    split_ifs <;> linarith
  have h := I.data.mass_ledger n I.order A.P.gammaH (by linarith [A.P.gammaH_small])
    s (F.mover n.val ω) hs (F.mover_nonneg n.val ω) (F.mover_total n.val ω)
  have hstat := I.stationary_allowance n s hs hs'
  have hdecomp : (fun p=>s p+F.mover n.val ω p)=F.filtered n.val ω := by funext p; dsimp [s] <;> ring
  have hpost (b : X→ℝ) : (∑ p,s p*b p)+b (I.data.center n)=linearPotential (F.post (n.val+1) ω) b := by
    unfold linearPotential
    simp only [F.update,add_mul,sum_add_distrib,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,ite_true, if_true]
    rfl
  simp only [congrFun hdecomp] at h
  rw [hpost] at h
  dsimp only [linearPotential] at h ⊢
  change _≤98*I.charges n+_
  change _≤98*I.charges n at hstat
  have hstat' : (∑ p,s p*I.data.stationaryAllowance I.order A.P.gammaH n p)≤98*I.charges n := hstat
  exact h.trans (add_le_add hstat' le_rfl)

theorem key_mass_step (A : Config X) (D : HiddenFlow.Data X Ω k) (hk : 2≤k)
    (ω : Ω) (n : Fin N) :
    A.keyEditCost (N:=N) (J:=J) D hk n.val ω+
      linearPotential (HiddenFlow.current D (n.val+1) ω) (A.auxiliary (N:=N) (J:=J) D hk (n.val+1) ω)-
      linearPotential (HiddenFlow.filtered D n.val ω) (A.auxiliary (N:=N) (J:=J) D hk n.val ω)≤
    147*A.totalPilotCharge (N:=N) (J:=J) D hk n.val ω+
      A.editRate*(1+Real.log k)*moverCost (HiddenFlow.flow D) n.val ω := by
  let I := A.input (N:=N) (J:=J) D hk ω
  let F := HiddenFlow.flow D
  have hm := sum_le_sum (fun p (_ : p∈(univ : Finset X))=>
    mul_le_mul_of_nonneg_left (I.mover_allowance_sum n p) (F.mover_nonneg n.val ω p))
  have hme : (∑ p,F.mover n.val ω p*(49*(∑ j∈range J,(I.level j).charges n)+
       I.editCoefficient*(1+Real.log I.k)*dist (I.center n) p))=
      49*(∑ j∈range J,(I.level j).charges n)+A.editRate*(1+Real.log k)*moverCost F n.val ω := by
    simp only [mul_add,sum_add_distrib,←sum_mul,F.mover_total,one_mul]
    congr 1
    unfold moverCost
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    change F.mover n.val ω p*((A.editRate*1+A.editRate*Real.log k)*dist (I.center n) p)=
      (A.editRate*1+A.editRate*Real.log k)*(F.mover n.val ω p*dist (I.center n) p)
    ring
  rw [hme] at hm
  have h := sum_le_sum (s:=range J) (fun j _=>A.level_mass_step (J:=J) D hk ω n j)
  change (∑ j∈range J,((∑ p,F.filtered n.val ω p*(I.level j).data.editCost n (I.level j).order p)+
    linearPotential (F.post (n.val+1) ω) ((I.level j).data.auxiliary (I.level j).order (n.val+1))-
    linearPotential (F.filtered n.val ω) ((I.level j).data.auxiliary (I.level j).order n.val)))≤
    ∑ j∈range J,(98*(I.level j).charges n+∑ p,F.mover n.val ω p*
      (I.level j).data.moverAllowance (I.level j).order A.P.gammaH n p) at h
  rw [sum_sub_distrib,sum_add_distrib,sum_add_distrib,←mul_sum] at h
  have hlin (μ : X→ℝ) (t : ℕ) :
      (∑ j∈range J,linearPotential μ ((I.level j).data.auxiliary (I.level j).order t))=
      linearPotential μ (A.auxiliary (N:=N) (J:=J) D hk t ω) := by
    unfold linearPotential auxiliary
    rw [sum_comm]
    simp only [mul_sum]
    rfl
  rw [hlin,hlin] at h
  have hm2 : (∑ j∈range J,∑ p,F.mover n.val ω p*(I.level j).data.moverAllowance (I.level j).order A.P.gammaH n p)=
      ∑ p,F.mover n.val ω p*∑ j∈range J,(I.level j).data.moverAllowance (I.level j).order A.P.gammaH n p := by
    rw [sum_comm]
    simp only [mul_sum]
  rw [hm2] at h
  change (∑ p,F.mover n.val ω p*∑ j∈range J,(I.level j).data.moverAllowance (I.level j).order A.P.gammaH n p)≤_ at hm
  have hc : (∑ j∈range J,(I.level j).charges n)=A.totalPilotCharge (N:=N) (J:=J) D hk n.val ω := A.charges_identity D hk ω n
  rw [hc] at h hm
  rw [keyEditCost,dite_eq_left n.isLt]
  change (∑ j∈range J,∑ p,F.filtered n.val ω p*(I.level j).data.editCost n (I.level j).order p)+
    linearPotential (F.post (n.val+1) ω) (A.auxiliary (N:=N) (J:=J) D hk (n.val+1) ω)-
    linearPotential (F.filtered n.val ω) (A.auxiliary (N:=N) (J:=J) D hk n.val ω)≤_
  linarith only [h,hm]

end UniformKServer.ActualPartitions.Config

end

end OAI
end


