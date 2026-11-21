-- Prove2me | Definitions.Def_SourceProof_8f9f280f81d8e75768b9aa58
-- name    : SourceProof_8f9f280f81d8e75768b9aa58
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:34:20.512018+00:00
-- url     : https://prove2.me/theorems/627d9ac6-be66-4ecd-afd0-439746991757
-- title:
--   LevyStochCalc source module: SourceProof_8f9f280f81d8e75768b9aa58
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_of_mean_zero` comes from the `LevyStochCalc.Driver.JointRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint range of a Lévy driver

The `L²` ranges of the `d` coordinate Itô integrals and of the compensated integral are pairwise
orthogonal and each closed, so their sum is closed and a square-integrable weight splits into a
part in the sum and a part orthogonal to it. The orthogonal part is a weight of mean zero,
measurable before the horizon, orthogonal to both ranges; when only the zero weight is such, the
weight is a joint integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated

section Range

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
  (hℱN : Poisson.IsPoissonFiltration D.N ℱ)


theorem _root_.Prove2MeSourceProof.h_8f9f280f81d8e75768b9aa58 (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T)
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ T] r P → (∫ ω, r ω ∂P = 0) →
      (∀ (i : Fin d) (G : HorizonIntegrand P ℱ T),
        ∫ ω, r ω * G.integral (D.W.W i) (hcoord i) ω ∂P = 0) →
      (∀ K : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, r ω * K.integral D.N hℱN ω ∂P = 0) →
      r =ᵐ[P] 0)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) (K : MarkedHorizonIntegrand P ν ℱ T),
      Z =ᵐ[P] jointIntegral hcoord hℱN G K := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set V : Option (Fin d) → Submodule ℝ (Lp ℝ 2 P) := LevyStochCalc.Driver.LevyDriver.jointRange hcoord hℱN hT with hVdef
  haveI hcl : IsClosed ((⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    LevyStochCalc.Driver.LevyDriver.isClosed_iSup_jointRange hcoord hℱN 𝒲 hT
  haveI : CompleteSpace (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) := hcl.completeSpace_coe
  haveI : ∀ i : Option (Fin d), CompleteSpace (V i) := by
    intro i
    match i with
    | some i => exact (_root_.Prove2MeSourceProof.h_940e1d5a45abf4f7e61b42fb (D.W.W i) (hcoord i) hT).completeSpace_coe
    | none => exact (_root_.Prove2MeSourceProof.h_5b889f5df8fcc6a23c71c429 D.N hℱN hT).completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)).exists_add_mem_mem_orthogonal (hZ2.toLp Z)
  have hproj : ∑ i, (V i).starProjection y = y :=
    (LevyStochCalc.Driver.LevyDriver.orthogonalFamily_jointRange hcoord hℱN 𝒲 hT).sum_projection_of_mem_iSup y hy
  have hcompB : ∀ i : Fin d, ∃ G : LevyStochCalc.Brownian.Ito.HorizonIntegrand P ℱ T,
      (((V (some i)).starProjection y : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] G.integral (D.W.W i) (hcoord i) :=
    fun i => (V (some i)).starProjection_apply_mem y
  choose G hG using hcompB
  obtain ⟨K, hK⟩ : ∃ K : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T,
      (((V none).starProjection y : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] K.integral D.N hℱN :=
    (V none).starProjection_apply_mem y
  have hyfun : (y : Ω → ℝ) =ᵐ[P] LevyStochCalc.Driver.LevyDriver.jointIntegral hcoord hℱN G K := by
    have hsumfun : ((∑ i, (V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] fun ω => ∑ i : Option (Fin d),
          (((V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ) ω :=
      MeasureTheory.Lp.coeFn_fun_finsetSum _ _
    rw [← hproj]
    filter_upwards [hsumfun, hK, Filter.eventually_all.2 (fun i : Fin d => hG i)]
      with ω e1 e2 e3
    rw [e1, Fintype.sum_option, e2, LevyStochCalc.Driver.LevyDriver.jointIntegral, LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.vectorIntegral, add_comm]
    exact congrArg (fun x => x + K.integral D.N hℱN ω) (Finset.sum_congr rfl fun i _ => e3 i)
  have hsplit : Z =ᵐ[P] fun ω => LevyStochCalc.Driver.LevyDriver.jointIntegral hcoord hℱN G K ω + (z : Ω → ℝ) ω := by
    filter_upwards [hZ2.coeFn_toLp, Lp.coeFn_add y z, hyfun] with ω e1 e2 e3
    rw [← e1, hyz, e2, Pi.add_apply, e3]
  have hzmem : MemLp (z : Ω → ℝ) 2 P := Lp.memLp z
  have hzmeas : AEStronglyMeasurable[ℱ T] (z : Ω → ℝ) P := by
    have hd : (z : Ω → ℝ) =ᵐ[P] fun ω => Z ω - LevyStochCalc.Driver.LevyDriver.jointIntegral hcoord hℱN G K ω := by
      filter_upwards [hsplit] with ω e1
      rw [e1]; ring
    exact (hZm.sub (LevyStochCalc.Driver.LevyDriver.aestronglyMeasurable_jointIntegral hcoord hℱN G K)).congr hd.symm
  have hyint : Integrable (LevyStochCalc.Driver.LevyDriver.jointIntegral hcoord hℱN G K) P :=
    (LevyStochCalc.Driver.LevyDriver.memLp_jointIntegral hcoord hℱN G K).integrable (by norm_num)
  have hzint : Integrable (z : Ω → ℝ) P := hzmem.integrable (by norm_num)
  have hzmean : ∫ ω, (z : Ω → ℝ) ω ∂P = 0 := by
    have hone := integral_congr_ae (μ := P) hsplit
    rw [integral_add hyint hzint, LevyStochCalc.Driver.LevyDriver.integral_jointIntegral_eq_zero hcoord hℱN hT.le G K,
      zero_add] at hone
    rw [← hone, hZ0]
  have hzperpB : ∀ (i : Fin d) (L : LevyStochCalc.Brownian.Ito.HorizonIntegrand P ℱ T),
      ∫ ω, (z : Ω → ℝ) ω * L.integral (D.W.W i) (hcoord i) ω ∂P = 0 := by
    intro i L
    have hmem : (LevyStochCalc.Brownian.Ito.HorizonIntegrand.memLp (D.W.W i) (hcoord i) L).toLp
        (L.integral (D.W.W i) (hcoord i)) ∈ (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) :=
      Submodule.mem_iSup_of_mem (some i) ⟨L, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp
      (LevyStochCalc.Brownian.Ito.HorizonIntegrand.memLp (D.W.W i) (hcoord i) L)] with ω e1
    rw [RCLike.inner_apply, e1]
    simp
  have hzperpN : ∀ L : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, (z : Ω → ℝ) ω * L.integral D.N hℱN ω ∂P = 0 := by
    intro L
    have hmem : (LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp D.N hℱN L).toLp (L.integral D.N hℱN)
        ∈ (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) :=
      Submodule.mem_iSup_of_mem none ⟨L, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp D.N hℱN L)] with ω e1
    rw [RCLike.inner_apply, e1]
    simp
  have hzzero := hsep (z : Ω → ℝ) hzmem hzmeas hzmean hzperpB hzperpN
  refine ⟨G, K, ?_⟩
  filter_upwards [hsplit, hzzero] with ω e1 e2
  rw [e1, e2]
  simp
end Range

end LevyDriver

end LevyStochCalc.Driver


