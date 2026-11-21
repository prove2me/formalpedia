-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointRange_F000
-- name    : LevyStochCalc_Driver_JointRange_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:28:34.944861+00:00
-- url     : https://prove2.me/theorems/a5d413d0-3137-4711-a1c4-eb6f573c2960
-- title:
--   Source declarations: LevyStochCalc.Driver.JointRange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointRange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPMultidimRange_F000
import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
import Definitions.Def_SourceProof_194396c8b70b364460393af6
import Definitions.Def_SourceProof_454d3940367616169eae66cb
import Definitions.Def_SourceProof_5b889f5df8fcc6a23c71c429
import Definitions.Def_SourceProof_da55a4195e0b45ce7b0016e9

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

/-- The `L²` ranges of the coordinate Itô integrals and of the compensated integral. -/
noncomputable def jointRange (hT : 0 < T) : Option (Fin d) → Submodule ℝ (Lp ℝ 2 P)
  | none => compensatedRange D.N hℱN hT
  | some i => itoRange (D.W.W i) (hcoord i) hT
/-- An Itô integral against a coordinate is orthogonal to a compensated integral in `L²`. -/
theorem inner_itoRange_compensatedRange (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T)
    (i : Fin d) (u : itoRange (D.W.W i) (hcoord i) hT) (v : compensatedRange D.N hℱN hT) :
    (inner ℝ (u : Lp ℝ 2 P) (v : Lp ℝ 2 P) : ℝ) = 0 := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  obtain ⟨G, hG⟩ := u.2
  obtain ⟨K, hK⟩ := v.2
  have hcross : ∫ ω, G.integral (D.W.W i) (hcoord i) ω * K.integral D.N hℱN ω ∂P = 0 :=
    _root_.Prove2MeSourceProof.h_da55a4195e0b45ce7b0016e9 𝒲 hcoord hℱN G.measurable_uncurry
      G.progressive G.sq_int_global K.measurable_uncurry K.progressive K.sq_int_global hT.le
  rw [MeasureTheory.L2.inner_def, ← hcross]
  refine integral_congr_ae ?_
  filter_upwards [hG, hK] with ω e1 e2
  rw [RCLike.inner_apply, e1, e2]
  simp [mul_comm]
/-- The two ranges and the coordinate ranges form an orthogonal family. -/
theorem orthogonalFamily_jointRange (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T) :
    OrthogonalFamily ℝ (fun i => (jointRange hcoord hℱN hT i : Submodule ℝ (Lp ℝ 2 P)))
      (fun i => (jointRange hcoord hℱN hT i).subtypeₗᵢ) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  intro i j hij u v
  match i, j, u, v with
  | some i, some j, u, v =>
      exact _root_.Prove2MeSourceProof.h_6c3d71b7c655311c8008106f D.W hcoord hT (fun h => hij (by rw [h])) u v
  | some i, none, u, v => exact inner_itoRange_compensatedRange hcoord hℱN 𝒲 hT i u v
  | none, some j, u, v =>
      rw [real_inner_comm]
      exact inner_itoRange_compensatedRange hcoord hℱN 𝒲 hT j v u
  | none, none, _, _ => exact absurd rfl hij
/-- The joint range is closed in `L²`. -/
theorem isClosed_iSup_jointRange (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T) :
    IsClosed ((⨆ i : Option (Fin d), jointRange hcoord hℱN hT i :
      Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI : ∀ i : Option (Fin d), CompleteSpace (jointRange hcoord hℱN hT i) := by
    intro i
    match i with
    | some i => exact (_root_.Prove2MeSourceProof.h_940e1d5a45abf4f7e61b42fb (D.W.W i) (hcoord i) hT).completeSpace_coe
    | none => exact (_root_.Prove2MeSourceProof.h_5b889f5df8fcc6a23c71c429 D.N hℱN hT).completeSpace_coe
  exact _root_.Prove2MeSourceProof.h_77f46c5419a62c1d9a9e451e (orthogonalFamily_jointRange hcoord hℱN 𝒲 hT)
/-- The joint integral of coordinate integrands and a marked integrand. -/
noncomputable def jointIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) : Ω → ℝ :=
  fun ω => vectorIntegral D.W hcoord G ω + K.integral D.N hℱN ω
theorem memLp_jointIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) : MemLp (jointIntegral hcoord hℱN G K) 2 P :=
  (memLp_vectorIntegral D.W hcoord G).add (MarkedHorizonIntegrand.memLp D.N hℱN K)
theorem integral_jointIntegral_eq_zero (hT : 0 ≤ T)
    (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) (K : MarkedHorizonIntegrand P ν ℱ T) :
    ∫ ω, jointIntegral hcoord hℱN G K ω ∂P = 0 := by
  have hrw : jointIntegral hcoord hℱN G K
      = fun ω => vectorIntegral D.W hcoord G ω + K.integral D.N hℱN ω := rfl
  rw [hrw, integral_add ((memLp_vectorIntegral D.W hcoord G).integrable (by norm_num))
      ((MarkedHorizonIntegrand.memLp D.N hℱN K).integrable (by norm_num)),
    integral_vectorIntegral_eq_zero D.W hcoord hT G,
    _root_.Prove2MeSourceProof.h_454d3940367616169eae66cb D.N hℱN hT K, add_zero]
theorem aestronglyMeasurable_jointIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) :
    AEStronglyMeasurable[ℱ T] (jointIntegral hcoord hℱN G K) P :=
  (_root_.Prove2MeSourceProof.h_194396c8b70b364460393af6 D.W hcoord G).add
    (MarkedHorizonIntegrand.aestronglyMeasurable D.N hℱN K)
end Range

end LevyDriver

end LevyStochCalc.Driver


