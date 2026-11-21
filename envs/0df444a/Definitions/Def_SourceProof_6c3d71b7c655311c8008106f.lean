-- Prove2me | Definitions.Def_SourceProof_6c3d71b7c655311c8008106f
-- name    : SourceProof_6c3d71b7c655311c8008106f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:25:44.424868+00:00
-- url     : https://prove2.me/theorems/2e19e999-c376-46ce-b468-502901b1207f
-- title:
--   LevyStochCalc source module: SourceProof_6c3d71b7c655311c8008106f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.orthogonalFamily_itoRange` comes from the `LevyStochCalc.Brownian.PRPMultidimRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F002
import Definitions.Def_SourceProof_52bc6f9c5c34d4f858067e35

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The closed range of the multidimensional Brownian Itô integral

The multidimensional Itô integral is the sum over the coordinates of the scalar integrals, so its
range in `L²` is the supremum of the scalar ranges. Those are closed, and orthogonal to one
another, so the supremum is closed: a point of its closure is the sum of its orthogonal
projections, each of which lies in the corresponding scalar range. The orthogonal decomposition
along the supremum then represents every square-integrable weight of mean zero, measurable before
the horizon, as a sum of coordinate Itô integrals, given the separation hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

section Range

variable (W : MultidimBrownianMotion P d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)


theorem _root_.Prove2MeSourceProof.h_6c3d71b7c655311c8008106f (hT : 0 < T) :
    OrthogonalFamily ℝ
      (fun i : Fin d => (itoRange (W.W i) (hcoord i) hT : Submodule ℝ (Lp ℝ 2 P)))
      (fun i => (itoRange (W.W i) (hcoord i) hT).subtypeₗᵢ) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  intro i j hij u v
  obtain ⟨G, hG⟩ := u.2
  obtain ⟨K, hK⟩ := v.2
  have hcross : ∫ ω, G.integral (W.W i) (hcoord i) ω * K.integral (W.W j) (hcoord j) ω ∂P = 0 :=
    _root_.Prove2MeSourceProof.h_52bc6f9c5c34d4f858067e35 W hij hcoord G.measurable_uncurry G.progressive
      G.sq_int_global K.measurable_uncurry K.progressive K.sq_int_global hT.le
  change (inner ℝ ((u : Lp ℝ 2 P)) ((v : Lp ℝ 2 P)) : ℝ) = 0
  rw [MeasureTheory.L2.inner_def, ← hcross]
  refine integral_congr_ae ?_
  filter_upwards [hG, hK] with ω e1 e2
  rw [RCLike.inner_apply, e1, e2]
  simp [mul_comm]
end Range

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion


