-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PRPMultidimRange_F000
-- name    : LevyStochCalc_Brownian_PRPMultidimRange_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:28:46.791633+00:00
-- url     : https://prove2.me/theorems/94375b54-0457-4f5c-be71-c4119ded78f5
-- title:
--   Source declarations: LevyStochCalc.Brownian.PRPMultidimRange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PRPMultidimRange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F001
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F002
import Definitions.Def_SourceProof_6c3d71b7c655311c8008106f
import Definitions.Def_SourceProof_77f46c5419a62c1d9a9e451e
import Definitions.Def_SourceProof_940e1d5a45abf4f7e61b42fb
import Definitions.Def_SourceProof_9af27f0e9a5c51338bfc8fcb

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

/-- The range of the multidimensional Itô integral is closed in `L²`. -/
theorem isClosed_iSup_itoRange (hT : 0 < T) :
    IsClosed ((⨆ i : Fin d, itoRange (W.W i) (hcoord i) hT :
      Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI : ∀ i : Fin d, CompleteSpace (itoRange (W.W i) (hcoord i) hT) := fun i =>
    (_root_.Prove2MeSourceProof.h_940e1d5a45abf4f7e61b42fb (W.W i) (hcoord i) hT).completeSpace_coe
  exact _root_.Prove2MeSourceProof.h_77f46c5419a62c1d9a9e451e (_root_.Prove2MeSourceProof.h_6c3d71b7c655311c8008106f W hcoord hT)
/-- The multidimensional Itô integral of a family of admissible integrands. -/
noncomputable def vectorIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) : Ω → ℝ :=
  fun ω => ∑ i : Fin d, (G i).integral (W.W i) (hcoord i) ω
theorem memLp_vectorIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) :
    MemLp (vectorIntegral W hcoord G) 2 P :=
  memLp_finsetSum (f := fun (i : Fin d) ω => (G i).integral (W.W i) (hcoord i) ω) Finset.univ
    fun i _ => HorizonIntegrand.memLp (W.W i) (hcoord i) (G i)
theorem integral_vectorIntegral_eq_zero (hT : 0 ≤ T)
    (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) :
    ∫ ω, vectorIntegral W hcoord G ω ∂P = 0 := by
  have hrw : vectorIntegral W hcoord G
      = fun ω => ∑ i : Fin d, (G i).integral (W.W i) (hcoord i) ω := rfl
  rw [hrw, integral_finsetSum _ fun i _ =>
    (HorizonIntegrand.memLp (W.W i) (hcoord i) (G i)).integrable (by norm_num)]
  exact Finset.sum_eq_zero fun i _ =>
    _root_.Prove2MeSourceProof.h_9af27f0e9a5c51338bfc8fcb (W.W i) (hcoord i) hT (G i)
end Range

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion


