-- Prove2me | Definitions.Def_SourceProof_77f46c5419a62c1d9a9e451e
-- name    : SourceProof_77f46c5419a62c1d9a9e451e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:22:20.738598+00:00
-- url     : https://prove2.me/theorems/547843d5-51c1-4cb6-b021-44e5129f1e7b
-- title:
--   LevyStochCalc source module: SourceProof_77f46c5419a62c1d9a9e451e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isClosed_iSup_of_orthogonalFamily` comes from the `LevyStochCalc.Brownian.PRPMultidimRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F001
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F002

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


theorem _root_.Prove2MeSourceProof.h_77f46c5419a62c1d9a9e451e {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type*} [Finite ι] {V : ι → Submodule 𝕜 E}
    [∀ i, CompleteSpace (V i)]
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    IsClosed ((⨆ i, V i : Submodule 𝕜 E) : Set E) := by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx => ?_
  have hsum : ∀ n, ∑ i, (V i).starProjection (f n) = f n :=
    fun n => hV.sum_projection_of_mem_iSup (f n) (hf n)
  have hlim : Tendsto (fun n => ∑ i, (V i).starProjection (f n)) atTop
      (𝓝 (∑ i, (V i).starProjection x)) :=
    tendsto_finsetSum _ fun i _ => ((V i).starProjection.continuous.tendsto x).comp hx
  have hxeq : x = ∑ i, (V i).starProjection x := by
    refine tendsto_nhds_unique ?_ hlim
    simpa only [hsum] using hx
  rw [SetLike.mem_coe, hxeq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.mem_iSup_of_mem i ((V i).starProjection_apply_mem x)
section Range

variable (W : MultidimBrownianMotion P d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

end Range

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion


