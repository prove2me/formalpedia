-- Prove2me | Definitions.Def_SourceProof_b23612bd7f724e39ce57d7eb
-- name    : SourceProof_b23612bd7f724e39ce57d7eb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:12:10.502971+00:00
-- url     : https://prove2.me/theorems/049624e6-e668-42c8-9c83-37df9df670a0
-- title:
--   LevyStochCalc source module: SourceProof_b23612bd7f724e39ce57d7eb
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.perpItoIntegrals_combineBM` comes from the `LevyStochCalc.Brownian.PRPMultidim` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_PRPGrid_F001
import Definitions.Def_SourceProof_d5966497ad5bdb51775a8311

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One window of the multidimensional Brownian predictable representation

A weight orthogonal to every coordinate's Itô integrals is orthogonal to the integrals against
any unit linear combination of the coordinates, so the one-window statement transfers, and a
multidimensional cell character is a scalar character of the combination.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}


theorem _root_.Prove2MeSourceProof.h_b23612bd7f724e39ce57d7eb (W : Multidim.MultidimBrownianMotion P d) {c : Fin d → ℝ}
    (hc : ∑ i, c i ^ 2 = 1) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱB : IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    {Z : Ω → ℂ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z) :
    PerpItoIntegrals (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ hℱB Z := by
  constructor
  intro K hm hp hq t ht
  have hlin := _root_.Prove2MeSourceProof.h_d5966497ad5bdb51775a8311 W hc ℱ hℱB hℱi K hm hp hq ht.le
  have hint : ∀ i : Fin d, Integrable
      (fun ω => Z ω * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) K hm hp hq t ω : ℝ) : ℂ))
      P := fun i =>
    hZ2.integrable_mul (LevyStochCalc.Brownian.Ito.memLp_ofReal (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (W.W i) ℱ (hℱi i)
      K hm hp hq t))
  have hcong : ∫ ω, Z ω * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combineBM W hc) ℱ hℱB K hm hp hq t ω : ℝ) : ℂ) ∂P
      = ∫ ω, ∑ i, ((c i : ℝ) : ℂ)
        * (Z ω * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱi i) K hm hp hq t ω : ℝ) : ℂ)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hlin] with ω hω
    rw [hω]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hcong, integral_finsetSum _ fun i _ => (hint i).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, (hperp i).perp K hm hp hq t ht, mul_zero]
end LevyStochCalc.Brownian.Ito


