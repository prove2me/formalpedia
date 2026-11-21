-- Prove2me | Definitions.Def_SourceProof_f13a945dd65a666877de115a
-- name    : SourceProof_f13a945dd65a666877de115a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:13:22.30525+00:00
-- url     : https://prove2.me/theorems/75df631b-4da7-45a2-b2a1-192945ee4bab
-- title:
--   LevyStochCalc source module: SourceProof_f13a945dd65a666877de115a
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral` comes from the `LevyStochCalc.Brownian.CrossOrthogonalityLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

Cross terms over intervals in any relative position reduce to the direct cross identity by
splitting at the later left endpoint, so elementary integrals against two distinct coordinates
`Wⁱ` and `Wʲ` of a `d`-dimensional Brownian motion have zero pairing. Continuity of the `L²`
pairing carries that vanishing to the limit along approximating simple integrands, giving the
orthogonality in `L²` of the Itô integrals against `Wⁱ` and against `Wʲ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section SimpleIntegrands

open LevyStochCalc.Brownian.Ito

variable {W : MultidimBrownianMotion P d}

end SimpleIntegrands

section L2Limit

open LevyStochCalc.Brownian.Ito


theorem _root_.Prove2MeSourceProof.h_f13a945dd65a666877de115a (V : BrownianMotion P) {T : ℝ} (G : SimplePredictable Ω T) (t : ℝ) :
    MemLp (fun ω => simpleIntegral V G t ω) 2 P := by
  have hnn : ∀ a : Fin G.N, 0 ≤ G.partition a.castSucc := fun a => by
    have h := G.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [G.partition_zero] at h
  have hlt : ∀ a : Fin G.N, G.partition a.castSucc < G.partition a.succ := fun a =>
    G.partition_strictMono Fin.castSucc_lt_succ
  have hrw : (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral V G t ω) = fun ω => ∑ a : Fin G.N,
      G.ξ a ω * (V.W (min (G.partition a.succ) t) ω
        - V.W (min (G.partition a.castSucc) t) ω) := rfl
  rw [hrw]
  refine memLp_finsetSum (f := fun (a : Fin G.N) ω => G.ξ a ω
    * (V.W (min (G.partition a.succ) t) ω - V.W (min (G.partition a.castSucc) t) ω))
    Finset.univ fun a _ => ?_
  rcases LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.min_eq_or_lt_min (hlt a) t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => G.ξ a ω * (V.W (min (G.partition a.succ) t) ω
        - V.W (min (G.partition a.castSucc) t) ω)) = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact memLp_const 0
  · obtain ⟨M, hM⟩ := G.ξ_bounded a
    rw [hpe]
    exact LevyStochCalc.Brownian.Ito.memLp_mul_increment V (hnn a) hplt 2 (by simp) (G.ξ_measurable a) hM
end L2Limit

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


