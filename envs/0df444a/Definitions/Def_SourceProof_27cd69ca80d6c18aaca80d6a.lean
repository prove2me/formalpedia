-- Prove2me | Definitions.Def_SourceProof_27cd69ca80d6c18aaca80d6a
-- name    : SourceProof_27cd69ca80d6c18aaca80d6a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:07:12.750205+00:00
-- url     : https://prove2.me/theorems/d28b5052-66d1-43da-844e-152347588187
-- title:
--   LevyStochCalc source proof: Dense.holderWith_extend
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000


@[expose] public section

open Bornology Filter

open scoped NNReal ENNReal Topology

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [CompleteSpace Y]
    {C r : ℝ≥0} {s : Set X} {f : s → Y}

theorem _root_.Prove2MeSourceProof.h_27cd69ca80d6c18aaca80d6a (hs : Dense s) (hf : HolderWith C r f) (hr : 0 < r) :
    HolderWith C r (hs.extend f) := by
  intro x y
  have hf' := hf.uniformContinuous hr
  have := neBot_comap_nhds hs
  have hx := hs.extend_spec hf' x
  have hy := hs.extend_spec hf' y
  refine le_of_tendsto_of_tendsto'
    (b := ((𝓝 x).comap ((↑) : s → X)) ×ˢ ((𝓝 y).comap ((↑) : s → X))) ?_ ?_
    fun z : s × s ↦ hf z.1 z.2
  · change Tendsto (edist.uncurry ∘ (fun z : s × s ↦ (f z.1, f z.2))) _ _
    refine (Continuous.tendsto (by fun_prop) (hs.extend f x, hs.extend f y)).comp ?_
    exact Tendsto.prodMk_nhds (hx.comp tendsto_fst) (hy.comp tendsto_snd)
  · simp_rw [Subtype.edist_eq]
    change Tendsto ((fun z ↦ C * edist z.1 z.2 ^ r.toReal) ∘ (fun z : s × s ↦ (z.1.1, z.2.1))) _ _
    refine (Continuous.tendsto ?_ (x, y)).comp ?_
    · fun_prop (disch := exact ENNReal.coe_ne_top)
    exact Tendsto.prodMk_nhds (tendsto_comap.comp tendsto_fst) (tendsto_comap.comp tendsto_snd)


