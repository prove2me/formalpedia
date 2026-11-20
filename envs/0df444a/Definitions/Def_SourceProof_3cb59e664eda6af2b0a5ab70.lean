-- Prove2me | Definitions.Def_SourceProof_3cb59e664eda6af2b0a5ab70
-- name    : SourceProof_3cb59e664eda6af2b0a5ab70
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:49:55.149015+00:00
-- url     : https://prove2.me/theorems/d04bebfa-526c-43f1-a774-5956ffd309b9
-- title:
--   LevyStochCalc source module: SourceProof_3cb59e664eda6af2b0a5ab70
-- statement:
--   The original source theorem `Dense.holderOnWith_extend` comes from the `BrownianMotion.Continuity.KolmogorovChentsov` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
import Definitions.Def_BrownianMotion_Auxiliary_Topology_F001
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_Gaussian_StochasticProcesses_F000
import Definitions.Def_SourceProof_62dfde857e76a0eeed3ee854

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

theorem _root_.Prove2MeSourceProof.h_3cb59e664eda6af2b0a5ab70 {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [CompleteSpace Y] {C r : ℝ≥0} {s : Set X} {f : s → Y} {U : Set X} (hU : IsOpen U) (hs : Dense s)
    (hf : HolderOnWith C r f {x | ↑x ∈ U}) (hr : 0 < r) :
    HolderOnWith C r (hs.extend f) U := by
  intro x hx y hy
  have := neBot_comap_nhds hs
  have h_mem x (hx : x ∈ U) : ∀ᶠ z in (𝓝 x).comap ((↑) : s → X), ↑z ∈ U := by
    simp only [eventually_comap, Subtype.forall]
    suffices ∀ᶠ z in 𝓝 x, z ∈ U by
      filter_upwards [this] with z hz
      rintro _ h rfl
      exact hz
    rw [eventually_mem_set]
    exact hU.mem_nhds hx
  have h_prod_mem : ∀ᶠ z : s × s in
      ((𝓝 x).comap ((↑) : s → X)) ×ˢ ((𝓝 y).comap ((↑) : s → X)),
      ↑z.1 ∈ U ∧ ↑z.2 ∈ U := by
    simp only [eventually_and]
    exact ⟨(h_mem x hx).prod_inl _, (h_mem y hy).prod_inr _⟩
  have hfx : Tendsto f ((𝓝 x).comap ((↑) : s → X)) (𝓝 (hs.extend f x)) := by
    refine tendsto_nhds_limUnder ?_
    exact _root_.Prove2MeSourceProof.h_62dfde857e76a0eeed3ee854 hs hU (hf.uniformContinuousOn hr) _ hx
  have hfy : Tendsto f ((𝓝 y).comap ((↑) : s → X)) (𝓝 (hs.extend f y)) := by
    refine tendsto_nhds_limUnder ?_
    exact _root_.Prove2MeSourceProof.h_62dfde857e76a0eeed3ee854 hs hU (hf.uniformContinuousOn hr) _ hy
  classical
  let f' : s × s → ℝ≥0∞ := fun z ↦ if ↑z.1 ∈ U ∧ ↑z.2 ∈ U then edist (f z.1) (f z.2) else 0
  let g' : s × s → ℝ≥0∞ := fun z ↦ C * edist z.1 z.2 ^ (r : ℝ)
  have hf'_eq : f' =ᶠ[((𝓝 x).comap ((↑) : s → X)) ×ˢ ((𝓝 y).comap ((↑) : s → X))]
      fun z ↦ edist (f z.1) (f z.2) := by
    filter_upwards [h_prod_mem] with z hz
    simp [f', hz]
  refine le_of_tendsto_of_tendsto (f := f') (g := g')
    (b := ((𝓝 x).comap ((↑) : s → X)) ×ˢ ((𝓝 y).comap ((↑) : s → X))) ?_ ?_ ?_
  · refine Tendsto.congr' hf'_eq.symm ?_
    change Tendsto (edist.uncurry ∘ (fun p : s × s ↦ (f p.1, f p.2))) _ _
    refine (Continuous.tendsto (by fun_prop) (hs.extend f x, hs.extend f y)).comp ?_
    refine Tendsto.prodMk_nhds ?_ ?_
    · exact hfx.comp tendsto_fst
    · exact hfy.comp tendsto_snd
  · simp_rw [g', Subtype.edist_eq]
    change Tendsto ((fun z ↦ C * edist z.1 z.2 ^ r.toReal) ∘ (fun z : s × s ↦ (z.1.1, z.2.1))) _ _
    refine (Continuous.tendsto ?_ (x, y)).comp ?_
    · fun_prop (disch := exact ENNReal.coe_ne_top)
    exact Tendsto.prodMk_nhds (tendsto_comap.comp tendsto_fst) (tendsto_comap.comp tendsto_snd)
  · filter_upwards [h_prod_mem] with z ⟨hz₁, hz₂⟩
    simp only [hz₁, hz₂, and_self, ↓reduceIte, ge_iff_le, f', g']
    exact hf z.1 hz₁ z.2 hz₂
end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

section HolderSet

end HolderSet

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [hE : Nonempty E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory


