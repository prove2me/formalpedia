-- Prove2me | Definitions.Def_SourceProof_252de1bf6fed3eea178fe837
-- name    : SourceProof_252de1bf6fed3eea178fe837
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:08.499187+00:00
-- url     : https://prove2.me/theorems/20f48949-7886-48a6-b316-6cd015e7fa7b
-- title:
--   LevyStochCalc source module: SourceProof_252de1bf6fed3eea178fe837
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.exists_markedHorizonIntegrand_of_mean_zero` comes from the `LevyStochCalc.Poisson.CompensatedRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F003
import Definitions.Def_SourceProof_454d3940367616169eae66cb
import Definitions.Def_SourceProof_5b889f5df8fcc6a23c71c429

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the compensated Poisson integral on a horizon

A marked integrand supported in `[0, T]`, jointly and progressively measurable and of finite
energy, is admissible for the compensated integral up to `T`. Such integrands are closed under
sums and scalar multiples, and the integral is additive and homogeneous on them, so their
integrals form a submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence
of integrands to an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Progressive

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Progressive

namespace MarkedHorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Integral

end MarkedHorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)


theorem _root_.Prove2MeSourceProof.h_252de1bf6fed3eea178fe837 (hT : 0 < T)
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ T] r P →
      (∫ ω, r ω ∂P = 0) →
      (∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, r ω * G.integral N hℱ ω ∂P = 0) → r =ᵐ[P] 0)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : MarkedHorizonIntegrand P ν ℱ T, Z =ᵐ[P] G.integral N hℱ := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI hcl : IsClosed ((LevyStochCalc.Poisson.Compensated.compensatedRange N hℱ hT : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    _root_.Prove2MeSourceProof.h_5b889f5df8fcc6a23c71c429 N hℱ hT
  haveI : CompleteSpace (LevyStochCalc.Poisson.Compensated.compensatedRange N hℱ hT) := hcl.completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (LevyStochCalc.Poisson.Compensated.compensatedRange N hℱ hT).exists_add_mem_mem_orthogonal (hZ2.toLp Z)
  obtain ⟨G₀, hG₀⟩ := hy
  have hsplit : Z =ᵐ[P] fun ω => G₀.integral N hℱ ω + (z : Ω → ℝ) ω := by
    filter_upwards [hZ2.coeFn_toLp, Lp.coeFn_add y z, hG₀] with ω e1 e2 e3
    rw [← e1, hyz, e2, Pi.add_apply, e3]
  have hzmem : MemLp (z : Ω → ℝ) 2 P := Lp.memLp z
  have hzmeas : AEStronglyMeasurable[ℱ T] (z : Ω → ℝ) P := by
    have hd : (z : Ω → ℝ) =ᵐ[P] fun ω => Z ω - G₀.integral N hℱ ω := by
      filter_upwards [hsplit] with ω e1
      rw [e1]; ring
    exact (hZm.sub (LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.aestronglyMeasurable N hℱ G₀)).congr hd.symm
  have hymean : ∫ ω, G₀.integral N hℱ ω ∂P = 0 :=
    _root_.Prove2MeSourceProof.h_454d3940367616169eae66cb N hℱ hT.le G₀
  have hzint : Integrable (z : Ω → ℝ) P := hzmem.integrable (by norm_num)
  have hyint : Integrable (G₀.integral N hℱ) P :=
    (LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ G₀).integrable (by norm_num)
  have hzmean : ∫ ω, (z : Ω → ℝ) ω ∂P = 0 := by
    have := integral_congr_ae (μ := P) hsplit
    rw [integral_add hyint hzint, hymean, zero_add] at this
    rw [← this, hZ0]
  have hzperp : ∀ G : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, (z : Ω → ℝ) ω * G.integral N hℱ ω ∂P = 0 := by
    intro G
    have hmem : (LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ G).toLp (G.integral N hℱ)
        ∈ LevyStochCalc.Poisson.Compensated.compensatedRange N hℱ hT := ⟨G, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [L2.inner_def] at hinner
    have hcongr : ∫ ω, (((LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ G).toLp (G.integral N hℱ) :
          Ω → ℝ) ω * (z : Ω → ℝ) ω) ∂P = ∫ ω, G.integral N hℱ ω * (z : Ω → ℝ) ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ G)] with ω e1
      rw [e1]
    have hrw : ∫ ω, G.integral N hℱ ω * (z : Ω → ℝ) ω ∂P = 0 := by
      rw [← hcongr, ← hinner]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        simp [RCLike.inner_apply, mul_comm])
    rw [← hrw]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hzzero := hsep (z : Ω → ℝ) hzmem hzmeas hzmean hzperp
  refine ⟨G₀, ?_⟩
  filter_upwards [hsplit, hzzero] with ω e1 e2
  rw [e1, e2]
  simp
end Representation

end LevyStochCalc.Poisson.Compensated


