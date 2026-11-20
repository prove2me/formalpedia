-- Prove2me | Definitions.Def_SourceProof_e4022c8f2f69eecbce88538a
-- name    : SourceProof_e4022c8f2f69eecbce88538a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:06:19.455177+00:00
-- url     : https://prove2.me/theorems/386d73df-811d-42e2-a1f7-34a0070e88a3
-- title:
--   LevyStochCalc source module: SourceProof_e4022c8f2f69eecbce88538a
-- statement:
--   The original source theorem `MathFin.pair_integral_eq` comes from the `MathFin.Foundations.PoissonCompensatedIntegralOperator` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_MathFin_Foundations_ExtendOfNormIsometry_F000
import Definitions.Def_MathFin_Foundations_PoissonCompensatedSimpleIntegrand_F000
import Definitions.Def_SourceProof_2118dd8af0bc41a167ea34d2

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

/-!
# The compensated-Poisson integral operator on marked simple integrands

The two linear maps out of the marked simple-integrand module `levySimpleModule`, mirroring the
continuous `ItoIntegralL2.itoAssembly` / `simpleAssembly`:

* `intAssembly : levySimpleModule N →ₗ[ℝ] Lp ℝ 2 P` — the elementary compensated integral
  `∑_b φ_b · Ñ(box b)`, viewed in `L²(P)`;
* `emb : levySimpleModule N →ₗ[ℝ] Lp ℝ 2 (P.prod (referenceIntensity ν))` — the integrand
  `∑_b φ_b · 𝟙_{box b}`, viewed in `L²(dP ⊗ dν̂)` (the sibling module).

The `L²` isometry `‖intAssembly V‖ = ‖emb V‖`, obtained by summing the overlapping-box bilinear
pairing `integral_bilinear_pairing`, and the `extendOfNorm` CLM are built on these.

## Provenance

Mirrors the continuous `ItoIntegralL2` assembly; the compensated-integral content is our own.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The elementary compensated integral as a linear map -/

/-! ### The integrand embedding into the predictable `L²(dP ⊗ dν̂)` -/

/-! ### The isometry `‖intAssembly V‖ = ‖emb V‖` (summing the bilinear pairing) -/


theorem _root_.Prove2MeSourceProof.h_e4022c8f2f69eecbce88538a (N : PoissonRandomMeasure P ν) (V : levySimpleModule N)
    {ba bb : ℝ × ℝ × Set E} (hba : ba ∈ V.1.support) (hbb : bb ∈ V.1.support) :
    ∫ ω, (V.1 ba ω * N.compensated (indexBox ba) ω)
          * (V.1 bb ω * N.compensated (indexBox bb) ω) ∂P
      = ∫ p, (V.1 ba p.1 * (indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
              * (V.1 bb p.1 * (indexBox bb).indicator (fun _ => (1 : ℝ)) p.2)
          ∂(P.prod (referenceIntensity ν)) := by
  haveI : SFinite (MathFin.referenceIntensity ν) := by unfold MathFin.referenceIntensity; infer_instance
  obtain ⟨C, _, hC⟩ := V.2.bound_coe
  have hboxams : MeasurableSet (MathFin.indexBox ba) := measurableSet_Ioc.prod (V.2.markMeasurable ba hba)
  have hboxbms : MeasurableSet (MathFin.indexBox bb) := measurableSet_Ioc.prod (V.2.markMeasurable bb hbb)
  -- the compensated pairing equals `𝔼[φ_ba φ_bb] · ν̂(box ba ∩ box bb)` (WLOG order by start)
  have hLHS : ∫ ω, (V.1 ba ω * N.compensated (MathFin.indexBox ba) ω)
        * (V.1 bb ω * N.compensated (MathFin.indexBox bb) ω) ∂P
      = (∫ ω, V.1 ba ω * V.1 bb ω ∂P)
          * (MathFin.referenceIntensity ν (MathFin.indexBox ba ∩ MathFin.indexBox bb)).toReal := by
    rcases le_total ba.1 bb.1 with hab | hab
    · exact _root_.Prove2MeSourceProof.h_2118dd8af0bc41a167ea34d2 N hab (V.2.markMeasurable ba hba) (V.2.markMeasurable bb hbb)
        (V.2.markFinite ba hba) (V.2.markFinite bb hbb) (V.2.adapted ba hba) (V.2.adapted bb hbb)
        (fun ω => hC ba ω) (fun ω => hC bb ω)
    · have hpair := _root_.Prove2MeSourceProof.h_2118dd8af0bc41a167ea34d2 N (ta := bb.2.1) (tb := ba.2.1) hab
        (V.2.markMeasurable bb hbb) (V.2.markMeasurable ba hba) (V.2.markFinite bb hbb)
        (V.2.markFinite ba hba) (V.2.adapted bb hbb) (V.2.adapted ba hba)
        (fun ω => hC bb ω) (fun ω => hC ba ω)
      calc ∫ ω, (V.1 ba ω * N.compensated (MathFin.indexBox ba) ω)
              * (V.1 bb ω * N.compensated (MathFin.indexBox bb) ω) ∂P
          = ∫ ω, (V.1 bb ω * N.compensated (MathFin.indexBox bb) ω)
              * (V.1 ba ω * N.compensated (MathFin.indexBox ba) ω) ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
        _ = (∫ ω, V.1 bb ω * V.1 ba ω ∂P)
              * (MathFin.referenceIntensity ν (MathFin.indexBox bb ∩ MathFin.indexBox ba)).toReal := hpair
        _ = (∫ ω, V.1 ba ω * V.1 bb ω ∂P)
              * (MathFin.referenceIntensity ν (MathFin.indexBox ba ∩ MathFin.indexBox bb)).toReal := by
            rw [Set.inter_comm (MathFin.indexBox bb) (MathFin.indexBox ba)]
            congr 1
            exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  -- the integrand pairing equals the same, by Fubini
  have hRHS : ∫ p, (V.1 ba p.1 * (MathFin.indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
        * (V.1 bb p.1 * (MathFin.indexBox bb).indicator (fun _ => (1 : ℝ)) p.2)
          ∂(P.prod (MathFin.referenceIntensity ν))
      = (∫ ω, V.1 ba ω * V.1 bb ω ∂P)
          * (MathFin.referenceIntensity ν (MathFin.indexBox ba ∩ MathFin.indexBox bb)).toReal := by
    have hind : (fun z : ℝ × E => (MathFin.indexBox ba).indicator (fun _ => (1 : ℝ)) z
          * (MathFin.indexBox bb).indicator (fun _ => (1 : ℝ)) z)
        = (MathFin.indexBox ba ∩ MathFin.indexBox bb).indicator (fun _ => (1 : ℝ)) := by
      funext z; by_cases hzi : z ∈ MathFin.indexBox ba <;> by_cases hzj : z ∈ MathFin.indexBox bb <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, hzi, hzj]
    rw [show (fun p : Ω × (ℝ × E) =>
            (V.1 ba p.1 * (MathFin.indexBox ba).indicator (fun _ => (1 : ℝ)) p.2)
              * (V.1 bb p.1 * (MathFin.indexBox bb).indicator (fun _ => (1 : ℝ)) p.2))
          = fun p => (V.1 ba p.1 * V.1 bb p.1)
              * ((MathFin.indexBox ba).indicator (fun _ => (1 : ℝ)) p.2
                  * (MathFin.indexBox bb).indicator (fun _ => (1 : ℝ)) p.2) from by funext p; ring,
      integral_prod_mul (fun ω => V.1 ba ω * V.1 bb ω)
        (fun z => (MathFin.indexBox ba).indicator (fun _ => (1 : ℝ)) z
          * (MathFin.indexBox bb).indicator (fun _ => (1 : ℝ)) z),
      hind, integral_indicator (hboxams.inter hboxbms), setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def]
  rw [hLHS, hRHS]
/-! ### The Itô–Lévy integral CLM on the `L²` closure of the simple integrands -/

end MathFin


