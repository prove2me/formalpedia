-- Prove2me | Definitions.Def_SourceProof_787ce4e71ca6c7d3e8f85694
-- name    : SourceProof_787ce4e71ca6c7d3e8f85694
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:57:17.574444+00:00
-- url     : https://prove2.me/theorems/64fb921a-1fac-4c9d-8500-82ef85537e56
-- title:
--   LevyStochCalc source module: SourceProof_787ce4e71ca6c7d3e8f85694
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists` comes from the `LevyStochCalc.Brownian.Multidim` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Brownian_Multidim_F000
import Definitions.Def_SourceProof_c83c751666c401b491a738db

open private project_BM from Definitions.Def_LevyStochCalc_Brownian_Multidim_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# d-dimensional Brownian motion

A `d`-dimensional Brownian motion is a `Fin d`-tuple of independent 1-D
Brownian motions on the same probability space. Constructed on the finite
product `MeasureTheory.Measure.pi` of copies of a space carrying one, whose
coordinates are independent by `ProbabilityTheory.iIndepFun_pi`.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.1.

## Contents

* `MultidimBrownianMotion` — the structure; `components_independent` is
  stated with `iIndepFun`, and `joint_continuous_paths` makes the almost-sure
  continuity of the vector-valued path explicit.
* `MultidimBrownianMotion.exists` — existence, via `MeasureTheory.Measure.pi` (finite
  product of probability spaces) and the independence of coordinate
  evaluations on a product measure; each coordinate is a 1-D Brownian motion
  lifted along the corresponding projection.
* `MultidimBrownianMotion.joint_increment_gaussian_diagonal` — each
  coordinate increment is Gaussian and the coordinate increments are
  independent.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim

universe u

section Definition
variable {Ω : Type u} [MeasurableSpace Ω]

end Definition

section MeasurePreserving
variable {Ω : Type u} [MeasurableSpace Ω]

end MeasurePreserving

section Existence
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_787ce4e71ca6c7d3e8f85694 (d : ℕ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (MultidimBrownianMotion P d) := by
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, ⟨W₀⟩⟩ :=
    _root_.Prove2MeSourceProof.h_c83c751666c401b491a738db
  refine ⟨Fin d → Ω₀, MeasurableSpace.pi,
    MeasureTheory.Measure.pi (fun _ => P₀), inferInstance, ?_⟩
  refine ⟨{
    W := fun i => project_BM W₀ d i
    components_independent := ?_
    joint_continuous_paths := ?_
  }⟩
  pick_goal 2
  · -- joint continuity from per-component continuity (a.s. over the product
    -- measure) via `continuous_pi_iff`: a `Fin d → ℝ`-valued function of `t`
    -- is continuous iff each projection `(fun t => f t i)` is.  Each
    -- `(project_BM W₀ d i).continuous_paths` is already an a.s. statement, and
    -- the conjunction over the finite set `Fin d` remains a.s.
    have h_each : ∀ i : Fin d, ∀ᵐ ω ∂(MeasureTheory.Measure.pi (fun _ : Fin d => P₀)),
        Continuous (fun (t : ℝ) => (project_BM W₀ d i).W t ω) :=
      fun i => (project_BM W₀ d i).continuous_paths
    have h_all : ∀ᵐ ω ∂(MeasureTheory.Measure.pi (fun _ : Fin d => P₀)),
        ∀ i : Fin d, Continuous (fun (t : ℝ) => (project_BM W₀ d i).W t ω) :=
      MeasureTheory.ae_all_iff.mpr h_each
    filter_upwards [h_all] with ω hω
    exact continuous_pi (fun i => hω i)
  -- Components are independent: use ProbabilityTheory.iIndepFun_pi
  -- with X_i = (fun ω : Ω₀ => fun t => W₀.W t ω) for each i.
  have h_meas_W₀ : ∀ _ : Fin d,
      AEMeasurable (fun ω₀ : Ω₀ => fun t : ℝ => W₀.W t ω₀) P₀ := by
    intro _
    -- Function into ℝ → ℝ is measurable iff each evaluation is measurable.
    refine (measurable_pi_iff.mpr ?_).aemeasurable
    intro t
    exact W₀.measurable_eval t
  have := ProbabilityTheory.iIndepFun_pi
    (X := fun _ : Fin d => fun ω₀ : Ω₀ => fun t : ℝ => W₀.W t ω₀)
    (μ := fun _ : Fin d => P₀) h_meas_W₀
  convert this using 1
  rfl
end Existence

end LevyStochCalc.Brownian.Multidim


