-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardFixedPoint_F001
-- name    : LevyStochCalc_Ito_PicardFixedPoint_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:03:05.897542+00:00
-- url     : https://prove2.me/theorems/83968928-a2a1-4d7d-8095-d31960394f5c
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardFixedPoint
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardFixedPoint. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence and uniqueness via the Banach fixed-point theorem

This file packages Banach's fixed-point theorem (`ContractingWith.fixedPoint`)
in the `∃!` shape of a Picard iteration, and states the existence/uniqueness
theorem for the jump-diffusion SDE in the form consumed by `Ito/Setting.lean`,
forwarding to `exists_jumpDiffusion_unique_of_solvesOn` in
`Ito/PicardWellPosed.lean`.

## Contents

* `picardFixedPoint_generic`, `picardFixedPoint`, `picardFixedPoint_of_exists`
  — the abstract fixed-point packaging.
* `picardFixedPoint_jumpDiffusion_exists_unique` — the concrete
  existence/uniqueness statement for the jump-diffusion SDE, relative to a
  filtration satisfying the usual conditions.
* `JumpDiffusion.exists_unique`, `JumpDiffusion.agree_at_zero` — the form
  consumed by `Ito/Setting.lean`.
-/
open MeasureTheory ProbabilityTheory Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

end LevyStochCalc.Ito.Picard

/-! ## Literature theorem: `JumpDiffusion.exists_unique`

This is the headline existence-and-uniqueness theorem cited from
Applebaum 2009 Theorem 6.2.9 / Ikeda-Watanabe IV. Its qualified name is
`LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` — we re-open
that namespace explicitly here so the original location in
`Ito/Setting.lean` (a module that this file imports) is preserved at
the level of qualified names.

**Why the theorem lives here, not in `Ito/Setting.lean`**: the proof
forwards through `picardFixedPoint_jumpDiffusion_exists_unique` (above),
which forwards to `exists_jumpDiffusion_unique_of_solvesOn` in
`Ito/PicardWellPosed.lean`. Putting the theorem in `LevyStochCalc.Ito.Setting`
would require that module to import `LevyStochCalc.Ito.PicardWellPosed`,
which already imports `LevyStochCalc.Ito.Setting` for the `JumpDiffusion`
structure definition, creating a cycle. -/

namespace LevyStochCalc.Ito.Setting
namespace JumpDiffusion

/-- **Pairwise a.s. agreement at `t = 0`.** Any two jump-diffusion
solutions for the same coefficients and initial condition agree a.s.
at `t = 0`. This is the degenerate-time slice of the headline a.s.
uniqueness conclusion that follows DIRECTLY from each structure's
`initial_value : ∀ᵐ ω, X 0 ω = x₀` field, WITHOUT invoking the
Picard/Banach contraction machinery. Useful as a public extractor for
downstream callers needing the `t = 0` uniqueness in isolation
(e.g. consistency checks on user-supplied JumpDiffusion candidates). -/
theorem agree_at_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
    {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
    {coeffs : JumpDiffusionCoeffs n d E}
    {x₀ : Fin n → ℝ}
    (jd jd' : JumpDiffusion W N coeffs x₀) :
    ∀ᵐ ω ∂P, jd.X 0 ω = jd'.X 0 ω := by
  -- Both jd.X 0 = x₀ a.s. and jd'.X 0 = x₀ a.s. ; transitivity through the
  -- common value x₀ gives jd.X 0 = jd'.X 0 a.s. on the intersection of
  -- the two a.s. events, which is itself a.s.
  filter_upwards [jd.initial_value, jd'.initial_value] with ω h₁ h₂
  rw [h₁, h₂]
end JumpDiffusion
end LevyStochCalc.Ito.Setting


