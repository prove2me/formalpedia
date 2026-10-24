-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
-- name    : KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:52:04.46143+00:00
-- url     : https://prove2.me/theorems/dae32ddd-b352-4a51-86c2-d28a9b4d2b4f
-- title:
--   Poisson piece laws and independent superposition space
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `PieceSpace 𝓧` is `ULift ℕ × (ℕ → 𝓧)`, containing a Poisson count and a sequence of marks. `pieceLaw r ρ` is the product of the pushforward of `Poisson(r)` to `ULift ℕ$ and the infinite product of the mark measure $\rho$; if $\rho$ is a probability measure, this is a probability measure. For a countable index type $\iota$, `superLaw r ρ` is the infinite product of these independent piece laws, and is again a probability measure when every $\rho_p$ is.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/PoissonSuperposition.lean#L33-L76 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.PoissonSuperposition`, definition bundle `KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/PoissonSuperposition.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory Complex Filter Function Topology
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
universe u
section Piece
variable {𝓧 : Type u} [MeasurableSpace 𝓧]
/-- The coordinates of one Poisson piece: a count and a sequence of marks. -/
abbrev PieceSpace (𝓧 : Type u) : Type u := ULift.{u} ℕ × (ℕ → 𝓧)
/-- The law of one piece: a Poisson count independent of a sequence of iid marks. -/
noncomputable def pieceLaw (r : ℝ≥0) (ρ : Measure 𝓧) : Measure (PieceSpace 𝓧) :=
  (Po(r).map ULift.up).prod (Measure.infinitePi fun _ : ℕ => ρ)
instance (r : ℝ≥0) (ρ : Measure 𝓧) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (pieceLaw r ρ) := by
  haveI : IsProbabilityMeasure (Po(r).map ULift.up) :=
    Measure.isProbabilityMeasure_map measurable_up.aemeasurable
  unfold pieceLaw
  infer_instance
variable {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧) [∀ p, IsProbabilityMeasure (ρ p)]
/-- The law of the superposition sample space: independent pieces. -/
noncomputable def superLaw : Measure (ι → PieceSpace 𝓧) :=
  Measure.infinitePi fun p => pieceLaw (r p) (ρ p)
instance : IsProbabilityMeasure (superLaw r ρ) := by
  unfold superLaw
  infer_instance
variable {r ρ}
variable (r ρ)
variable {r ρ}
variable (r ρ)
variable [Countable ι]
end Piece
end Poisson
end LevyStochCalc


