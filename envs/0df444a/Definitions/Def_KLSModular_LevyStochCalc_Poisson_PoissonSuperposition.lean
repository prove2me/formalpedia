-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_PoissonSuperposition
-- name    : KLSModular_LevyStochCalc_Poisson_PoissonSuperposition
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:41:32.740107+00:00
-- url     : https://prove2.me/theorems/611e21d8-5739-4aac-a1ee-7fdb9fa7f1f5
-- title:
--   Poisson piece laws and independent superposition space
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `PieceSpace 𝓧` is `ULift ℕ × (ℕ → 𝓧)`, containing a Poisson count and a sequence of marks. `pieceLaw r ρ` is the product of the pushforward of `Poisson(r)` to `ULift ℕ` and the infinite product of the mark measure $\rho$; if $\rho$ is a probability measure, this is a probability measure. For a countable index type $\iota$, `superLaw r ρ` is the infinite product of these independent piece laws, and is again a probability measure when every $\rho_p$ is.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Poisson.PoissonSplitting
--   import LevyStochCalc.Probability.IndepGrouping
--   import Mathlib.Probability.Independence.CharacteristicFunction
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   abbrev PieceSpace (𝓧 : Type u) : Type u := ULift.{u} ℕ × (ℕ → 𝓧)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Poisson/PoissonSplitting`](https://prove2.me/theorems/66e06598-17d9-4f53-9059-6ebb3b15c3b4), [`LevyStochCalc/Probability/IndepGrouping`](https://prove2.me/theorems/2ad3a44c-c896-485d-ae09-3cb66276f5cb).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/PoissonSuperposition.lean) · `LevyStochCalc.Poisson.PoissonSuperposition` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/PoissonSuperposition.lean#L33-L76 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.PoissonSuperposition`, definition bundle `KLSModular_LevyStochCalc_Poisson_PoissonSuperposition`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_PoissonSplitting
import Definitions.Def_KLSModular_LevyStochCalc_Probability_IndepGrouping
import Mathlib.Probability.Independence.CharacteristicFunction

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


