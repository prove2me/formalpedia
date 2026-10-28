-- Prove2me | Definitions.Def_KLSModular_MathFin_Foundations_DoobLpMaximalInequality
-- name    : KLSModular_MathFin_Foundations_DoobLpMaximalInequality
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:48:20.658106+00:00
-- url     : https://prove2.me/theorems/246417cb-a393-4700-8546-3a2d7f728869
-- title:
--   Running maximum auxiliary definition
-- statement:
--   Vendored from the formal-mathfin library (https://github.com/raphaelrrcoelho/formal-mathfin). The private definition `MeasureTheory.runMax` assigns to a real-valued discrete-time process $f$, an index $n$, and an outcome $\omega$ the finite supremum of $f(k,\omega)$ over $k\in\{0,\ldots,n\}$. The uploaded declarations contain this auxiliary definition only; the module text does not provide the stated $L^p$ maximal-inequality theorem.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.Probability.Martingale.OptionalStopping
--   public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
--   public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
--   public import Mathlib.MeasureTheory.Integral.MeanInequalities
--   public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
--   public import Mathlib.Analysis.MeanInequalities
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def runMax (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
--     (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k ↦ f k ω)
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`inner_t_integral`](https://prove2.me/theorems/3ddc797c-837a-4b85-8121-292fb503538b)
--   - [`fubini_swap`](https://prove2.me/theorems/44a8d562-86b4-4fc8-8ba6-8f6c932e07c0)
--   - [`fubini_swap_truncated`](https://prove2.me/theorems/d6dd1ec2-dc45-4bb7-acdd-bd178c7f7911)
--   - [`A_K_le_layer_integral`](https://prove2.me/theorems/3605b7cf-82c6-4d1c-9553-8a7bb463ed50)
--   - [`holder_step_truncated`](https://prove2.me/theorems/f00a2353-058c-42b6-ba1e-aa2cf1b3b4c6)
--   - [`holder_step`](https://prove2.me/theorems/a6c79680-7ffa-4ec5-b28a-2e9350b5db77)
--   - [`runMax_pow_lintegral_lt_top`](https://prove2.me/theorems/421f4987-079a-483b-8873-a3f60d5b510d)
--   - [`maximal_ineq_Lp`](https://prove2.me/theorems/3d6a746c-5b37-4dc6-83c9-71b26ca49833)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/MathFin/MathFin/Foundations/DoobLpMaximalInequality.lean) · `MathFin.Foundations.DoobLpMaximalInequality` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/raphaelrrcoelho/formal-mathfin/blob/784a8311f75a1519a23717856df9982bd6a9a370/MathFin/Foundations/DoobLpMaximalInequality.lean#L57-L62 (repository human-ai-mathematics/kls-lean, commit 408915f, module `MathFin.Foundations.DoobLpMaximalInequality`, definition bundle `KLSModular_MathFin_Foundations_DoobLpMaximalInequality`; the repository is private at upload time). Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.MeanInequalities

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal
namespace MeasureTheory
variable {Ω : Type*}
/-- Internal abbreviation for the running maximum
`max {f 0 ω, f 1 ω, …, f n ω}`. Kept `private`: the theorem
states the bound in terms of the explicit `Finset.sup'` form to match
`MeasureTheory.maximal_ineq`. -/
 def runMax (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k ↦ f k ω)
variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}
end MeasureTheory


