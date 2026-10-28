-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
-- name    : KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:10:24.462837+00:00
-- url     : https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4
-- title:
--   Continuous adapted version of a vector Itô process
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `IsVectorItoVersion X₀ bdrift X` records that $X:\mathbb R\to\Omega\to(\mathrm{Fin}\,n\to\mathbb R)$ has continuous sample paths, is strongly measurable with respect to the filtration at every time, and agrees $P$-almost everywhere at every nonnegative time with `vectorItoProcess`. Its generated projection and recursion declarations are the standard structure operations.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoProcess
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure IsVectorItoVersion (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
--       (X : ℝ → Ω → Fin n → ℝ) : Prop where
--     /-- every path is continuous -/
--     continuous_path : ∀ ω : Ω, Continuous fun t => X t ω
--     /-- the process is adapted -/
--     adapted : ∀ t : ℝ, @MeasureTheory.StronglyMeasurable Ω (Fin n → ℝ) _ (ℱ t) (X t)
--     /-- at each nonnegative time it agrees almost surely with the vector Itô process -/
--     ae_eq : ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcessVersion.lean) · `LevyStochCalc.Brownian.VectorItoProcessVersion` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcessVersion.lean#L51-L60 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcessVersion`, definition bundle `KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorVersion
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
/-- A continuous adapted `Fin n → ℝ`-valued process agreeing at each nonnegative time with the
vector Itô process `X₀ + ∫ b ds + ∑ₖ ∫ H^{·,k} dWᵏ`. -/
structure IsVectorItoVersion (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
    (X : ℝ → Ω → Fin n → ℝ) : Prop where
  /-- every path is continuous -/
  continuous_path : ∀ ω : Ω, Continuous fun t => X t ω
  /-- the process is adapted -/
  adapted : ∀ t : ℝ, @MeasureTheory.StronglyMeasurable Ω (Fin n → ℝ) _ (ℱ t) (X t)
  /-- at each nonnegative time it agrees almost surely with the vector Itô process -/
  ae_eq : ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
end VectorVersion
end Ito
end Brownian
end LevyStochCalc


