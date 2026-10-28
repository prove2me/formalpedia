-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
-- name    : KLSModular_LevyStochCalc_Brownian_Construction
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:33:53.521477+00:00
-- url     : https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3
-- title:
--   Brownian motion structure
-- statement:
--   Vendored from the upstream LevyStochCalc repository at commit `984dbf0b790031eac05d56fe5a84b65e15e1e932` under Apache-2.0. `LevyStochCalc.Brownian.BrownianMotion P` packages an $\mathbb R$-indexed process on a probability space with measurable evaluations and jointly measurable paths, almost-sure zero initial value, Gaussian increments $\mathcal N(0,t-s)$ for $0≤s<t$, almost-surely continuous paths, zero values for negative times, and sigma-algebra-level independence between the past through time $s$ and the increment from $s$ to $t$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Basic
--   import Mathlib.Probability.Distributions.Gaussian.Real
--   import Mathlib.Probability.Independence.Basic
--   import Mathlib.Probability.Kernel.Defs
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Opening lines and body omitted; this is not the complete declaration.
--
--   ```lean
--     needed to apply `MeasureTheory.condExp_indep_eq` to derive the
--     conditional-expectation identities `𝔼[W_t − W_s | ℱ_s] = 0` and
--     `𝔼[(W_t − W_s)² | ℱ_s] = t − s`.
--     For Brownian motion this follows from joint Gaussianity; we package it as
--     a structural hypothesis since the eventual `BrownianMotion.exists` will
--     provide it directly via `iIndepFun_pi` on the increment family. -/
--     joint_increment_independent :
--       ∀ {s t : ℝ}, 0 ≤ s → s < t →
--         ProbabilityTheory.Indep
--           (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W j) inferInstance)
--           (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance)
--           P
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Basic`](https://prove2.me/theorems/0adc36c3-8b48-4256-a1bd-556fe85cdbbb).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/Construction.lean) · `LevyStochCalc.Brownian.Construction` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/Construction.lean#L37-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.Construction`, definition bundle `KLSModular_LevyStochCalc_Brownian_Construction`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Construction.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A *Brownian motion* on the probability space `(Ω, P)`: an `ℝ`-indexed
process (interpreted on `t ≥ 0`) with the three defining properties (zero
start, Gaussian independent increments, continuous paths a.s.). -/
structure BrownianMotion (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- The path map `(t, ω) ↦ W_t(ω)`. -/
  W : ℝ → Ω → ℝ
  /-- For each `t : ℝ`, `ω ↦ W_t(ω)` is measurable. -/
  measurable_eval : ∀ t : ℝ, Measurable (W t)
  /-- The path map is jointly measurable in `(t, ω)`. Required for the
  L²-Itô integral against `W` (Karatzas-Shreve §3.2 implicitly assumes
  this). The Wiener-measure construction delivers this directly via the
  projective limit's product σ-algebra. -/
  joint_measurable : Measurable (Function.uncurry W)
  /-- `W₀ = 0` almost surely under `P`. -/
  initial_zero : ∀ᵐ ω ∂P, W 0 ω = 0
  /-- For `0 ≤ s < t`, the law of the increment `W_t − W_s` is `𝒩(0, t − s)`. -/
  increment_gaussian :
    ∀ {s t : ℝ} (_hs : 0 ≤ s) (hst : s < t),
      P.map (fun ω => W t ω - W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩
  /-- Almost surely, `t ↦ W_t(ω)` is continuous on `[0, ∞)`. -/
  continuous_paths : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => W t ω)
  /-- For `s < 0`, the structure extends `W` trivially: `W_s = 0` almost surely.
  This is a convention that makes the natural filtration well-defined for all
  real `s` and lets `(W_s)_{s ≥ 0}` be viewed as an `ℝ`-indexed process. -/
  negative_zero : ∀ s : ℝ, s < 0 → ∀ᵐ ω ∂P, W s ω = 0
  /-- **σ-algebra-level joint independence of past and future increment.** For
  `0 ≤ s < t`, the σ-algebra `⨆ u ≤ s, σ(W_u)` (which is the natural filtration
  at time `s`) is independent of `σ(W_t − W_s)`. This is strictly stronger than
  the derived pairwise statement `BrownianMotion.increment_independent` and is
  needed to apply `MeasureTheory.condExp_indep_eq` to derive the
  conditional-expectation identities `𝔼[W_t − W_s | ℱ_s] = 0` and
  `𝔼[(W_t − W_s)² | ℱ_s] = t − s`.
  For Brownian motion this follows from joint Gaussianity; we package it as
  a structural hypothesis since the eventual `BrownianMotion.exists` will
  provide it directly via `iIndepFun_pi` on the increment family. -/
  joint_increment_independent :
    ∀ {s t : ℝ}, 0 ≤ s → s < t →
      ProbabilityTheory.Indep
        (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W j) inferInstance)
        (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance)
        P
end Brownian
end LevyStochCalc


