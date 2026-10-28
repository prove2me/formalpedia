-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedSimple
-- name    : KLSModular_LevyStochCalc_Poisson_CompensatedSimple
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:43:02.462302+00:00
-- url     : https://prove2.me/theorems/e31661e6-5ece-4a83-a5a6-f85de245dba0
-- title:
--   Simple predictable compensated-Poisson integrands
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `Compensated.SimplePredictable` consists of a finite partition $0=t_0<t_1<\cdots<t_N\le T$, measurable mark sets $A_i\subseteq E$ of finite $\nu$-measure, and bounded measurable coefficients $\xi_i:\Omega\to\mathbb R$. `timeRect φ i t` is $(t_i\wedge t,t_{i+1}\wedge t]\times A_i$. `simpleIntegral N φ t` is the finite sum $$\sum_i\xi_i(\omega)\,\widetilde N(\mathrm{timeRect}(\phi,i,t))(\omega),$$ with the compensated evaluations defined using `toReal`.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Poisson.RandomMeasure
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure SimplePredictable
--       (Ω : Type u) [MeasurableSpace Ω]
--       (E : Type v) [MeasurableSpace E]
--       (ν : Measure E) [SigmaFinite ν]
--       (T : ℝ) where
--     /-- Number of partition pieces. -/
--     N : ℕ
--     /-- Time-partition points `0 = t_0 < t_1 < ⋯ < t_N ≤ T`. -/
--     partition : Fin (N + 1) → ℝ
--     partition_zero : partition 0 = 0
--     partition_le_T : partition (Fin.last N) ≤ T
--     partition_strictMono : StrictMono partition
--     /-- Mark sets `A_i ⊆ E`, each measurable with `ν(A_i) < ∞`. -/
--     A : Fin N → Set E
--     A_measurable : ∀ i : Fin N, MeasurableSet (A i)
--     A_finite : ∀ i : Fin N, ν (A i) ≠ ⊤
--     /-- Per-piece bounded coefficients `ξ_i : Ω → ℝ`. -/
--     ξ : Fin N → Ω → ℝ
--     ξ_bounded : ∀ i : Fin N, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M
--     ξ_measurable : ∀ i : Fin N, Measurable (ξ i)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Poisson/RandomMeasure`](https://prove2.me/theorems/92289c3b-28d6-4c67-9d55-ae3cfb38fcf3).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/CompensatedSimple.lean) · `LevyStochCalc.Poisson.CompensatedSimple` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedSimple.lean#L28-L328 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedSimple`, definition bundle `KLSModular_LevyStochCalc_Poisson_CompensatedSimple`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedSimple.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- A *simple predictable* integrand: a finite linear combination of
indicators on time-interval × measurable-set products. -/
structure SimplePredictable
    (Ω : Type u) [MeasurableSpace Ω]
    (E : Type v) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν]
    (T : ℝ) where
  /-- Number of partition pieces. -/
  N : ℕ
  /-- Time-partition points `0 = t_0 < t_1 < ⋯ < t_N ≤ T`. -/
  partition : Fin (N + 1) → ℝ
  partition_zero : partition 0 = 0
  partition_le_T : partition (Fin.last N) ≤ T
  partition_strictMono : StrictMono partition
  /-- Mark sets `A_i ⊆ E`, each measurable with `ν(A_i) < ∞`. -/
  A : Fin N → Set E
  A_measurable : ∀ i : Fin N, MeasurableSet (A i)
  A_finite : ∀ i : Fin N, ν (A i) ≠ ⊤
  /-- Per-piece bounded coefficients `ξ_i : Ω → ℝ`. -/
  ξ : Fin N → Ω → ℝ
  ξ_bounded : ∀ i : Fin N, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M
  ξ_measurable : ∀ i : Fin N, Measurable (ξ i)
/-- The time-rectangle `(t_i ∧ t, t_{i+1} ∧ t] × A_i` for the `i`-th piece
of the partition, evaluated at running time `t`. -/
noncomputable def SimplePredictable.timeRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ) : Set (ℝ × E) :=
  Set.Ioc (min (φ.partition i.castSucc) t) (min (φ.partition i.succ) t) ×ˢ φ.A i
/-- Integral of a simple predictable integrand against the compensated
Poisson random measure:

  `∑_i ξ_i · [N((t_i ∧ t, t_{i+1} ∧ t] × A_i)`
  `      − ((t_{i+1} ∧ t − t_i ∧ t)·ν(A_i))]`

Using the `compensated` field of the time-aware `PoissonRandomMeasure`. -/
noncomputable def simpleIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin φ.N,
    φ.ξ i ω * N.compensated (φ.timeRect i t) ω
end Compensated
end Poisson
end LevyStochCalc


