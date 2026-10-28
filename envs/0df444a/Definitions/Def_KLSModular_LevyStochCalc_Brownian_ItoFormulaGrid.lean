-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaGrid
-- name    : KLSModular_LevyStochCalc_Brownian_ItoFormulaGrid
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:11:01.140186+00:00
-- url     : https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f
-- title:
--   Uniform time grid and grid simple integrands
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `unifGrid T m i` is the grid point $iT/m$; when $m\ne0$, the grid starts at $0$, ends at $T$, has mesh $T/m$, and is strictly increasing when $T>0$. `SimplePredictable.ofUnifGrid` packages bounded measurable coefficients on the $m$ cells into a simple predictable integrand on $[0,T]$, with accompanying declarations exposing its partition, coefficients, and adaptedness condition.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoProcess
--   import LevyStochCalc.Brownian.RiemannSum
--   import LevyStochCalc.Brownian.ItoIncrementMoment
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def unifGrid (T : ℝ) (m : ℕ) (i : ℕ) : ℝ := (i : ℝ) * T / (m : ℝ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoProcess`](https://prove2.me/theorems/0e852a7e-a66b-4b2e-af71-2e5817bdbfa8), [`LevyStochCalc/Brownian/RiemannSum`](https://prove2.me/theorems/2b726e4a-2c86-4838-a0d1-c62388e10386), [`LevyStochCalc/Brownian/ItoIncrementMoment`](https://prove2.me/theorems/9d2f693b-1d18-45b2-b295-411fcadbdbe2).
--
--   Theorems in source order:
--
--   - [`exists_unifGrid_cell`](https://prove2.me/theorems/6498e1ec-297e-4445-a8b4-20374c8bb9d6)
--   - [`integral_abs_add_pow_three_le`](https://prove2.me/theorems/4a99bb18-8c7c-4d98-a0f3-3e51e759119b)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFormulaGrid.lean) · `LevyStochCalc.Brownian.ItoFormulaGrid` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFormulaGrid.lean#L44-L147 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFormulaGrid`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoFormulaGrid`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoProcess
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_RiemannSum
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaGrid.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The uniform grid on `[0, T]` with `m` cells. -/
noncomputable def unifGrid (T : ℝ) (m : ℕ) (i : ℕ) : ℝ := (i : ℝ) * T / (m : ℝ)
@[simp] theorem unifGrid_zero (T : ℝ) (m : ℕ) : unifGrid T m 0 = 0 := by simp [unifGrid]
theorem unifGrid_self {T : ℝ} {m : ℕ} (hm : m ≠ 0) : unifGrid T m m = T := by
  rw [unifGrid]
  field_simp
theorem unifGrid_succ_sub {T : ℝ} {m : ℕ} (hm : m ≠ 0) (i : ℕ) :
    unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [unifGrid, unifGrid]
  push_cast
  field_simp
  ring
theorem unifGrid_lt_succ {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0) (i : ℕ) :
    unifGrid T m i < unifGrid T m (i + 1) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have h := unifGrid_succ_sub (T := T) hm i
  have : 0 < T / (m : ℝ) := div_pos hT hm'
  linarith
/-- The simple integrand on the uniform grid of `[0, T]` with the given cell coefficients. -/
noncomputable def SimplePredictable.ofUnifGrid {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) : SimplePredictable Ω T where
  N := m
  partition := fun i => unifGrid T m (i : ℕ)
  partition_zero := by simp
  partition_le_T := le_of_eq (by simpa using unifGrid_self (T := T) hm)
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    simpa using unifGrid_lt_succ hT hm (i : ℕ)
  ξ := ξ
  ξ_bounded := hbdd
  ξ_measurable := hmeas
@[simp] theorem SimplePredictable.ofUnifGrid_partition {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin (m + 1)) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).partition i = unifGrid T m (i : ℕ) := rfl
@[simp] theorem SimplePredictable.ofUnifGrid_xi {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin m) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).ξ i = ξ i := rfl
theorem SimplePredictable.ofUnifGrid_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i)) :
    ∀ i : Fin (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).partition i.castSucc))
        ((SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).ξ i) := hadapt
end Ito
end Brownian
end LevyStochCalc


