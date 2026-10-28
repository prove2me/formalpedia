-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoCutoff
-- name    : KLSModular_LevyStochCalc_Brownian_ItoCutoff
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:31:27.053128+00:00
-- url     : https://prove2.me/theorems/d791d26a-839e-4e82-822a-989d323afe06
-- title:
--   Itô cutoff functions and derivative vectors
-- statement:
--   Vendored from the upstream `LevyStochCalc` library at https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932` (Apache-2.0). For $f : (\mathrm{Fin}\,n \to \mathbb{R}) \to \mathbb{R}$ and radius $k$, `cutoffFun f k` multiplies $f$ by the smooth box cutoff `boxCut k`; `gradVec g z` records the first Fréchet derivative of $g$ at $z$ on the coordinate vectors, and `hessVec g z` records the corresponding second derivative coordinates. The auxiliary theorem `energy_lt_top_of_bounded` states that a pointwise bounded real integrand has finite $L^2$ energy, expressed as an `ENNReal` double integral over $\omega$ and $s \in [0,T]$ for every $T>0$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoFormula
--   import LevyStochCalc.Brownian.SmoothCutoff
--   import LevyStochCalc.Brownian.ItoLocality
--   import LevyStochCalc.Probability.ExitTime
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def cutoffFun (f : (Fin n → ℝ) → ℝ) (k : ℝ) : (Fin n → ℝ) → ℝ :=
--     fun z => f z * boxCut k z
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoFormula`](https://prove2.me/theorems/fd5fe3af-3527-442e-9c98-db6ff7b03e09), [`LevyStochCalc/Brownian/SmoothCutoff`](https://prove2.me/theorems/85fcd788-0ea4-412f-b77d-911eacf30754), [`LevyStochCalc/Brownian/ItoLocality`](https://prove2.me/theorems/24c85544-31a3-4ffd-a08e-f5b9ac9b8eba), [`LevyStochCalc/Probability/ExitTime`](https://prove2.me/theorems/afef0596-dfb2-4d26-a303-b02e54dda356).
--
--   Theorems in source order:
--
--   - [`IsVectorItoVersion.itoFormula_localise`](https://prove2.me/theorems/2fb489df-09de-4dc9-af35-c8013b4a86e5)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoCutoff.lean) · `LevyStochCalc.Brownian.ItoCutoff` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoCutoff.lean#L35-L257 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoCutoff`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoCutoff`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormula
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_SmoothCutoff
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLocality
import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoCutoff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
open scoped Topology
section Cutoff
variable {n : ℕ}
/-- The product of `f` with the smooth box cutoff of radius `k`. -/
noncomputable def cutoffFun (f : (Fin n → ℝ) → ℝ) (k : ℝ) : (Fin n → ℝ) → ℝ :=
  fun z => f z * boxCut k z
/-- The coordinates of the first derivative, as a vector. -/
noncomputable def gradVec (g : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun p => fderiv ℝ g z (Pi.single p 1)
/-- The coordinates of the second derivative, as a vector. -/
noncomputable def hessVec (g : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : Fin n × Fin n → ℝ :=
  fun pq => fderiv ℝ (fderiv ℝ g) z (Pi.single pq.1 1) (Pi.single pq.2 1)
end Cutoff
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
section Bounded
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
/-- A pointwise bounded integrand has finite energy on every window. -/
theorem energy_lt_top_of_bounded {K : Ω → ℝ → ℝ} {M : ℝ} (hM : ∀ ω s, |K ω s| ≤ M) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T _hT
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ((Real.toNNReal M : ℝ≥0) : ℝ≥0∞) ^ 2 := by
    intro ω s
    have h0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM ω s)
    have h1 : ‖K ω s‖₊ ≤ Real.toNNReal M := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M h0]
      simpa [Real.norm_eq_abs] using hM ω s
    exact pow_le_pow_left' (by exact_mod_cast h1) 2
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
          ((Real.toNNReal M : ℝ≥0) : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω => MeasureTheory.lintegral_mono fun s => hpt ω s
    _ < ⊤ := by
        simp only [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_Icc, measure_univ, mul_one]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ENNReal.ofReal_lt_top
end Bounded
end Ito
end Brownian
end LevyStochCalc


