-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp
-- name    : KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:13:29.075396+00:00
-- url     : https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb
-- title:
--   Clamped coefficients for vector Itô processes
-- statement:
--   Vendored from the upstream `LevyStochCalc` library at https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932` (Apache-2.0). `clampCoeff H j` and `clampDrift b j` apply the scalar clamp `clampAt (j : ℝ)` pointwise to diffusion and drift coefficients, respectively. The bundle includes measurability and progressive-measurability results for the clamped diffusion coefficients, the pointwise bound $|\operatorname{clampCoeff}\,H\,j|\le j$, and finiteness of each clamped coefficient's `ENNReal` energy on $[0,T]$ when $T>0$. `clampMesh` is the sum over state coordinates of the drift and diffusion squared-energy discrepancies from the original coefficients, with the displayed factors $2$, $\operatorname{ofReal}(T)$, and $d$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.VectorItoProcessDiff
--   import LevyStochCalc.Brownian.ItoCutoff
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def clampCoeff (H : Fin n → Fin d → Ω → ℝ → ℝ) (j : ℕ) :
--       Fin n → Fin d → Ω → ℝ → ℝ := fun p k ω s => clampAt (j : ℝ) (H p k ω s)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/VectorItoProcessDiff`](https://prove2.me/theorems/cd1eb156-9d40-4d90-80b1-58b54714509a), [`LevyStochCalc/Brownian/ItoCutoff`](https://prove2.me/theorems/d791d26a-839e-4e82-822a-989d323afe06).
--
--   Theorems in source order:
--
--   - [`tendsto_energy_window_clamp`](https://prove2.me/theorems/cdd4a95d-5776-480a-ae2b-6a1001a8347e)
--   - [`lintegral_sq_norm_clampProcess_sub_le`](https://prove2.me/theorems/3cedae93-25d4-48aa-8734-4c7f786afa37)
--   - [`lintegral_sq_norm_version_clamp_sub_le`](https://prove2.me/theorems/6384e99c-cf6e-4a54-9bca-3a969c3bbe48)
--   - [`lintegral_window_sq_norm_version_clamp_sub_le`](https://prove2.me/theorems/c96d8a38-efbf-4a2e-a1e2-fc59d1d0efa6)
--   - [`tendsto_of_tendsto_sq_enorm`](https://prove2.me/theorems/98542836-cccb-4492-8290-6e6d19d114a0)
--   - [`exists_seq_ae_tendsto_of_tendsto_lintegral`](https://prove2.me/theorems/3562f88f-3c78-4ff5-ad93-01edc45ad90f)
--   - [`ae_ae_tendsto_version_clamp`](https://prove2.me/theorems/4b4b00a1-8893-4a14-9b71-7455375e4cb1)
--   - [`ae_tendsto_version_clamp_at`](https://prove2.me/theorems/749d431d-d8f1-44b6-ba64-5d3e7974a377)
--   - [`version_ae_eq_zero`](https://prove2.me/theorems/ee3afebe-ae0f-4c3f-aa5d-fab65a71b613)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean) · `LevyStochCalc.Ito.ItoFormulaUnboundedClamp` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L36-L95 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`, definition bundle `KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoProcessDiff
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoCutoff

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
section Clamped
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
/-- The diffusion matrix clamped at level `j`. -/
noncomputable def clampCoeff (H : Fin n → Fin d → Ω → ℝ → ℝ) (j : ℕ) :
    Fin n → Fin d → Ω → ℝ → ℝ := fun p k ω s => clampAt (j : ℝ) (H p k ω s)
/-- The drift clamped at level `j`. -/
noncomputable def clampDrift (b : Fin n → Ω → ℝ → ℝ) (j : ℕ) : Fin n → Ω → ℝ → ℝ :=
  fun p ω s => clampAt (j : ℝ) (b p ω s)
theorem measurable_clampCoeff {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k))) (j : ℕ) (p : Fin n) (k : Fin d) :
    Measurable (Function.uncurry (clampCoeff H j p k)) :=
  (continuous_clampAt (j : ℝ)).measurable.comp (hm p k)
theorem progressivelyMeasurable_clampCoeff {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)) (j : ℕ) (p : Fin n) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (clampCoeff H j p k) :=
  Probability.ProgressivelyMeasurable.comp_continuous (continuous_clampAt (j : ℝ))
    (clampAt_zero (Nat.cast_nonneg j)) (hp p k)
omit [MeasurableSpace Ω] in
theorem abs_clampCoeff_le (H : Fin n → Fin d → Ω → ℝ → ℝ) (j : ℕ)
    (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ) : |clampCoeff H j p k ω s| ≤ (j : ℝ) :=
  abs_clampAt_le (Nat.cast_nonneg j) _
theorem energy_clampCoeff_lt_top {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (j : ℕ) (p : Fin n) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampCoeff H j p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  energy_lt_top_of_bounded (fun ω s => abs_clampCoeff_le H j p k ω s) T hT
/-- The combination of energies that bounds the `L²` distance on `[0, T]` between a vector Itô
process and the one driven by its coefficients clamped at level `j`. -/
noncomputable def clampMesh (P : Measure Ω) (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (b : Fin n → Ω → ℝ → ℝ) (T : ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ p : Fin n, (2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
end Clamped
end Ito
end Brownian
end LevyStochCalc


