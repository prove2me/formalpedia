-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess
-- name    : KLSModular_LevyStochCalc_Brownian_VectorItoProcess
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:09:26.764008+00:00
-- url     : https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977
-- title:
--   Vector Itô process and coordinate integrals
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For a $d$-dimensional Brownian motion with coordinates satisfying `IsBrownianFiltration`, a coefficient array $H_{m,k}(\omega,s)$, and the stated measurability, progressive-measurability, and finite $L^2$-energy assumptions, `coordItoIntegral` is the Itô integral of $H_{m,k}$ against coordinate $k$, and `vectorItoMartingale` sums these integrals over $k<d$. `vectorItoProcess` is the $\mathrm{Fin}\,n\to\mathbb R$-valued process $X_0+\int_{[0,t]}b_s\,ds+\sum_k\int_0^tH^{\cdot,k}_s\,dW^k_s$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoProcess
--   import LevyStochCalc.Brownian.MultidimFiltered
--   import Mathlib.Algebra.Order.Chebyshev
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) (ω : Ω) : ℝ :=
--     stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k) (hHs m k) t ω
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoProcess`](https://prove2.me/theorems/0e852a7e-a66b-4b2e-af71-2e5817bdbfa8), [`LevyStochCalc/Brownian/MultidimFiltered`](https://prove2.me/theorems/b4d1ac23-3fea-40f2-8621-83c034eb1b1a).
--
--   Theorems in source order:
--
--   - [`integrable_abs_sum_and_le`](https://prove2.me/theorems/17bd37cc-5804-4e07-8559-5fe19077a354)
--   - [`integrable_sq_sum_and_le`](https://prove2.me/theorems/d4b79fef-61af-4942-9baf-cd68b6846eef)
--   - [`integrable_abs_sum_pow_three`](https://prove2.me/theorems/48f45feb-9f6f-43a8-836d-11f12b473c4e)
--   - [`integrable_sq_add_and_le`](https://prove2.me/theorems/84c68f33-8dc4-400b-b0e0-ff74d29b1e54)
--   - [`integrable_abs_add_and_le`](https://prove2.me/theorems/ee1f9d4b-e8aa-494d-8fe1-af42c7a5d32e)
--   - [`integral_sq_vectorItoMartingale_sub_le`](https://prove2.me/theorems/d36fc9ed-f7c1-4780-bf4d-334940405111)
--   - [`integral_abs_vectorItoMartingale_sub_le`](https://prove2.me/theorems/8b157a78-e3e6-4128-ac91-5b7ce7b8fb41)
--   - [`measurable_vectorItoProcess_sub`](https://prove2.me/theorems/a8a3a0c4-bf0d-4b14-81c4-23f97e4dcb97)
--   - [`integral_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/8034fbf3-4cec-4cc1-8421-d12baf9f25de)
--   - [`integral_sq_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/4ad59ff0-71f2-424a-9d06-361263c34b7c)
--   - [`integrable_norm_vectorItoProcess_sub_pow_three`](https://prove2.me/theorems/4ebc222e-11b8-4943-afb1-b14792258eba)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean) · `LevyStochCalc.Brownian.VectorItoProcess` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L217-L230 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, definition bundle `KLSModular_LevyStochCalc_Brownian_VectorItoProcess`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoProcess
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MultidimFiltered
import Mathlib.Algebra.Order.Chebyshev

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorProcess
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
/-- The Itô integral of the `(m, k)` entry of the diffusion matrix against the `k`-th Brownian
coordinate. -/
noncomputable def coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) (ω : Ω) : ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k) (hHs m k) t ω
/-- The martingale part of the `m`-th coordinate of a vector Itô process. -/
noncomputable def vectorItoMartingale (m : Fin n) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin d, coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t ω
/-- The vector Itô process `X_t = X₀ + ∫_{[0,t]} b_s ds + ∑ₖ ∫_0^t H^{·,k}_s dWᵏ_s`. -/
noncomputable def vectorItoProcess (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
    (t : ℝ) (ω : Ω) : Fin n → ℝ := fun m =>
  X₀ ω m + (∫ s in Set.Icc (0 : ℝ) t, bdrift m ω s ∂volume)
    + vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t ω
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
end VectorProcess
end Ito
end Brownian
end LevyStochCalc


