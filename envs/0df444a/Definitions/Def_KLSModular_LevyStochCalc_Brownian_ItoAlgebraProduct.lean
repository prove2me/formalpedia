-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct
-- name    : KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:27:01.80868+00:00
-- url     : https://prove2.me/theorems/99205bea-847c-43ba-a041-1e0384d4d19c
-- title:
--   Products and elementary integrals of simple integrands
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `SimplePredictable.mul_on_common` constructs the product of two bounded simple integrands on their merged common partition, assuming their final partition points agree. `SimplePredictable.integralAgainst` is the finite sum of coefficient-weighted increments of an arbitrary real process over the truncated partition intervals. The bundle contains these constructions only, while the module documentation describes their use in later elementary-integral identities.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   noncomputable def SimplePredictable.mul_on_common
--       {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
--       (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
--       SimplePredictable Ω T
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand`](https://prove2.me/theorems/09c55224-b261-4948-9982-f2ec68361149).
--
--   Theorems in source order:
--
--   - [`sum_ite_mul_sum_ite`](https://prove2.me/theorems/7b3182dd-5410-4504-8fdb-fdf2d08f8bb4)
--   - [`SimplePredictable.eval_mul_on_common`](https://prove2.me/theorems/0eb3f171-e89b-4176-adbc-20be9554ddb1)
--   - [`SimplePredictable.sum_xi_mul_simpleIntegral_sub`](https://prove2.me/theorems/dfbfbaef-e395-42fa-a4db-142dc1f926ee)
--   - [`SimplePredictable.appendInterval_integralAgainst`](https://prove2.me/theorems/9a670acc-4886-40c7-9771-97961383f589)
--   - [`SimplePredictable.exists_mul_simple`](https://prove2.me/theorems/2d890f64-d894-41e2-b8b4-bc4a0edaf483)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraProduct.lean) · `LevyStochCalc.Brownian.ItoAlgebraProduct` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraProduct.lean#L60-L228 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraProduct`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The product of two simple integrands, carried on their common refinement. -/
noncomputable def SimplePredictable.mul_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T where
  N := H₁.mergedM H₂
  partition := H₁.mergedπ H₂
  partition_zero := H₁.mergedπ_zero H₂
  partition_le_T := (H₁.mergedπ_last H₂ h_eq) ▸ H₁.partition_le_T
  partition_strictMono := H₁.mergedπ_strictMono H₂
  ξ := fun j ω => H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
    * H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω
  ξ_bounded := fun j => by
    obtain ⟨C₁, hC₁⟩ := H₁.ξ_bounded (H₁.mergedIdxMap_left H₂ h_eq j)
    obtain ⟨C₂, hC₂⟩ := H₂.ξ_bounded (H₁.mergedIdxMap_right H₂ h_eq j)
    refine ⟨max C₁ 0 * max C₂ 0, fun ω => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hC₁ ω).trans (le_max_left _ _)) ((hC₂ ω).trans (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)
  ξ_measurable := fun j =>
    (H₁.ξ_measurable _).mul (H₂.ξ_measurable _)
/-- The elementary integral of a simple integrand against an arbitrary process. -/
noncomputable def SimplePredictable.integralAgainst {T : ℝ} (G : SimplePredictable Ω T)
    (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin G.N, G.ξ i ω *
    (M (min (G.partition i.succ) t) ω - M (min (G.partition i.castSucc) t) ω)
end Ito
end Brownian
end LevyStochCalc


