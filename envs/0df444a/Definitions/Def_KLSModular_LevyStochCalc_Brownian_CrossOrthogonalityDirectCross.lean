-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
-- name    : KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:05:30.252552+00:00
-- url     : https://prove2.me/theorems/fd42d764-e99f-4994-8020-f8822509f5ef
-- title:
--   Affine grid for Brownian cross-variation arguments
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `MultidimBrownianMotion.affineGrid a h k` is the arithmetic grid point $a+kh$ for $a,h\in\mathbb R$ and $k\in\mathbb N$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.MultidimFiltered
--   import LevyStochCalc.Brownian.AugmentedFiltration
--   import LevyStochCalc.Brownian.ItoFourthMoment
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def affineGrid (a h : ℝ) (k : ℕ) : ℝ := a + k * h
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/MultidimFiltered`](https://prove2.me/theorems/b4d1ac23-3fea-40f2-8621-83c034eb1b1a), [`LevyStochCalc/Brownian/AugmentedFiltration`](https://prove2.me/theorems/3cbf8b32-8c2c-4826-b624-2939bc0b44c4), [`LevyStochCalc/Brownian/ItoFourthMoment`](https://prove2.me/theorems/bcb038e3-f0ed-457a-b5d3-77a5f1cbd884).
--
--   Theorems in source order:
--
--   - [`integral_crossSum_sq`](https://prove2.me/theorems/ef40178c-963c-4c39-b6b5-7722afb01efd)
--   - [`integral_mul_increment_mul_increment_eq_crossSum`](https://prove2.me/theorems/27178f99-4152-4a50-8019-f02f8e023497)
--   - [`integral_mul_increment_mul_increment_eq_zero`](https://prove2.me/theorems/072f3669-7226-4448-b3cd-1af95cb1fa42)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean) · `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean#L69-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross`, definition bundle `KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
namespace Multidim
namespace MultidimBrownianMotion
section DirectCross
/-- The uniform grid `a, a + h, a + 2h, …`. -/
noncomputable def affineGrid (a h : ℝ) (k : ℕ) : ℝ := a + k * h
end DirectCross
end MultidimBrownianMotion
end Multidim
end Brownian
end LevyStochCalc


