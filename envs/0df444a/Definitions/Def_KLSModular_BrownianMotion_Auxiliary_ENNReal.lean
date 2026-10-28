-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_ENNReal
-- name    : KLSModular_BrownianMotion_Auxiliary_ENNReal
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:34:29.03986+00:00
-- url     : https://prove2.me/theorems/171cbd8b-7a32-47c8-8ad9-ffaf31ca7bf0
-- title:
--   Elementary ENNReal geometric-series bounds
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `ENNReal.sum_geometric_two_le` states that the finite geometric sum $\sum_{i<n}(1/2)^i$ in `ENNReal` is at most $2$, and the bundle also provides an order-preserving alias for converting the corresponding `ENat` inequality to `ENNReal`.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   lemma sum_geometric_two_le (n : ℕ) : ∑ i ∈ Finset.range n, ((1 : ENNReal) / 2) ^ i ≤ 2 := by
--     rw [← ENNReal.toReal_le_toReal (by simp) (by simp), toReal_ofNat, toReal_sum (by simp)]
--     simpa [-one_div] using _root_.sum_geometric_two_le _
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/ENNReal.lean) · `BrownianMotion.Auxiliary.ENNReal` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/ENNReal.lean#L11-L13 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.ENNReal`, definition bundle `KLSModular_BrownianMotion_Auxiliary_ENNReal`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/ENNReal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ENNReal
namespace ENNReal
lemma sum_geometric_two_le (n : ℕ) : ∑ i ∈ Finset.range n, ((1 : ENNReal) / 2) ^ i ≤ 2 := by
  rw [← ENNReal.toReal_le_toReal (by simp) (by simp), toReal_ofNat, toReal_sum (by simp)]
  simpa [-one_div] using _root_.sum_geometric_two_le _
end ENNReal
@[gcongr]
alias ⟨_, ENat.toENNReal_le'⟩ := ENat.toENNReal_le


