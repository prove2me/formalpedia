-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
-- name    : KLS408915f_BrownianMotion_Auxiliary_ENNReal
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:04:50.710358+00:00
-- url     : https://prove2.me/theorems/41166a32-e1f0-4222-af5e-319ada829794
-- title:
--   Elementary ENNReal geometric-series bounds
-- statement:
--   Vendored from `RemyDegenne/brownian-motion` at commit `a7ad7af662044313bc80a7c0756360fb3745f931` under Apache-2.0. `ENNReal.sum_geometric_two_le` states that the finite geometric sum $\sum_{i<n}(1/2)^i$ in `ENNReal` is at most $2$, and the bundle also provides an order-preserving alias for converting the corresponding `ENat` inequality to `ENNReal`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/ENNReal.lean#L11-L13 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.ENNReal`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_ENNReal`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

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


