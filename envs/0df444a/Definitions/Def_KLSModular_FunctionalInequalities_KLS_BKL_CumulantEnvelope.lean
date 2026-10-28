-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:58:43.348614+00:00
-- url     : https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7
-- title:
--   BKL cumulant envelope
-- statement:
--   `envelope K m` is the real-valued sequence $b_m=K^{m-1}((m-1)!)^2$ for $K,m\in\mathbb{R}\times\mathbb{N}$. It is a deterministic arithmetic expression used as an induction envelope; the definition alone asserts no cumulant estimate or KLS bound.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.SpecialFunctions.Pow.Real
--   import Mathlib.Analysis.SpecialFunctions.Sqrt
--   import Mathlib.Data.Nat.Choose.Basic
--   import Mathlib.Algebra.Order.BigOperators.Group.Finset
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def envelope (K : ℝ) (m : ℕ) : ℝ := K ^ (m - 1) * ((m - 1).factorial : ℝ) ^ 2
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`choose_mul_sqrt_envelope`](https://prove2.me/theorems/f0ee94f4-c2c1-45a3-acf2-8e29ffebda5f)
--   - [`sum_choose_mul_sqrt_envelope`](https://prove2.me/theorems/df3413be-ea97-45c4-9aa9-5f4083d525a8)
--   - [`absorption_le_envelope`](https://prove2.me/theorems/615a5017-49a3-413a-a89d-db3bf9fa1564)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean) · `FunctionalInequalities.KLS.BKL.CumulantEnvelope` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item T41. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L19-L20 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnvelope`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope`; the repository is private at upload time).

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
namespace FunctionalInequalities
namespace KLS
namespace BKL
/-- The cumulant envelope `b_m = K^{m-1} ((m-1)!)²` of BKL (94). -/
def envelope (K : ℝ) (m : ℕ) : ℝ := K ^ (m - 1) * ((m - 1).factorial : ℝ) ^ 2
end BKL
end KLS
end FunctionalInequalities


