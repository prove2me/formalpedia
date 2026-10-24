-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnvelope
-- name    : KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnvelope
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:45:04.261957+00:00
-- url     : https://prove2.me/theorems/0e9d2b49-aaa5-460e-bb25-c2752fd1ef6c
-- title:
--   BKL cumulant envelope
-- statement:
--   `envelope K m` is the real-valued sequence $b_m=K^{m-1}((m-1)!)^2$ for $K,m\in\mathbb{R}\times\mathbb{N}$. It is a deterministic arithmetic expression used as an induction envelope; the definition alone asserts no cumulant estimate or KLS bound.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item T41. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L19-L20 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnvelope`, definition bundle `KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnvelope`; the repository is private at upload time).

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic

noncomputable section
namespace FunctionalInequalities
namespace KLS
namespace BKL
/-- The cumulant envelope `b_m = K^{m-1} ((m-1)!)²` of BKL (94). -/
def envelope (K : ℝ) (m : ℕ) : ℝ := K ^ (m - 1) * ((m - 1).factorial : ℝ) ^ 2
end BKL
end KLS
end FunctionalInequalities


