-- Prove2me | Definitions.Def_LLMThroughput_TokenBudget_Supplement_BatchTime
-- name    : LLMThroughput_TokenBudget_Supplement_BatchTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:02:58.310953+00:00
-- url     : https://prove2.me/theorems/a1b55e2e-d01a-41a1-ba70-0abf2bd33432
-- title:
--   Real-cost batch processing time, Eq. (4)
-- statement:
--   Let $a,c,b_0,s$ be real numbers. The batch processing time is
--
--   $$t_s=c+a\lceil s/b_0\rceil.$$
--
--   The geometric results use $a>0$, $c\ge0$, $b_0>0$ and nonnegative loads. The ceiling takes its ordinary integer value and is then included in the real numbers. This definition supplies the common processing-time formula for both added results, without the published queue model's integer-slot restriction on costs.
--
--   **Formalization Note** The definition is total; the stated results restrict its parameters. At $s=0$ it returns $c$. On invalid inputs it still evaluates this same formula using Lean's real division convention, including $s/0=0$; no result uses $b_0=0$.
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, p. 10, Eq. (4); p. 11, Assumption 1; p. 48, Lemma 24

import Mathlib

namespace LLMThroughput.TokenBudget.Supplement

/-- Equation (4), with real processing costs. At zero load this is `c`.
The integer ceiling is cast to the reals before multiplication. -/
noncomputable def batchTime (a c b0 s : ℝ) : ℝ :=
  c + a * (⌈s / b0⌉ : ℤ)

end LLMThroughput.TokenBudget.Supplement


