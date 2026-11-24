-- Prove2me | Definitions.Def_LLMThroughput_TokenBudget_Supplement_NecessaryCondition9
-- name    : LLMThroughput_TokenBudget_Supplement_NecessaryCondition9
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:03:30.800157+00:00
-- url     : https://prove2.me/theorems/a44e3ee4-65a3-4d54-9b57-16d34eca7c17
-- title:
--   Common subprobability time allocation, Eqs. (33)–(34)
-- statement:
--   Let $b_{\max},k_{\max}$ be positive integer token and request budgets, and let $t_s=c+a\lceil s/b_0\rceil$ with positive integer $b_0$, real $a>0$ and $c\ge0$. Define the mixed-batch index set and the allocation set by
--
--   $$M=\{(x,y)\in\mathbb N^2:x+y\le b_{\max},\ y<k_{\max}\},\qquad S=M\cup\{(0,k_{\max})\}.$$
--
--   For real arrival rates $\lambda_p,\lambda_d$, the necessary-condition predicate means that there are weights $u_s\ge0$ for $s\in S$ such that
--
--   $$\sum_{s\in S}u_s\le1,\qquad
--   \lambda_p\le\sum_{(x,y)\in M}\frac{x}{t_{x+y}}u_{x,y},\qquad
--   \lambda_d\le\sum_{(x,y)\in M}\frac{y}{t_{x+y}}u_{x,y}+\frac{k_{\max}}{t_{k_{\max}}}u_{0,k_{\max}}.$$
--
--   The same weights satisfy both inequalities. This is the algebraic necessary relaxation from Condition 9, rather than a definition of stochastic stability or a sufficient stability condition. Unused mass is idle time; the empty batch contributes zero, including when $c=0$.
--
--   **Formalization Note** Weights are functions on natural pairs, but only their values on the finite set $S$ are constrained or used. Any witness can be extended by zero outside $S$, giving exactly the source's nonnegative subprobability vector. Natural numbers include zero. No bounds on individual prefill request sizes are imposed. Outside the admissible budget domain the same finite formulas remain defined; they have no scheduling interpretation asserted here.
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, p. 27, Condition 9, Eqs. (33)–(34)

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Supplement_BatchTime

open scoped BigOperators

namespace LLMThroughput.TokenBudget.Supplement

/-- The mixed-batch summation domain in (33)--(34), including pure prefill
and the empty batch. No restriction on individual prefill request sizes. -/
def mixedBatches (bmax kmax : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (bmax + 1)).product (Finset.range kmax)).filter
    (fun s => s.1 + s.2 ≤ bmax)

/-- Only these coordinates of the time allocation can contribute. For
positive `kmax`, the inserted decode-only batch is not a mixed batch. -/
def allocationBatches (bmax kmax : ℕ) : Finset (ℕ × ℕ) :=
  insert (0, kmax) (mixedBatches bmax kmax)

/-- The simultaneous inequalities (33)--(34). Weights outside the finite
allocation domain are immaterial and may be zeroed. The same nonnegative
weights witness both bounds; unused mass is idle time. Real division assigns
zero contribution to the empty batch, also when `c = 0`. -/
noncomputable def NecessaryCondition9 (a c : ℝ) (b0 bmax kmax : ℕ)
    (lambdaP lambdaD : ℝ) : Prop :=
  ∃ u : ℕ × ℕ → ℝ,
    (∀ s ∈ allocationBatches bmax kmax, 0 ≤ u s) ∧
    (∑ s ∈ allocationBatches bmax kmax, u s) ≤ 1 ∧
    lambdaP ≤ ∑ s ∈ mixedBatches bmax kmax,
      (s.1 : ℝ) / batchTime a c (b0 : ℝ) ((s.1 : ℝ) + (s.2 : ℝ)) * u s ∧
    lambdaD ≤ (∑ s ∈ mixedBatches bmax kmax,
      (s.2 : ℝ) / batchTime a c (b0 : ℝ) ((s.1 : ℝ) + (s.2 : ℝ)) * u s) +
      (kmax : ℝ) / batchTime a c (b0 : ℝ) (kmax : ℝ) * u (0, kmax)

end LLMThroughput.TokenBudget.Supplement


