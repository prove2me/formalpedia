-- Prove2me | Definitions.Def_NSWBetter_WellBehaved
-- name    : NSWBetter_WellBehaved
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:54:48.830366+00:00
-- url     : https://prove2.me/theorems/cfbbb058-86a9-447e-9ae6-c0b46c0616c3
-- title:
--   Well-behaved instance (Properties A–E)
-- statement:
--   An instance with $\Delta$ identical agents, $\ell$ large goods and mean value $\mu$ (with round robin allocation $W$ and small bundles $S_i$) is **well-behaved** if
--   1. (A) $\ell/\Delta\in[1-\tfrac1e-\gamma,\ 1-\tfrac1e+\gamma]$;
--   2. (B) for all but at most $\gamma\Delta$ agents $i$, $v(S_i)\in[(1-\gamma)\mu,(1+\gamma)\mu]$;
--   3. (C) for all but at most $\gamma^2\Delta$ agents $i\le\ell$ (who receive the large good $g_i$), $v(S_i)<\gamma^2v(g_i)$;
--   4. (D) for all but at most $\gamma^2\Delta$ agents $i\le\ell$, $v(g_i)>\mu/\gamma$;
--   5. (E) for all agents $i$, $v(S_i)\ge10^{-4}\mu$.
--
--   Here $\gamma=10^{-10}$. Well-behaved instances are the worst case of the round robin allocation (Theorem 3.9).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 3, p.13 (Properties A–E)

import Mathlib
import Definitions.Def_NSWBetter_gamma
import Definitions.Def_NSWBetter_largeCount
import Definitions.Def_NSWBetter_meanVal
import Definitions.Def_NSWBetter_smallBundle
import Definitions.Def_NSWBetter_largeGood

namespace NSWBetter

open Classical in
/-- **Well-behaved instances.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 3, p.13: "we say that the instance I (and the corresponding round robin allocation W) is well-behaved if it satisfies the following properties: Property A ℓ/∆ ∈ [1 − 1/e − γ, 1 − 1/e + γ]. Property B For all but at most γ∆ agents i ∈ [∆], v(Si) ∈ [(1 − γ)µ, (1 + γ)µ]. Property C For all but at most γ²∆ agents i ∈ [ℓ] who receive a large good, v(Si) < γ²v(gi). Property D For all but at most γ²∆ agents i ∈ [ℓ] who receive a large good, v(gi) > µ/γ. Property E For all agents i ∈ [∆], v(Si) ≥ 10^−4 µ."

"For all but at most k agents" is: the number of agents violating the condition is `≤ k`. Agents are 0-based; agent `i < ℓ` receives the large good `g_i`. -/
def WellBehaved (Δ : ℕ) (s : Multiset ℝ) : Prop :=
  ((largeCount Δ s : ℝ) / Δ ∈
      Set.Icc (1 - 1 / Real.exp 1 - gamma) (1 - 1 / Real.exp 1 + gamma)) ∧
  ((Finset.univ.filter (fun i : Fin Δ => smallBundle Δ s i ∉
      Set.Icc ((1 - gamma) * meanVal Δ s) ((1 + gamma) * meanVal Δ s))).card : ℝ) ≤ gamma * Δ ∧
  ((Finset.univ.filter (fun i : Fin Δ => i.val < largeCount Δ s ∧
      ¬ smallBundle Δ s i < gamma ^ 2 * largeGood s i)).card : ℝ) ≤ gamma ^ 2 * Δ ∧
  ((Finset.univ.filter (fun i : Fin Δ => i.val < largeCount Δ s ∧
      ¬ meanVal Δ s / gamma < largeGood s i)).card : ℝ) ≤ gamma ^ 2 * Δ ∧
  ∀ i : Fin Δ, (1 / 10 ^ 4 : ℝ) * meanVal Δ s ≤ smallBundle Δ s i

end NSWBetter


