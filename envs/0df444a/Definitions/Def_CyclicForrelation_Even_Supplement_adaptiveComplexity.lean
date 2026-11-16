-- Prove2me | Definitions.Def_CyclicForrelation_Even_Supplement_adaptiveComplexity
-- name    : CyclicForrelation_Even_Supplement_adaptiveComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:46:42.831477+00:00
-- url     : https://prove2.me/theorems/c1fe0148-754b-44a8-abab-35d8697a652f
-- title:
--   Least achievable adaptive query cost for cyclic Forrelation
-- statement:
--   For $n,k\in\mathbb N$, let $N=2^n$ and let $T_k(f)=N^{-1}\operatorname{Tr}(D_{f_1}H\cdots D_{f_k}H)$ be the published cyclic trace on all $k$-tuples of sign functions on $\mathbb F_2^n$. Query locations form $Q=\{0,\ldots,k-1\}\times\mathbb F_2^n$. A cost $q\in\mathbb N$ is **adaptively achievable** at accuracy $\varepsilon$ and success $p$ if some private-randomness adaptive real-output algorithm makes at most $q$ total queries on every input and every seed and estimates $T_k$ with probability at least $p$ separately on every input.
--
--   For $\varepsilon\ge0$, the **adaptive complexity** is the actual least achievable cost:
--   $$R^{\mathrm{ad}}_\varepsilon(T_k)=\min\{q\in\mathbb N:\ q\text{ is adaptively achievable at }(\varepsilon,2/3)\}.$$
--   Exhaustive evaluation is a genuine algorithm with cost $kN$ and exact output. The feasibility proof precedes the minimum, ensuring its defining set is nonempty for every $n,k$ and $\varepsilon\ge0$.
--
--   This definition supplies the operational quantity bounded in Theorem 16. It contains no collision assumption, lower-bound certificate or restriction to planted inputs.
--
--   **Formalization Note** The minimum is `Nat.find` applied to proved exhaustive feasibility. Negative accuracies are outside the source domain and are assigned complexity zero. The trace, cube, sign encoding and input tuples are the published base definitions.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 4, §1.1 and footnote 2; p. 21, Theorem 16

import Definitions.Def_CyclicForrelation_Even_Supplement_adaptiveModel
import Definitions.Def_CyclicForrelation_Even_cyclicTrace

namespace CyclicForrelation.Even.Supplement

/-- Existence of a bounded adaptive algorithm estimating the cyclic trace. -/
def AdaptiveAchievable (n k : ℕ) (ε p : ℝ) (q : ℕ) : Prop :=
  ∃ A : AdaptiveAlgorithm (Fin k × Cube n),
    AdaptiveCostAtMost A q ∧ AdaptiveEstimates A (traceTarget n k) ε p

theorem adaptiveAchievable_nonempty (n k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ q, AdaptiveAchievable n k ε (2 / 3) q :=
  ⟨Fintype.card (Fin k × Cube n), adaptiveExhaustive (traceTarget n k),
    adaptive_exhaustive_feasible (traceTarget n k) ε (2 / 3) hε (by norm_num)⟩

/-- `R^ad_ε(T_k)`: least worst-case total adaptive cost at success 2/3 on every input.
For negative accuracies only, return zero outside the source's domain. -/
noncomputable def adaptiveComplexity (n k : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if hε : 0 ≤ ε then Nat.find (adaptiveAchievable_nonempty n k ε hε) else 0

end CyclicForrelation.Even.Supplement


