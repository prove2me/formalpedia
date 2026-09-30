-- Prove2me | Definitions.Def_SpecActions_model
-- name    : SpecActions_model
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-10T18:41:50.606009+00:00
-- url     : https://prove2.me/theorems/74860c85-efa8-42ba-ad0b-5153f14a69d8
-- title:
--   Speculative actions: the cost--latency model
-- statement:
--   The formal model underlying the cost--latency analysis of *Speculative Actions* (ICLR 2026), §5 and Appendices A, C.
--
--   An agentic system runs for a horizon of $T$ steps. At each step an **actor** issues a real API call with latency $\mathrm{Exp}(\beta)$ while a **speculator** guesses the action with latency $\mathrm{Exp}(\alpha)$; a guess implies the correct next call with probability $p$, independently across steps.
--
--   The bundle defines: $p(k)=1-(1-p)^k$, the probability at least one of $k$ branches hits (`phit`); the expected hit count $S_n$ and its claimed closed form (`hits`, `hitsClosed`); the expected latency and token cost of sequential and speculative execution in the breadth regime (`seqTime`, `specTime`, `seqCost`, `specCost`); their depth-regime analogues under deterministic latencies $a$ and $b<a$ (`depthSeqTime`, `depthSpecTime`, `depthSeqCost`, `depthSpecCost`); and the confidence-aware quantities $q(m)$, $\delta q(m)$ and the per-window objective $q(m)\Delta-cm$ (`qhit`, `dqhit`, `specObjective`).
--
--   Following the paper's own proofs, the expected latency and cost are *defined* by the expressions Appendix A derives for them; the theorems then assert the algebraic and asymptotic identities relating them.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, §5 (pp. 9-10) and Appendices A, C (pp. 13-14, 19-24)

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic

/-!
# Speculative actions: the cost–latency model

The model underlying the cost–latency analysis of *Speculative Actions: A
Lossless Framework for Faster Agentic Systems* (ICLR 2026), §5 and
Appendices A, C.

An agentic system runs for a horizon of `T` steps.  At each step an *actor*
issues a real API call whose latency is `Exp(β)`, while a *speculator*
guesses the action with latency `Exp(α)`, `β < α`.  A guess implies the
correct next call with probability `p`, independently across steps.
-/

namespace SpecActions

/-! ## Breadth-focused speculation (Algorithm 1) -/

/-- `phit k p = 1 - (1 - p) ^ k`: the probability that at least one of `k`
independent speculative branches implies the correct next call.  Written
`p(k)` in the paper. -/
noncomputable def phit (k : ℕ) (p : ℝ) : ℝ := 1 - (1 - p) ^ k

/-- Expected number of speculation hits by round `n` (`S n` in Appendix A).
A hit consumes the following round's speculation window, which gives the
two-term recursion
`S 0 = 0`, `S 1 = p`, `S (n+2) = p (1 + S n) + (1 - p) S (n+1)`. -/
noncomputable def hits (p : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => p
  | (n + 2) => p * (1 + hits p n) + (1 - p) * hits p (n + 1)

/-- The closed form that Appendix A derives for `hits`:
`S n = p/(1+p) · n + p²/(1+p)² · (1 - (-p)^n)`. -/
noncomputable def hitsClosed (p : ℝ) (n : ℕ) : ℝ :=
  p / (1 + p) * n + p ^ 2 / (1 + p) ^ 2 * (1 - (-p) ^ n)

/-- Expected runtime of strictly sequential execution: each of the `T` steps
costs one real API call of mean latency `1 / β`. -/
noncomputable def seqTime (T : ℕ) (β : ℝ) : ℝ := T / β

/-- Expected runtime of Algorithm 1: the sequential runtime less the expected
saving, namely `S (T-1)` hits each saving `E[(B - A)⁺] = α / (β(α+β))`. -/
noncomputable def specTime (T : ℕ) (α β pk : ℝ) : ℝ :=
  T / β - hits pk (T - 1) * (α / (β * (α + β)))

/-- Token-cost proxy for sequential execution (fixed tokens per unit time). -/
noncomputable def seqCost (T : ℕ) (β : ℝ) : ℝ := T / β

/-- Token-cost proxy for Algorithm 1.  `kt` is `k̃`, the number of *distinct*
actions across the `k` speculative branches (duplicates are killed). -/
noncomputable def specCost (T : ℕ) (α β pk kt : ℝ) : ℝ :=
  T / β * (kt + 1) - hits pk (T - 1) * (kt * (1 / β) + α / (β * (α + β)))

/-! ## Depth-focused speculation -/

/-- Sequential runtime when the real API latency is deterministically `a`. -/
noncomputable def depthSeqTime (T : ℕ) (a : ℝ) : ℝ := a * T

/-- Runtime of the depth-focused policy: `a·T + (T-1)·p·(b - a)`. -/
noncomputable def depthSpecTime (T : ℕ) (a b p : ℝ) : ℝ :=
  a * T + (T - 1) * p * (b - a)

/-- Sequential token cost with deterministic real latency `a`. -/
noncomputable def depthSeqCost (T : ℕ) (a : ℝ) : ℝ := a * T

/-- Token cost of the depth-focused policy.  A step whose guess is correct
spends `a + ⌊a/b⌋·b`; a step whose guess is wrong also pays for the branches
spawned before the real response arrived, the series
`a + (a - b) + ⋯ + (a - ⌊a/b⌋·b)`. -/
noncomputable def depthSpecCost (T : ℕ) (a b p : ℝ) : ℝ :=
  a + (T - 1) *
    (p * (a + ⌊a / b⌋ * b) +
      (1 - p) * (a * (⌊a / b⌋ + 1) - (1 + ⌊a / b⌋) * ⌊a / b⌋ / 2 * b))

/-! ## Confidence-aware selective speculation -/

/-- `qhit pv m = 1 - ∏_{j < m} (1 - pv j)`: probability of obtaining a cached
action when the top `m` branches are launched, where `pv` lists the realized
per-branch confidences in descending order. -/
noncomputable def qhit (pv : ℕ → ℝ) (m : ℕ) : ℝ :=
  1 - ∏ j ∈ Finset.range m, (1 - pv j)

/-- Marginal gain in hit probability from launching one more branch:
`δq(m) = (∏_{j<m} (1 - pv j)) · pv m`. -/
noncomputable def dqhit (pv : ℕ → ℝ) (m : ℕ) : ℝ :=
  (∏ j ∈ Finset.range m, (1 - pv j)) * pv m

/-- The per-window objective `q(m) · Δ - c·m` maximized by the optimal
speculative breadth. -/
noncomputable def specObjective (pv : ℕ → ℝ) (Δ c : ℝ) (m : ℕ) : ℝ :=
  qhit pv m * Δ - c * m

end SpecActions


