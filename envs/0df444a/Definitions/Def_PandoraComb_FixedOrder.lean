-- Prove2me | Definitions.Def_PandoraComb_FixedOrder
-- name    : PandoraComb_FixedOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:33.819185+00:00
-- url     : https://prove2.me/theorems/00dca68b-736d-4374-b612-4c64a515417f
-- title:
--   Fixed order strategies and fixed order strategies with thresholds $(\sigma,t)$
-- statement:
--   Let $n=|\iota|$ and let $\sigma$ be an ordering of the boxes, $\sigma(0),\dots,\sigma(n-1)$.
--
--   1. A strategy has **fixed order** $\sigma$ if at every round $k$, after it has opened $\sigma(0),\dots,\sigma(k-1)$ in this order, it either opens $\sigma(k)$ or halts, whatever the observed values and the seed.
--   2. The **fixed order strategy with thresholds** $t_0,\dots,t_{n-1}\in\mathbb R\cup\{\pm\infty\}$ and order $\sigma$ halts at round $k$ if and only if
--   $$t_k\ \le\ \max\Big(0,\ \max_{j<k}V_{\sigma(j)}\Big),$$
--   and otherwise opens $\sigma(k)$; after $n$ rounds it halts. The maximum so far is $0$ before any box is opened.
--
--   These are the strategies of Observation 1 and Theorem 4.1: the theorem asserts that, for submodular costs, one of the threshold strategies is optimal among all strategies.
--
--   **Formalization Note** Rounds are indexed from $0$ and $\sigma$ is an equivalence `Fin n ≃ ι`. The fixed order condition constrains the decision rule only on histories that open $\sigma(0),\dots,\sigma(k-1)$ in order; other histories are never reached by such a strategy. Thresholds are extended reals: a threshold $+\infty$ never halts. The paper's definition (p.7) writes $t_i\in\mathbb R$, but its proof of Observation 1 (p.33) sets $t_i=\infty$ when no finite threshold works, and with real thresholds Observation 1 and Theorem 4.1 fail (two i.i.d. exponential boxes with cost $0$: the optimum opens both, but every real second threshold halts after one box with positive probability).
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, §2, p.7 (fixed order strategy; fixed order strategy with thresholds); Appendix D, p.33 (t_i = ∞ if C_i = ∅)

import Definitions.Def_PandoraComb_Model

open MeasureTheory

noncomputable section

namespace PandoraComb

/-- **Fixed order strategy** with order `σ` (arXiv:2303.01078v1, §2, p.7): "such a strategy is
characterized by a permutation σ : [n] → [n] such that at every round i, the strategy either
opens the box σ(i), or halts."

**Formalization Note.** Rounds are indexed from `0`: at round `k` (after the boxes
`σ 0, …, σ (k − 1)` were opened in this order) the strategy returns `none` or `some (σ k)`, for
every seed and every observed values. Histories that do not open `σ 0, …, σ (k − 1)` in order are
never reached by such a strategy and are not constrained. -/
def IsFixedOrder {ι : Type*} [Fintype ι] (σ : Fin (Fintype.card ι) ≃ ι) (π : Strategy ι) :
    Prop :=
  ∀ (h : History ι) (s : ℝ) (hk : h.length < Fintype.card ι),
    h.map Prod.fst = (List.ofFn σ).take h.length →
      π.next h s = none ∨ π.next h s = some (σ ⟨h.length, hk⟩)

/-- **The fixed order strategy with thresholds** `t` and order `σ` (§2, p.7): "A strategy π is
called a fixed order strategy with thresholds t1, . . . , tn ∈ ℝ if it is fixed order, and at
every round i, π halts if and only if the maximum value inspected so far is at least ti."

**Formalization Note.** Rounds are indexed from `0`: at round `k` it halts iff
`t k ≤ max(0, maximum value inspected so far)` (the maximum is `0` at round `0`, as in the proof
of Observation 1, p.33, where `x ≥ 0`), and otherwise opens `σ k`; after `n` rounds it halts.
The thresholds take values in `EReal`: the proof of Observation 1 (p.33) sets `t_i = ∞` when
`C_i = ∅`, and with real thresholds Observation 1 and Theorem 4.1 are false (two i.i.d. Exp(1)
boxes with cost `0`: the optimum opens both boxes, while every real threshold `t_2` halts after
one box with positive probability). -/
def thresholdStrategy {ι : Type*} [Fintype ι] (σ : Fin (Fintype.card ι) ≃ ι)
    (t : Fin (Fintype.card ι) → EReal) : Strategy ι where
  next h _ :=
    if hk : h.length < Fintype.card ι then
      if t ⟨h.length, hk⟩ ≤ ((reward h : ℝ) : EReal) then none else some (σ ⟨h.length, hk⟩)
    else none

end PandoraComb


