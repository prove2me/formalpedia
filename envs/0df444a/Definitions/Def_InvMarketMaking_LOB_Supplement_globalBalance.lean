-- Prove2me | Definitions.Def_InvMarketMaking_LOB_Supplement_globalBalance
-- name    : InvMarketMaking_LOB_Supplement_globalBalance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:31:57.121181+00:00
-- url     : https://prove2.me/theorems/3011e140-fd27-4b8f-ba8e-b890c8b0a6b9
-- title:
--   Algorithm 6 (Global Inventory Balance Metaprocedure)
-- statement:
--   Given a horizon $T$, an integer imbalance bound $I_{\mathcal A}$ and an input algorithm $\mathcal A$ with prices $(B^{\mathcal A}_t,A^{\mathcal A}_t)$, Algorithm 6 posts $\mathcal A$'s prices in rounds $1,\dots,T-I_{\mathcal A}$. It then enters a balancing loop. While its own imbalance $I_{t-1}$ is nonzero, it posts $(1,1)$ if it is short ($\sum_{\tau<t}\mathbb I(V^{\mathrm{buy}}_\tau\ge A_\tau)>\sum_{\tau<t}\mathbb I(V^{\mathrm{sell}}_\tau\le B_\tau)$) and $(0,0)$ otherwise. Once a round starts with $I_{t-1}=0$, it posts the no-trade pair $(0,1)$ for the rest of the horizon. Under the standing assumptions $(1,1)$ buys and does not sell, and $(0,0)$ sells and does not buy, almost surely.
--
--   This wrapper turns any algorithm with a per-round imbalance guarantee into one that ends with zero inventory (Theorem 7.1).
--
--   **Formalization Note** $T-I_{\mathcal A}$ is natural subtraction, so there are no input rounds if $I_{\mathcal A}\ge T$. The pairs $(1,1)$ and $(0,0)$ lie outside $B<A$; the paper allows them (p. 55). An explicit exit flag keeps the procedure at $(0,1)$ after Line 14.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Algorithm 6, p. 55; footnote 6, p. 55

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_IsRoundModel

namespace InvMarketMaking.LOB.Supplement

/-- The state of Algorithm 6 after a round: its own imbalance `I_t` and whether it has left the
balancing loop (Line 14). -/
structure WrapState where
  inv : ℝ
  exited : Bool

/-- The pair Algorithm 6 posts in round `t`, given the state after round `t − 1` (p. 55): the input
algorithm's pair `(B^A_t, A^A_t)` for `t ≤ T − I_A` (Lines 2–5); afterwards, while the loop runs and
`I_{t−1} ≠ 0`, `(1, 1)` if `Σ_{τ<t} I(V^buy_τ ≥ A_τ) > Σ_{τ<t} I(V^sell_τ ≤ B_τ)` (i.e. `I_{t−1} < 0`)
and `(0, 0)` otherwise (Lines 6–13); once a round starts with `I_{t−1} = 0`, `(0, 1)` for ever
(Line 14). `T − I_A` is natural subtraction (no input round if `I_A ≥ T`). -/
noncomputable def wrapPrice (T IA : ℕ) (bidA askA : ℕ → ℝ) (t : ℕ) (s : WrapState) : ℝ × ℝ :=
  if t ≤ T - IA then (bidA t, askA t)
  else if s.exited = true ∨ s.inv = 0 then (0, 1)
  else if s.inv < 0 then (1, 1) else (0, 0)

/-- The states of Algorithm 6 after rounds `0, 1, 2, …` on the valuation sequences `vs`, `vb`:
`I_0 = 0`, and `I_t = I_{t−1} + I(V^sell_t ≤ B_t) − I(V^buy_t ≥ A_t)` at the posted pair. The exit flag
is set in the first balancing round that starts with `I_{t−1} = 0` and is never cleared. -/
noncomputable def wrapRun (T IA : ℕ) (bidA askA vs vb : ℕ → ℝ) : ℕ → WrapState
  | 0 => ⟨0, false⟩
  | t + 1 =>
    let s := wrapRun T IA bidA askA vs vb t
    let p := wrapPrice T IA bidA askA (t + 1) s
    ⟨s.inv + (if vs (t + 1) ≤ p.1 then 1 else 0) - (if p.2 ≤ vb (t + 1) then 1 else 0),
      s.exited || (decide (T - IA < t + 1) && decide (s.inv = 0))⟩

/-- **Algorithm 6** (Global Inventory Balance Metaprocedure; Maran, Restelli, Stradi, No-Regret
Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1,
p. 55) instantiated with an input algorithm whose prices are `bidA`, `askA`: the pair posted in round
`t ≥ 1`.

**Formalization Note** (i) The input algorithm is given by its price processes, run for horizon `T`;
only its rounds `1, …, T − I_A` are used. (ii) The pairs `(1, 1)` and `(0, 0)` lie outside `B < A`;
the paper allows them (p. 55). (iii) The explicit exit flag keeps the procedure at `(0, 1)` after
Line 14 even if a later (null-probability) trade moves the imbalance. -/
noncomputable def globalBalance (T IA : ℕ) (bidA askA vs vb : ℕ → ℝ) (t : ℕ) : ℝ × ℝ :=
  wrapPrice T IA bidA askA t (wrapRun T IA bidA askA vs vb (t - 1))

/-- The bid process of Algorithm 6 on the market `M` with input prices `bidA`, `askA`. -/
noncomputable def wrapBid {Ω : Type*} (T IA : ℕ) (bidA askA : ℕ → Ω → ℝ) (M : Market Ω) (t : ℕ)
    (ω : Ω) : ℝ :=
  (globalBalance T IA (fun s => bidA s ω) (fun s => askA s ω) (fun s => M.Vs s ω)
    (fun s => M.Vb s ω) t).1

/-- The ask process of Algorithm 6 on the market `M` with input prices `bidA`, `askA`. -/
noncomputable def wrapAsk {Ω : Type*} (T IA : ℕ) (bidA askA : ℕ → Ω → ℝ) (M : Market Ω) (t : ℕ)
    (ω : Ω) : ℝ :=
  (globalBalance T IA (fun s => bidA s ω) (fun s => askA s ω) (fun s => M.Vs s ω)
    (fun s => M.Vb s ω) t).2

end InvMarketMaking.LOB.Supplement


