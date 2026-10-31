-- Prove2me | Definitions.Def_FiniteMemPOMDP_avgReward
-- name    : FiniteMemPOMDP_avgReward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:58.940338+00:00
-- url     : https://prove2.me/theorems/6f51e26a-8758-47ec-b4e8-32afbd01394e
-- title:
--   Average reward $\frac1n\sum_{m=1}^n G_m$
-- statement:
--   Along a play, the **stage reward** at stage $m$ is $G_m=g(K_m,A_m)$, and the **average reward** over the first $n$ stages is
--
--   $$\frac1n\sum_{m=1}^n G_m .$$
--
--   The module also defines the state $K_{n+1}$ and the history $H_{n+1}=((A_1,S_1),\dots,(A_n,S_n))$ read off a play.
--
--   **Formalization Note** Lean indexes stages from $0$: `stageReward Γ m` is $G_{m+1}$, `stateAt m` is $K_{m+1}$ and `historyAt m` is $H_{m+1}$, a list of length $m$. At $n=0$ the average is $0$.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §2.1, p.2

import Mathlib
import Definitions.Def_FiniteMemPOMDP_POMDP
import Definitions.Def_FiniteMemPOMDP_PlayStep

namespace FiniteMemPOMDP

variable {K A S : Type}

/-- The state `K_{n+1}` at stage `n + 1` of the play `ω` (stored in coordinate `n`). -/
def stateAt (n : ℕ) (ω : ℕ → PlayStep A S K) : K := (ω n).state

/-- The history `H_{n+1} = ((A_1, S_1), …, (A_n, S_n))` before stage `n + 1` of the play `ω`, as a
list of length `n` in chronological order (stored in coordinates `1, …, n`). -/
def historyAt (n : ℕ) (ω : ℕ → PlayStep A S K) : List (A × S) :=
  List.ofFn fun j : Fin n => ((ω (j.1 + 1)).act, (ω (j.1 + 1)).sig)

/-- The stage reward `G_{n+1} = g(K_{n+1}, A_{n+1})` of the play `ω`. -/
def stageReward (Γ : POMDP K A S) (n : ℕ) (ω : ℕ → PlayStep A S K) : ℝ :=
  Γ.g (ω n).state (ω (n + 1)).act

/-- **The average reward `(1/n) ∑_{m=1}^n G_m` over the first `n` stages.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §2.1, p.2: "This action determines a stage
reward Gm := g(Km, Am), where Km is the (random) state at stage m", and the average
`(1/n) ∑_{m=1}^n G_m` of the long-run payoff.

`avgReward Γ n ω = (1/n) ∑_{m=0}^{n-1} stageReward Γ m ω`, i.e. `(1/n)(G_1 + ⋯ + G_n)`.

**Formalization Note** Stages are indexed from `0` in Lean: `stageReward Γ m` is `G_{m+1}`,
`stateAt m` is `K_{m+1}` and `historyAt m` is `H_{m+1}` (a list of length `m`). At `n = 0` the
average is `0` (Lean's `1/0 = 0`); only its behaviour as `n → ∞` and at `n ≥ 1` is used. -/
noncomputable def avgReward (Γ : POMDP K A S) (n : ℕ) (ω : ℕ → PlayStep A S K) : ℝ :=
  (1 / (n : ℝ)) * ∑ m ∈ Finset.range n, stageReward Γ m ω

end FiniteMemPOMDP


