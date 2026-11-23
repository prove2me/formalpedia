-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_Gadget
-- name    : OnlineMaxWeightMatch_Approx_Supplement_Gadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:20:57.812771+00:00
-- url     : https://prove2.me/theorems/da9d8b52-0e2a-428e-b53e-2eac7ac57a15
-- title:
--   §3.2, pp. 7–8 — the RideHail instance $\mathcal I_\phi$ and the clause-ball gain $B$
-- statement:
--   Let $\phi$ be a MAX-SSAT formula with variables $x_1,\dots,x_n$ and clauses $C_1,\dots,C_m$, and let $k\in\mathbb N$. The RideHail instance $\mathcal I_\phi$ of §3.2 has $2n$ bins, one for each literal $x_i$, $\bar x_i$, and $n+m$ balls arriving in order.
--
--   1. **Deterministic literal balls.** For odd $t\le n$, ball $t$ arrives with probability $1$, has weight $1$, and has edges to the bins $x_t$ and $\bar x_t$.
--   2. **Random literal balls.** For even $t\le n$, ball $t$ arrives with probability $1/2$, has weight $1$, and has an edge only to bin $x_t$.
--   3. **Clause balls.** Ball $n+r$, for $r=1,\dots,m$, arrives with probability $m^{-4}$, has weight $m^4/(2k)$, and has edges to the bins of the literals of $C_r$.
--
--   All weights of non-edges are $0$. For an online policy $\pi$ on $\mathcal I_\phi$, $B$ is the profit $\pi$ collects from the clause balls, and $\mathbb E[B]$ its expectation over the random arrivals.
--
--   **Formalization Note** The instance uses the published RideHail model: bins are pairs (variable, sign), balls are $\{0,\dots,n+m-1\}$ with Lean ball $t$ the paper's ball $t+1$, and the literal balls come first. A non-edge is an edge of weight $0$.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, pp. 7–8, §3.2 (construction of I_φ and Figure 1); p. 8, Lemma 3.5 (definition of B)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_RideHail
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_MaxSSAT

open Classical

namespace OnlineMaxWeightMatch.Approx.Supplement

open OnlineMaxWeightMatch.Approx

/-- The literal bins of `I_φ`: bin `(v, s)` is the literal `x_{v+1}` (`s = true`) or
`¬x_{v+1}` (`s = false`), for `v < n`; there are `2n` of them. -/
abbrev LitBin (n : ℕ) : Type := Fin n × Bool

/-- The **RideHail instance `I_φ`** of §3.2 (pp. 7–8), built from a MAX-SSAT formula `φ` with
`n` variables and `m` clauses and the occurrence bound `k`. Balls `0, …, n-1` are the literal
balls (Lean ball `t` is the paper's ball `t+1`) and balls `n, …, n+m-1` the clause balls (ball
`n + r` is clause `C_{r+1}`).

1. A deterministic literal ball `t` (Lean `t` even) arrives with probability 1, has weight 1,
   and neighbours the two bins `x_{t+1}` and `¬x_{t+1}`.
2. A random literal ball `t` (Lean `t` odd) arrives with probability `1/2`, has weight 1, and
   neighbours only the bin `x_{t+1}`.
3. The clause ball of clause `C` arrives with probability `m^{-4}`, has weight `m^4/(2k)`, and
   neighbours the bins of the literals of `C`.

A non-edge has weight `0`. -/
noncomputable def gadget (φ : SSATFormula) (k : ℕ) :
    RideHailInstance (LitBin φ.n) (φ.n + φ.clauses.length) where
  w i t :=
    if t.val < φ.n then
      (if i.1.val = t.val ∧ (¬ IsRandomVar t.val ∨ i.2 = true) then 1 else 0)
    else
      (if (i.1.val, i.2) ∈ φ.clauses.getD (t.val - φ.n) [] then
        (φ.clauses.length : ℝ) ^ 4 / (2 * k) else 0)
  p t :=
    if t.val < φ.n then (if IsRandomVar t.val then 1 / 2 else 1)
    else ((φ.clauses.length : ℝ) ^ 4)⁻¹
  w_nonneg i t := by
    split_ifs <;> positivity
  p_nonneg t := by
    split_ifs <;> positivity
  p_le_one t := by
    split_ifs with h1 h2
    · norm_num
    · norm_num
    · rcases Nat.eq_zero_or_pos φ.clauses.length with h | h
      · simp [h]
      · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast h))

/-- `B`: the expected gain of policy `π` on `I_φ` from the clause balls only. -/
noncomputable def clauseGain (φ : SSATFormula) (k : ℕ)
    (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) : ℝ :=
  ∑ a : Fin (φ.n + φ.clauses.length) → Bool, arrivalProb (gadget φ k) a *
    ∑ e ∈ (π.matching a).filter (fun e => φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2

end OnlineMaxWeightMatch.Approx.Supplement


