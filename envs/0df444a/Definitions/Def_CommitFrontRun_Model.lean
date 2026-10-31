-- Prove2me | Definitions.Def_CommitFrontRun_Model
-- name    : CommitFrontRun_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:27.449029+00:00
-- url     : https://prove2.me/theorems/4ea5f76d-3dfd-46b3-b726-874408be1c57
-- title:
--   Commit-reveal front-running model: states, messages, prior, payoffs, costs $c<f$, $q$, $\beta$
-- statement:
--   The model of front running with a commit-reveal protocol of Canidio and Danos (§2 and §3).
--
--   There are two players, $A$ (Alice) and $B$ (Bob). A **state of the world** $s\in S$ is drawn from a prior $p$ on $S$ and observed by $A$ only; $B$ knows $p$. Messages range over a set $\Sigma$. Both $S$ and $\Sigma$ are finite and non-empty. The data are:
--
--   1. $\tilde P_A(\tilde\sigma_A,s)$, the benefit to $A$ when her message $\tilde\sigma_A$ is executed in state $s$;
--   2. $\tilde P_B(\tilde\sigma_B,\tilde\sigma_A,s)$, the benefit to $B$ when his message $\tilde\sigma_B$ is included before $A$'s message $\tilde\sigma_A$ in state $s$ (and then $A$ earns nothing);
--   3. $A$'s message $\sigma_A(s)$, the **unique** maximizer of $\tilde P_A(\cdot,s)$, with distinct messages in distinct states;
--   4. the cost $c>0$ of a regular message, the cost $f>c$ of a fast message, which is included before $A$'s regular message with probability $q\in[0,1]$, and the discount factor $\beta\in[0,1]$ of one block delay.
--
--   The commit-reveal analysis assumes that no state has
--   $$
--   P_A(s)\in\Big[c,\;c+\frac c\beta\Big],\qquad P_A(s)=\tilde P_A(\sigma_A(s),s).
--   $$
--
--   **Formalization Note** The paper assumes $\sigma_A$ is a bijection; only injectivity is imposed. The interval assumption is written $P_A(s)<c$ or $c<\beta\,(P_A(s)-c)$, which is the printed condition for $\beta>0$ and reads $c/0=+\infty$ at $\beta=0$. The prior need not have full support.
-- source:
--   Canidio, Danos, Commitment Against Front-Running Attacks, arXiv:2301.13785v3, §2, pp.8–10; §3, pp.13–14

import Mathlib

namespace CommitFrontRun

/-- **The front-running model with the commit-reveal protocol.**
Canidio, Danos, *Commitment Against Front-Running Attacks*, arXiv:2301.13785v3, §2, pp.8–10, and §3, pp.13–14.

* `S` is the finite non-empty set of states of the world, which only A learns; `Msg` is the
  finite non-empty message space Σ (p.8: "Both the set S and the set Σ are non-empty and finite").
* `p` is the prior over states, known to B (p.12: "Assuming that B knows the probability
  distribution over the possible states of the world").
* `PtA σ s` is P̃_A(σ̃_A, s), A's benefit when her message σ̃_A is executed in state s;
  `PtB σ σ' s` is P̃_B(σ̃_B, σ̃_A, s), B's benefit when his σ̃_B is included before A's σ̃_A (p.8).
* `σA s` is A's message σ_A(s) = argmax P̃_A(·, s) (p.10), the unique maximizer
  (`σA_argmax`), and distinct across states (`σA_injective`).
* `c > 0` is the cost of a regular message, `f > c` the cost of a fast message, which lands
  before A's regular message with probability `q` (p.8); `β ∈ [0, 1]` is the discount factor of
  one block (p.13).
* `interval`: no state has P_A(s) ∈ [c, c + c/β] (p.14).

**Formalization Note**
* The paper assumes "σA(s) is a bijection" (p.10); only injectivity is required here, which is
  what makes A's message reveal the state.
* The interval assumption is stated multiplicatively, `P_A(s) < c ∨ c < β (P_A(s) − c)`. For
  β > 0 this is exactly P_A(s) ∉ [c, c + c/β]; at β = 0 it reads c/0 = +∞ (so P_A(s) < c for all
  s), avoiding Lean's `c / 0 = 0`.
* `q ∈ [0, 1]` because q is a probability. The prior need not have full support. -/
structure Model (S Msg : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype Msg] [DecidableEq Msg] [Nonempty Msg] where
  /-- The prior over states of the world. -/
  p : S → ℝ
  p_nonneg : ∀ s, 0 ≤ p s
  p_sum : ∑ s, p s = 1
  /-- P̃_A(σ̃_A, s). -/
  PtA : Msg → S → ℝ
  /-- P̃_B(σ̃_B, σ̃_A, s). -/
  PtB : Msg → Msg → S → ℝ
  /-- A's message σ_A(s). -/
  σA : S → Msg
  σA_argmax : ∀ s σ, σ ≠ σA s → PtA σ s < PtA (σA s) s
  σA_injective : Function.Injective σA
  /-- Cost of a regular message. -/
  c : ℝ
  /-- Cost of a fast message. -/
  f : ℝ
  /-- Probability that a fast message lands before A's regular message. -/
  q : ℝ
  /-- Discount factor of one block. -/
  β : ℝ
  c_pos : 0 < c
  c_lt_f : c < f
  q_nonneg : 0 ≤ q
  q_le_one : q ≤ 1
  β_nonneg : 0 ≤ β
  β_le_one : β ≤ 1
  interval : ∀ s, PtA (σA s) s < c ∨ c < β * (PtA (σA s) s - c)

end CommitFrontRun


