-- Prove2me | Definitions.Def_SennottDP_DiscountedASM_tabooProb
-- name    : SennottDP_DiscountedASM_tabooProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T07:33:38.447564+00:00
-- url     : https://prove2.me/theorems/7b84484c-63bf-46e2-8c2c-e75afb6879ac
-- title:
--   Taboo probabilities and the discounted first passage time out of $S_N$
-- statement:
--   Let $e$ be a stationary policy of the MDC $\Delta$, with transition probabilities $P_{ij}(e)=P_{ij}(e(i))$. The $t$-step transition probability of the induced Markov chain is
--   $$
--   P^{(t)}_{ij}(e)=\sum_{k_1\in S}\cdots\sum_{k_{t-1}\in S}P_{ik_1}(e)P_{k_1k_2}(e)\cdots P_{k_{t-1}j}(e),
--   $$
--   with $P^{(0)}_{ij}=1$ if $i=j$ and $0$ otherwise.
--
--   For a finite set $T\subseteq S$ (below $T=S_N$), the **taboo probability** ${}_{T*}P^{(t)}_{ij}(e)$, $t\ge1$, is the probability of going from $i$ to $j$ in $t$ steps while avoiding $S-T$ at the intermediate steps $1,\dots,t-1$ (the initial and final states may lie anywhere):
--   $$
--   {}_{T*}P^{(1)}_{ij}(e)=P_{ij}(e),\qquad {}_{T*}P^{(t+1)}_{ij}(e)=\sum_{k\in T}P_{ik}(e)\,{}_{T*}P^{(t)}_{kj}(e).
--   $$
--
--   Starting at $i$, let $\tau\ge1$ be the number of steps until the chain first enters $S-T$ ($\tau=\infty$ if it never does). Then $P(\tau=n)=\sum_{j\notin T}{}_{T*}P^{(n)}_{ij}(e)$ and, for $0<\alpha<1$,
--   $$
--   E_e[\alpha^{\tau}]=\sum_{n=1}^{\infty}\alpha^n P(\tau=n),
--   $$
--   with the convention $\alpha^\infty=0$.
--
--   These quantities describe how the original chain leaves the truncated state space $S_N$, which is what the ATAS results of Section 4.7 control.
--
--   **Formalization Note** $P^{(t)}$ is computed by first-step decomposition, which is equivalent to the path sum (2.7). The taboo probability at $t=0$ is set to the identity; the book defines it only for $t\ge1$ and no statement uses $t=0$. $E_e[\alpha^\tau]$ is defined directly by the series above, in $[0,\infty]$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 23 (2.7); p. 78 (taboo probability); pp. 78–79 Lemma 4.7.3, (4.45)

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC

open scoped ENNReal NNReal
open Classical

namespace SennottDP.DiscountedASM

namespace MDC

variable {S Act : Type} (M : MDC S Act)

/-- `P^{(t)}_{ij}(f)`, the `t`-step transition probability of the Markov chain induced by the
stationary policy `f` (equation (2.7), p. 23), computed by first-step decomposition:
`P^{(0)}_{ij} = 1{i = j}`, `P^{(t+1)}_{ij} = Σ_k P_{ik}(f) P^{(t)}_{kj}`. -/
noncomputable def stepProb (f : S → Act) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | t + 1, i, j => ∑' k, M.P i (f i) k * stepProb f t k j

/-- The taboo probability `_{T*}P^{(t)}_{ij}(f)` (p. 78): the probability that the chain of the
stationary policy `f` goes from `i` to `j` in `t ≥ 1` steps while staying in the finite set `T`
at the intermediate times `1, …, t-1` (the initial and final states are unrestricted):
`_{T*}P^{(1)}_{ij} = P_{ij}(f)`, `_{T*}P^{(t+1)}_{ij} = Σ_{k ∈ T} P_{ik}(f) _{T*}P^{(t)}_{kj}`.
The value at `t = 0` (`1{i = j}`) is a convention and is not used. -/
noncomputable def tabooProb (T : Finset S) (f : S → Act) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | 1, i, j => M.P i (f i) j
  | t + 2, i, j => ∑' k, (if k ∈ T then M.P i (f i) k * tabooProb T f (t + 1) k j else 0)

/-- `E_f[α^{T}]` for the first passage time `T ≥ 1` of the chain of `f`, started at `i`, into
the complement `S - T` of the finite set `T`, counting `α^∞ = 0` (equation (4.45), p. 79):
`Σ_{n ≥ 1} α^n P(T = n)` with `P(T = n) = Σ_{j ∉ T} _{T*}P^{(n)}_{ij}(f)`. -/
noncomputable def firstPassageDisc (T : Finset S) (f : S → Act) (α : ℝ≥0) (i : S) : ℝ≥0∞ :=
  ∑' n : ℕ, (α : ℝ≥0∞) ^ (n + 1) *
    ∑' j : S, (if j ∈ T then 0 else M.tabooProb T f (n + 1) i j)

end MDC

end SennottDP.DiscountedASM


