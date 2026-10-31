-- Prove2me | Definitions.Def_FoundationsRL_TabularRL_optQ
-- name    : FoundationsRL_TabularRL_optQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:43.856031+00:00
-- url     : https://prove2.me/theorems/b7ef9ba7-62f1-432b-be90-884db61f0499
-- title:
--   Optimistic value functions $\bar Q_h$ of one episode, Eq. (5.29)
-- statement:
--   Let $M$ be a finite-horizon episodic MDP with finite state space $\mathcal S$, finite action space $\mathcal A$ and horizon $H$, with known rewards $r_h(s,a)$. Given **estimated transitions** $\widehat P_h(\cdot\mid s,a)$ and **bonus functions** $b_{h,\delta}:\mathcal S\times\mathcal A\to\mathbb R$, the estimated Bellman operator is
--
--   $$
--   [\mathcal T^{\widehat M}_h Q](s,a)=r_h(s,a)+\mathbb E_{s'\sim\widehat P_h(\cdot\mid s,a)}\max_{a'}Q(s',a'),
--   $$
--
--   and the **optimistic value functions** are defined by backward induction from $\bar Q_{H+1}\equiv0$:
--
--   $$
--   \bar Q_h(s,a)=\Big\{[\mathcal T^{\widehat M}_h\bar Q_{h+1}](s,a)+b_{h,\delta}(s,a)\Big\}\wedge 1,\qquad \bar V_h(s)=\max_a\bar Q_h(s,a).
--   $$
--
--   These are the value functions analyzed in Lemmas 16 and 17: within one episode of UCB-VI they are the algorithm's estimates, with $\widehat P$ the empirical transitions and $b$ the exploration bonus.
--
--   **Formalization Note** Layers are $0$-indexed: `optQ H r Phat b h` is $\bar Q_{h+1}$ for $h<H$ and is $0$ for $h\ge H$ (the convention $\bar Q_{H+1}\equiv0$). $\bar V_h$ is written `⨆ a, optQ H r Phat b h s a`, the maximum over the finite action set.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eqs. (5.28)–(5.29), p. 90

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace FoundationsRL.TabularRL

open FoundationsRL.RLBasics

/-- The optimistic value functions of one episode (Foster & Rakhlin, *Foundations of
Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eqs. (5.28)–(5.29),
p. 90): given known rewards `r`, estimated transitions `Phat` (`Phat h s a s'` is
`P̂_h(s' ∣ s, a)`) and bonus functions `b`, the sequence
`Q̄_h(s,a) = {[T^{M̂}_h Q̄_{h+1}](s,a) + b_{h,δ}(s,a)} ∧ 1` with
`[T^{M̂}_h Q](s,a) = r_h(s,a) + E_{s' ∼ P̂_h(·∣s,a)} max_{a'} Q(s',a')` and `Q̄_{H+1} ≡ 0`,
computed by backward induction. The book's `V̄_h(s) = max_a Q̄_h(s,a)` is `⨆ a, optQ … h s a`.

**Formalization Note.** Layers are `0`-indexed, as in `FoundationsRL.RLBasics.Core`:
`optQ H r Phat b h` is the book's `Q̄_{h+1}` for `h < H`, and `optQ H r Phat b h = 0` for
`h ≥ H` is the book's `Q̄_{H+1} ≡ 0`. `∧ 1` is `min 1`. The maximum over the finite action set
is written `⨆`. -/
noncomputable def optQ {S A : Type*} [Fintype S] [Fintype A] (H : ℕ) (r : ℕ → S → A → ℝ)
    (Phat : ℕ → S → A → S → ℝ) (b : ℕ → S → A → ℝ) : ℕ → S → A → ℝ
  | h, s, a =>
      if h < H then
        min 1 (r h s a + ∑ s' : S, Phat h s a s' * (⨆ a' : A, optQ H r Phat b (h + 1) s' a')
          + b h s a)
      else 0
  termination_by h => H - h
  decreasing_by omega

end FoundationsRL.TabularRL


