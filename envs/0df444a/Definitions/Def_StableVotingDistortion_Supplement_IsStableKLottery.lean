-- Prove2me | Definitions.Def_StableVotingDistortion_Supplement_IsStableKLottery
-- name    : StableVotingDistortion_Supplement_IsStableKLottery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:54:23.129804+00:00
-- url     : https://prove2.me/theorems/ce230c4c-e001-4a07-9e99-2b3f863747bf
-- title:
--   Stable $k$-lottery (Definition 2): the $g$-stable lottery for $g(r)=r^k$
-- statement:
--   Fix an election and a positive integer $k$. In the **$k$ vs $1$ Condorcet game** the attacker draws $a\sim D^\dagger$, the defender draws $b_1,\dots,b_k\sim D$ independently, and the attacker wins if a uniformly random voter $v$ prefers $a$ to all of $b_1,\dots,b_k$. A **stable $k$-lottery** is the defender's solution of
--   $$
--   \arg\min_{D}\ \max_{D^\dagger}\ \Pr_{v\sim V,\ a\sim D^\dagger,\ b_1,\dots,b_k\sim D}[a\succ_v b_1,\dots,b_k].
--   $$
--   With the copy convention, a random copy of $a$ beats $k$ independent draws with probability $\mathrm{rank}_v(a;D)^k$, where the rank is that of a uniformly random point of $a$'s interval on $v$'s rank line; so the objective is $\min_D\max_{D^\dagger}\mathbb E_{v\sim V,\,a\sim D^\dagger}[\mathrm{rank}_v(a;D)^k]$, and a stable $k$-lottery is exactly a $g$-stable lottery for $g(r)=r^k$.
--
--   Stable $k$-lotteries are the family whose distortion Theorems 3, 6 and 8 describe.
--
--   **Formalization Note** Defined as the base mission's `IsGStable` at $g(r)=r^k$ with $k\in\mathbb N$; the theorems assume $k\ge1$. At $k=1$ it coincides with the maximal lottery.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Definition 2, p.9; Equations (6)–(7), p.9; Definition 3, p.10

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsGStable

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion.Supplement

/-- `D` is a **stable `k`-lottery** of the election `E`: the defender's solution of the `k` vs `1` Condorcet
game `arg min_D max_{D†} Pr_{v ∼ V, a ∼ D†, b₁, …, b_k ∼ D}[a ≻_v b₁, …, b_k]`, which is the `g`-stable lottery
for the activation `g(r) = r ^ k`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Definition 2, p.9: "Given an election, a stable
k-lottery is an equilibrium distribution for the defender in the k vs 1 Condorcet game, given by a solution to
the following minimax optimization: arg min_D max_{D†} Pr_{v∼V, a∼D†, b1,...,bk∼D}[a ≻v b1, . . . , bk]. (4)";
p.9, Equations (6)–(7): the objective is `min_D max_{D†} E_{v∼V, a∼D†}[rank_v(a; D)^k]`; Definition 3, p.10:
"For g(r) = r^k, we recover the stable k-lottery objective".

**Formalization Note.** With the copy convention (p.5), for a random copy of the attacker `a` the probability of
beating `k` independent draws is `rank_v(a; D)^k` with the random-copy rank (p.9), i.e. the base mission's
`activation (fun r => r ^ k)`; the maximum over mixed attackers is the maximum over pure ones. `k` is a natural
number; the paper's `k` is an integer `≥ 1`, and the theorems assume `1 ≤ k`. At `k = 1` this is
`IsMaximalLottery`. -/
def IsStableKLottery {V C : Type} [Fintype V] [Fintype C] [Nonempty C] (k : ℕ)
    (E : Election V C) (D : C → ℝ) : Prop :=
  IsGStable (fun r => r ^ k) E D

end StableVotingDistortion.Supplement


