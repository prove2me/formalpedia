-- Prove2me | Definitions.Def_StableVotingDistortion_Supplement_IsMaximalLottery
-- name    : StableVotingDistortion_Supplement_IsMaximalLottery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:53:54.775981+00:00
-- url     : https://prove2.me/theorems/ce028124-2092-45df-b71c-0747f4b57e06
-- title:
--   Maximal lottery (Definition 1): the $g$-stable lottery for $g(r)=r$
-- statement:
--   Fix an election with voters $V$ and candidates $C$. In the **Condorcet game** an attacker and a defender choose lotteries $D^\dagger$ and $D$ over $C$; a candidate $a\sim D^\dagger$, a candidate $b\sim D$ and a uniformly random voter $v$ are drawn, and the attacker wins if $a\succ_v b$. A **maximal lottery** is a solution of
--   $$
--   \arg\min_{D}\ \max_{D^\dagger}\ \Pr_{v\sim V,\ a\sim D^\dagger,\ b\sim D}[a\succ_v b].
--   $$
--   Probabilities use the paper's copy convention: each candidate is a continuum of copies, and a draw from a lottery is a uniformly random copy, so a draw of $a$ against a copy of $a$ wins with probability $1/2$. For a pure attacker $a$ the winning probability is then $\mathbb E_{v\sim V}[\mathrm{rank}_v(a;D)]$ with the random-copy rank $\mathrm{rank}_v(a;D)+D(a)/2$, and the maximum over mixed attackers equals the maximum over pure ones. A maximal lottery is therefore exactly a $g$-stable lottery for the activation $g(r)=r$.
--
--   Maximal lotteries are the randomized analogue of a Condorcet winner; they are the $k=1$ case of stable $k$-lotteries.
--
--   **Formalization Note** Defined as the base mission's `IsGStable` at $g(r)=r$; a lottery is a point of the standard simplex and full support is not assumed.
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Definition 1, p.7; Equation (3), p.8; Definition 3, p.10

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsGStable

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion.Supplement

/-- `D` is a **maximal lottery** of the election `E`: a solution of the Condorcet game's minimax problem
`arg min_D max_{D†} Pr_{v ∼ V, a ∼ D†, b ∼ D}[a ≻_v b]`, which is the `g`-stable lottery for the identity
activation `g(r) = r`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Definition 1, p.7: "Given an election, a
maximal lottery is an equilibrium strategy of the Condorcet game, given by a solution to the following minimax
optimization: arg min_D max_{D†} Pr_{v∼V, a∼D†, b∼D}[a ≻_v b]. (1)"; §3, p.8, Equation (3) (the payoff as
`E_v[rank_v(a; D)]`); Definition 3, p.10: "g(r) = r, corresponding to maximal lotteries".

**Formalization Note.** With the copy convention (p.5: ties between copies of one candidate broken uniformly), a
pure attacker `a` wins with probability `E_v[rank_v(a; D) + D(a)/2]`, which is the base mission's
`activation (fun r => r)`; the maximum over mixed attackers `D†` is the maximum over pure ones (the payoff is
linear in `D†`). So Definition 1 is `IsGStable` at `g(r) = r`. -/
def IsMaximalLottery {V C : Type} [Fintype V] [Fintype C] [Nonempty C]
    (E : Election V C) (D : C → ℝ) : Prop :=
  IsGStable (fun r => r) E D

end StableVotingDistortion.Supplement


