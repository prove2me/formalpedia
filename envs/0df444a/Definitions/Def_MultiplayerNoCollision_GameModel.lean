-- Prove2me | Definitions.Def_MultiplayerNoCollision_GameModel
-- name    : MultiplayerNoCollision_GameModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:18.732637+00:00
-- url     : https://prove2.me/theorems/c525fde8-2b67-40ff-aa24-f51bc1732958
-- title:
--   The stochastic model: i.i.d. reward vectors in $[0,1]$, private uniform seeds, and the means $\mu_i$
-- statement:
--   On a probability space $(\Omega,\mathcal F,P)$ there are $K$ arms and $m$ players.
--
--   1. **Rewards.** $Y_{i,t}$ is the reward of arm $i$ in round $t$. Each $Y_{i,t}$ is a random variable with values in $[0,1]$ (Assumption 2), and the reward vectors $(Y_{1,t},\dots,Y_{K,t})$, $t=1,2,\dots$, are independent and identically distributed.
--   2. **Private randomness.** $U_{j,t}$ is the fresh random seed of player $j$ in round $t$. Each seed is uniform on $[0,1]$ and the family $(U_{j,t})_{j,t}$ is independent.
--   3. **Independence.** The whole reward process is independent of the whole seed family.
--   4. **Means.** $\mu_i=\mathbb E\,Y_{i,t}$, which does not depend on $t$.
--
--   This is the environment of the multiplayer bandit game: nature draws the rewards, and each player randomizes only through her own seeds.
--
--   **Formalization Note** Rounds are 0-based and arms, players are `Fin K`, `Fin m`. The i.i.d. requirement is on whole reward vectors, so arms may depend on each other within a round; the model with all $Y_{i,t}$ independent is a special case. The bound $0\le Y_{i,t}\le 1$ is imposed at every outcome. The means are computed at round $0$.
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, §1.1, p.3 (model), Assumption 2, p.4; §3, p.9 ("collisions and rewards are independent")

import Mathlib

namespace MultiplayerNoCollision

open MeasureTheory ProbabilityTheory

/-- **Stochastic rewards of a `K`-armed bandit with i.i.d. reward vectors in `[0,1]`.**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, §1.1, p.3: "Let `Y_{i,t}` be the reward of arm `i` in round `t`, so the
`{Y_{i,t}}_{t=1}^∞` are independent and identically distributed (i.i.d.) and `E Y_{i,t} = µ_i`",
and Assumption 2, p.4: "`Y_{A_j(t),t}` is supported on `[0,1]`".

`Y i t ω` is the reward of arm `i` in (0-based) round `t`. The rewards are measurable with values
in `[0,1]`; the reward vectors `(Y_{1,t}, …, Y_{K,t})`, `t = 0, 1, …`, are mutually independent and
identically distributed.

**Formalization Note.** Rounds are 0-based (paper round `t` is Lean round `t − 1`) and arms are
`Fin K` (paper arm `i` is index `i − 1`). The i.i.d. requirement is imposed on whole reward vectors
across rounds; within a round the arms may depend on each other arbitrarily (this contains the
model with all `Y_{i,t}` independent). The bound `0 ≤ Y ≤ 1` is required at every outcome, which
excludes no law. -/
structure IIDRewards {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω)
    (Y : Fin K → ℕ → Ω → ℝ) : Prop where
  /-- Each reward is a random variable. -/
  measurable : ∀ i t, Measurable (Y i t)
  /-- Rewards lie in `[0,1]` (Assumption 2). -/
  mem_Icc : ∀ i t ω, Y i t ω ∈ Set.Icc (0 : ℝ) 1
  /-- The reward vectors of different rounds are mutually independent. -/
  indep : iIndepFun (fun t ω i => Y i t ω) P
  /-- The reward vectors of all rounds have the law of the round-0 vector. -/
  ident : ∀ t, IdentDistrib (fun ω i => Y i t ω) (fun ω i => Y i 0 ω) P P

/-- **Private randomization of the players.** Lugosi, Mehrabian, arXiv:1808.08416v2, p.4: "the
strategy can randomize hence `A_j(t)` can be random".

`U j t` is the fresh random seed of player `j` in round `t`: the seeds are measurable, each is
uniform on `[0,1]`, and the whole family `(U j t)_{j,t}` is mutually independent.

**Formalization Note.** A player's randomization in round `t` is a measurable function of her own
seed `U j t`; every randomized choice of the paper (a uniformly random arm, a uniformly random arm of
a set) is realized this way. -/
structure UniformSeeds {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (P : Measure Ω)
    (U : Fin m → ℕ → Ω → ℝ) : Prop where
  /-- Each seed is a random variable. -/
  measurable : ∀ j t, Measurable (U j t)
  /-- Each seed is uniform on `[0,1]`. -/
  uniform : ∀ j t, P.map (U j t) = volume.restrict (Set.Icc (0 : ℝ) 1)
  /-- All seeds are mutually independent. -/
  indep : iIndepFun (fun p : Fin m × ℕ => U p.1 p.2) P

/-- **The stochastic model of the game.** Lugosi, Mehrabian, arXiv:1808.08416v2, §1.1, pp.3–4.

`m` players and `K` arms on a probability space `(Ω, P)`: the rewards `Y` satisfy `IIDRewards`,
the players' private seeds `U` satisfy `UniformSeeds`, and the whole reward process is independent
of the whole seed family.

**Formalization Note.** The independence of rewards and seeds is the paper's "collisions and rewards
are independent" (p.9) in its primitive form: the players' randomness is independent of nature's. -/
structure GameModel {Ω : Type*} [MeasurableSpace Ω] {m K : ℕ} (P : Measure Ω)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) : Prop where
  /-- The reward model. -/
  rewards : IIDRewards P Y
  /-- The seed model. -/
  seeds : UniformSeeds P U
  /-- Rewards and seeds are independent. -/
  indep : IndepFun (fun ω t i => Y i t ω) (fun ω (p : Fin m × ℕ) => U p.1 p.2 ω) P

/-- **The arm means** `µ_i = E Y_{i,t}` (Lugosi, Mehrabian, arXiv:1808.08416v2, §1.1, p.3), computed
at round `0`; by `IIDRewards.ident` every round has the same means. -/
noncomputable def means {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (P : Measure Ω)
    (Y : Fin K → ℕ → Ω → ℝ) : Fin K → ℝ :=
  fun i => ∫ ω, Y i 0 ω ∂P

end MultiplayerNoCollision


