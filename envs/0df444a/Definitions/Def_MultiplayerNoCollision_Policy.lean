-- Prove2me | Definitions.Def_MultiplayerNoCollision_Policy
-- name    : MultiplayerNoCollision_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:23.589798+00:00
-- url     : https://prove2.me/theorems/dc04ed86-a27c-4c9d-97b2-c746e67a70dc
-- title:
--   Decentralized strategies without collision information: histories, policies, and uniform choices from a seed
-- statement:
--   In the weak feedback model a player observes only her own reward, never whether a collision occurred. The players do not communicate, know $m$, $K$, $T$, and all play the same algorithm, which may randomize.
--
--   1. A player's **history** after $t$ rounds is the list of pairs $(A_j(s),r_j(s))$, $s<t$: the arm she pulled and the reward she received.
--   2. A **policy** is a rule $\pi$ that, in round $t$, maps the history of the first $t$ rounds and a fresh private seed $u\in[0,1]$ to an arm $\pi_t(h,u)\in[K]$, measurably in $(h,u)$. Every player uses the same rule.
--   3. A **uniformly random arm** from a seed $u$ is arm $\min(\lfloor Ku\rfloor,K-1)$ (0-based); a **uniformly random element** of a set $G$ of arms is its $\min(\lfloor |G|u\rfloor,|G|-1)$-th element in increasing order. If $u$ is uniform on $[0,1]$ these choices are uniform.
--   4. The **uniform-exploration rule** pulls a uniformly random arm in every round.
--
--   The policy class is part of the meaning of "there is an algorithm" in Theorem 1: a rule that saw collision indicators, other players' arms, the means, or the player's index would solve a different problem.
--
--   **Formalization Note** The rule does not receive the player's index, so all players run the same algorithm. Measurability makes the regret a random variable. `NeZero K` supplies a default arm.
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, §1, pp.2–3 (weak feedback model), Assumption 3 and the paragraph after it, p.4; p.4 ("the strategy can randomize")

import Mathlib

namespace MultiplayerNoCollision

/-- **A player's own history after `t` rounds**: for each earlier round `s < t` the arm she pulled
and the reward she received (Lugosi, Mehrabian, arXiv:1808.08416v2, pp.2–3, the weak feedback model:
"the player just receives a reward without observing whether a collision has occurred").

**Formalization Note.** Rounds are 0-based. The history contains neither collision indicators nor
other players' arms or rewards. -/
abbrev History (K t : ℕ) := Fin t → Fin K × ℝ

/-- **A decentralized strategy without collision information, run by every player.**
Lugosi, Mehrabian, arXiv:1808.08416v2, pp.3–4: the players do not communicate, observe only their
own rewards, "all players play the same algorithm", know `T` and `m` (Assumption 3), and "the
strategy can randomize".

`act t h u` is the arm a player pulls in round `t` given her own history `h` of the first `t`
rounds and her fresh private seed `u ∈ [0,1]`. The rule is measurable in `(h, u)` for every `t`.

**Formalization Note.** The same rule is used by every player (it does not receive the player's
index). It sees no collision indicator, no other player's arm or reward, no mean and no law. It may
depend on `m`, `K`, `T`, which are fixed before it is chosen. Measurability makes the regret a random
variable. -/
structure Policy (K : ℕ) where
  /-- The arm pulled in round `t` from the own history and the current seed. -/
  act : (t : ℕ) → History K t → ℝ → Fin K
  /-- The rule is measurable in (history, seed). -/
  measurable_act : ∀ t, Measurable (fun p : History K t × ℝ => act t p.1 p.2)

/-- **A uniformly random arm from a seed** `u ∈ [0,1]`: arm `⌊K u⌋`, clamped to `K − 1`.
If `u` is uniform on `[0,1]`, this arm is uniform on `[K]` (the value `u = 1` has probability `0`). -/
noncomputable def unifArm {K : ℕ} [NeZero K] (u : ℝ) : Fin K :=
  ⟨min ⌊(K : ℝ) * u⌋₊ (K - 1), by have := NeZero.pos K; omega⟩

/-- **A uniformly random element of a set of arms** `G` from a seed `u ∈ [0,1]`: the
`min(⌊|G| u⌋, |G| − 1)`-th element of `G` in increasing order (arm `0` if `G = ∅`).
If `u` is uniform on `[0,1]` and `G ≠ ∅`, it is uniform on `G`. -/
noncomputable def unifElem {K : ℕ} [NeZero K] (G : Finset (Fin K)) (u : ℝ) : Fin K :=
  (G.sort (· ≤ ·)).getD (min ⌊(G.card : ℝ) * u⌋₊ (G.card - 1)) 0

/-- **The uniform-exploration rule**: pull a uniformly random arm in every round, ignoring the
history (Phase 1 of Algorithm 1, Lugosi, Mehrabian, arXiv:1808.08416v2, p.8). -/
noncomputable def uniformAct {K : ℕ} [NeZero K] : (t : ℕ) → History K t → ℝ → Fin K :=
  fun _ _ u => unifArm u

end MultiplayerNoCollision


