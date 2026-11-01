-- Prove2me | Definitions.Def_MultiplayerNoCollision_algorithm1
-- name    : MultiplayerNoCollision_algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:44.232565+00:00
-- url     : https://prove2.me/theorems/370220da-a1dd-4c8f-a1e9-a6a10eb23e31
-- title:
--   Algorithm 1 (four phases with MusicalChairs1) as a decentralized policy
-- statement:
--   Every player runs the following algorithm, knowing $m$, $K$, $T$. Let
--   $$g=128K\log(3Km^2T^2).$$
--
--   1. **Phase 1.** Pull a uniformly random arm each round and keep the estimates $\hat\mu_{i,\tau}$ after $\tau$ rounds. Let $\hat\mu_{i_1,\tau}\ge\dots\ge\hat\mu_{i_K,\tau}$ be the sorted estimates. Phase 1 ends at the first $\tau\ge1$ with
--   $$\hat\mu_{i_m,\tau}-\hat\mu_{i_{m+1},\tau}\ge3\sqrt{g/\tau},$$
--   and $G=\{i_1,\dots,i_m\}$.
--   2. **Phase 2.** For $24\tau$ rounds, pull a uniformly random arm.
--   3. **Phase 3 (MusicalChairs1).** Each round pull a uniformly random arm of $G$; at the first positive reward the player has *occupied* that arm.
--   4. **Phase 4.** Pull the occupied arm until the end of the game.
--
--   The phases of different players are not synchronized. Every state variable ($\hat\mu$, $\tau$, $G$, the occupied arm) is a function of the player's own history, so the algorithm is a policy in the class of `Policy`. For the analysis, in the $T$-round game: $\tau_j$ is player $j$'s Phase-1 length ($\infty$ if Phase 1 is not over by round $T$), $G_j$ her list of best arms, and the number of rounds she spends in Phase 3 is counted.
--
--   **Formalization Note** Rounds are 0-based: Phase 1 is rounds $0,\dots,\tau-1$, Phase 2 rounds $\tau,\dots,25\tau-1$, and Phase 3 starts at round $25\tau$. At the stopping round the estimated gap is positive, so $G$ is the unique top-$m$ set of the estimates and the sort's tie-breaking is irrelevant. "$\infty$" is `none`. Measurability of this rule is not proved here; it is needed to use it as the policy of Theorem 1.
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, §3, Phases 1–4, pp.8–9; Algorithm 1 and MusicalChairs1, p.10

import Mathlib
import Definitions.Def_MultiplayerNoCollision_Policy
import Definitions.Def_MultiplayerNoCollision_kthLargest
import Definitions.Def_MultiplayerNoCollision_phase1Estimate
import Definitions.Def_MultiplayerNoCollision_profile

namespace MultiplayerNoCollision

open Finset

/-- **The exploration parameter** `g := 128 K log(3 K m² T²)` (Lugosi, Mehrabian,
arXiv:1808.08416v2, §3, p.8, and Algorithm 1, line 1, p.10); `log` is the natural logarithm (p.6).
The argument of the logarithm is positive whenever `m, K, T ≥ 1`. -/
noncomputable def gParam (m K T : ℕ) : ℝ :=
  128 * K * Real.log (3 * K * m ^ 2 * T ^ 2)

/-- The first `τ` rounds of a history of `t ≥ τ` rounds. -/
def restrictHist {K t : ℕ} (h : History K t) (τ : ℕ) (hτ : τ ≤ t) : History K τ :=
  fun s => h (Fin.castLE hτ s)

/-- **The stopping rule of Phase 1** (Lugosi, Mehrabian, arXiv:1808.08416v2, p.9, and Algorithm 1,
line 9, p.10): on a history of `τ` rounds, `µ̂_{i_m,τ} − µ̂_{i_{m+1},τ} ≥ 3 √(g/τ)`, where
`µ̂_{i_1,τ} ≥ ··· ≥ µ̂_{i_K,τ}` are the sorted estimates. -/
def StopRule (m K T : ℕ) {τ : ℕ} (h : History K τ) : Prop :=
  3 * Real.sqrt (gParam m K T / τ) ≤
    kthLargest (phase1Estimate m K h) (m - 1) - kthLargest (phase1Estimate m K h) m

/-- **The length `τ` of Phase 1** as seen in a history of `t` rounds: the least `τ ∈ [1, t]` such that
the stopping rule holds on the first `τ` rounds, or `none` if there is none (Phase 1 is not over).
Lugosi, Mehrabian, arXiv:1808.08416v2, p.9: "Let `τ` be the first round when
`µ̂_{i_m,τ} − µ̂_{i_{m+1},τ} ≥ 3√(g/τ)`. The first phase finishes at the end of round `τ`."

**Formalization Note.** `τ ≥ 1` because the loop of Algorithm 1 (p.10) increments `τ` before it
tests the rule. The rule at `τ` depends only on the first `τ` rounds, so the value is the same for
every `t` at which Phase 1 is over. -/
noncomputable def phase1Length (m K T : ℕ) {t : ℕ} (h : History K t) : Option ℕ :=
  open Classical in
  if hex : ∃ τ, ∃ hτ : τ ≤ t, 1 ≤ τ ∧ StopRule m K T (restrictHist h τ hτ)
  then some (Nat.find hex) else none

/-- **The best-`m`-arms list `G`** chosen at the end of Phase 1 of length `τ`: the `m` arms with the
largest estimates after `τ` rounds (Lugosi, Mehrabian, arXiv:1808.08416v2, p.9, and Algorithm 1,
line 10, p.10, `Best-m-arms ← {i_1, …, i_m}`); `∅` if `τ > t`.

**Formalization Note.** At the stopping round the estimated gap is `≥ 3√(g/τ) > 0`, so the top-`m`
set of the estimates is unique and no tie-breaking is involved. -/
noncomputable def bestArms (m K : ℕ) {t : ℕ} (h : History K t) (τ : ℕ) : Finset (Fin K) :=
  if hτ : τ ≤ t then topSet (phase1Estimate m K (restrictHist h τ hτ)) m else ∅

/-- **Rounds of Phases 3–4 with a positive reward**: the rounds `s < t` with `s ≥ 25τ` in which the
player received a positive reward. The first of them is the round at which she occupied an arm
(MusicalChairs1, p.10: "if positive reward is received then output `i`"). -/
noncomputable def positiveRounds {K t : ℕ} (h : History K t) (τ : ℕ) : Finset (Fin t) :=
  open Classical in univ.filter fun s => 25 * τ ≤ (s : ℕ) ∧ 0 < (h s).2

/-- **The phase (1, 2, 3 or 4) of Algorithm 1 in round `t`**, given the player's history of the first
`t` rounds (Lugosi, Mehrabian, arXiv:1808.08416v2, §3, pp.8–9, Algorithm 1, p.10):
1. Phase 1 while the stopping rule has not held;
2. Phase 2 in rounds `τ, …, 25τ − 1` (0-based), i.e. `24τ` rounds after Phase 1;
3. Phase 3 (MusicalChairs1) from round `25τ` until the first positive reward;
4. Phase 4 afterwards. -/
noncomputable def alg1Phase (m K T : ℕ) {t : ℕ} (h : History K t) : ℕ :=
  match phase1Length m K T h with
  | none => 1
  | some τ => if t < 25 * τ then 2 else if (positiveRounds h τ).Nonempty then 4 else 3

/-- **Algorithm 1 with MusicalChairs1** (Lugosi, Mehrabian, arXiv:1808.08416v2, §3, pp.8–10), as a
rule of the policy class: the arm pulled in round `t` from the own history `h` of `t` rounds and the
fresh seed `u`.
* Phases 1 and 2: a uniformly random arm, `unifArm u`.
* Phase 3: a uniformly random arm of `G = bestArms m K h τ`, `unifElem G u`.
* Phase 4: the occupied arm, i.e. the arm pulled in the first round `s ≥ 25τ` with a positive reward.

**Formalization Note.** Every quantity of the algorithm (`µ̂`, `τ`, `G`, the occupied arm) is a
deterministic function of the own history, so the algorithm is this memoryless rule. It uses `m`,
`K`, `T` (through `g`) and nothing else. -/
noncomputable def algorithm1 (m K T : ℕ) [NeZero K] (t : ℕ) (h : History K t) (u : ℝ) : Fin K :=
  match phase1Length m K T h with
  | none => unifArm u
  | some τ =>
    if t < 25 * τ then unifArm u
    else if hne : (positiveRounds h τ).Nonempty then (h ((positiveRounds h τ).min' hne)).1
    else unifElem (bestArms m K h τ) u

/-- **The Phase-1 length `τ_j` of player `j` in the `T`-round game** run with Algorithm 1: the value
of `phase1Length` on her full history of `T` rounds (`none` if Phase 1 has not finished by round
`T`). -/
noncomputable def stopRound {Ω : Type*} (m K T : ℕ) [NeZero K] (Y : Fin K → ℕ → Ω → ℝ)
    (U : Fin m → ℕ → Ω → ℝ) (ω : Ω) (j : Fin m) : Option ℕ :=
  phase1Length m K T (history (algorithm1 m K T) Y U ω j T)

/-- **The list `G_j` of player `j`** in the `T`-round game run with Algorithm 1, when her Phase 1
has length `τ`. -/
noncomputable def bestArmsOf {Ω : Type*} (m K T : ℕ) [NeZero K] (Y : Fin K → ℕ → Ω → ℝ)
    (U : Fin m → ℕ → Ω → ℝ) (ω : Ω) (j : Fin m) (τ : ℕ) : Finset (Fin K) :=
  bestArms m K (history (algorithm1 m K T) Y U ω j T) τ

/-- **The number of rounds `t < T` that player `j` spends in Phase 3** of Algorithm 1 in the
`T`-round game. -/
noncomputable def phase3Rounds {Ω : Type*} (m K T : ℕ) [NeZero K] (Y : Fin K → ℕ → Ω → ℝ)
    (U : Fin m → ℕ → Ω → ℝ) (ω : Ω) (j : Fin m) : ℕ :=
  open Classical in
  ((range T).filter fun t => alg1Phase m K T (history (algorithm1 m K T) Y U ω j t) = 3).card

end MultiplayerNoCollision


