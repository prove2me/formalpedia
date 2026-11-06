-- Prove2me | Definitions.Def_AdvMultiplayer_Strategy
-- name    : AdvMultiplayer_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:57.87957+00:00
-- url     : https://prove2.me/theorems/5416aa20-7a9f-42fc-a0e0-c783fdffee2c
-- title:
--   Model (1): strategies, private tapes, observations and regret (2)
-- statement:
--   There are $m$ players, with labels $0,\dots,m-1$, and an oblivious adversary fixes rewards $r_t(a)\in[0,1]$. In round $t$ player $i$ chooses an arm $A_{i,t}$ and observes only
--   $$Y_{i,t}=r_t(A_{i,t})\,\mathbf 1\{A_{j,t}\ne A_{i,t}\text{ for every }j\ne i\}.$$
--   A strategy gives each player's action as a function of the round, its own previous actions and observations, and its private randomness. The regret against $r$ is
--   $$R_T(r)=\max_{S\in\mathcal S}\sum_{t=1}^T r_t(S)-\mathbb E\sum_{t=1}^T\sum_{i=0}^{m-1}Y_{i,t},$$
--   where $\mathcal S$ is the family of $m$-subsets of the arms and the expectation is over the private randomness.
--
--   This is the model in which the main theorem is stated.
--
--   **Formalization Note.** The private randomness is a tape of independent $\mathrm{Unif}([0,1))$ coordinates per player, four per round, and the joint law of the tapes is a product over players. The type of a strategy has no argument for other players' data or for the rewards.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 1.1, (1), (2), pp.3-4

import Mathlib
import Definitions.Def_AdvMultiplayer_Size

open MeasureTheory

namespace AdvMultiplayer

/-- `Unif([0,1))`, the unit-cost draw of Section 8 (p.48). -/
noncomputable def unif : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif]⟩

/-- A player's private tape: four `Unif([0,1))` coordinates per round. -/
abbrev Tape (p : Size) := Fin p.T → Fin 4 → ℝ

/-- The tapes of all players. -/
abbrev Tapes (p : Size) := Fin p.m → Tape p

/-- The joint law of the private tapes: all coordinates independent `Unif([0,1))`, so distinct
players are independent and there is no common seed. -/
noncomputable def tapeLaw (p : Size) : Measure (Tapes p) :=
  Measure.pi fun _ => Measure.pi fun _ => Measure.pi fun _ => unif

/-- A player's own history: its arms and observations in the rounds so far. -/
abbrev History (p : Size) := List (Fin p.K × ℝ)

/-- **Strategy profile of model (1).** Gan, arXiv:2610.05688, Section 1.1, p.3: "Its action may
depend on the common knowledge, its own previous actions and observations, and its private
randomness. There is no other communication channel and no common random seed."

For each player and calendar round, a function of the player's own history and its own tape. Rewards
and other players' data are not arguments, so the type admits nothing else.

**Formalization Note.** Arm label `a ∈ [K]` is the element `a - 1` of `Fin K`, and calendar rounds
are `1, …, T`. The private randomness is a concrete tape of `Unif([0,1))` coordinates (`encoding`):
Section 8 counts such draws as the unit of randomness. -/
def Strategy (p : Size) := Fin p.m → ℕ → History p → Tape p → Fin p.K

/-- A reward matrix: `r t a` for calendar round `t ∈ [T]` and arm `a`; values off `[T]` are never
read. -/
abbrev Rewards (p : Size) := ℕ → Fin p.K → ℝ

/-- `r ∈ [0,1]^{T×K}` (p.3). -/
def IsRewards (p : Size) (r : Rewards p) : Prop :=
  ∀ t ∈ Finset.Icc 1 p.T, ∀ a, 0 ≤ r t a ∧ r t a ≤ 1

/-- The observation (1), p.3: `Y_{i,t} = r_t(A_{i,t}) 1{A_{j,t} ≠ A_{i,t} for every j ≠ i}`. -/
noncomputable def payoff (p : Size) (r : Rewards p) (t : ℕ) (a : Fin p.m → Fin p.K) (i : Fin p.m) :
    ℝ := by
  classical exact if ∀ j, j ≠ i → a j ≠ a i then r t (a i) else 0

/-- The players' histories after `n` rounds of play. -/
noncomputable def histories (p : Size) (s : Strategy p) (r : Rewards p) (ω : Tapes p) :
    ℕ → Fin p.m → History p
  | 0 => fun _ => []
  | n + 1 => fun i =>
      histories p s r ω n i ++
        [(s i (n + 1) (histories p s r ω n i) (ω i),
          payoff p r (n + 1) (fun j => s j (n + 1) (histories p s r ω n j) (ω j)) i)]

/-- The arm `A_{i,t}` in the play of `s`. -/
noncomputable def armAt (p : Size) (s : Strategy p) (r : Rewards p) (ω : Tapes p) (t : ℕ)
    (i : Fin p.m) : Fin p.K :=
  s i t (histories p s r ω (t - 1) i) (ω i)

/-- The observation `Y_{i,t}` in the play of `s`. -/
noncomputable def obsAt (p : Size) (s : Strategy p) (r : Rewards p) (ω : Tapes p) (t : ℕ)
    (i : Fin p.m) : ℝ :=
  payoff p r t (fun j => armAt p s r ω t j) i

/-- `Σ_t Σ_i Y_{i,t}`. -/
noncomputable def totalReward (p : Size) (s : Strategy p) (r : Rewards p) (ω : Tapes p) : ℝ :=
  ∑ t ∈ Finset.Icc 1 p.T, ∑ i, obsAt p s r ω t i

/-- `r_t(S) = Σ_{a∈S} r_t(a)`. -/
def setReward (p : Size) (r : Rewards p) (t : ℕ) (S : Finset (Fin p.K)) : ℝ := ∑ a ∈ S, r t a

/-- The family `𝒮` of `m`-subsets of the arms, nonempty because `m < K`. -/
def mSets (p : Size) : Finset (Finset (Fin p.K)) := Finset.powersetCard p.m Finset.univ

lemma mSets_nonempty (p : Size) : (mSets p).Nonempty :=
  Finset.powersetCard_nonempty.2 (by simpa using p.m_lt_K.le)

/-- The regret (2), p.4: `max_{S∈𝒮} Σ_t r_t(S) - E Σ_t Σ_i Y_{i,t}`, the expectation over the
private tapes. It is a signed real number; `Y` are the true, unrounded rewards. -/
noncomputable def regret (p : Size) (s : Strategy p) (r : Rewards p) : ℝ :=
  (mSets p).sup' (mSets_nonempty p) (fun S => ∑ t ∈ Finset.Icc 1 p.T, setReward p r t S)
    - ∫ ω, totalReward p s r ω ∂(tapeLaw p)

end AdvMultiplayer


