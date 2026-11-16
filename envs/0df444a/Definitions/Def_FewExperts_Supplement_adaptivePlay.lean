-- Prove2me | Definitions.Def_FewExperts_Supplement_adaptivePlay
-- name    : FewExperts_Supplement_adaptivePlay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:54:56.814208+00:00
-- url     : https://prove2.me/theorems/b9c1d205-f33c-4b27-ba30-073855114d9a
-- title:
--   Adaptive adversaries, the adaptive interaction, and the number of distinct experts played
-- statement:
--   1. For an action sequence $a$, let $D_T(a)=|\{a_1,\dots,a_T\}|$ be the **number of distinct experts played** in rounds $1,\dots,T$.
--   2. An **adaptive adversary** chooses the gain vector $g_t$ of round $t$ as a function of the experts $a_1,\dots,a_{t-1}$ played in the earlier rounds. It has gains in $[0,1]$ over the horizon $T$ if $g_t\in[0,1]^N$ for every round $t\le T$ and every history.
--   3. A randomized online algorithm $\mathcal A$ with randomness $\omega$ plays $a_t=\mathcal A(\omega,t,g_1,\dots,g_{t-1})$ at round $t$. Against an adaptive adversary the interaction is recursive:
--   $$a_t=\mathcal A(\omega,t,g_1,\dots,g_{t-1}),\qquad g_s=\mathrm{adv}(s,a_1,\dots,a_{s-1}).$$
--   The realized gains and plays determine the realized regret.
--
--   These are the objects of the lower bounds of §6: Theorem 6 (oblivious adversaries) uses $D_T$, and Theorem 7 uses the adaptive interaction.
--
--   **Formalization Note** The interaction is defined by recursion on the number of rounds played (`actsUpTo`), and `adaptivePlay` reads off the action of each round. The learner sees each round's full gain vector after acting. The adversary sees the learner's past actions, not its randomness.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §1, p.2 (PDF p.3), and §6, Theorems 6–7, p.34 (PDF p.35)

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting
import Definitions.Def_FewExperts_gainRegret

namespace FewExperts.Supplement

/-- The number of distinct experts played in rounds `1, …, T` by the action sequence `a`
(Theorems 6 and 7, p.34: "the number of distinct experts played"). -/
def numPlayed {N : ℕ} (T : ℕ) (a : ℕ → Fin N) : ℕ :=
  ((Finset.Icc 1 T).image a).card

/-- An **adaptive adversary** (§1, p.2; Theorem 7, p.34): at round `t` it chooses the gain vector
`g_t ∈ ℝ^N` as a function of the experts `a_1, …, a_{t−1}` played in the previous rounds (given as a
function on `Fin (t − 1)`, entry `s` being `a_{s+1}`). -/
abbrev AdaptiveAdv (N : ℕ) : Type := (t : ℕ) → (Fin (t - 1) → Fin N) → Fin N → ℝ

/-- An adaptive adversary over the horizon `T` has gains in `[0, 1]` at every round `1, …, T`. -/
def IsAdaptiveAdv {N : ℕ} (T : ℕ) (adv : AdaptiveAdv N) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ (hist : Fin (t - 1) → Fin N) (i : Fin N), adv t hist i ∈ Set.Icc (0 : ℝ) 1

/-- The gain vector of round `s` chosen by `adv` when the actions played so far are `acts`
(only `acts 1, …, acts (s − 1)` are read). -/
def advGain {N : ℕ} (adv : AdaptiveAdv N) (acts : ℕ → Fin N) (s : ℕ) : Fin N → ℝ :=
  adv s (fun r : Fin (s - 1) => acts (r.val + 1))

/-- The actions of the interaction after `t` rounds (rounds `1, …, t`; later rounds set to expert
`0`): at round `t + 1` the algorithm `A` (randomness `ω`) is fed the gain vectors
`g_1, …, g_t` that `adv` chose in response to the earlier actions, and plays `A ω (t + 1) (g_1..g_t)`.
-/
def actsUpTo {Ω : Type*} {N : ℕ} [NeZero N] (A : LimitedSwitching.HighProb.OnlineAlg Ω N)
    (adv : AdaptiveAdv N) (ω : Ω) : ℕ → ℕ → Fin N
  | 0 => fun _ => 0
  | t + 1 =>
    let a := actsUpTo A adv ω t
    fun u => if u = t + 1 then A ω (t + 1) (fun s => advGain adv a (s.val + 1)) else a u

/-- **The interaction of an online algorithm with an adaptive adversary** (§1, p.2; proof of
Theorem 7, p.34): the expert `a_t` played at round `t`, where `a_t = A ω t (g_1, …, g_{t−1})` and
`g_s = adv s (a_1, …, a_{s−1})`.
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §1, p.2 (PDF 3), and Theorem 7, p.34 (PDF 35).

**Formalization Note** The learner sees each round's full gain vector after acting (full
information); the adversary sees the learner's past actions, not its randomness. -/
def adaptivePlay {Ω : Type*} {N : ℕ} [NeZero N] (A : LimitedSwitching.HighProb.OnlineAlg Ω N)
    (adv : AdaptiveAdv N) (ω : Ω) : ℕ → Fin N :=
  fun t => actsUpTo A adv ω t t

/-- The gain array realized in the interaction: `g_s = adv s (a_1, …, a_{s−1})`. -/
def adaptiveGains {Ω : Type*} {N : ℕ} [NeZero N] (A : LimitedSwitching.HighProb.OnlineAlg Ω N)
    (adv : AdaptiveAdv N) (ω : Ω) : ℕ → Fin N → ℝ :=
  advGain adv (adaptivePlay A adv ω)

end FewExperts.Supplement


