-- Prove2me | Definitions.Def_SambaPG_SambaNoise
-- name    : SambaPG_SambaNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:43.830604+00:00
-- url     : https://prove2.me/theorems/7f0723ae-06a9-4564-9877-d8e984877993
-- title:
--   The randomness of SAMBA: arm uniforms, tie-break uniforms and the Bernoulli reward table
-- statement:
--   On a probability space $(\Omega,\mathcal F,\mathbb P)$, the randomness used by SAMBA on a Bernoulli bandit consists of, for every time $t\in\mathbb Z_+$:
--
--   1. a uniform variable $U_t$ on $[0,1]$, used to draw the arm played at time $t$;
--   2. a uniform variable $V_t$ on $[0,1]$, used to break ties when choosing the leading arm;
--   3. the rewards $R_a(t)\in\{0,1\}$ of all arms, with $\mathbb P(R_a(t)=1)=r_a$.
--
--   All of these scalar variables, over all times and arms, are mutually independent. In particular the reward table $(R_a(t):t\in\mathbb Z_+,a\in\mathcal A)$ is independent, as assumed in the paper.
--
--   **Formalization Note** The rewards are $\{0,1\}$-valued almost surely. Independence is stated as mutual independence of the family indexed by (time, source), where a source is the arm uniform, the tie-break uniform or the reward of one arm.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, §3.1, p.6; §3.2, p.7; §3.4, p.7

import Mathlib
import Definitions.Def_SambaPG_BernoulliBandit

open MeasureTheory ProbabilityTheory

namespace SambaPG

/-- The scalar sources of randomness used at each time step of SAMBA: the uniform variable that
draws the arm (`arm`), the uniform variable that breaks ties for the leading arm (`tie`), and the
reward `R_a(t)` of each arm `a` (`reward a`). -/
inductive Src (A : Type*) where
  | arm : Src A
  | tie : Src A
  | reward : A → Src A

/-- The scalar random variable attached to the source `c` at time `t`. -/
def Src.coord {A Ω : Type*} (U V : ℕ → Ω → ℝ) (R : ℕ → Ω → A → ℝ) :
    ℕ × Src A → Ω → ℝ
  | (t, .arm) => U t
  | (t, .tie) => V t
  | (t, .reward a) => fun ω => R t ω a

/-- **The randomness driving SAMBA on a Bernoulli bandit.**
Denisov & Walton, arXiv:2007.10229v3, §3.1, p.6 (rewards), §3.2, p.7 (randomized policies), §3.4,
p.7 (random tie-breaking of the leading arm).

On a probability space `(Ω, μ)`:
* `R t ω a` is the reward `R_a(t)` of arm `a` at time `t`: `R_a(t) ∈ {0, 1}` and
  `P(R_a(t) = 1) = r_a` (p.6);
* `U t` is the independent uniform `[0, 1]` variable with which the policy draws its arm at time
  `t` (p.7: "an independent uniform [0, 1] random variable used for randomization");
* `V t` is the uniform `[0, 1]` variable with which a tie for the leading arm is broken at time `t`
  (p.7: "we select `a⋆(t)` at random amongst the set of maximizing arms").

All these scalar variables, over all times, are mutually independent (`indep`). In particular the
reward table `(R_a(t) : t ∈ ℤ₊, a ∈ A)` is independent, as assumed on p.6.

**Formalization Note.** The rewards are `{0, 1}`-valued almost surely. The joint independence of
the uniforms with each other and with the rewards is the paper's "independent" randomization. -/
structure SambaNoise {A : Type*} [Fintype A] (B : BernoulliBandit A) {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- Arm-drawing uniforms. -/
  U : ℕ → Ω → ℝ
  /-- Tie-breaking uniforms. -/
  V : ℕ → Ω → ℝ
  /-- The reward table `R_a(t)`. -/
  R : ℕ → Ω → A → ℝ
  measurable_U : ∀ t, Measurable (U t)
  measurable_V : ∀ t, Measurable (V t)
  measurable_R : ∀ t a, Measurable fun ω => R t ω a
  law_U : ∀ t, μ.map (U t) = volume.restrict (Set.Icc (0 : ℝ) 1)
  law_V : ∀ t, μ.map (V t) = volume.restrict (Set.Icc (0 : ℝ) 1)
  bernoulli_R : ∀ t a, ∀ᵐ ω ∂μ, R t ω a = 0 ∨ R t ω a = 1
  mean_R : ∀ t a, μ {ω | R t ω a = 1} = ENNReal.ofReal (B.r a)
  indep : iIndepFun (Src.coord U V R) μ

end SambaPG


