-- Prove2me | Definitions.Def_RobustCtxPricing_Supplement_Learner
-- name    : RobustCtxPricing_Supplement_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:04:27.980866+00:00
-- url     : https://prove2.me/theorems/b4479570-d9f4-42e8-85f4-a8e35914a02a
-- title:
--   Randomized online pricing learners without knowledge of $C$, and the high-probability guarantee of Theorem 6.1
-- statement:
--   This module defines the objects in which the impossibility result of §6 of Castiglioni–Stradi is stated, for dimension $d=1$.
--
--   1. **Learner.** A randomized learner has internal randomness $\omega$ on a probability space $\Omega$ and, for each horizon $T$, a price rule: the price of round $t$ is $\pi_T(\omega;u_1,\dots,u_t;Y_1,\dots,Y_{t-1})$, a function of the contexts so far and the feedback before round $t$, measurable in $\omega$ for every fixed history. It is not given the corruption budget $C$.
--   2. **Guarantee.** For a constant $a$, a function $g$ and a horizon $T$, the learner *guarantees $R_T\le aC+g(T)$ with probability at least $1-1/T$* if for every budget $C$, every $\theta^\star\in[-1,1]$, every context sequence $u_t\in[-1,1]$ with $v_t=\theta^\star u_t\ge0$, every set $S\subseteq[T]$ of at most $C$ attacked rounds fixed in advance, and every family of measurable maps $g_t:\mathbb R\to\{0,1\}$, the execution in which $Y_t=g_t(p_t)$ for $t\in S$ and $Y_t=\mathbb I\{p_t\le v_t\}$ for $t\notin S$ satisfies
--   $$
--   \mathbb P\big(R_T\le aC+g(T)\big)\ge1-\frac1T .
--   $$
--
--   **Formalization Note** $\mathbb R^1$ is `EuclideanSpace ℝ (Fin 1)` and $[-1,1]$ is its closed unit ball. The execution's feedback is given by its defining equations; since the learner is online, they have exactly one solution on the rounds $t<T$. A deterministic learner is the case of a one-point $\Omega$.
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, §6, pp.31–34 (Theorem 6.1, p.32; Equation (14), p.32; attacks fixed in advance, p.31; learner not given C, p.33)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model

open MeasureTheory

namespace RobustCtxPricing.Supplement

/-- **A randomized pricing algorithm that is not given the corruption budget (d = 1).**
Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual Pricing*,
arXiv:2607.11210, §6, pp.31–34 ("algorithm without knowledge of `C`, even randomized"; "Since the
learner is not given `C`, equal histories and equal learner randomness imply equal posted prices",
p.33).

A learner with internal randomness `ω ∈ Ω` is a map `π` such that `π T ω u Y t` is the price posted
in round `t` (`0`-based) of an interaction with horizon `T`, contexts `u` and observed feedback `Y`.
`IsOnlineLearner π` says:

1. (online) `π T ω u Y t` depends only on the contexts `u_0, …, u_t` and the feedback
   `Y_0, …, Y_{t−1}`;
2. (randomized algorithm) for every fixed horizon, context sequence, feedback sequence and round,
   the price is a measurable function of the internal randomness `ω`.

**Formalization Note.** The price map may depend on the horizon `T` but has no argument for the
corruption budget `C`: that is "without knowledge of `C`". A deterministic learner is the case of a
one-point `Ω`. Contexts lie in `ℝ¹ = EuclideanSpace ℝ (Fin 1)` (the theorem is "even when
`d = 1`"). -/
def IsOnlineLearner {Ω : Type*} [MeasurableSpace Ω]
    (π : ℕ → Ω → (ℕ → EuclideanSpace ℝ (Fin 1)) → (ℕ → Bool) → ℕ → ℝ) : Prop :=
  (∀ T ω (u u' : ℕ → EuclideanSpace ℝ (Fin 1)) (Y Y' : ℕ → Bool) t,
    (∀ s ≤ t, u s = u' s) → (∀ s < t, Y s = Y' s) → π T ω u Y t = π T ω u' Y' t) ∧
  (∀ T (u : ℕ → EuclideanSpace ℝ (Fin 1)) (Y : ℕ → Bool) t, Measurable fun ω => π T ω u Y t)

/-- **The high-probability guarantee `R_T ≤ aC + g(T)` with probability `≥ 1 − 1/T`, against
attacks fixed in advance (d = 1).** Castiglioni–Stradi, arXiv:2607.11210, §6, Theorem 6.1, p.32,
and Equation (14), p.32: "guarantee … `R_T = O(C) + o(log² T)`, with probability at least
`1 − 1/T` for every corruption budget `C`"; "all attacked rounds are selected before the interaction
begins" (p.31).

`HighProbGuarantee π a g T` says: for every corruption budget `C`, every parameter `θ⋆ ∈ Θ = [−1,1]`
(`d = 1`), every context sequence `u_t ∈ Θ` with valuations `v_t = ⟨θ⋆, u_t⟩ ≥ 0`, every set of
attacked rounds `S ⊆ {0, …, T−1}` with `|S| ≤ C` and every family of measurable attack maps
`g_t : ℝ → {0,1}`, the execution of `π` with horizon `T` (feedback `Y_t = g_t(p_t)` for `t ∈ S` and
the true sale bit `Y_t = 𝕀{p_t ≤ v_t}` for `t ∉ S`) has regret `R_T ≤ a·C + g(T)` with probability
at least `1 − 1/T` over the learner's randomness.

**Formalization Note.** The execution's feedback `Y ω` is given relationally: every `Y` satisfying
the feedback equations in all rounds `t < T` is quantified; because `π` is online, there is exactly
one such `Y ω` on the rounds `t < T` for each `ω`, and the regret depends only on those rounds. The
probability is `volume` on `Ω` (a probability measure in Theorem 6.1); the event is measurable for
an online learner and measurable attack maps. -/
def HighProbGuarantee {Ω : Type*} [MeasureSpace Ω]
    (π : ℕ → Ω → (ℕ → EuclideanSpace ℝ (Fin 1)) → (ℕ → Bool) → ℕ → ℝ)
    (a : ℝ) (g : ℕ → ℝ) (T : ℕ) : Prop :=
  ∀ (C : ℕ) (θ : EuclideanSpace ℝ (Fin 1)), θ ∈ Theta 1 →
  ∀ u : ℕ → EuclideanSpace ℝ (Fin 1), (∀ t < T, u t ∈ Theta 1 ∧ 0 ≤ inner ℝ θ (u t)) →
  ∀ S : Finset ℕ, S ⊆ Finset.range T → S.card ≤ C →
  ∀ atk : ℕ → ℝ → Bool, (∀ t, Measurable (atk t)) →
  ∀ Y : Ω → ℕ → Bool,
    (∀ ω, ∀ t < T, Y ω t =
      if t ∈ S then atk t (π T ω u (Y ω) t) else decide (π T ω u (Y ω) t ≤ inner ℝ θ (u t))) →
    ENNReal.ofReal (1 - 1 / (T : ℝ)) ≤
      volume {ω | regret T θ u (π T ω u (Y ω)) ≤ a * C + g T}

end RobustCtxPricing.Supplement


