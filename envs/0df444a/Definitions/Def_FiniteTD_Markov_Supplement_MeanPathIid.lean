-- Prove2me | Definitions.Def_FiniteTD_Markov_Supplement_MeanPathIid
-- name    : FiniteTD_Markov_Supplement_MeanPathIid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:38:43.427007+00:00
-- url     : https://prove2.me/theorems/a8603944-87d8-4cc9-8ec4-1dcb5e586651
-- title:
--   §6, §7, pp. 9, 13 — mean-path TD, the i.i.d. observation model (15), σ², unprojected TD(0), iterate averages
-- statement:
--   This file defines the algorithms of §§6–7 on top of the finite Markov reward process, the features and the mean TD direction $\bar g$ of the published mission.
--
--   1. **Iterate average.** For a parameter sequence $\theta_0,\theta_1,\dots$ in $\mathbb R^d$, $\bar\theta_T = T^{-1}\sum_{t=0}^{T-1}\theta_t$.
--   2. **Mean-path TD** (§6) with step $\alpha$: the deterministic recursion $\theta_{t+1} = \theta_t + \alpha\,\bar g(\theta_t)$ from a given $\theta_0$.
--   3. **Stationary tuple law** (15). A tuple $(s, R(s,s'), s')$ is drawn with probability $\pi(s)P(s'\mid s)$; for a function $f$ of the tuple, $\mathbb E f = \sum_{s,s'}\pi(s)P(s'\mid s)f(s,s')$.
--   4. **Noise level.** $\sigma^2 = \mathbb E\|g_t(\theta^*)\|_2^2 = \sum_{s,s'}\pi(s)P(s'\mid s)\,\|g(\theta^*;s,s')\|_2^2$.
--   5. **i.i.d. observation model.** $T$ tuples $O_t=(s_t,R(s_t,s'_t),s'_t)$, $t<T$, are independent, each with law (15); the list $(s_0,s'_0),\dots,(s_{T-1},s'_{T-1})$ has probability $\prod_{t<T}\pi(s_t)P(s'_t\mid s_t)$, and expectations are the corresponding finite sums. Nothing ties $s'_t$ to $s_{t+1}$.
--   6. **TD(0)** (Algorithm 1) driven by these tuples: $\theta_{t+1} = \theta_t + \alpha_t\,g(\theta_t; s_t, s'_t)$ for $t<T$, from a deterministic $\theta_0$, with no projection.
--
--   These are the objects in which Theorems 1 and 2 and Lemma 5 are stated.
--
--   **Formalization Note** The TD(0) recursion is driven by a list of exactly $T$ tuples and is kept constant after time $T$; every statement evaluates it at times $\le T$, where only the tuples $O_0,\dots,O_{t-1}$ enter $\theta_t$. The average uses $\theta_0,\dots,\theta_{T-1}$, as defined on p. 6 and recalled on p. 13.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 6 (θ̄_t), p. 9 and §6 (mean-path TD), p. 13 ((15), σ²), Algorithm 1 p. 7

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

namespace FiniteTD.Markov.Supplement

open scoped InnerProductSpace

variable {S : Type} [Fintype S] {d : ℕ}

/-- The average `T⁻¹ Σ_{t=0}^{T-1} θ_t` of the first `T` terms of a parameter sequence. -/
noncomputable def avgSeq (θ : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : EuclideanSpace ℝ (Fin d) :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, θ t

/-- Mean-path TD (§6) with constant step `α`: `θ₀` given and `θ_{t+1} = θ_t + α ḡ(θ_t)`. -/
noncomputable def meanPath (π : S → ℝ) (P : S → S → ℝ) (γ : ℝ) (Rw : S → S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (α : ℝ) (θ0 : EuclideanSpace ℝ (Fin d)) :
    ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => θ0
  | t + 1 => meanPath π P γ Rw φ α θ0 t + α • gbar π P γ Rw φ (meanPath π P γ Rw φ α θ0 t)

/-- Expectation of `f(s, s')` for one tuple `(s, R(s, s'), s')` drawn from the stationary tuple law
(15): `P[(s_t, s'_t) = (s, s')] = π(s) P(s'|s)`. -/
noncomputable def tupleExp (π : S → ℝ) (P : S → S → ℝ) (f : S → S → ℝ) : ℝ :=
  ∑ s, ∑ s', π s * P s s' * f s s'

/-- `σ² = E‖g_t(θ*)‖₂²` under the stationary tuple law (15). -/
noncomputable def sigmaSq (π : S → ℝ) (P : S → S → ℝ) (γ : ℝ) (Rw : S → S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d)) : ℝ :=
  tupleExp π P (fun s s' => ‖tdDir γ Rw φ θstar s s'‖ ^ 2)

/-- Probability of the list of tuples `(s_0, s'_0), …, (s_{T-1}, s'_{T-1})` in the i.i.d.
observation model: independent tuples, each with law (15). -/
noncomputable def iidProb (π : S → ℝ) (P : S → S → ℝ) (T : ℕ) (o : Fin T → S × S) : ℝ :=
  ∏ i : Fin T, π (o i).1 * P (o i).1 (o i).2

/-- Expectation `E[F(O_0, …, O_{T-1})]` over `T` independent stationary tuples, as a finite sum. -/
noncomputable def iidExp [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ) (T : ℕ)
    (F : (Fin T → S × S) → ℝ) : ℝ :=
  ∑ o : Fin T → S × S, iidProb π P T o * F o

/-- Unprojected TD(0) (Algorithm 1) driven by the tuples `o 0, …, o (T-1)`: `θ₀` given and
`θ_{t+1} = θ_t + α_t g(θ_t; s_t, s'_t)` for `t < T`; the sequence is frozen after time `T`. -/
noncomputable def tdIid (γ : ℝ) (Rw : S → S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (α : ℕ → ℝ)
    (θ0 : EuclideanSpace ℝ (Fin d)) {T : ℕ} (o : Fin T → S × S) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => θ0
  | t + 1 =>
      if h : t < T then
        tdIid γ Rw φ α θ0 o t + α t • tdDir γ Rw φ (tdIid γ Rw φ α θ0 o t) (o ⟨t, h⟩).1 (o ⟨t, h⟩).2
      else tdIid γ Rw φ α θ0 o t

end FiniteTD.Markov.Supplement


