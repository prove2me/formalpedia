-- Prove2me | Definitions.Def_CoupledLearning_IsModel
-- name    : CoupledLearning_IsModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:13.993166+00:00
-- url     : https://prove2.me/theorems/afb7790c-6981-4ea6-8051-f691cef7c842
-- title:
--   The learning model of §2: strategy sets, payoff densities, utilities and strategy updates
-- statement:
--   The model consists of strategy sets $Q_i\subseteq\mathbb R^{d_i}$, payoff densities $\varphi^s(y|q)$, average payoffs $u_i^s(q)$ and strategy updates $F_i(\theta,q)$, subject to:
--
--   1. each $Q_i$ is convex, closed and bounded;
--   2. for every $s$ and $q$, $\varphi^s(\cdot|q)$ is a probability density on $\mathbb R^I$ (nonnegative, measurable, integral $1$);
--   3. $\varphi^s(y|q)$ is continuous in $q$ for every $s$ and $y$;
--   4. $u_i^s$ is continuous on $Q$;
--   5. $F_i:\Delta(S)\times Q\rightrightarrows Q_i$, i.e. $F_i(\theta,q)\subseteq Q_i$ for every belief $\theta$ and $q\in Q$.
--
--   These are the standing hypotheses of every result of the mission.
--
--   **Formalization Note** The densities are required for every profile, not only for $q\in Q$; every instance of the paper extends by composing with the componentwise Euclidean projection onto $Q$, and the dynamics only evaluates them on $Q$ almost surely. The paper's decomposition $y_i=u_i^s(q)+\epsilon_i^s(q)$ with zero-mean noise (so that $u_i^s$ is the mean of $y_i$) is not imposed. No closed, compact or nonempty values of $F_i$ are assumed.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, §2, pp.7–8, eq. (1), (q-update)

import Mathlib
import Definitions.Def_CoupledLearning_Prof

open MeasureTheory

namespace CoupledLearning

/-- The standing model of §2 (arXiv:2206.05637v2, pp.7–8). The data are strategy sets
`Q i ⊆ ℝ^{d i}`, payoff densities `φ s q y = φ^s(y|q)` on payoff vectors `y ∈ ℝ^I`, average
payoff functions `u s i q = u_i^s(q)` and strategy updates `F i θ q = F_i(θ, q)`. The model
requires:

1. each `Q_i` is convex, closed and bounded (p.7);
2. for every parameter `s` and profile `q`, `φ^s(·|q)` is a probability density on `ℝ^I`
   (nonnegative, measurable, integral `1`) (p.7);
3. `φ^s(y|q)` is continuous in `q` for every `s` and `y` (p.7);
4. `u_i^s(q)` is continuous in `q` on `Q` (p.7);
5. `F_i : Δ(S) × Q ⇒ Q_i`: for a belief `θ ∈ Δ(S)` and `q ∈ Q`, `F_i(θ, q) ⊆ Q_i` (p.8).

**Formalization Note.** (a) The paper's densities are given for `q ∈ Q` only; here `φ` is a density
for every `q ∈ ℝ^{d}` and continuous in `q` on all of it. This loses no instance: compose the
paper's `φ` with the componentwise Euclidean projection onto the closed convex sets `Q_i`; the
learning process stays in `Q` almost surely, so only values on `Q` matter. (b) The paper writes
`y_i = u_i^s(q) + ε_i^s(q)` with zero-mean noise, i.e. `u_i^s` is the mean of `y_i`; that link is
not imposed: `u` is any family of functions continuous on `Q`. (c) No closed, compact or
nonempty values of `F_i` are assumed. -/
structure IsModel {I S : Type*} [Fintype I] [Fintype S] {d : I → ℕ}
    (Q : (i : I) → Set (EuclideanSpace ℝ (Fin (d i))))
    (φ : S → Prof d → (I → ℝ) → ℝ) (u : S → I → Prof d → ℝ)
    (F : (i : I) → (S → ℝ) → Prof d → Set (EuclideanSpace ℝ (Fin (d i)))) : Prop where
  convex : ∀ i, Convex ℝ (Q i)
  closed : ∀ i, IsClosed (Q i)
  bounded : ∀ i, Bornology.IsBounded (Q i)
  density_nonneg : ∀ s q y, 0 ≤ φ s q y
  density_measurable : ∀ s q, Measurable (φ s q)
  density_integral : ∀ s q, ∫ y, φ s q y = 1
  density_continuous : ∀ s y, Continuous (fun q => φ s q y)
  utility_continuous : ∀ s i, ContinuousOn (u s i) (Qset Q)
  update_maps : ∀ i, ∀ θ ∈ stdSimplex ℝ S, ∀ q ∈ Qset Q, F i θ q ⊆ Q i

end CoupledLearning


