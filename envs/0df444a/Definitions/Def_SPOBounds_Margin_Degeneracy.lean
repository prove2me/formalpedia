-- Prove2me | Definitions.Def_SPOBounds_Margin_Degeneracy
-- name    : SPOBounds_Margin_Degeneracy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:31:29.85132+00:00
-- url     : https://prove2.me/theorems/40f1cab4-6768-4ce0-b12f-3ae3949320ce
-- title:
--   Degenerate costs $\mathcal C^\circ$, distance to degeneracy $\nu_S$, strength property, $\gamma$-margin SPO loss
-- statement:
--   Let $S\subseteq E$ be a feasible region in a finite-dimensional real normed space, with cost vectors the continuous linear functionals on $E$ and dual norm $\|\cdot\|_*$; let $w^*$ be an optimization oracle for $S$ and $\ell_{\rm SPO}$, $\omega_S$ as in `SPOBounds.Margin.Model`.
--
--   1. **Degenerate cost vectors** (Definition 2). $\mathcal C^\circ := \{\hat c : P(\hat c) \text{ has multiple optimal solutions}\}$, where $P(\hat c)$ is $\min_{w\in S}\hat c^\top w$; that is, $\hat c\in\mathcal C^\circ$ iff there are $u\ne v$ in $S$ that both minimize $\hat c^\top w$ over $S$.
--   2. **Distance to degeneracy** (Definition 2). $\nu_S(\hat c) := \inf_{c\in\mathcal C^\circ}\|c-\hat c\|_*$.
--   3. **Strength property** (Definition 3). $S$ satisfies the strength property with parameter $\mu$ (for the oracle $w^*$) if
--   $$\hat c^\top\big(w - w^*(\hat c)\big) \;\ge\; \Big(\frac{\mu\,\nu_S(\hat c)}{2}\Big)\,\|w - w^*(\hat c)\|^2 \qquad\text{for all } w\in S \text{ and all } \hat c .$$
--   4. **$\gamma$-margin SPO loss** (Definition 4). For $\gamma>0$,
--   $$\ell^\gamma_{\rm mSPO}(\hat c,c) := \begin{cases}\ell_{\rm SPO}(\hat c,c) & \text{if } \nu_S(\hat c) > \gamma,\\[2pt] \dfrac{\nu_S(\hat c)}{\gamma}\,\ell_{\rm SPO}(\hat c,c) + \Big(1-\dfrac{\nu_S(\hat c)}{\gamma}\Big)\,\omega_S(c) & \text{if } \nu_S(\hat c) \le \gamma.\end{cases}$$
--   From Section 4.2 on the paper writes $\ell^\gamma_{\rm SPO}$ for the same loss.
--
--   When $S$ has at least two points, the zero cost vector is degenerate, so $\nu_S$ is finite, $0\le\nu_S(\hat c)\le\|\hat c\|_*$, and $\nu_S$ is 1-Lipschitz. The margin loss interpolates between the SPO loss and its upper bound $\omega_S(c)$ on the $\gamma$-neighbourhood of $\mathcal C^\circ$, and the strength property is what makes it Lipschitz in $\hat c$.
--
--   **Formalization Note** $\nu_S$ is `Metric.infDist` to $\mathcal C^\circ$ in the operator norm of `StrongDual ℝ E`, which is the dual norm. The strength property takes the oracle as a parameter, literally as in (5); by the paper's Remark 2 it does not depend on which oracle is used. The requirement $\mu>0$ of Definition 3 and $\gamma>0$ of Definition 4 are carried as hypotheses by every theorem, and every theorem also assumes that $S$ is not a singleton (the standing assumption of Section 4).
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 13 (Definition 2), p. 14 (Definition 3, eq. (5)), p. 15 (Definition 4)

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model

namespace SPOBounds.Margin

/-- The set of degenerate cost vector predictions (Definition 2, p. 13):
`𝒞° = {ĉ : P(ĉ) has multiple optimal solutions}`, i.e. `v ↦ ĉ v` has two distinct minimizers
over `S`. -/
def degenerate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) : Set (StrongDual ℝ E) :=
  {chat | ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ IsMinOn (fun x => chat x) S u ∧
    IsMinOn (fun x => chat x) S v}

/-- The distance to degeneracy `ν_S(ĉ) = inf_{c ∈ 𝒞°} ‖c − ĉ‖_*` (Definition 2, p. 13),
measured in the operator (= dual) norm. When `S` has two distinct points, `0 ∈ 𝒞°`, so the
infimum is over a nonempty set. -/
noncomputable def nu {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (chat : StrongDual ℝ E) : ℝ :=
  Metric.infDist chat (degenerate S)

/-- The strength property (Definition 3, p. 14), for the oracle `w` and parameter `μ`:
`ĉᵀ(v − w*(ĉ)) ≥ (μ ν_S(ĉ) / 2) ‖v − w*(ĉ)‖²` for all `v ∈ S` and all `ĉ`.
The requirement `μ > 0` is carried separately by every theorem. -/
def StrengthProperty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (μ : ℝ) (w : StrongDual ℝ E → E) : Prop :=
  ∀ chat : StrongDual ℝ E, ∀ v ∈ S,
    μ * nu S chat / 2 * ‖v - w chat‖ ^ 2 ≤ chat (v - w chat)

/-- The `γ`-margin SPO loss (Definition 4, p. 15; written `ℓ^γ_SPO` from p. 18 on):
`ℓ_SPO(ĉ, c)` if `ν_S(ĉ) > γ`, and
`(ν_S(ĉ)/γ) ℓ_SPO(ĉ, c) + (1 − ν_S(ĉ)/γ) ω_S(c)` if `ν_S(ĉ) ≤ γ`.
Every theorem using it assumes `γ > 0`. -/
noncomputable def marginLoss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ) (chat c : StrongDual ℝ E) : ℝ :=
  if γ < nu S chat then spoLoss w chat c
  else nu S chat / γ * spoLoss w chat c + (1 - nu S chat / γ) * omega S c

end SPOBounds.Margin


