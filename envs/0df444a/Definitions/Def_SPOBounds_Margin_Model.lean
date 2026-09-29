-- Prove2me | Definitions.Def_SPOBounds_Margin_Model
-- name    : SPOBounds_Margin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:30:55.725681+00:00
-- url     : https://prove2.me/theorems/c8d10c0c-9fb2-46f0-b126-c5f64cc37f59
-- title:
--   Predict-then-optimize model: optimization oracle, SPO loss, linear optimization gap $\omega_S$, cost radius $\rho(\mathcal C)$
-- statement:
--   This file fixes the optimization model of the predict-then-optimize framework in a finite-dimensional real normed space $E$ (the paper's $\mathbb R^d$ with a generic norm $\|\cdot\|$). A cost vector is a continuous linear functional $c$ on $E$, so $c^\top w$ is the value $c(w)$, and the operator norm $\|c\|$ is the dual norm $\|c\|_* = \max_{\|w\|\le 1} c^\top w$.
--
--   1. **Optimization oracle.** For a feasible region $S\subseteq E$, a map $w^*$ from cost vectors to $E$ is an *oracle* for $S$ if, for every cost vector $c$,
--   $$w^*(c)\in S \quad\text{and}\quad c(w^*(c))\le c(v)\ \text{ for all } v\in S,$$
--   i.e. $w^*(c)\in\arg\min_{w\in S} c^\top w$. No tie-breaking rule is imposed.
--   2. **SPO loss.** For a predicted cost $\hat c$ and a realized cost $c$,
--   $$\ell_{\rm SPO}(\hat c, c) := c^\top w^*(\hat c) - c^\top w^*(c).$$
--   3. **Linear optimization gap.** $\omega_S(c) := \max_{w\in S} c^\top w - \min_{w\in S} c^\top w$, and for a set $\mathcal C$ of cost vectors $\omega_S(\mathcal C) := \sup_{c\in\mathcal C}\omega_S(c)$.
--   4. **Cost radius.** $\rho(\mathcal C) := \sup_{c\in\mathcal C}\|c\|_*$; in the $\ell_2$ set-up this is the paper's $\rho_2(\mathcal C)=\sup_{c\in\mathcal C}\|c\|_2$.
--
--   For an oracle, $0\le\ell_{\rm SPO}(\hat c,c)\le\omega_S(c)$, so $\omega_S(\mathcal C)$ is the range of the SPO loss on costs in $\mathcal C$. Together with $\rho(\mathcal C)$ it sets the scale of the margin-based bounds.
--
--   **Formalization Note** Cost vectors are elements of the continuous dual `StrongDual ℝ E`. The maximum and minimum in $\omega_S(c)$ are `sSup` and `sInf` of the image of $S$; they are attained whenever $S$ is nonempty and compact, which every theorem assumes. $\omega_S(\mathcal C)$ and $\rho(\mathcal C)$ are `sSup`s over $\mathcal C$ and are used only for nonempty bounded $\mathcal C$.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 5 (§2, oracle, eq. (2)), p. 6 (SPO loss), p. 8 (§2.1, linear optimization gap, dual norm), p. 19 ($\rho_2(\mathcal C)$)

import Mathlib

namespace SPOBounds.Margin

/-- `w` is an optimization oracle for the feasible region `S` (arXiv:1905.11488v3, p. 5):
for every cost vector `c` (a continuous linear functional, so `cᵀv` is `c v`), `w c` lies in
`S` and minimizes `v ↦ c v` over `S`. No tie-breaking rule is imposed. -/
def IsOracle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (w : StrongDual ℝ E → E) : Prop :=
  ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ v ∈ S, c (w c) ≤ c v

/-- The SPO loss `ℓ_SPO(ĉ, c) = cᵀ w*(ĉ) − cᵀ w*(c)` of the oracle `w` (p. 6). -/
noncomputable def spoLoss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : StrongDual ℝ E → E) (chat c : StrongDual ℝ E) : ℝ :=
  c (w chat) - c (w c)

/-- The linear optimization gap `ω_S(c) = max_{w ∈ S} cᵀw − min_{w ∈ S} cᵀw` (p. 8), written
with `sSup`/`sInf` of the image `c '' S` (attained for nonempty compact `S`). -/
noncomputable def omega {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (c : StrongDual ℝ E) : ℝ :=
  sSup ((fun v => c v) '' S) - sInf ((fun v => c v) '' S)

/-- `ω_S(𝒞) = sup_{c ∈ 𝒞} ω_S(c)` (p. 8). Used only for nonempty bounded `C`. -/
noncomputable def omegaSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (C : Set (StrongDual ℝ E)) : ℝ :=
  sSup (omega S '' C)

/-- `ρ(𝒞) = sup_{c ∈ 𝒞} ‖c‖_*` (p. 19; `ρ₂(𝒞)` in the ℓ₂ set-up, where the dual norm is the
Euclidean norm). The norm of a continuous linear functional is its operator norm, i.e. the dual
norm. Used only for nonempty bounded `C`. -/
noncomputable def rhoSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set (StrongDual ℝ E)) : ℝ :=
  sSup ((fun c => ‖c‖) '' C)

end SPOBounds.Margin


