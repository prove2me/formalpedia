-- Prove2me | Definitions.Def_DirectedSearch_Approx_Star
-- name    : DirectedSearch_Approx_Star
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:08.047059+00:00
-- url     : https://prove2.me/theorems/c0dec229-1b70-4a2c-abfe-f24433b9bacf
-- title:
--   §4.2.2 — f*_mw_i, idealized thresholds τ̂_w_i and equilibria (12) where f_mw_i = f*_mw_i
-- statement:
--   Consider a type $m$ (in a star-shaped market, the only type of its side), a list $w_1,\dots,w_n$ of types of the other side, and a matrix $\beta$. Set
--   $$f^*_{mw_i}:=\frac{\beta_{mw_i}}{\delta+\int_{\rho_{mw_i}}^\infty dF_{mw_i}}.$$
--
--   A number $\hat\tau_{w_i}$ is an **idealized threshold** of $w_i$ when $\hat\tau_{w_i}\ge0$ and
--   $$\hat\tau_{w_i}=\frac1{\alpha_{w_i}}f^*_{mw_i}\int_{\hat\tau_{w_i}}^\infty u\,dF_{mw_i},$$
--   the threshold type $w_i$ would set if $\tau_m=0$.
--
--   An **equilibrium where $f_{mw_i}=f^*_{mw_i}$** is a pair of nonnegative thresholds $\tau_m$, $(\tau_{w_i})_i$ solving the fixed-point equations (12):
--   $$\tau_m=\frac1{\alpha_m}\sum_{i=1}^n f^*_{mw_i}\int_{\max(\tau_m,\tau_{w_i})}^\infty u\,dF_{mw_i},\qquad \tau_{w_i}=\frac1{\alpha_{w_i}}f^*_{mw_i}\int_{\max(\tau_m,\tau_{w_i})}^\infty u\,dF_{mw_i}.$$
--
--   These are the objects of Lemmas 4.10–4.12, the internal chain of Proposition 4.8.
--
--   **Formalization Note.** The list is `ws : Fin n → W`, indexed from 0. Idealized thresholds are restricted to $[0,\infty)$: the threshold $w_i$ would set is an expected utility, and on all of $\mathbb R$ the equation can have a second, negative root. Equilibrium thresholds are nonnegative for the same reason (they are expected utilities by Proposition 3.1). Equation (12) is the paper's rescaling of (6e) by $\eta_\theta$ at $f=f^*$.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 25, §4.2.2: f*_mw_i, (12), idealized thresholds τ̂_w_i

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting

namespace DirectedSearch.Approx

/-- `f*_{mw_i} := β*_{mw_i} / (δ + ∫_{ρ_{mw_i}}^∞ dF_{mw_i})` (§4.2.2, p. 25), for the type `m`
of a star-shaped market and the listed types `w_1, …, w_n` (`ws : Fin n → W`). -/
noncomputable def fstar {M W : Type} (mk : Market M W) (β : M → W → ℝ) (m : M) {n : ℕ}
    (ws : Fin n → W) (i : Fin n) : ℝ :=
  β m (ws i) / (mk.δ + tailMass (mk.F m (ws i)) (rho mk m (ws i)))

/-- `t` is an idealized threshold `τ̂_{w_i}` (§4.2.2, p. 25): the threshold type `w_i` would set
if `τ_m = 0`, i.e. a solution in `[0, ∞)` of `τ̂ = (1/α_{w_i}) f*_{mw_i} ∫_{τ̂}^∞ u dF_{mw_i}`. -/
def IsIdealThreshold {M W : Type} (mk : Market M W) (β : M → W → ℝ) (m : M) {n : ℕ}
    (ws : Fin n → W) (i : Fin n) (t : ℝ) : Prop :=
  0 ≤ t ∧ t = (1 / mk.αW (ws i)) * fstar mk β m ws i * tailInt (mk.F m (ws i)) t

/-- An equilibrium where `f_{mw_i} = f*_{mw_i}` (§4.2.2, p. 25): nonnegative thresholds `τ_m`,
`τ_{w_i}` solving the fixed-point equations (12) for `m` and for every `w_i`. -/
def IsStarEquilibrium {M W : Type} (mk : Market M W) (β : M → W → ℝ) (m : M) {n : ℕ}
    (ws : Fin n → W) (τm : ℝ) (τw : Fin n → ℝ) : Prop :=
  0 ≤ τm ∧ (∀ i, 0 ≤ τw i) ∧
  τm = (1 / mk.αM m) * ∑ i, fstar mk β m ws i * tailInt (mk.F m (ws i)) (max τm (τw i)) ∧
  ∀ i, τw i = (1 / mk.αW (ws i)) * fstar mk β m ws i *
    tailInt (mk.F m (ws i)) (max τm (τw i))

end DirectedSearch.Approx


