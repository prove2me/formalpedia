-- Prove2me | Definitions.Def_StatComplexityDM_E2D_Contextual
-- name    : StatComplexityDM_E2D_Contextual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:21.89798+00:00
-- url     : https://prove2.me/theorems/5039a08a-a6f9-40b2-a2ec-de257d482577
-- title:
--   §8, (84)–(86), pp. 54–55 — projected classes M|_x, dec^D_γ(M, M̂), contextual regret and contextual Est_D
-- statement:
--   This module defines the objects of the contextual decision-making setting (§8).
--
--   A **contextual model** $M$ assigns to every context $x \in \mathcal X$ and decision $\pi \in \Pi$ a distribution $M(x,\pi)$ over outcomes. For a class $\mathcal M$ of contextual models and a context $x$, the **projected class** is
--   $$
--   \mathcal M|_x := \{ M(x, \cdot) \mid M \in \mathcal M \}.
--   $$
--   For a set $\widehat{\mathcal M}$ of reference models, $\mathrm{dec}^D_\gamma(\mathcal M, \widehat{\mathcal M}) := \sup_{\bar M\in\widehat{\mathcal M}} \mathrm{dec}^D_\gamma(\mathcal M, \bar M)$ (p. 55). Given contexts $x^{(1)},\dots,x^{(T)}$ and distributions $p^{(t)}$, the **regret** (84) against the true model $M^\star$ is
--   $$
--   \mathrm{Reg}_{\mathrm{DM}} := \sum_{t=1}^T \mathbb E_{\pi\sim p^{(t)}}\big[f^\star(x^{(t)}, \boldsymbol\pi^\star(x^{(t)})) - f^\star(x^{(t)}, \pi)\big],
--   $$
--   where $f^\star = f^{M^\star}$ and $\boldsymbol\pi^\star(x)$ maximizes $f^\star(x,\cdot)$; for estimates $\widehat M^{(t)}$ the **estimation error** (86) is
--   $$
--   \mathrm{Est}_D := \sum_{t=1}^T \mathbb E_{\pi\sim p^{(t)}}\big[D(M^\star(x^{(t)},\pi) \,\|\, \widehat M^{(t)}(x^{(t)},\pi))\big].
--   $$
--
--   These are the quantities in the regret bound for the contextual E2D algorithm.
--
--   **Formalization Note** The optimal policy $\boldsymbol\pi_M(x)$ is the maximizer selector applied to the model $M(x,\cdot)$, so it is the same selector as in the non-contextual setting. The context space is an arbitrary type; decisions and outcomes are finite. Rounds are 0-based.
-- source:
--   arXiv:2112.13487v3, §8, (84), p. 54; (86) and the definitions of M|_x and dec^D_γ(M, M̂), p. 55

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_StatComplexityDM_E2D_GeneralDivergence

namespace StatComplexityDM.E2D

open FoundationsRL.GeneralDM

/-- The projection of a class of contextual models `M(x, π)` onto a context `x`, p. 55:
`M|_x := {M(x, ·) | M ∈ M}`. A contextual model is `m : X → Π → Δ(R × O)`. -/
def projClass {X S Y : Type*} (𝓜 : Set (X → S → Y → ℝ)) (x : X) : Set (S → Y → ℝ) :=
  (fun m => m x) '' 𝓜

/-- The general-divergence DEC of a class against a set of reference models, p. 55:
`dec^D_γ(M, M̂) := sup_{M̄∈M̂} dec^D_γ(M, M̄)`, with `dec^D_γ(M, M̄)` the point version (44). -/
noncomputable def decDivSet {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ))
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S) (γ : ℝ) (Dv : (Y → ℝ) → (Y → ℝ) → ℝ)
    (Mhat : Set (S → Y → ℝ)) : ℝ :=
  sSup ((decDivPt 𝓜 rew piStar γ Dv) '' Mhat)

/-- Contextual regret (84), p. 54, on a realized sequence of contexts `x^{(t)}` and decision
distributions `p^{(t)}` (0-based rounds):
`Reg_DM := Σ_t E_{π∼p^{(t)}}[f⋆(x^{(t)}, π⋆(x^{(t)})) − f⋆(x^{(t)}, π)]`, where `f⋆ = f^{M⋆}` and the
optimal policy `π⋆(x) = π_{M⋆(x, ·)}` is read off the selector `piStar` applied to the model
`M⋆(x, ·)`. -/
noncomputable def regretCtx {X S Y : Type*} [Fintype S] [Fintype Y] {T : ℕ} (rew : Y → ℝ)
    (piStar : (S → Y → ℝ) → S) (Mstar : X → S → Y → ℝ) (x : Fin T → X) (p : Fin T → S → ℝ) : ℝ :=
  ∑ t : Fin T, ∑ π, p t π *
    (fM rew (Mstar (x t)) (piStar (Mstar (x t))) - fM rew (Mstar (x t)) π)

/-- The contextual estimation error (86), p. 55, on the observed sequence of contexts:
`Est_D := Σ_t E_{π∼p^{(t)}}[D(M⋆(x^{(t)}, π) ‖ M̂^{(t)}(x^{(t)}, π))]`. -/
noncomputable def estDCtx {X S Y : Type*} [Fintype S] {T : ℕ} (Dv : (Y → ℝ) → (Y → ℝ) → ℝ)
    (Mstar : X → S → Y → ℝ) (Mhat : Fin T → X → S → Y → ℝ) (x : Fin T → X)
    (p : Fin T → S → ℝ) : ℝ :=
  ∑ t : Fin T, ∑ π, p t π * Dv (Mstar (x t) π) (Mhat t (x t) π)

end StatComplexityDM.E2D


