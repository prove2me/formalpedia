-- Prove2me | Definitions.Def_StatComplexityDM_E2D_GeneralDivergence
-- name    : StatComplexityDM_E2D_GeneralDivergence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:21:30.874035+00:00
-- url     : https://prove2.me/theorems/21dccdb8-5ddc-4feb-8490-6ee1d75bfd50
-- title:
--   (44)–(46), p. 27 — the DEC for a general divergence D and randomized estimators, and the estimation error Est_D
-- statement:
--   This module defines the Decision-Estimation Coefficient for a general divergence and for randomized estimators (§4.3).
--
--   Let $D(P \,\|\, Q) \ge 0$ be a divergence between outcome distributions. For a reference model $\bar M$, the **general-divergence DEC** (44) is
--   $$
--   \mathrm{dec}^D_\gamma(\mathcal M, \bar M) = \inf_{p\in\Delta(\Pi)} \sup_{M\in\mathcal M} \mathbb E_{\pi\sim p}\big[f^M(\pi_M) - f^M(\pi) - \gamma\, D(M(\pi) \,\|\, \bar M(\pi))\big].
--   $$
--   For a distribution $\nu$ over models (a **randomized estimate**), the DEC (45) is
--   $$
--   \mathrm{dec}^D_\gamma(\mathcal M, \nu) = \inf_{p\in\Delta(\Pi)} \sup_{M\in\mathcal M} \mathbb E_{\pi\sim p}\Big[f^M(\pi_M) - f^M(\pi) - \gamma\, \mathbb E_{\bar M\sim\nu}\big[D(M(\pi) \,\|\, \bar M(\pi))\big]\Big].
--   $$
--   Given randomized estimates $\nu^{(1)},\dots,\nu^{(T)}$, distributions $p^{(1)},\dots,p^{(T)}$ and the true model $M^\star$, the **estimation error** (46) is
--   $$
--   \mathrm{Est}_D := \sum_{t=1}^T \mathbb E_{\pi\sim p^{(t)}} \mathbb E_{\widehat M\sim\nu^{(t)}}\big[D(M^\star(\pi) \,\|\, \widehat M(\pi))\big].
--   $$
--   Finally, $\nu \in \Delta(A)$ for a set $A$ of models means that $\nu$ is a finitely supported probability distribution with support in $A$.
--
--   These are the quantities of the E2D variant for general divergences (Algorithm 3) and of the contextual E2D algorithm.
--
--   **Formalization Note** Distributions over models are finitely supported (`Finsupp`), following the paper's convention that the model class carries the discrete topology (footnote 5, p. 11). The divergence is any function `Dv` on pairs of outcome vectors; its nonnegativity is a hypothesis of the theorems that use it. Rounds are 0-based.
-- source:
--   arXiv:2112.13487v3, §4.3, (44), (45), (46), p. 27; footnote 5, p. 11

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_StatComplexityDM_LowerBound_Core

namespace StatComplexityDM.E2D

open FoundationsRL.GeneralDM

/-- A finitely supported probability distribution `ν ∈ Δ(A)` on models, supported in the set `A`
(§4.3, p. 27; models carry the discrete topology, footnote 5, p. 11). `ν m` is the mass of the
model `m`. -/
def IsFinDistOn {S Y : Type*} (A : Set (S → Y → ℝ)) (ν : (S → Y → ℝ) →₀ ℝ) : Prop :=
  (∀ m, 0 ≤ ν m) ∧ (ν.sum fun _ w => w) = 1 ∧ (↑ν.support : Set (S → Y → ℝ)) ⊆ A

/-- The Decision-Estimation Coefficient for a general divergence `D` and a randomized estimator `ν`,
(45), p. 27:
`dec^D_γ(M, ν) = inf_{p∈Δ(Π)} sup_{M∈M} E_{π∼p}[f^M(π_M) − f^M(π) − γ · E_{M̄∼ν}[D(M(π) ‖ M̄(π))]]`.
`Dv P Q` is `D(P ‖ Q)` for outcome distributions `P, Q`. -/
noncomputable def decDiv {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ))
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S) (γ : ℝ) (Dv : (Y → ℝ) → (Y → ℝ) → ℝ)
    (ν : (S → Y → ℝ) →₀ ℝ) : ℝ :=
  sInf ((fun p : S → ℝ =>
      sSup ((fun m : S → Y → ℝ =>
          ∑ π, p π * (fM rew m (piStar m) - fM rew m π -
            γ * ν.sum (fun mb w => w * Dv (m π) (mb π)))) '' 𝓜))
    '' {p : S → ℝ | StatComplexityDM.LowerBound.IsDist p})

/-- The Decision-Estimation Coefficient for a general divergence `D` at a point reference model
`M̄`, (44), p. 27:
`dec^D_γ(M, M̄) = inf_{p∈Δ(Π)} sup_{M∈M} E_{π∼p}[f^M(π_M) − f^M(π) − γ · D(M(π) ‖ M̄(π))]`. -/
noncomputable def decDivPt {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ))
    (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S) (γ : ℝ) (Dv : (Y → ℝ) → (Y → ℝ) → ℝ)
    (mbar : S → Y → ℝ) : ℝ :=
  sInf ((fun p : S → ℝ =>
      sSup ((fun m : S → Y → ℝ =>
          ∑ π, p π * (fM rew m (piStar m) - fM rew m π - γ * Dv (m π) (mbar π))) '' 𝓜))
    '' {p : S → ℝ | StatComplexityDM.LowerBound.IsDist p})

/-- The estimation error of randomized estimates `ν^{(1)}, …, ν^{(T)}` with respect to the divergence
`D`, (46), p. 27, on a realized run (0-based rounds):
`Est_D := Σ_t E_{π∼p^{(t)}} E_{M̂∼ν^{(t)}}[D(M⋆(π) ‖ M̂(π))]`. -/
noncomputable def estD {S Y : Type*} [Fintype S] {T : ℕ} (Dv : (Y → ℝ) → (Y → ℝ) → ℝ)
    (Mstar : S → Y → ℝ) (ν : Fin T → (S → Y → ℝ) →₀ ℝ) (p : Fin T → S → ℝ) : ℝ :=
  ∑ t : Fin T, ∑ π, p t π * (ν t).sum (fun mb w => w * Dv (Mstar π) (mb π))

end StatComplexityDM.E2D


