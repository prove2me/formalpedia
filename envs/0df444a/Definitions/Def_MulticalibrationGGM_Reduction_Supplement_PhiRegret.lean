-- Prove2me | Definitions.Def_MulticalibrationGGM_Reduction_Supplement_PhiRegret
-- name    : MulticalibrationGGM_Reduction_Supplement_PhiRegret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:40:16.377876+00:00
-- url     : https://prove2.me/theorems/a69820d2-1d97-418f-a2c8-09d412e6b59d
-- title:
--   Best responses to forecasts, the tests $h_\phi$, and Φ-regret
-- statement:
--   Let $Z\subseteq\mathbb R^d$ be a set of actions, $L\subseteq\mathbb R^d$ a set of loss vectors, and $\Phi\subseteq\{Z\to Z\}$ a family of deviations. A map $\sigma:L\to Z$ is a **best-response map** if
--
--   $$\sigma(p)\in\arg\min_{z\in Z}p^\top z\qquad\text{for every }p\in L.$$
--
--   Ties may be broken by any deterministic scheme, and no continuity or uniqueness is assumed. For $\phi\in\Phi$, the test $h_\phi:L\to\mathbb R^d$ is $h_\phi(p)=\sigma(p)-\phi(\sigma(p))$, and $H_\Phi=\{h_\phi:\phi\in\Phi\}$ (Equation (4)).
--
--   In a run of Algorithm 2, round $t$ consists of a forecast law $D_t$ on $L$ and the loss $\ell_t\in L$, which is fed back to the forecaster as the outcome $y_t=\ell_t$. The action law $\mu_t$ is the pushforward of $D_t$ under $\sigma$. The **Φ-regret** against $\phi$ (Definition 2) is
--
--   $$\Phi\text{-}\mathrm{Regret}_T(\phi)=\sum_{t=1}^T\mathbb E_{z_t\sim\mu_t}\big[\ell_t^\top(z_t-\phi(z_t))\big].$$
--
--   The source's shorthands $\mathrm{Regret}^\Phi_T=\sup_{\phi\in\Phi}\Phi\text{-}\mathrm{Regret}_T(\phi)$ and $\mathrm{MC\text{-}Err}_T=\sup_{h\in H}\mathrm{MC\text{-}Err}_T(h)$ are taken as extended-real suprema.
--
--   These objects state Theorem 5: best-responding to forecasts of the losses turns multicalibration into Φ-regret minimization.
--
--   **Formalization Note** $Z$ and $L$ are subtypes of `Fin d → ℝ`. The tests $h_\phi$ have the one-point context type `Unit`. The pushforward is Mathlib's `Measure.map`. That is the zero measure when $\sigma$ is not almost-everywhere measurable, so every theorem using it assumes that measurability. The suprema are in `EReal`, so the empty supremum is $-\infty$ and an unbounded one is $+\infty$.
-- source:
--   Gabriele Farina, Juan Perdomo, An Efficient Black-Box Reduction from Online Learning to Multicalibration, and a New Route to Φ-Regret Minimization, STOC 2027 submission #721 (October 2026), Definition 2, p. 5; Equation (4), p. 14; Algorithm 2 and Theorem 5, p. 15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf. PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

import Mathlib
import Definitions.Def_MulticalibrationGGM_Reduction_Model
import Definitions.Def_MulticalibrationGGM_Reduction_Supplement_Forecaster

open MeasureTheory

namespace MulticalibrationGGM.Reduction.Supplement

/-!
Farina and Perdomo, STOC 2027 submission #721 (October 2026), Definition 2, p. 5;
Equation (4), p. 14; Algorithm 2 and Theorem 5, p. 15.
https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf
PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

Best response to a forecast, the tests `h_ϕ`, the class `H_Φ`, the pushforward action law
`µ_t = σ#D_t`, the Φ-regret of a run of Algorithm 2, and the extended-real suprema used by
the shorthands `Regret^Φ_T` and `MC-Err_T`.
-/

/-- Text after Equation (4), p. 14: `σ : L → Z` is a best-response map,
`σ(p) ∈ argmin_{z ∈ Z} pᵀz`, with ties broken by an arbitrary deterministic scheme.
No continuity, uniqueness or particular selection is required. -/
def IsBestResponseMap {d : ℕ} {Z L : Set (Vector d)} (σ : L → Z) : Prop :=
  ∀ (p : L) (z : Z), ∑ i : Fin d, p.val i * (σ p).val i ≤ ∑ i : Fin d, p.val i * z.val i

/-- Equation (4), p. 14 and Theorem 5: the context-free test `h_ϕ(p) = σ(p) − ϕ(σ(p))` on
the forecast set `L` (the context set is `Unit`). -/
def hPhi {d : ℕ} {Z L : Set (Vector d)} (σ : L → Z) (ϕ : Z → Z) : Test Unit L :=
  fun _ p => (σ p).val - (ϕ (σ p)).val

/-- Equation (4), p. 14: `H_Φ = {h_ϕ : ϕ ∈ Φ}`. -/
def HPhi {d : ℕ} {Z L : Set (Vector d)} (σ : L → Z) (Φ : Set (Z → Z)) : Set (Test Unit L) :=
  hPhi σ '' Φ

/-- Algorithm 2, line 3: the action law `µ_t`, the pushforward of the forecast law `D` under
`σ`. Every use is guarded by (a.e.-)measurability of `σ` for `D`; without it Mathlib's
`Measure.map` would be the zero measure. -/
noncomputable def actionLaw {d : ℕ} {Z L : Set (Vector d)} (σ : L → Z)
    (D : ProbabilityMeasure L) : Measure Z :=
  Measure.map σ (D : Measure L)

/-- Definition 2, p. 5: the loss difference `ℓᵀz − ℓᵀϕ(z) = ℓᵀ(z − ϕ(z))`. -/
def deviationLoss {d : ℕ} {Z L : Set (Vector d)} (ℓ : L) (ϕ : Z → Z) (z : Z) : ℝ :=
  ∑ i : Fin d, ℓ.val i * (z.val i - (ϕ z).val i)

/-- Definition 2, p. 5 and Theorem 5: `Φ-Regret_T(ϕ) = ∑_{t=1}^T E_{z_t∼µ_t}[ℓ_tᵀ(z_t − ϕ(z_t))]`
for a run whose round `t` carries the forecast law `D_t` on `L` and the loss `ℓ_t ∈ L`
(stored as the round's outcome, Algorithm 2 line 5: `y_t = ℓ_t`); `µ_t = σ#D_t`. -/
noncomputable def phiRegret {d : ℕ} {Z L : Set (Vector d)} (σ : L → Z)
    (R : ℕ → FRound Unit L) (T : ℕ) (ϕ : Z → Z) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∫ z, deviationLoss (R t).outcome ϕ z ∂(actionLaw σ (R t).forecast)

/-- Definition 2, p. 5: `Regret^Φ_T = sup_{ϕ ∈ Φ} Φ-Regret_T(ϕ)`, an extended-real supremum
(Φ may be infinite and the family unbounded; the empty supremum is `⊥`). -/
noncomputable def phiRegretSup {d : ℕ} {Z L : Set (Vector d)} (σ : L → Z)
    (Φ : Set (Z → Z)) (R : ℕ → FRound Unit L) (T : ℕ) : EReal :=
  ⨆ ϕ ∈ Φ, (phiRegret σ R T ϕ : EReal)

/-- Definition 1, p. 5: `MC-Err_T = sup_{h ∈ H} MC-Err_T(h)`, an extended-real supremum
(the empty supremum is `⊥`). -/
noncomputable def mcErrorSup {X : Type*} {d : ℕ} {Y : Set (Vector d)}
    (H : Set (Test X Y)) (R : ℕ → FRound X Y) (T : ℕ) : EReal :=
  ⨆ h ∈ H, (roundsMCError R T h : EReal)

end MulticalibrationGGM.Reduction.Supplement


