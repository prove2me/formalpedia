-- Prove2me | Definitions.Def_IllCondRegMem_IsPrunedCov
-- name    : IllCondRegMem_IsPrunedCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:47.8536+00:00
-- url     : https://prove2.me/theorems/d2531509-be52-43a7-bcd0-1cdd0c20e04c
-- title:
--   Definition 11 — pruned random covariance matrices
-- statement:
--   Let $\Sigma$ be a random positive semidefinite $d\times d$ matrix. Its distribution is **$\delta_{\max}$-pruned for dimension proxy $d_0$** (in Lemma 13: "$(d_0,\delta)$-pruned") if
--   $$
--   \mathbb P\big(w^\top\Sigma w<\delta^2\|w\|^2\big)\le\delta^{d_0}\qquad\text{for all } w\in\mathbb R^d,\ \delta\in[0,\delta_{\max}].
--   $$
--   This anticoncentration condition extends Definition 4 from projection matrices to general covariances, and is the hypothesis of the directional smoothing lemma (Lemma 13).
--
--   **Formalization Note** Vectors are `Fin d → ℝ` and $w^\top\Sigma w$ is a dot product. The standing ranges $\delta_{\max}\in(0,1)$, $d_0\in(d/2,d]$ and positive semidefiniteness of $\Sigma$ are not built in; each theorem states the ranges and positivity it uses.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Definition 11, p.11 (PDF p.12)

import Mathlib

open MeasureTheory Matrix

namespace IllCondRegMem

/-- **Pruned random covariance** (Definition 11).
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…),
Definition 11, p.11: "Let Σ ∈ S^d_+ be a random PSD matrix and δ_max ∈ (0,1), d₀ ∈ (d/2, d] be
parameters. We say that the distribution of Σ is δ_max pruned for dimension proxy d₀ if the
following anticoncentration condition is met: ∀ w ∈ ℝ^d, δ ∈ [0, δ_max],
P(wᵀΣw < δ²‖w‖²) ≤ δ^{d₀}."

`IsPrunedCov P Sig d₀ δmax` is this anticoncentration condition for the random matrix `Sig`
on the probability space `(Ω, P)`; Lemma 13 calls it "(d₀, δ)-pruned".

**Formalization Note.** Vectors are `Fin d → ℝ`, `wᵀΣw` is `w ⬝ᵥ (Σ *ᵥ w)` and `‖w‖² = w ⬝ᵥ w`.
The parameter ranges `δ_max ∈ (0,1)`, `d₀ ∈ (d/2, d]` and positive semidefiniteness of `Σ` are
not built in: each theorem states the ranges and the positivity it uses. -/
def IsPrunedCov {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (Sig : Ω → Matrix (Fin d) (Fin d) ℝ) (d₀ : ℕ) (δmax : ℝ) : Prop :=
  ∀ w : Fin d → ℝ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ δmax →
    P {ω | w ⬝ᵥ (Sig ω *ᵥ w) < δ ^ 2 * (w ⬝ᵥ w)} ≤ ENNReal.ofReal (δ ^ d₀)

end IllCondRegMem


