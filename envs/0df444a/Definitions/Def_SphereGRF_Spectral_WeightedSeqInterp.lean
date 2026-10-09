-- Prove2me | Definitions.Def_SphereGRF_Spectral_WeightedSeqInterp
-- name    : SphereGRF_Spectral_WeightedSeqInterp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:04.920152+00:00
-- url     : https://prove2.me/theorems/f9c8983d-3462-499a-ada2-ae7a38dd632a
-- title:
--   Weighted sequence spaces $\ell^2(w)$, their K-functional and the interpolation norm of $(\ell^2(w_0), \ell^2(w_1))_{\theta,2}$
-- statement:
--   For a weight $w = (w_\ell)_{\ell \in \mathbb N_0}$ of positive reals, the weighted sequence space $\ell^2(w)$ has the squared norm
--
--   $$
--   \|a\|^2_{\ell^2(w)} = \sum_{\ell=0}^\infty w_\ell\,a_\ell^2 \in [0,+\infty].
--   $$
--
--   For two weights $w_0, w_1$ and $t > 0$ the K-functional is $K(t,a) = \inf_{a = b + c}\big(\|b\|_{\ell^2(w_0)} + t\,\|c\|_{\ell^2(w_1)}\big)$, and for $0 < \theta < 1$ the squared norm of the real interpolation space $(\ell^2(w_0), \ell^2(w_1))_{\theta,2}$ is
--
--   $$
--   \|a\|^2_{\theta,2} = \int_0^\infty t^{-2\theta}\,K(t,a)^2\,\frac{dt}{t} \in [0,+\infty].
--   $$
--
--   These are the spaces $\ell_n$ and $\ell_\eta$ of the paper's Section 3, in which the theorem of Stein and Weiss identifies the interpolation space as a weighted $\ell^2$ space.
--
--   **Formalization Note** All norms take values in $[0,+\infty]$; a sequence outside the space has norm $+\infty$, and the K-functional is an infimum in $[0,+\infty]$ over all decompositions.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §3, pp. 10–12 (ℓ_n, ℓ_η, 'The definition of the interpolation spaces ℓ_η for η ∉ ℕ₀ is done similarly')

import Mathlib

open scoped ENNReal

namespace SphereGRF.Spectral

/-- The squared norm of the weighted sequence space `ℓ²(w)`: `Σ_ℓ w_ℓ a_ℓ²`, in `[0, ∞]`. -/
noncomputable def seqNormSq (w : ℕ → ℝ) (a : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, ENNReal.ofReal (w ℓ * a ℓ ^ 2)

/-- The K-functional of the couple `(ℓ²(w₀), ℓ²(w₁))`:
`K(t,a) = inf_{a = b + c} (‖b‖_{ℓ²(w₀)} + t ‖c‖_{ℓ²(w₁)})`. -/
noncomputable def seqKfun (w₀ w₁ : ℕ → ℝ) (t : ℝ) (a : ℕ → ℝ) : ℝ≥0∞ :=
  ⨅ (b : ℕ → ℝ) (c : ℕ → ℝ) (_ : a = b + c),
    seqNormSq w₀ b ^ (1 / 2 : ℝ) + ENNReal.ofReal t * seqNormSq w₁ c ^ (1 / 2 : ℝ)

/-- The squared norm of the real interpolation space `(ℓ²(w₀), ℓ²(w₁))_{θ,2}`:
`∫_0^∞ t^{−2θ} K(t,a)² dt/t`. -/
noncomputable def seqInterpNormSq (w₀ w₁ : ℕ → ℝ) (θ : ℝ) (a : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-2 * θ) / t) * seqKfun w₀ w₁ t a ^ 2

end SphereGRF.Spectral


