-- Prove2me | Definitions.Def_FractionalSpectralGP_unitaryW
-- name    : FractionalSpectralGP_unitaryW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:53.507267+00:00
-- url     : https://prove2.me/theorems/5894d4aa-8a61-47fd-9baf-35b8b90d3b47
-- title:
--   The unitary $W:L^2(d\sigma)\to L^2(\mathbb R,dx)$, $W(e_{\lambda_n})=h_n$
-- statement:
--   Given a spectral setting $(\sigma,(\lambda_n))$ and an orthonormal basis $(h_n)_{n\ge0}$ of $L^2(\mathbb R,dx)$, the unitary map
--
--   $$
--   W:L^2(d\sigma)\to L^2(\mathbb R,dx),\qquad W(e_{\lambda_n})=h_n,\quad n=0,1,\dots
--   $$
--
--   sends one orthonormal basis onto the other.
--
--   **Formalization Note** The paper's letter $W$ is kept in the Lean name; the mission's prose writes $U$ for it where it could be confused with the white noise space $\mathcal W$ or the process $W_\sigma$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §5, p.12

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The unitary map `W : L²(dσ) → L²(ℝ, dx)` with `W(e_{λ_n}) = h_n`, `n = 0, 1, …`
(Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §5, p.12).

**Formalization Note.** The paper's letter `W` is kept in the name; in prose of this mission it is
written `U` to avoid a clash with the white noise space `𝒲`. It is the composite of the
coordinate isometry of the basis `(e_{λ_n})` with the inverse coordinate isometry of `(h_n)`. -/
noncomputable def unitaryW (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    Lp ℂ 2 S.σ ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (HilbertBasis.mk S.orthonormal S.dense).repr.trans h.repr.symm

end FractionalSpectralGP


