-- Prove2me | Definitions.Def_CubeSampling_outsideCov
-- name    : CubeSampling_outsideCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:12.253199+00:00
-- url     : https://prove2.me/theorems/2fc89c0f-dc1f-425b-9b84-a6cb68561d13
-- title:
--   Outside covariance $\mathbb E[\Phi(X)\Phi(X)^\top\mathbf 1\{X\notin E\}]$
-- statement:
--   For an orthonormal family $\Phi$ and $E \subseteq \{-1,1\}^d$, the **outside covariance** is the $m\times m$ matrix
--   $$
--   \mathbb E\bigl[\Phi(X)\Phi(X)^\top \mathbf 1\{X \notin E\}\bigr], \qquad X \sim \mu_d .
--   $$
--   By (3), $\mathbb E[\Phi\Phi^\top\mathbf 1\{X\notin E\}] \preceq \rho I_m$ holds iff every $h \in V$ satisfies $\mathbb E[h^2\mathbf 1_{E^c}] \le \rho\,\mathbb E[h^2]$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), (3), p.8; Lemma 6.1, p.22

import Mathlib
import Definitions.Def_CubeSampling_cubeMean

namespace CubeSampling

/-- The outside covariance `E[Φ(X) Φ(X)^⊤ 1{X ∉ E}]` of an `m`-family `Φ` and a set `E` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79),
(3), p.8 and Lemma 6.1, p.22); `E[ΦΦ^⊤ 1{X ∉ E}] ⪯ ρ I_m` is
`(ρ • 1 - outsideCov d Φ E).PosSemidef`. -/
noncomputable def outsideCov (d : ℕ) {m : ℕ} (Φ : Fin m → Cube d → ℝ) (E : Set (Cube d)) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => cubeMean d (Eᶜ.indicator fun x => Φ i x * Φ j x)

end CubeSampling


