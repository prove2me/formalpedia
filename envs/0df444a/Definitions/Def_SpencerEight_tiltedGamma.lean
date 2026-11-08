-- Prove2me | Definitions.Def_SpencerEight_tiltedGamma
-- name    : SpencerEight_tiltedGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:01.978131+00:00
-- url     : https://prove2.me/theorems/a934131c-b18a-4072-9055-2470bce68ca7
-- title:
--   Tilted Gaussian $\nu$
-- statement:
--   For $\kappa>0$ and $\Gamma\succeq0$, $\nu$ is the probability measure proportional to $e^{-\kappa\xi^\top\Gamma\xi}\,d\gamma_m(\xi)$.
--
--   **Formalization Note** Mathlib's `Measure.tilted`, which divides by the total mass; the weight is bounded under these conditions.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.15, p.78 (PDF p.78)

import Mathlib
import Definitions.Def_SpencerEight_gammaM
open MeasureTheory
open scoped Matrix

namespace SpencerEight

/-- The probability measure `ν` proportional to `e^{−κ ξᵀΓξ} dγ_m(ξ)` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.15, p.78 (PDF p.78)).

**Formalization Note** Mathlib's `Measure.tilted`, which divides by the total mass. For `κ > 0` and `Γ ⪰ 0` the exponent is nonpositive, so the weight is bounded and integrable and `ν` is a probability measure. -/
noncomputable def tiltedGamma {m : ℕ} (κ : ℝ) (Γ : Matrix (Fin m) (Fin m) ℝ) :
    Measure (Fin m → ℝ) :=
  (gammaM (Fin m)).tilted fun ξ => -(κ * (ξ ⬝ᵥ Γ *ᵥ ξ))

end SpencerEight


