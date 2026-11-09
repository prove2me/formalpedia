-- Prove2me | Definitions.Def_LinfContractionFP_potentials
-- name    : LinfContractionFP_potentials
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:13.599007+00:00
-- url     : https://prove2.me/theorems/e3c55e11-b28b-4010-9580-34ef3fd7eafe
-- title:
--   Exponential potentials $\Phi_\pm(F)$
-- statement:
--   For integer vote tallies $F$, the **exponential potentials** of the bands of $\sigma+b$ at tolerance $\tau$ are
--   $$\Phi_+(F)=\sum_{i\in S_+}\sqrt3^{\,-F_i},\qquad \Phi_-(F)=\sum_{i\in S_-}\sqrt3^{\,F_i}.$$
--   Amplify keeps upper bounds $B_\pm$ on them and shrinks the bounds by $\sqrt3/2$ per boosting round.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), p.14

import Mathlib
import Definitions.Def_LinfContractionFP_bands

namespace LinfContractionFP

/-- The exponential potential `Φ₊(F) = Σ_{i ∈ S₊} √3^{−F_i}` of the vote tally `F` on the band
`S₊` of `σ + b` at tolerance `τ` (p.14).

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), p.14: "the corresponding
exponential potentials as a function of the votes F_i on each coordinate
Φ+(F) := Σ_{i∈S+} √3^{−F_i}, Φ−(F) := Σ_{i∈S−} √3^{F_i}."

**Formalization Note.** Votes are integers (`F : κ → ℤ`) and `√3^{−F_i}` is the integer power
`Real.sqrt 3 ^ (-(F i))` (`zpow`). -/
noncomputable def phiPlus {κ : Type} [Fintype κ] (σ b : κ → ℝ) (τ : ℝ) (F : κ → ℤ) : ℝ :=
  ∑ i ∈ bandSplus σ b τ, Real.sqrt 3 ^ (-(F i))

/-- `Φ₋(F) = Σ_{i ∈ S₋} √3^{F_i}` (p.14). -/
noncomputable def phiMinus {κ : Type} [Fintype κ] (σ b : κ → ℝ) (τ : ℝ) (F : κ → ℤ) : ℝ :=
  ∑ i ∈ bandSminus σ b τ, Real.sqrt 3 ^ (F i)

end LinfContractionFP


