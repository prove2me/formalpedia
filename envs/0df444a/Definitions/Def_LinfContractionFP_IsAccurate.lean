-- Prove2me | Definitions.Def_LinfContractionFP_IsAccurate
-- name    : LinfContractionFP_IsAccurate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:03.237214+00:00
-- url     : https://prove2.me/theorems/87b88546-30eb-439d-8ef9-a3787032c18f
-- title:
--   $\tau$-accurate labeling of a vector
-- statement:
--   A labeling $\ell$ of the coordinates of a vector $v\in\mathbb R^n$ is **$\tau$-accurate** if for every coordinate $j$
--   $$v_j\ge\max_i v_i-\tau\ \Longrightarrow\ \ell_j=\mathsf{hi}\ (+1),\qquad v_j\le\min_i v_i+\tau\ \Longrightarrow\ \ell_j=\mathsf{lo}\ (-1).$$
--   This is condition (3) of Definition 1, and also the validity condition of an Oracle answer and the $\kappa$-accuracy target in Problem 1.
--
--   **Formalization Note** "Within distance $\tau$" is closed, as in (3). On an empty coordinate set the condition is vacuous.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Definition 1, (3), p.6; Problem 1, p.11

import Mathlib
import Definitions.Def_LinfContractionFP_Lbl

namespace LinfContractionFP

/-- A labeling `ℓ` of the coordinates of a vector `v` is `τ`-accurate: every coordinate within
`τ` of the maximum of `v` is labelled `hi` (`+1`), and every coordinate within `τ` of the
minimum is labelled `lo` (`−1`):
`v_j ≥ max v − τ ⟹ ℓ_j = hi` and `v_j ≤ min v + τ ⟹ ℓ_j = lo`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…): Definition 1, condition (3),
p.6 ("σ_j ≥ σmax − τ ⟹ ℓ_j = hi, σ_j ≤ σmin + τ ⟹ ℓ_j = lo"), and Problem 1, p.11 (a valid
Oracle answer for `σ + b` at accuracy ρ, and a κ-accurate labeling for σ: "tags as −1 those
coordinates that are within κ of the minimum of σ, and as +1 those that are within κ of the
maximum of σ").

**Formalization Note.** "Within distance τ" is closed (`≥`, `≤`), as in (3) and footnote 5,
p.16. The maximum and minimum are `⨆ i, v i` and `⨅ i, v i`, which on a finite nonempty index
type are attained; on an empty index type the condition is vacuous. -/
def IsAccurate {κ : Type} [Fintype κ] (τ : ℝ) (v : κ → ℝ) (ℓ : κ → Lbl) : Prop :=
  ∀ j, (v j ≥ (⨆ i, v i) - τ → ℓ j = .hi) ∧ (v j ≤ (⨅ i, v i) + τ → ℓ j = .lo)

end LinfContractionFP


