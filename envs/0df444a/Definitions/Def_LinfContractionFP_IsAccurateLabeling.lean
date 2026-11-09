-- Prove2me | Definitions.Def_LinfContractionFP_IsAccurateLabeling
-- name    : LinfContractionFP_IsAccurateLabeling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:05.654373+00:00
-- url     : https://prove2.me/theorems/0c4800b5-82fa-4821-8430-b9853fce2ab7
-- title:
--   $\tau$-accurate labeling of a box (Definition 1)
-- statement:
--   Let $[L,U]$ be a possibly degenerate box and $x^*$ the fixed point. With $\sigma_{\max}$, $\sigma_{\min}$ the largest and smallest of the $2d$ face slacks, an assignment of labels $\ell_{i,-},\ell_{i,+}\in\{\mathsf{lo},\mathsf{hi}\}$ is **$\tau$-accurate** if
--   $$\sigma_j\ge\sigma_{\max}-\tau\ \Longrightarrow\ \ell_j=\mathsf{hi},\qquad \sigma_j\le\sigma_{\min}+\tau\ \Longrightarrow\ \ell_j=\mathsf{lo}$$
--   for every face $j$. Label (Algorithm 4) returns such labelings, and Solve uses them to shrink its search cube.
--
--   **Formalization Note** For $d=0$ there are no faces and every labeling is accurate.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Definition 1, p.6

import Mathlib
import Definitions.Def_LinfContractionFP_slack
import Definitions.Def_LinfContractionFP_IsAccurate

namespace LinfContractionFP

/-- A `τ`-accurate labeling of a (possibly degenerate) box `[L, U]` with respect to the fixed
point `xs` (Definition 1): the face labels `ℓ : ι × Bool → Lbl` are `τ`-accurate for the vector
of the `2d` face slacks.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Definition 1, p.6: "Let
σmax and σmin denote the maximum and minimum values of σ_j, taken over all 2d faces of the box.
We call assignment of labels ℓ_{i,−}, ℓ_{i,+} ∈ {lo, hi} to all faces j ∈ {1, . . . , d} × {−, +}
τ-accurate if it satisfies σ_j ≥ σmax − τ ⟹ ℓ_j = hi, σ_j ≤ σmin + τ ⟹ ℓ_j = lo. (3)"

**Formalization Note.** Faces are `ι × Bool` (`false` = `−`, `true` = `+`); see `slack`.
Degenerate boxes are allowed. For `d = 0` there are no faces and every labeling is accurate. -/
def IsAccurateLabeling {ι : Type} [Fintype ι] (τ : ℝ) (L U xs : ι → ℝ)
    (ℓ : ι × Bool → Lbl) : Prop :=
  IsAccurate τ (slack L U xs) ℓ

end LinfContractionFP


