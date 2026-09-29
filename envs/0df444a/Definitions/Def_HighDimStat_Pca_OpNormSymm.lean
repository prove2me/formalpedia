-- Prove2me | Definitions.Def_HighDimStat_Pca_OpNormSymm
-- name    : HighDimStat_Pca_OpNormSymm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:11:41.597603+00:00
-- url     : https://prove2.me/theorems/d2459409-d9c3-4036-9b58-3d7bf8be34b3
-- title:
--   The l2-operator norm of a symmetric matrix
-- statement:
--   This is the **`ℓ2`-operator norm** `|||A|||₂` of a symmetric `d × d` real matrix `A`, used
--   for the perturbation matrix `P` throughout Section 8.2 (e.g. Eq. (8.9), Theorem 8.5).
--
--   For a symmetric $A \in \mathbb R^{d\times d}$,
--
--   $$
--   |\!|\!|A|\!|\!|_2 \;:=\; \sup_{v \in \mathbb R^d,\, \|v\|_2=1} |\langle v, Av\rangle|.
--   $$
--
--   **Formalization Note** Realized via the Rayleigh-quotient variational characterization,
--   which for a symmetric matrix coincides exactly with the usual operator norm $\sup_{\|v\|=1}
--   \|Av\|_2$ (largest singular value); this mission only ever applies `opNormSymm` to
--   symmetric matrices, matching how the book itself only ever writes `|||P|||₂` for symmetric
--   `P` in this chapter. The `⨆` is a real supremum over the subtype of unit vectors, `0` (junk)
--   at `d = 0` where no unit vector exists.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 241 (PDF p. 261), Eq. (8.9)

import Mathlib

namespace HighDimStat.Pca

/-- The `ℓ2`-operator norm `|||A|||₂` of a *symmetric* `d × d` real matrix `A`, realized via its
Rayleigh-quotient variational characterization `sup_{‖v‖₂=1} |⟨v, Av⟩|`, as used for the
perturbation matrix `P` throughout Wainwright, *High-Dimensional Statistics* (2019), Section 8.2
(e.g. Eq. (8.9), Theorem 8.5). For a symmetric matrix this coincides with the largest singular
value / largest eigenvalue magnitude, the book's own `|||·|||₂`. -/
noncomputable def opNormSymm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ v : {v : Fin d → ℝ // ∑ j, (v j) ^ 2 = 1}, |∑ i, v.1 i * (A.mulVec v.1) i|

end HighDimStat.Pca


