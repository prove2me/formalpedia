-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_hsNormSq
-- name    : OptimalSpectrum_Entangled_hsNormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:21.775488+00:00
-- url     : https://prove2.me/theorems/e36d7f8e-76e4-4743-8a95-ff2ca6e25b42
-- title:
--   Squared Hilbert–Schmidt norm $\|A\|_{\mathrm{HS}}^2$
-- statement:
--   For a square complex matrix $A$,
--
--   $$\|A\|_{\mathrm{HS}}^2=\sum_{x,y}|A_{xy}|^2=\mathrm{tr}(A^*A).$$
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 7.3, p. 22 (PDF p. 24)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Squared Hilbert–Schmidt norm `‖A‖²_HS`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 7.3, printed p. 22 (PDF p. 24): the norm `∥·∥_HS`.

`‖A‖²_HS = ∑_(x,y) |A_(xy)|² = tr(A*A)`. -/
noncomputable def hsNormSq {κ : Type*} [Fintype κ] (A : Matrix κ κ ℂ) : ℝ :=
  ∑ x, ∑ y, ‖A x y‖ ^ 2

end OptimalSpectrum.Entangled


