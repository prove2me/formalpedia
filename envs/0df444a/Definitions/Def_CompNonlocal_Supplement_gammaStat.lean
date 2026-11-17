-- Prove2me | Definitions.Def_CompNonlocal_Supplement_gammaStat
-- name    : CompNonlocal_Supplement_gammaStat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:11:42.560193+00:00
-- url     : https://prove2.me/theorems/32f6191e-9324-442c-88e7-3b50f4b50ddd
-- title:
--   The statistical threshold $\Gamma_{\mathrm{stat}}(v)$
-- statement:
--   For $v\in\mathbb R$,
--   $$\Gamma_{\mathrm{stat}}(v)=\tfrac12\big(v-\tfrac12\big)_+=\tfrac12\max\big(v-\tfrac12,0\big).$$
--   It vanishes for $v\le1/2$. It is the threshold of Theorem 10.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Theorem 10, p.66; Figure 1, p.5

import Mathlib

set_option autoImplicit false

namespace CompNonlocal.Supplement

/-- The statistical threshold. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 10, p.66: "Γstat(v) := (1/2)(v − 1/2)_+" (also
Figure 1, p.5: "Γstat(v) = (1/2)(v − 1/2)_+"), with `(t)_+ = max(t, 0)`. -/
noncomputable def gammaStat (v : ℝ) : ℝ := (1 / 2) * max (v - 1 / 2) 0

end CompNonlocal.Supplement


