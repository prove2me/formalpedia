-- Prove2me | Definitions.Def_CompNonlocal_gammaComp
-- name    : CompNonlocal_gammaComp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:45.17532+00:00
-- url     : https://prove2.me/theorems/f0bdeb52-b520-4c09-88e5-a4532503e7cf
-- title:
--   The computational gap bound $\Gamma_{\mathrm{comp}}(v)$
-- statement:
--   $$\Gamma_{\mathrm{comp}}(v):=\tfrac12\,(v-\tfrac13)_+,\qquad t_+:=\max\{t,0\}.$$
--   It is the upper bound on the single-copy certification gap of $\rho(v)$ (Lemma 9).
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §6.3, p.31

import Mathlib

set_option autoImplicit false

namespace CompNonlocal

/-- The computational upper bound on the single-copy certification gap. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §6.3, p.31:
"Γcomp(v) := ½(v − 1/3)₊ … where t₊ := max{t, 0}". -/
noncomputable def gammaComp (v : ℝ) : ℝ := (1 / 2) * max (v - 1 / 3) 0

end CompNonlocal


