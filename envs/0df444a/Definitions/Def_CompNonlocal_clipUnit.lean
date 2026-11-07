-- Prove2me | Definitions.Def_CompNonlocal_clipUnit
-- name    : CompNonlocal_clipUnit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:51.252002+00:00
-- url     : https://prove2.me/theorems/8a25105a-bd9d-4cae-a933-b762f2c48edd
-- title:
--   Clipping to $[-1,1]$
-- statement:
--   $\mathrm{clip}(t)=\max\{-1,\min\{1,t\}\}$. Predictors of the paper output values in $[-1,1]$; a decoded real output is read through this clip.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 15, p.34; Lemmas 17, 18, pp.44–45

import Mathlib

set_option autoImplicit false

namespace CompNonlocal

/-- Clipping to `[−1, 1]`. Predictors in Głuch, Morimae, *From Computational Nonlocality to
Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), output
values in `[−1, 1]` (Definition 15, p.34; Lemmas 17 and 18, pp.44–45, "A(T⁺) ∈ [−1, 1]",
"B̂_S ∈ [−1, 1]"); a decoded real output is read through this clip. -/
noncomputable def clipUnit (t : ℝ) : ℝ := max (-1) (min 1 t)

end CompNonlocal


