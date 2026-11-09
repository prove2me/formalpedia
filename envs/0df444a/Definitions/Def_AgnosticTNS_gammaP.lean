-- Prove2me | Definitions.Def_AgnosticTNS_gammaP
-- name    : AgnosticTNS_gammaP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:39.976761+00:00
-- url     : https://prove2.me/theorems/910c0f8a-36cd-4349-a0be-0bf79570198b
-- title:
--   Tomography accuracy $\gamma_i$
-- statement:
--   At step $i$, the reduced state is estimated to trace-norm accuracy
--   $$
--   \gamma_i:=\frac{\alpha^2}{128\,r_i}.
--   $$
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 3.2, p.18

import Mathlib
import Definitions.Def_AgnosticTNS_rr
import Definitions.Def_AgnosticTNS_alphaP

namespace AgnosticTNS

/-- **The tomography accuracy `γ_i := α²/(128 r_i)`**, §3.2, p.18 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). -/
noncomputable def gammaP {n : ℕ} (G : SimpleGraph (Fin n)) (χ : ℕ) (Ls : LearningSequence n)
    (ε ϑ : ℝ) (i : Fin Ls.L) : ℝ :=
  alphaP Ls ε ϑ ^ 2 / (128 * (rr G χ Ls i : ℝ))

end AgnosticTNS


