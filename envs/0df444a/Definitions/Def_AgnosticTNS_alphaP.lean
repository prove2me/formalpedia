-- Prove2me | Definitions.Def_AgnosticTNS_alphaP
-- name    : AgnosticTNS_alphaP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:11.596207+00:00
-- url     : https://prove2.me/theorems/79298e5c-8dc3-4500-ab7e-2e785a3bad0a
-- title:
--   Per-step overlap budget $\alpha$
-- statement:
--   For a learning sequence of length $L$, accuracy $\epsilon\in(0,1]$ and overlap lower bound $\vartheta\in(0,1]$,
--   $$
--   \alpha:=\frac{\min\{\epsilon,\vartheta\}}{4L}.
--   $$
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 3.2, Eq. (3.25), p.18

import Mathlib
import Definitions.Def_AgnosticTNS_LearningSequence

namespace AgnosticTNS

/-- **The per-step overlap budget `α := min{ϵ, ϑ}/(4L)`**, Eq. (3.25), p.18 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). -/
noncomputable def alphaP {n : ℕ} (Ls : LearningSequence n) (ε ϑ : ℝ) : ℝ :=
  min ε ϑ / (4 * Ls.L)

end AgnosticTNS


