-- Prove2me | Definitions.Def_RandPurIso_Completion_traceDist
-- name    : RandPurIso_Completion_traceDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:38.708097+00:00
-- url     : https://prove2.me/theorems/16653a00-a6a6-4530-95bd-0bdfe3eaf1b3
-- title:
--   Trace distance $\mathrm{TD}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$
-- statement:
--   The **trace distance** of two operators is
--   $$\mathrm{TD}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1,\qquad \|M\|_1=\operatorname{Tr}\sqrt{M^\dagger M}.$$
--
--   **Formalization Note** The trace norm is the published `QAlgorithms.traceNorm` (real part of $\operatorname{Tr}\sqrt{M^\dagger M}$).
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §3.1, p. 17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
open Matrix

namespace RandPurIso.Completion

/-- **Trace distance** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §3.1, p. 17): `TD(ρ, σ) = ½ ‖ρ − σ‖₁`, with the trace norm
`QAlgorithms.traceNorm M = Re Tr √(M†M)`. -/
noncomputable def traceDist {X : Type} [Fintype X] [DecidableEq X] (ρ σ : Matrix X X ℂ) : ℝ :=
  (1 / 2 : ℝ) * QAlgorithms.traceNorm (ρ - σ)

end RandPurIso.Completion


