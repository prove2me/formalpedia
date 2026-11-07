-- Prove2me | Definitions.Def_MultiSelectPandora_gridPts
-- name    : MultiSelectPandora_gridPts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:18:47.661242+00:00
-- url     : https://prove2.me/theorems/4cd47d36-a55e-49ba-a419-c22a20f6d262
-- title:
--   The grid points $\theta_1,\dots,\theta_m$
-- statement:
--   The set of grid points: all the points $\theta_l$ of the sequence, together with the last point $\theta_m:=\mathrm{MaxV}$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.21, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_thetaSeq
import Definitions.Def_MultiSelectPandora_MaxV

namespace MultiSelectPandora

/-- **The set of grid points `θ_1, …, θ_m`.** Beyhaghi–Han–Luqman manuscript, Definition 3.21, p.15 (PDF p.16): the points of
`thetaSeq`, and "the last point is `θ_m := MaxV`". -/
def gridPts (I : Inst) (k : ℕ) (ε : ℝ) : Set ℝ := {x | (∃ l, x = thetaSeq I k ε l) ∨ x = MaxV I k ε}

end MultiSelectPandora


