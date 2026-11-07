-- Prove2me | Definitions.Def_MultiSelectPandora_Levels
-- name    : MultiSelectPandora_Levels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:22:18.11299+00:00
-- url     : https://prove2.me/theorems/47053471-e2b9-4cae-95ab-26192cdca0fa
-- title:
--   The levels of a state of $I^{SL}$
-- statement:
--   The entries a state of $I^{SL}$ may hold: the small grid points, that is the multiples $q\delta$ below $\theta$; the grid points $\theta_1,\dots,\theta_m$; and $\top$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.23, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_delta
import Definitions.Def_MultiSelectPandora_theta
import Definitions.Def_MultiSelectPandora_gridPts
import Definitions.Def_MultiSelectPandora_topLevel

namespace MultiSelectPandora

/-- **The levels of a state of `I^SL`.** Beyhaghi–Han–Luqman manuscript, Definition 3.23, p.15 (PDF p.16): "sorted `k`-tuples whose
entries are small grid points, `θ_1, …, θ_m`, or `⊤`". A small grid point is a multiple of `δ` below `θ`. -/
def Levels (I : Inst) (k : ℕ) (ε : ℝ) : Set ℝ :=
  {x | (∃ q : ℕ, x = q * delta I k ε ∧ x < theta I k ε) ∨ x ∈ gridPts I k ε ∨ x = topLevel I k ε}

end MultiSelectPandora


