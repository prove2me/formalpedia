-- Prove2me | Definitions.Def_MultiSelectPandora_A3Output
-- name    : MultiSelectPandora_A3Output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:13.527282+00:00
-- url     : https://prove2.me/theorems/8eca3c97-c6d0-4ac2-af24-1eedf60f3f69
-- title:
--   The objects computed by Claim A.3
-- statement:
--   The rational objects computed from an instance: the reservation values, $W(M,0)$ and $\mathrm{OPT}_C$, the threshold $\theta$, the grid points, the values $w_i$ and $D^L(w_i)$ by support position, and $I^{SL}$ as a table. The probabilities of $w_i$ and $D^L(w_i)$ are those of the instance.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Claim A.3, p.31 (PDF p.32); p.17 (PDF p.18)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP

namespace MultiSelectPandora

/-- **The objects computed by Claim A.3.** Beyhaghi–Han–Luqman manuscript, Claim A.3, p.31 (PDF p.32), and p.17 (PDF p.18): the reservation values, `W(M, 0)` and `OPT_C`, the threshold,
the grid points, the laws of `w_i` and `D^L(w_i)` (their values by support position; the probabilities are the instance's), and `I^SL` as a table. -/
structure A3Output where
  /-- the reservation values -/
  sigma : List ℚ
  /-- `W(M, 0)` -/
  W : ℚ
  /-- `OPT_C` -/
  OPTC : ℚ
  /-- `θ` -/
  theta : ℚ
  /-- the grid points, in increasing order -/
  grid : List ℚ
  /-- the values `w_i`, by support position -/
  wVals : List (List ℚ)
  /-- the values `D^L(w_i)`, by support position -/
  xVals : List (List ℚ)
  /-- `I^SL` as a table -/
  table : RawSSDP

end MultiSelectPandora


