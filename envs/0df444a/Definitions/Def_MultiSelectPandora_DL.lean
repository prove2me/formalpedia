-- Prove2me | Definitions.Def_MultiSelectPandora_DL
-- name    : MultiSelectPandora_DL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:21:17.183512+00:00
-- url     : https://prove2.me/theorems/6e18bd10-6332-437c-a7ac-2a51b25cf1e4
-- title:
--   The large-value rounding $D^L$
-- statement:
--   $$D^L(v):=\begin{cases}v,&v<\theta,\\ \min\{\theta_l:\theta_l\ge v\},&\theta\le v\le\mathrm{MaxV},\\ \top,&v>\mathrm{MaxV}.\end{cases}$$
--   Small values are unchanged and large values are rounded up to the grid.
--
--   **Formalization Note** The minimum is an `sInf`. The set contains $\mathrm{MaxV}$ and, for a valid instance with $0<\mathrm{OPT}$, it is finite, so the `sInf` is the minimum.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.21, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_theta
import Definitions.Def_MultiSelectPandora_MaxV
import Definitions.Def_MultiSelectPandora_gridPts
import Definitions.Def_MultiSelectPandora_topLevel

namespace MultiSelectPandora

/-- **The large-value rounding `D^L`.** Beyhaghi–Han–Luqman manuscript, Definition 3.21, p.15 (PDF p.16): `D^L(v) = v` for
`v < θ`, `D^L(v) = min{θ_l : θ_l ≥ v}` for `θ ≤ v ≤ MaxV`, and `D^L(v) = ⊤` for `v > MaxV`.

**Formalization Note.** The `min` is an `sInf`: the set is nonempty (it holds `MaxV`), finite and bounded below for a valid
instance with `0 < OPT` and `ε > 0`, so `sInf` is its minimum. -/
noncomputable def DL (I : Inst) (k : ℕ) (ε v : ℝ) : ℝ :=
  if v < theta I k ε then v
  else if v ≤ MaxV I k ε then sInf {x | x ∈ gridPts I k ε ∧ v ≤ x}
  else topLevel I k ε

end MultiSelectPandora


