-- Prove2me | Definitions.Def_MultiSelectPandora_MaxV
-- name    : MultiSelectPandora_MaxV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:09.896199+00:00
-- url     : https://prove2.me/theorems/6d4e6dda-402f-47eb-ae4c-d2095cd6610d
-- title:
--   The value $\mathrm{MaxV}$
-- statement:
--   $\mathrm{MaxV}:=\max\{\theta,\max_{i\in M}\sigma_i\}$. Since $\kappa_i\le\sigma_i$, $\varphi(x)=0$ for $x\ge\mathrm{MaxV}$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.21, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_resv
import Definitions.Def_MultiSelectPandora_theta

namespace MultiSelectPandora

/-- **`MaxV := max{θ, max_i σ_i}`.** Beyhaghi–Han–Luqman manuscript, Definition 3.21, p.15 (PDF p.16). -/
noncomputable def MaxV (I : Inst) (k : ℕ) (ε : ℝ) : ℝ := Finset.univ.fold max (theta I k ε) (resv I)

end MultiSelectPandora


