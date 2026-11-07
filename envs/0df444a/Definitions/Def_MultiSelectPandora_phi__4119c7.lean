-- Prove2me | Definitions.Def_MultiSelectPandora_phi__4119c7
-- name    : MultiSelectPandora_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:09.339687+00:00
-- url     : https://prove2.me/theorems/4119c73f-6f01-42ae-8010-0763f83b9b8a
-- title:
--   The function $\varphi$
-- statement:
--   $\varphi(x):=\Phi(M,\alpha)$ for any state $\alpha$ with $\alpha_k=x$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.21, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Phi

namespace MultiSelectPandora

/-- **`φ(x) := Φ(M, α)` for any state `α` with `α_k = x`.** Beyhaghi–Han–Luqman manuscript, Definition 3.21, p.15 (PDF p.16). -/
noncomputable def phi (I : Inst) (x : ℝ) : ℝ := Phi I Finset.univ x

end MultiSelectPandora


