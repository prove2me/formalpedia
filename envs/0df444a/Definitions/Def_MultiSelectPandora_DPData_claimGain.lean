-- Prove2me | Definitions.Def_MultiSelectPandora_DPData_claimGain
-- name    : MultiSelectPandora_DPData_claimGain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:53.443096+00:00
-- url     : https://prove2.me/theorems/f9ec9995-8084-4f39-aeb7-af8c416625e9
-- title:
--   The marginal reward of a closed claim
-- statement:
--   The marginal reward of claiming box $i$ closed at state $\alpha$ is $g(\alpha,a_i^1)=(b_i-\alpha_k)_+$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Table 1, p.7 (PDF p.8); Definition 3.19, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_MultiSelectPandora_DPData
import Definitions.Def_MultiSelectPandora_stFloor

namespace MultiSelectPandora

/-- **The marginal reward of a closed claim.** Beyhaghi–Han–Luqman manuscript, Table 1, p.7 (PDF p.8):
`g(α, a¹_i) = (E[v_i] − α_k)_+`; Definition 3.19, p.14 (PDF p.15). -/
noncomputable def DPData.claimGain {n : ℕ} {s : Fin n → ℕ} (J : DPData n s) {k : ℕ} (α : Fin k → ℝ) (i : Fin n) : ℝ :=
  max (J.b i - stFloor α) 0

end MultiSelectPandora


