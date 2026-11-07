-- Prove2me | Definitions.Def_MultiSelectPandora_DPData_openGain
-- name    : MultiSelectPandora_DPData_openGain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:09.259389+00:00
-- url     : https://prove2.me/theorems/2e873d99-0e00-4699-a8de-4ec3e636fb4d
-- title:
--   The marginal reward of opening
-- statement:
--   The marginal reward of opening box $i$ at state $\alpha$ when position $j$ comes up is
--   $$g(\alpha,a_i^0)=(w_{ij}-\alpha_k)_+-c_i=\max\{\alpha_k,w_{ij}\}-\alpha_k-c_i.$$
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Table 1, p.7 (PDF p.8); Definition 3.19, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_MultiSelectPandora_DPData
import Definitions.Def_MultiSelectPandora_stFloor

namespace MultiSelectPandora

/-- **The marginal reward of opening.** Beyhaghi–Han–Luqman manuscript, Table 1, p.7 (PDF p.8):
`g(α, a⁰_i) = max{α_k, v_i} − α_k − c_i`; Definition 3.19, p.14 (PDF p.15). -/
noncomputable def DPData.openGain {n : ℕ} {s : Fin n → ℕ} (J : DPData n s) {k : ℕ} (α : Fin k → ℝ) (i : Fin n)
    (j : Fin (s i)) : ℝ :=
  max (J.w i j - stFloor α) 0 - J.c i

end MultiSelectPandora


