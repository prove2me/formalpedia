-- Prove2me | Definitions.Def_MultiSelectPandora_GW
-- name    : MultiSelectPandora_GW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:09.721365+00:00
-- url     : https://prove2.me/theorems/aa9b7ae6-a3d7-441c-8000-e02804370316
-- title:
--   The Weitzman continuation gain $G^W(U,\alpha)$
-- statement:
--   For a set $U$ of boxes and a state $\alpha$,
--   $$G^W(U,\alpha):=E\Big[\sum_{j=1}^k\tilde\alpha_j\Big]-\sum_{j=1}^k\alpha_j,\qquad\tilde\alpha=\mathrm{top}_k(\alpha\cup\{\kappa_i\}_{i\in U}).$$
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.10, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_cappedTop

namespace MultiSelectPandora

/-- **The Weitzman continuation gain `G^W(U, α)`.** Beyhaghi–Han–Luqman manuscript, Definition 3.10, p.10 (PDF p.11):
`G^W(U, α) := E[Σ_j α̃_j] − Σ_j α_j`, where `α̃ = top_k(α ∪ {κ_i}_{i ∈ U})`. -/
noncomputable def GW (I : Inst) {k : ℕ} (U : Finset (Fin I.n)) (α : Fin k → ℝ) : ℝ := cappedTop I U α - ∑ j, α j

end MultiSelectPandora


