-- Prove2me | Definitions.Def_MultiSelectPandora_stFloor
-- name    : MultiSelectPandora_stFloor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:59.359245+00:00
-- url     : https://prove2.me/theorems/2f9dd6d4-09f5-4cde-b2ad-90e39717217e
-- title:
--   The floor $\alpha_k$
-- statement:
--   The floor of a state is its last entry $\alpha_k$, the value a newly secured value has to beat.
--
--   **Formalization Note** At $k=0$ there is no last entry and the value is $0$; every result that uses the floor assumes $k\ge1$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.2, p.6 (PDF p.7)

import Mathlib

namespace MultiSelectPandora

/-- **The floor `α_k`**, the last entry of a state. Beyhaghi–Han–Luqman manuscript, §2.2, p.6 (PDF p.7).

**Formalization Note.** At `k = 0` there is no floor and the value is the junk `0`; every result that uses it assumes `1 ≤ k`. -/
noncomputable def stFloor {k : ℕ} (α : Fin k → ℝ) : ℝ := if h : 0 < k then α ⟨k - 1, by omega⟩ else 0

end MultiSelectPandora


