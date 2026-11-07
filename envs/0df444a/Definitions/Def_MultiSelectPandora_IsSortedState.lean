-- Prove2me | Definitions.Def_MultiSelectPandora_IsSortedState
-- name    : MultiSelectPandora_IsSortedState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:54.586883+00:00
-- url     : https://prove2.me/theorems/7d50dd30-8774-49dc-b5cd-27264ad267a0
-- title:
--   States: sorted nonnegative tuples
-- statement:
--   A state is a tuple $\alpha=(\alpha_1\ge\dots\ge\alpha_k)$ of nonnegative reals: the $k$ best values secured so far.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.2, pp.5–6 (PDF pp.6–7); Table 1, p.7 (PDF p.8)

import Mathlib

namespace MultiSelectPandora

/-- **A state**: a sorted tuple `α_1 ≥ ⋯ ≥ α_k` of nonnegative reals. Beyhaghi–Han–Luqman manuscript, §2.2, pp.5–6
(PDF pp.6–7), and Table 1, p.7 (PDF p.8).

**Formalization Note.** States are plain functions `Fin k → ℝ` with this predicate on the side, and `α_j` of the page is
`α ⟨j − 1, _⟩`. -/
def IsSortedState {k : ℕ} (α : Fin k → ℝ) : Prop := Antitone α ∧ ∀ j, 0 ≤ α j

end MultiSelectPandora


