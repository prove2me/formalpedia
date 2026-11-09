-- Prove2me | Definitions.Def_AgnosticTNS_decodeTTN
-- name    : AgnosticTNS_decodeTTN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:54.286011+00:00
-- url     : https://prove2.me/theorems/f3f80935-19c1-4ea9-a7c0-2097e2d8faaf
-- title:
--   Decoder of learner outputs
-- statement:
--   An output string $s$ decodes to the TTN description $D$, with Gaussian-rational tensor entries, whose binary description is a prefix of $s$; otherwise to nothing. The description is self-delimiting, so at most one $D$ qualifies. The decoder is one fixed function of the mission, so the output-form clauses of the theorems are not left to the learner.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.10, p.26

import Mathlib
import Definitions.Def_AgnosticTNS_encTTN

namespace AgnosticTNS

/-- **The fixed decoder of learner outputs**, Proposition 3.10, p.26 ("The output description")
(Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): an output string `s` decodes to the TTN `D` (with Gaussian-rational tensor entries) whose
description `encTTN D` is a prefix of `s`; `none` if there is no such `D`.

**Formalization Note** The description is self-delimiting, so at most one `D` qualifies; the choice
only makes the definition total. The decoder is one function fixed by the mission, not chosen by a
learner. -/
noncomputable def decodeTTN (n d : ℕ) (s : QAlgorithms.Complexity.Str) : Option (Σ m, TTN m n d) := by
  classical
  exact if h : ∃ D : Σ m, TTN m n d,
      (∀ k a b c, ∃ q : ℚ × ℚ, D.2.tensor k a b c = ⟨q.1, q.2⟩) ∧ encTTN D <+: s then
    some h.choose
  else none

end AgnosticTNS


