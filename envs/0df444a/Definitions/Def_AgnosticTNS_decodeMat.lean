-- Prove2me | Definitions.Def_AgnosticTNS_decodeMat
-- name    : AgnosticTNS_decodeMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:03.065735+00:00
-- url     : https://prove2.me/theorems/ea97afd2-d116-414a-b128-6fbb3149e434
-- title:
--   Decoder of density-matrix descriptions
-- statement:
--   A string $s$ decodes to the matrix $M$, with Gaussian-rational entries, whose description is a prefix of $s$ (the entry count is fixed, so at most one $M$ qualifies); otherwise to nothing. It reads the output of the tomography procedure of Lemma 3.9 ("a classical description of a density operator").
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 3.9, p.26

import Mathlib
import Definitions.Def_AgnosticTNS_encMat

namespace AgnosticTNS

/-- **The fixed decoder of a density-matrix description**, Lemma 3.9, p.26 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `s` decodes to
the matrix `M` with Gaussian-rational entries whose description `encMat M` is a prefix of `s`;
`none` if there is none. The entry count is fixed by `ι`, so at most one `M` qualifies. -/
noncomputable def decodeMat (ι : Type) [Fintype ι] (s : QAlgorithms.Complexity.Str) :
    Option (Matrix ι ι ℂ) := by
  classical
  exact if h : ∃ M : Matrix ι ι ℂ, (∀ a b, ∃ q : ℚ × ℚ, M a b = ⟨q.1, q.2⟩) ∧ encMat M <+: s then
    some h.choose
  else none

end AgnosticTNS


