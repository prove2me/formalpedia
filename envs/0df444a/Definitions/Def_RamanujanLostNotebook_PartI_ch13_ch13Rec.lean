-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Rec
-- name    : RamanujanLostNotebook_PartI_ch13_ch13Rec
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:29:28.894876+00:00
-- url     : https://prove2.me/theorems/1d04da91-19d3-420e-9f36-d193a0d2b986
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 13: ch13Rec
-- statement:
--   The left side of (13.5.1), after moving its q-power inside the bilateral sum.
--   This cancellation makes every exponent nonnegative, including q=0.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 13.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Partitions
import Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13ThetaScaled
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The left side of (13.5.1), after moving its q-power inside the bilateral sum.
This cancellation makes every exponent nonnegative, including q=0. -/
def ch13Rec (q : ℂ) (y : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    ∑ t ∈ ch13Partitions j,
      (-1 : ℂ) ^ (N - j + ∑ i : Fin j, (t i).val) *
      (∏ i : Fin j, y (i.val + 1) ^ (t i).val) *
      ch13ThetaScaled ((N - j + 1 : ℕ) : ℤ) (∑ i : Fin j, (t i).val)
        ((N - j) * (N - j + 1) / 2) q /
      (qPoch q q (N - j) * ∏ i : Fin j, ((Nat.factorial (t i).val : ℕ) : ℂ))

end RamanujanLostNotebook.PartI

end


