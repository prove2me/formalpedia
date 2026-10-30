-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09LambdaRegular
-- name    : RamanujanLostNotebook_PartII_ch09_ch09LambdaRegular
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:14:18.217404+00:00
-- url     : https://prove2.me/theorems/e341c956-9544-4ddf-8663-0d41adbbc554
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 9: ch09LambdaRegular
-- statement:
--   Source semantics for λₙ: positive index, convergent nonzero Euler
--   products at −q and −q³, and a positive value of λ. This regularity is
--   proved along with each identity, rather than assumed.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 9.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09EulerRegular
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09Lambda
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09Nome

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Source semantics for λₙ: positive index, convergent nonzero Euler
products at −q and −q³, and a positive value of λ. This regularity is
proved along with each identity, rather than assumed. -/
def ch09LambdaRegular (n : ℝ) : Prop :=
  0 < n ∧ ch09EulerRegular (-(ch09Nome n : ℂ)) ∧
    ch09EulerRegular (-((ch09Nome n : ℂ) ^ 3)) ∧ 0 < ch09Lambda n

end RamanujanLostNotebook.PartII

end


