-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch13_ch13SeriesDomain
-- name    : RamanujanLostNotebook_PartII_ch13_ch13SeriesDomain
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T09:41:32.028806+00:00
-- url     : https://prove2.me/theorems/3873f185-5521-4acb-853b-45a46155e4ad
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 13: ch13SeriesDomain
-- statement:
--   Analytic definedness of the chapter's Lambert series and Euler products at
--   q and q^d. This is a conclusion, never a theorem premise: it exposes convergence
--   and the nonzero denominators of all eta quotients used below.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 13.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch13_ch13LambertTerm
import Definitions.Def_RamanujanLostNotebook_PartII_shared_eulerF

noncomputable section

namespace RamanujanLostNotebook.PartII

/-- Analytic definedness of the chapter's Lambert series and Euler products at
q and q^d. This is a conclusion, never a theorem premise: it exposes convergence
and the nonzero denominators of all eta quotients used below. -/
def ch13SeriesDomain (d : ℕ) (q : ℂ) : Prop :=
  (∀ r ∈ ({1, 3, 5} : Finset ℕ),
    Summable (ch13LambertTerm r q) ∧ Summable (ch13LambertTerm r (q ^ d))) ∧
  Multipliable (fun n : ℕ => 1 - q ^ (n + 1)) ∧
  Multipliable (fun n : ℕ => 1 - (q ^ d) ^ (n + 1)) ∧
  eulerF q ≠ 0 ∧ eulerF (q ^ d) ≠ 0

end RamanujanLostNotebook.PartII

end


