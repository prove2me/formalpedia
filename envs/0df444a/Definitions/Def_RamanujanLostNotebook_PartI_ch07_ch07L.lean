-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07L
-- name    : RamanujanLostNotebook_PartI_ch07_ch07L
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T04:57:26.129986+00:00
-- url     : https://prove2.me/theorems/2dce059f-ae12-41b2-8a64-504677a0b5ea
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07L
-- statement:
--   The period-grouped Dirichlet L-value. Under the nonprincipal character conditions and s≥1, the grouped family is absolutely summable; the L-value identities assert HasSum rather than assuming convergence. Outside that domain this is a totalized tsum.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07LTerm

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The period-grouped Dirichlet L-value. Under the nonprincipal character conditions and s≥1, the grouped family is absolutely summable; the L-value identities assert HasSum rather than assuming convergence. Outside that domain this is a totalized tsum. -/
noncomputable def ch07L (k : ℕ) (χ : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑' m : ℕ, ch07LTerm k χ s m

end RamanujanLostNotebook.PartI

end


