-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch07_ch07Moment
-- name    : RamanujanLostNotebook_PartI_ch07_ch07Moment
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T04:53:38.101621+00:00
-- url     : https://prove2.me/theorems/c3002309-93e4-486a-88f6-921046c9596b
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 7: ch07Moment
-- statement:
--   The finite character moment M_j(χ)=∑_{r=1}^{k-1}χ(r)r^j, equations (7.2.2), (7.3.2). Empty ranges have their usual finite-sum meaning.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 7.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- The finite character moment M_j(χ)=∑_{r=1}^{k-1}χ(r)r^j, equations (7.2.2), (7.3.2). Empty ranges have their usual finite-sum meaning. -/
noncomputable def ch07Moment (k : ℕ) (χ : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (k - 1), χ r * (r : ℝ) ^ j

end RamanujanLostNotebook.PartI

end


