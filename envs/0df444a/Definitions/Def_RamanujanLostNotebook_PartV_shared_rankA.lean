-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_shared_rankA
-- name    : RamanujanLostNotebook_PartV_shared_rankA
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T16:05:59.577028+00:00
-- url     : https://prove2.me/theorems/1acdda41-71ee-4864-bd63-d18d106bd9f5
-- title:
--   Ramanujan's Lost Notebook Part V, shared: rankA
-- statement:
--   Ramanujan's `f_a(q) = ∑_{n ≥ 0} q^{n^2} / ∏_{j=1}^{n} (1 + a q^j + q^{2j})` ((4.1.3),
--   p. 35), for a complex parameter `a` (the book takes `a` real).
--
--   Domain: `‖q‖ < 1` and no factor `1 + a q^j + q^{2j}` equal to `0` (automatic for real
--   `a` with `|a| ≤ 2`).  There `f_a(q) = G(z, q)` for either root `z` of `z^2 + a z + 1 = 0`
--   ((4.1.4)).  Outside: a zero denominator gives a term `0`.
--   Reference: `f_2 = mockF3`, `f_0 = mockPhi3`, `f_1(1/5) = 1.1625295047869521633…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartV

/-- Ramanujan's `f_a(q) = ∑_{n ≥ 0} q^{n^2} / ∏_{j=1}^{n} (1 + a q^j + q^{2j})` ((4.1.3),
p. 35), for a complex parameter `a` (the book takes `a` real).

Domain: `‖q‖ < 1` and no factor `1 + a q^j + q^{2j}` equal to `0` (automatic for real
`a` with `|a| ≤ 2`).  There `f_a(q) = G(z, q)` for either root `z` of `z^2 + a z + 1 = 0`
((4.1.4)).  Outside: a zero denominator gives a term `0`.
Reference: `f_2 = mockF3`, `f_0 = mockPhi3`, `f_1(1/5) = 1.1625295047869521633…`. -/
def rankA (a q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) /
    (∏ j ∈ Finset.range n, (1 + a * q ^ (j + 1) + q ^ (2 * (j + 1))))

end RamanujanLostNotebook.PartV

end


