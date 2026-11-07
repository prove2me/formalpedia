-- Prove2me | Definitions.Def_Max3CutHard_Family
-- name    : Max3CutHard_Family
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:56.964089+00:00
-- url     : https://prove2.me/theorems/9cb77751-1e80-4fd3-b46d-d9582c856559
-- title:
--   A family $(I_0,I_1,I_2)$ of gadgets
-- statement:
--   A **family** for 3Lin($\mathbb Z_3$) is a triple $(I_0,I_1,I_2)$ of gadgets; $I_t$ is used for the equations of type $t$.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Gadgets, p.5

import Mathlib
import Definitions.Def_Max3CutHard_Gadget

namespace Max3CutHard

/-- **A family for 3Lin(ℤ₃).** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Gadgets, p.5: "A family for 3Lin(ℤ₃) is a triple
`(I0, I1, I2)` of gadgets, `I_t` to be used for equations of type `t`." -/
abbrev Family (k : ℕ) : Type := ZMod 3 → Gadget k

end Max3CutHard


