-- Prove2me | Definitions.Def_Max3CutHard_Supplement_Sval
-- name    : Max3CutHard_Supplement_Sval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:45:15.660051+00:00
-- url     : https://prove2.me/theorems/29459cad-b279-40d1-b637-2d5e0d4e57b0
-- title:
--   Pattern value $S_y(x)=\sum_t V_t(x,y)$ of a family
-- statement:
--   Let $(I_0,I_1,I_2)$ be a family of gadgets for Max-$k$-Cut, $I_t$ used for equations of type $t\in\mathbb Z_3$, and write $V_t=V_{I_t}$ for the gadget values. For a colouring $x\in[k]^3$ of the primaries and a colouring $y\in[k]^k$ of the global vertices, the **pattern value** is
--
--   $$S_y(x)=\sum_{t\in\mathbb Z_3}V_t(x,y).$$
--
--   It charges a colour pattern $x$ with the values of all three gadgets at once; its maximum is the numerator of the ratio $\rho$ of the soundness criterion (Theorem 4.1) and the left side of the barrier (Theorem 7.1).
--
--   **Formalization Note** The family is the published `Max3CutHard.Family k`, the value $V_t(x,y)$ the published `Gadget.gval`, defined for every $y$; primaries are 0-based.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Gadgets, p.5

import Mathlib
import Definitions.Def_Max3CutHard_Family
import Definitions.Def_Max3CutHard_Gadget_gval

namespace Max3CutHard.Supplement

open Max3CutHard

/-- **The pattern value `S_y(x)` of a family.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Gadgets, p.5:
"We write `V_t = V_{I_t}` and `S_y(x) = Σ_t V_t(x, y)`."

**Formalization Note.** `F : Family k` is the published triple `(I0, I1, I2)` indexed by
`t : ZMod 3`; `x : Fin 3 → Fin k` colours the primaries (0-based), `y : Fin k → Fin k` the
globals, and `V_t(x, y)` is the published `(F t).gval x y` (defined for every `y`). -/
noncomputable def Sval {k : ℕ} [NeZero k] (F : Family k) (x : Fin 3 → Fin k) (y : Fin k → Fin k) : ℝ :=
  ∑ t : ZMod 3, (F t).gval x y

end Max3CutHard.Supplement


