-- Prove2me | Definitions.Def_RoslingAssembly_Xpath
-- name    : RoslingAssembly_Xpath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:36:19.511479+00:00
-- url     : https://prove2.me/theorems/93b8e098-e741-440a-90a8-3c32bdfbaacb
-- title:
--   Echelon inventory position before ordering $X_{it}=Y_{i,t-1}-\xi_{t-1}$
-- statement:
--   $X_{it}$ is the **echelon inventory position of item $i$ before ordering** in period $t$: the position after ordering in period $t-1$ minus the demand of period $t-1$,
--   $$X_{it}=Y_{i,t-1}-\xi_{t-1}.$$
--   The amount $Y_{it}-X_{it}$ is ordered of item $i$ in period $t$ and arrives $l_i$ periods later.
--
--   **Formalization Note** Periods are integers; for $t=1$ the formula uses the pre-horizon history $Y_{i,0}$, $\xi_0$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, pp. 566–567, Problem P

import Mathlib
import Definitions.Def_RoslingAssembly_Ypath
import Definitions.Def_RoslingAssembly_demPath

namespace RoslingAssembly

/-- **Echelon inventory position before ordering**, X_it (§1, pp. 566–567). Rosling, *Optimal
Inventory Policies for Assembly Systems under Random Demands*, Operations Research 37(4), 1989,
p. 566: "X_it = echelon inventory position of item i in period t before ordering decisions are
made"; p. 567, Problem P: "X_it = Y_{i,t−1} − ξ_{t−1}".

`Xpath Yh ξh pol ω t i = Y_{i,t−1} − ξ_{t−1}` along the demand path `ω`.

**Formalization Note.** Periods are integers with the paper's numbering; for `t = 1` the formula
uses the pre-horizon history `Y_{i,0}`, `ξ_0`. -/
def Xpath {N : ℕ} (Yh : ℤ → Fin N → ℝ) (ξh : ℤ → ℝ) (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ)
    (ω : ℕ → ℝ) (t : ℤ) (i : Fin N) : ℝ :=
  Ypath Yh pol ω (t - 1) i - demPath ξh ω (t - 1)

end RoslingAssembly


