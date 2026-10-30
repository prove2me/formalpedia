-- Prove2me | Definitions.Def_RoslingAssembly_Network_h
-- name    : RoslingAssembly_Network_h
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:34:53.544749+00:00
-- url     : https://prove2.me/theorems/2cc441c5-9f49-4655-931a-05e00fe83797
-- title:
--   Echelon holding cost $h_i=H_i-\sum_{k\in P(i)}H_k$
-- statement:
--   Let $H_i\in\mathbb R$ be the **installation holding cost** of item $i$: the cost per period of one unit of $i$ in stock or in assembly into its successor. The **echelon holding cost** of $i$ is the value added by assembling it,
--   $$h_i=H_i-\sum_{k\in P(i)}H_k .$$
--
--   Problem P is written in echelon costs: the holding part of the period cost is $\sum_i\alpha^{l_i}h_iY_{it}$.
--
--   **Formalization Note** $H$ is an arbitrary real vector (no sign condition); $h$ is computed from it, so the identity $H_1=\sum_ih_i$ is a theorem, not an assumption.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 566

import Mathlib
import Definitions.Def_RoslingAssembly_Network_P

namespace RoslingAssembly

/-- **Echelon holding cost** h_i (§1, p. 566). Rosling, *Optimal Inventory Policies for Assembly
Systems under Random Demands*, Operations Research 37(4), 1989, p. 566 (unnumbered):
"H_i = unit installation holding cost per period of item i; h_i = unit echelon holding cost per
period of item i, h_i = H_i − Σ_{k∈P(i)} H_k;".

Given installation holding costs `H : Fin N → ℝ`, `net.h H i = H i − Σ_{k ∈ P(i)} H k`.

**Formalization Note.** The costs `H` are arbitrary reals: Theorem 4 assumes no sign condition.
Items are `Fin N`, 0-based (paper item `i` is Lean item `i − 1`). -/
def Network.h {N : ℕ} (net : Network N) (H : Fin N → ℝ) (i : Fin N) : ℝ :=
  H i - ∑ k ∈ net.P i, H k

end RoslingAssembly


