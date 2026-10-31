-- Prove2me | Definitions.Def_ArcFlowBPP_numRolls
-- name    : ArcFlowBPP_numRolls
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:07.827988+00:00
-- url     : https://prove2.me/theorems/ad994c91-fb44-40ff-ac42-f3290064f374
-- title:
--   Number of rolls (bins) used by a Gilmore–Gomory solution
-- statement:
--   The **objective** (6) of the Gilmore–Gomory model, $\sum_p x_p$: the total number of rolls (bins) used by a solution that cuts $x_p$ rolls according to pattern $p$.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, eq. (6), p.4

import Mathlib

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, eq. (6), p.4: the Gilmore–Gomory objective `∑_{j∈J} xⱼ`, the total number of
rolls (bins) used. -/
def numRolls {m : ℕ} {R : Type*} [AddCommMonoid R] (x : (Fin m → ℕ) →₀ R) : R :=
  x.sum fun _ c => c

end ArcFlowBPP


