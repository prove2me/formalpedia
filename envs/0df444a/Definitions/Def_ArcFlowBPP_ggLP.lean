-- Prove2me | Definitions.Def_ArcFlowBPP_ggLP
-- name    : ArcFlowBPP_ggLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:58.247283+00:00
-- url     : https://prove2.me/theorems/09bab73b-ed63-4867-baa9-c5b82aa8f0f5
-- title:
--   Linear-relaxation value of the Gilmore–Gomory model over a pattern set
-- statement:
--   The **linear-relaxation value** (lower bound) of the Gilmore–Gomory model (6)–(8) over the pattern set $P$ is the infimum of $\sum_p x_p$ over all real $x \ge 0$ that use only patterns of $P$ and satisfy (7).
--
--   **Formalization Note** The value is an infimum in `EReal`; it is $+\infty$ exactly when the relaxation is infeasible.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, model (6)–(8), p.4; "lower bounds", proof of Property 1, p.7

import Mathlib
import Definitions.Def_ArcFlowBPP_coverage
import Definitions.Def_ArcFlowBPP_numRolls
import Definitions.Def_ArcFlowBPP_GGFeasible

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, model (6)–(8), p.4, and "lower bounds", p.7: the optimal value of the linear
relaxation of the Gilmore–Gomory program over the pattern set `P`, `inf ∑_p x_p` over the real
`x ≥ 0` satisfying (7).

**Formalization Note.** The value is the infimum in `EReal`, so it is `⊤` exactly when the
relaxation is infeasible. -/
noncomputable def ggLP {m : ℕ} (P : Set (Fin m → ℕ)) (b : Fin m → ℕ) : EReal :=
  ⨅ (x : (Fin m → ℕ) →₀ ℝ) (_ : GGFeasible ℝ P b x), ((numRolls x : ℝ) : EReal)

end ArcFlowBPP


