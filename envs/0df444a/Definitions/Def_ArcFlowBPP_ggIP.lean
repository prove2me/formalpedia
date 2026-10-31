-- Prove2me | Definitions.Def_ArcFlowBPP_ggIP
-- name    : ArcFlowBPP_ggIP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:50.755335+00:00
-- url     : https://prove2.me/theorems/ef2bd2ba-01cc-4df3-8880-ba957f7c84c7
-- title:
--   Integer optimum of the Gilmore–Gomory model over a pattern set
-- statement:
--   The **integer optimum** of the Gilmore–Gomory model (6)–(8) over the pattern set $P$ with demands $b$ is the minimum of $\sum_p x_p$ over all integer feasible $x$.
--
--   **Formalization Note** The value is an infimum in `ℕ∞`; it is $\infty$ exactly when the program is infeasible.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, model (6)–(8), p.4

import Mathlib
import Definitions.Def_ArcFlowBPP_coverage
import Definitions.Def_ArcFlowBPP_numRolls
import Definitions.Def_ArcFlowBPP_GGFeasible

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, model (6)–(8), p.4: the optimal value of the integer Gilmore–Gomory program over the
pattern set `P`, `min ∑_p x_p` over the integer feasible `x`.

**Formalization Note.** The value is the infimum in `ℕ∞`, so it is `⊤` exactly when the program
is infeasible. -/
noncomputable def ggIP {m : ℕ} (P : Set (Fin m → ℕ)) (b : Fin m → ℕ) : ℕ∞ :=
  ⨅ (x : (Fin m → ℕ) →₀ ℕ) (_ : GGFeasible ℕ P b x), ((numRolls x : ℕ) : ℕ∞)

end ArcFlowBPP


