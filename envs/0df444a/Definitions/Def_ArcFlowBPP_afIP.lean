-- Prove2me | Definitions.Def_ArcFlowBPP_afIP
-- name    : ArcFlowBPP_afIP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:07:52.963129+00:00
-- url     : https://prove2.me/theorems/33264d6d-2534-4ccb-9da8-e58bff44cab8
-- title:
--   Integer optimum of the arc-flow model
-- statement:
--   The **integer optimum** of the arc-flow model (17)–(22) for the graph $G$, demands $b$ and exact-demand set $J$ is the minimum of $z$ over all integer feasible $(f, z)$.
--
--   **Formalization Note** The value is an infimum in $\mathbb N \cup \{\infty\}$ (`ℕ∞`); it is $\infty$ exactly when the program is infeasible.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, model (17)–(22), p.7

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph
import Definitions.Def_ArcFlowBPP_FlowConservation
import Definitions.Def_ArcFlowBPP_labelFlow
import Definitions.Def_ArcFlowBPP_ArcFlowFeasible

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, model (17)–(22), p.7: the optimal value of the integer arc-flow program,
`min z` over the integer feasible `(f, z)`.

**Formalization Note.** The value is the infimum in `ℕ∞`, so it is `⊤` exactly when the program
is infeasible. -/
noncomputable def afIP {m : ℕ} {V A : Type*} [Fintype A] [DecidableEq V] (G : LabelledGraph m V A)
    (b : Fin m → ℕ) (J : Finset (Fin m)) : ℕ∞ :=
  ⨅ (f : A → ℕ) (z : ℕ) (_ : ArcFlowFeasible ℕ G b J f z), (z : ℕ∞)

end ArcFlowBPP


