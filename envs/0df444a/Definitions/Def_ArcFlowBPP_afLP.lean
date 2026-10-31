-- Prove2me | Definitions.Def_ArcFlowBPP_afLP
-- name    : ArcFlowBPP_afLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:08:00.828078+00:00
-- url     : https://prove2.me/theorems/6c66e2cb-c9dc-4862-86ba-54894dbcc054
-- title:
--   Linear-relaxation value of the arc-flow model
-- statement:
--   The **linear-relaxation value** (lower bound) of the arc-flow model (17)–(22) is the infimum of $z$ over all real $(f, z)$ with $f \ge 0$ satisfying (18)–(21).
--
--   **Formalization Note** The value is an infimum in the extended reals (`EReal`): $+\infty$ when the relaxation is infeasible, $-\infty$ if it were unbounded below.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, model (17)–(22), p.7; "lower bounds", proof of Property 1, p.7

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph
import Definitions.Def_ArcFlowBPP_FlowConservation
import Definitions.Def_ArcFlowBPP_labelFlow
import Definitions.Def_ArcFlowBPP_ArcFlowFeasible

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, model (17)–(22), p.7, and "lower bounds", p.7: the optimal value of the linear
relaxation of the arc-flow program, `inf z` over the real `(f, z)` satisfying (18)–(21) and
`f ≥ 0`.

**Formalization Note.** The value is the infimum in `EReal`, so it is `⊤` exactly when the
relaxation is infeasible (and would be `⊥` if it were unbounded below). -/
noncomputable def afLP {m : ℕ} {V A : Type*} [Fintype A] [DecidableEq V] (G : LabelledGraph m V A)
    (b : Fin m → ℕ) (J : Finset (Fin m)) : EReal :=
  ⨅ (f : A → ℝ) (z : ℝ) (_ : ArcFlowFeasible ℝ G b J f z), (z : EReal)

end ArcFlowBPP


