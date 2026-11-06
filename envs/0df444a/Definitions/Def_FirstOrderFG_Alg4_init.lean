-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_init
-- name    : FirstOrderFG_Alg4_init
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:49:39.755835+00:00
-- url     : https://prove2.me/theorems/39605ff7-7130-439b-83ae-7d05c63e8c75
-- title:
--   Initialization of Algorithm 4
-- statement:
--   Algorithm 4 starts with $A_1=1$, $\theta_{1,1}=c/\Gamma_{A_1}$, $S=0$ and a fresh instance of Algorithm 2 with $(G,T,A_1,\theta_{1,1})$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 4, lines 1–2, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_State
import Definitions.Def_FirstOrderFG_Alg2_init
import Definitions.Def_FirstOrderFG_cConst
import Definitions.Def_FirstOrderFG_GammaA

namespace FirstOrderFG

/-- **Initialization of Algorithm 4.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 4, lines 1–2, p.32: `A₁ = 1`,
`θ_{1,1} = c/Γ_{A₁}`, `S = 0`, and an instance of Algorithm 2 with `(G, T, A₁, θ_{1,1})`. -/
noncomputable def Alg4.init {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) : Alg4.State K :=
  ⟨Alg2.init E 1 (cConst / GammaA E T 1), 0⟩

end FirstOrderFG


