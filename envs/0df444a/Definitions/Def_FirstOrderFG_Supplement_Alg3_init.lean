-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_init
-- name    : FirstOrderFG_Supplement_Alg3_init
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:51:24.305198+00:00
-- url     : https://prove2.me/theorems/1295508c-aa05-42c8-9466-b1a980d5b716
-- title:
--   Initialization of Algorithm 3
-- statement:
--   Algorithm 3 starts with $A_1=1$, $S=0$, and a fresh Algorithm 1 instance with
--
--   $$
--   \eta_{1,1}=\max\left\{\frac1{KT},\frac1{12A_1}\right\}.
--   $$
--
--   The embedded Algorithm 1 distribution is uniform.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 3, lines 1–2, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg3_State
import Definitions.Def_FirstOrderFG_Supplement_Alg1_init
import Definitions.Def_FirstOrderFG_Supplement_Alg1_initialEta

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Initialization of Algorithm 3.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Algorithm 3, lines 1–2, p.15: `A₁ = 1`,
`η₁,₁ = max{1/(KT),1/(12A₁)}`, `S = 0`, and a fresh uniform Algorithm 1 instance. -/
noncomputable def Alg3.init (K T : ℕ) : Alg3.State K :=
  ⟨1, Alg1.init K (Alg1.initialEta K T 1), 0⟩

end FirstOrderFG.Supplement


