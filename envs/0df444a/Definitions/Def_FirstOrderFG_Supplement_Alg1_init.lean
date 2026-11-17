-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_init
-- name    : FirstOrderFG_Supplement_Alg1_init
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:38:24.267287+00:00
-- url     : https://prove2.me/theorems/61076587-5fd3-45c0-8dc6-7429d809d61c
-- title:
--   Uniform initialization of Algorithm 1
-- statement:
--   Given $K$ arms and a learning rate $\eta$, Algorithm 1 starts with the uniform EXP3 distribution $p_{1,i}=1/K$ and keeps $\eta$ fixed for the instance.
--
--   This initialization is reused at every restart made by Algorithm 3.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 1, line 1, p.7

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_State

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Initialization of Algorithm 1.** Zhang–Zhang–Luo–Mineiro,
*Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Algorithm 1, line 1, p.7: `p₁` is uniform on the `K` arms and the input learning rate is
kept fixed throughout the instance. -/
noncomputable def Alg1.init (K : ℕ) (η : ℝ) : Alg1.State K :=
  ⟨η, fun _ => 1 / (K : ℝ)⟩

end FirstOrderFG.Supplement


