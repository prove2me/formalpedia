-- Prove2me | Definitions.Def_FirstOrderFG_sigmaConst
-- name    : FirstOrderFG_sigmaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:48:23.518837+00:00
-- url     : https://prove2.me/theorems/1df76994-e8dc-4814-9448-382526cf0583
-- title:
--   $\sigma=e^{1/J}$
-- statement:
--   The growth factor of the meta-action learning rate is $\sigma=e^{1/J}$, $J=\lceil\log_2(2MT)\rceil$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, line 1, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Jconst

namespace FirstOrderFG

/-- **`σ = e^{1/J}`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, line 1, p.10. -/
noncomputable def sigmaConst {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) : ℝ :=
  Real.exp (1 / (Jconst E T : ℝ))

end FirstOrderFG


