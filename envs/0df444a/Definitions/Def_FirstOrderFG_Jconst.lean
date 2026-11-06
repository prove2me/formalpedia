-- Prove2me | Definitions.Def_FirstOrderFG_Jconst
-- name    : FirstOrderFG_Jconst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:31.004571+00:00
-- url     : https://prove2.me/theorems/36ff1904-61a0-45a2-8ed7-16ecf5676e29
-- title:
--   $J=\lceil\log_2(2MT)\rceil$
-- statement:
--   With $M=|\mathcal B|$ and horizon $T$,
--   $$
--   J=\lceil\log_2(2MT)\rceil .
--   $$
--   It bounds the number of increases of the meta-action learning rate.
--
--   **Formalization Note** Computed as `Nat.clog 2 (2*M*T)`, the least $k$ with $2MT\le 2^k$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, line 1, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Bset

namespace FirstOrderFG

/-- **`J = ⌈log₂(2MT)⌉`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, line 1, p.10, with `M = |B|`.

**Formalization Note.** `Nat.clog 2 n` is the least `k` with `n ≤ 2^k`, i.e. `⌈log₂ n⌉` for
`n ≥ 1`. -/
def Jconst {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) : ℕ :=
  Nat.clog 2 (2 * (Bset E).card * T)

end FirstOrderFG


