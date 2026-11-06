-- Prove2me | Definitions.Def_MemQueryFeas_SucceedsNonAdaptive
-- name    : MemQueryFeas_SucceedsNonAdaptive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:50.207713+00:00
-- url     : https://prove2.me/theorems/8b37e8cc-5db8-4330-acd6-eb0a7df0bd48
-- title:
--   Deterministic success within $T$ queries against non-adaptive oracles
-- statement:
--   A deterministic $M$-bit algorithm **solves feasibility problems of accuracy $\varepsilon$ within $T$ queries against non-adaptive oracles** if for every feasibility instance $Q$ of accuracy $\varepsilon$ and every valid non-adaptive separation oracle for $Q$, one of the queries $x_0,\dots,x_{T-1}$ lies in $Q$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Theorem 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_MemQueryFeas_DetMemAlg_runN
import Definitions.Def_MemQueryFeas_IsFeasInstance
import Definitions.Def_MemQueryFeas_IsValidNonAdaptive

namespace MemQueryFeas

/-- **A deterministic algorithm solving feasibility problems within `T` queries against non-adaptive
oracles.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Theorem 1, p.2 (PDF p.3): "For deterministic algorithms, the oracle can be
non-adaptive."

`SucceedsNonAdaptive alg ε T`: for every feasibility instance `Q` of accuracy `ε` and every valid
non-adaptive separation oracle for `Q`, one of the first `T` queries `x_0, …, x_{T-1}` lies in `Q`. -/
def SucceedsNonAdaptive {d M : ℕ} (alg : DetMemAlg d M) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (Q : Set (Vec d)) (O : ℕ → Vec d → Option (Vec d)),
    IsFeasInstance ε Q → IsValidNonAdaptive Q O → ∃ t < T, alg.query (alg.runN O t) ∈ Q

end MemQueryFeas


