-- Prove2me | Definitions.Def_CutRankSched_Supplement_gdpSet
-- name    : CutRankSched_Supplement_gdpSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:45:42.608368+00:00
-- url     : https://prove2.me/theorems/0ede1266-2767-4e0a-a374-ae41c9ba58c1
-- title:
--   The state sets of the global-rank DP
-- statement:
--   For a rank factorization $A=BC$ and a budget $L$, the **state set** of the global-rank DP at cut $k$ is defined by recursion: at $k=0$ it is the single state with all $V_s=\{0\}$ and no labels; at cut $k+1$ it consists of the successors (8) of the states at cut $k$ under every trial layer $t$ passing the tests (7) and (5). Identical states are merged.
--
--   **Formalization Note** The recursion is the DP's transition, not the span invariant (6) it maintains.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.2, pp.8–9

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Supplement_GState
import Definitions.Def_CutRankSched_Supplement_gLegal
import Definitions.Def_CutRankSched_Supplement_gNext

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- The set of states held by the global-rank DP after processing the first `k` events
(Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.2, pp.8–9): initially the single state `(({0})_{s=1}^L, ∅)`; the states at cut `k + 1`
are the successors (8) of the states at cut `k` under the trial layers passing (7) and (5).
Identical states are merged (a set of states).

**Formalization Note** The recursion is the DP's transition, not the span invariant (6). The value
at `k + 1 > n` is set to the value at `k`. -/
noncomputable def gdpSet (I : Instance) {r : ℕ} (L : ℕ) (B : Matrix (Fin I.n) (Fin r) (ZMod 2))
    (C : Matrix (Fin r) (Fin I.n) (ZMod 2)) : ℕ → Set (GState I r L)
  | 0 => {((fun _ => ⊥), (fun _ => none))}
  | k + 1 =>
    if hk : k < I.n then
      {st' | ∃ st ∈ gdpSet I L B C k, ∃ t : Fin L,
        gLegal I L C ⟨k, hk⟩ st t ∧ st' = gNext I L B ⟨k, hk⟩ st t}
    else gdpSet I L B C k

end Supplement

end CutRankSched


