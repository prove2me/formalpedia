-- Prove2me | Definitions.Def_MemQueryFeas_GoodEvent
-- name    : MemQueryFeas_GoodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:39:15.93236+00:00
-- url     : https://prove2.me/theorems/f1aeeeb2-b87e-42e5-834c-c7329217e5bc
-- title:
--   The event of Lemma 1: a valid hard instance
-- statement:
--   For given $E_1,\dots,E_P$, versions and final oracle: $Q_{E_1,\dots,E_P}$ contains a closed ball of radius $\varepsilon$, and every response of the transform oracle to a query in the unit ball, after any history, is a valid response for $Q_{E_1,\dots,E_P}$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 1, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_MemQueryFeas_skelOracle
import Definitions.Def_MemQueryFeas_Qset
import Definitions.Def_MemQueryFeas_IsValidResp

namespace MemQueryFeas

/-- **The event of Lemma 1: a valid hard instance.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Lemma 1, p.9 (PDF p.10): "the set
`Q_{E_1,…,E_P}` contains a ball of radius `ϵ` and all oracle responses by `g` are valid separating
hyperplanes for `Q_{E_1,…,E_P}`."

`GoodEvent d ε P Eb c fin`: for base subspaces `Eb`, realized versions `c` and final oracle `fin`,
`Q_{E_1,…,E_P}` contains a closed ball of radius `ε`, and for every history and every query in the
closed unit ball the transform oracle's response is valid (`IsValidResp`) for `Q_{E_1,…,E_P}`.

**Formalization Note.** Queries lie in the unit ball (Problem setup, p.3), so validity is required
there. -/
def GoodEvent (d : ℕ) (ε : ℝ) (P : ℕ) (Eb : ℕ → Op d) (c : ℕ → List ℕ → ℕ → Op d)
    (fin : List (Vec d) → Vec d → Option (Vec d)) : Prop :=
  (∃ z : Vec d, Metric.closedBall z ε ⊆ Qset ε P Eb) ∧
    ∀ (h : List (Vec d)), ∀ x ∈ Metric.closedBall (0 : Vec d) 1,
      IsValidResp (Qset ε P Eb) x (skelOracle d ε P c fin h x)

end MemQueryFeas


