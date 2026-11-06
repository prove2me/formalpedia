-- Prove2me | Definitions.Def_MemQueryFeas_IsValidNonAdaptive
-- name    : MemQueryFeas_IsValidNonAdaptive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:41.54917+00:00
-- url     : https://prove2.me/theorems/e968341b-9898-4a43-8229-2fb58a9aff48
-- title:
--   Valid non-adaptive separation oracle
-- statement:
--   A **non-adaptive (oblivious) oracle** is a fixed sequence of response maps $O_0,O_1,\dots$: the query $x_t$ of round $t$ receives the response $O_t(x_t)$, which may depend on the round but not on earlier queries. It is **valid** for $Q$ if every $O_t(x)$ is a valid response for $Q$ at $x$.
--
--   **Formalization Note** Rounds are numbered from $0$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Theorem 1, p.2 (PDF p.3); footnote 2, p.3

import Mathlib
import Definitions.Def_MemQueryFeas_IsValidResp

namespace MemQueryFeas

/-- **Valid non-adaptive (oblivious) separation oracle.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Theorem 1, p.2 (PDF p.3): "For
deterministic algorithms, the oracle can be non-adaptive", with footnote 2, p.3: "non-adaptive
(oblivious) oracles"; Problem setup, p.3: "The oracle may be time-dependent".

A non-adaptive oracle is a fixed sequence of response maps `O : ℕ → Vec d → Option (Vec d)`; in round
`t` the query `x_t` receives `O t x_t`. It may depend on the round but not on past queries.
`IsValidNonAdaptive Q O` requires every `O t x` to be valid (`IsValidResp`).

**Formalization Note.** Rounds are 0-based. Validity is required at every round and every point. -/
def IsValidNonAdaptive {d : ℕ} (Q : Set (Vec d)) (O : ℕ → Vec d → Option (Vec d)) : Prop :=
  ∀ (t : ℕ) (x : Vec d), IsValidResp Q x (O t x)

end MemQueryFeas


