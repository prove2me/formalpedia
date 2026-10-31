-- Prove2me | Definitions.Def_AlgoTransparency_TState
-- name    : AlgoTransparency_TState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:19.369102+00:00
-- url     : https://prove2.me/theorems/8e89ea28-e3ac-4eb3-97a6-41dddbf496ca
-- title:
--   States $E,F$ of the transparent game
-- statement:
--   Once the firm discloses its correlational feature, every agent raises it (the paper's modelling assumption 2, pp.12–13), so agents differ only in education:
--
--   - $E$: education 0;
--   - $F$: education 1.
--
--   The firm's transparent hiring strategy assigns a hiring probability $P_S$ to each of the two states.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §3.1, p.13 (PDF 14)

import Mathlib

namespace AlgoTransparency

/-- **The two states of the transparent game**, Wang, Huang, Jasin & Singh, arXiv:2008.09283v1,
§3.1, p.13 (PDF 14): once the correlational feature is disclosed every agent is high on it
(the paper's modelling assumption 2, pp.12–13), so agents differ only in education:

* `E` — low education (0);
* `F` — high education (1).

The firm's transparent hiring strategy is a hiring probability `P S` for each state `S`. -/
inductive TState
  | E
  | F
  deriving DecidableEq, Repr

end AlgoTransparency


