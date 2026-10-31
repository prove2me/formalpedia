-- Prove2me | Definitions.Def_AlgoTransparency_OState
-- name    : AlgoTransparency_OState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:18.098209+00:00
-- url     : https://prove2.me/theorems/9de411b8-7761-41b1-9115-7a5801484528
-- title:
--   States $A,B,C,D$ of the opaque game
-- statement:
--   In the opaque game each agent ends in one of four states, by education (the causal feature) and by the undisclosed correlational feature:
--
--   - $A$: education 0, correlational feature 1;
--   - $B$: education 1, correlational feature 1;
--   - $C$: education 0, correlational feature 0;
--   - $D$: education 1, correlational feature 0.
--
--   The firm's opaque hiring strategy assigns a hiring probability $P_S$ to each state.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, §3, p.11 (PDF 12)

import Mathlib

namespace AlgoTransparency

/-- **The four states of the opaque game**, Wang, Huang, Jasin & Singh, arXiv:2008.09283v1, §3,
p.11 (PDF 12):

* `A` — low causal feature (education 0), high correlational feature;
* `B` — high causal feature (education 1), high correlational feature;
* `C` — low causal feature, low correlational feature;
* `D` — high causal feature, low correlational feature.

The firm's opaque hiring strategy is a hiring probability `P S` for each state `S`. -/
inductive OState
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

end AlgoTransparency


