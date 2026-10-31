-- Prove2me | Definitions.Def_ResistantSets_D3
-- name    : ResistantSets_D3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:39.588573+00:00
-- url     : https://prove2.me/theorems/a21e0291-bec8-4cdf-8ec9-eed3629273c9
-- title:
--   The set $D_3=\{000,100,110,111\}$
-- statement:
--   $$
--   D_3=\{000,100,110,111\}\subseteq\{0,1\}^3 .
--   $$
--   Proposition 5.3 excludes $D_3$ restrictions whose infeasible points lie on a given circuit.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.27, §5.1 (D₃)

import Mathlib

namespace ResistantSets

/-- **The set `D₃`** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §5.1, p.27): "Let D3 := {000, 100, 110, 111} ⊆ {0,1}³." -/
def D3 : Finset (Fin 3 → Bool) :=
  {![false, false, false], ![true, false, false], ![true, true, false], ![true, true, true]}

end ResistantSets


