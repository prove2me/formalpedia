-- Prove2me | Definitions.Def_IntMul_TraceRelocation
-- name    : IntMul_TraceRelocation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T05:01:08.055627+00:00
-- url     : https://prove2.me/theorems/206543b9-26fb-4994-b571-7656d625f19b
-- title:
--   Physical tape-window trace relocation retaining input and ancestor prefixes
-- source:
--   Original exact-clock tape-window relocation interface. Written by Codex.

import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.TraceRelocation

/-- Relocate the noninput tape windows of a configuration, retaining every
ancestor prefix and the complete outer input tape. This is proof-only data;
no address or bound is supplied to the machine's finite transition table. -/
def frame (N : MultitapeTM) (base : N.Cfg) (shift lower : Fin N.k → ℕ) (c : N.Cfg) : N.Cfg where
  state := c.state
  cells := fun i p => if i=N.inTape then base.cells i p
    else if p< shift i+lower i then base.cells i p else c.cells i (p-shift i)
  head := fun i => if i=N.inTape then base.head i else shift i+c.head i

end IntMul.TraceRelocation


