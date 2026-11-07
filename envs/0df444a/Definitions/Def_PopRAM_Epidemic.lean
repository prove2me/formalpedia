-- Prove2me | Definitions.Def_PopRAM_Epidemic
-- name    : PopRAM_Epidemic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:09.684942+00:00
-- url     : https://prove2.me/theorems/543bd822-9665-4896-bfe8-2b55972f7968
-- title:
--   The one-way epidemic
-- statement:
--   The **one-way epidemic** is the population protocol whose agents are susceptible ($0$) or infected ($1$), with the transition
--   $$(x,y)\to(x,\max\{x,y\}).$$
--   An infected initiator infects its responder; nothing else changes.
--
--   It is the dissemination primitive behind the phase clock and the MC+ subroutines of the paper.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), p.2 (PDF p.3)

import Mathlib

set_option autoImplicit false

namespace PopRAM

/-- **The one-way epidemic** (Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM
Simulation by Population Protocols*, arXiv:2611.06178, held version sha256 f13223b3…, p.2, PDF
p.3): "the one-way epidemic process [AAE08a], whose agents are either susceptible (0) or infected
(1), with transition (x, y) → (x, max{x, y})".

**Formalization Note** States are `Bool` (`false` = susceptible, `true` = infected); `max` on
`{0, 1}` is `||`. The initiator is first. -/
def epidemicδ (x y : Bool) : Bool × Bool := (x, x || y)

end PopRAM


