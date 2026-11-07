-- Prove2me | Definitions.Def_NSWBetter_encBools
-- name    : NSWBetter_encBools
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:57.621786+00:00
-- url     : https://prove2.me/theorems/7c3aac88-2266-420c-87d5-aeea03c78679
-- title:
--   Encoding of a list of booleans
-- statement:
--   A list of booleans written as a string of the symbols $0$ and $1$ (the indicator vector of a set of agents).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Corollary 4.15, p.25 (the output: the set of well-behaved agents)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit

namespace NSWBetter

/-- **Encoding of a bit list.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Corollary 4.15, p.25: the output is the set of well-behaved agents, as its indicator list.

`encBools l` writes each bit as the symbol `0` or `1`. -/
def encBools (l : List Bool) : List OnlineCRS.Combine.Sym := l.map OnlineCRS.Combine.bit

end NSWBetter


