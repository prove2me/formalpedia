-- Prove2me | Definitions.Def_ResourceScheduling_Graph_RAMParse
-- name    : ResourceScheduling_Graph_RAMParse
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T14:35:44.179883+00:00
-- url     : https://prove2.me/theorems/02fd5dd0-5069-4c30-9e65-6a1e8b3f0d74
-- title:
--   ResourceScheduling Graph RAMParse
-- statement:
--   Split leading unary ones and parse the first unary field using an explicit stack program.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMOps
import Definitions.Def_ResourceScheduling_Graph_StackPrefix

set_option autoImplicit false
namespace ResourceScheduling.Graph
open CookPvsNP

def splitOnes : List Letter → ℕ × List Letter
  | [] => (0, [])
  | .sep :: w => (0, .sep :: w)
  | .one :: w => let p := splitOnes w; (p.1 + 1, p.2)

def ramParseState {V : Type} [DecidableEq V] (t good : V) (s : RAMState V) : RAMState V :=
  let p := splitOnes s.word
  { (s.set t p.1).set good (if p.2 = [] then 0 else 1) with word := p.2.tail }

def ramParse {V : Type} [DecidableEq V] (t good : V) : StackProg (RAMWire V) Letter :=
  (ramZero t).seq <| (ramZero good).seq <|
  (prefixProg ramInput (ramReg t)).seq <| .act fun h k =>
    if k = ramInput then .pop else
    if k = ramReg good ∧ (h ramInput).isSome then .push Letter.one else .keep

end ResourceScheduling.Graph


