-- Prove2me | Definitions.Def_StableMSR_SeparatorLoopOrder
-- name    : StableMSR_SeparatorLoopOrder
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T01:33:58.541909+00:00
-- url     : https://prove2.me/theorems/f74bb79c-9be3-4b40-941f-7d43445dcf12
-- title:
--   The cut-tree preorder and positional decoding of a separator assignment
-- statement:
--   A cut prefix visits the possible larger vertices in decreasing order, keeping the original suffix for recursive calls. An assignment index is decoded by repeated division and remainder while scanning the separator backwards. A candidate tuple is admissible when every local index is feasible.
-- source:
--   Integer implementation of the separator traversal in the stable sum-of-radii clustering mission, Appendix A.6.

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration
open SingleCircuit TightLanguage WindowCSP
set_option autoImplicit false
set_option maxHeartbeats 2300000

/-- Each possible first vertex is paired with its increasing suffix. -/
def extensions : List ℕ→List (ℕ×List ℕ)
  | []=>[] | v::vs=>extensions vs++[(v,vs)]

/-- Preorder of the depth-limited cut tree. Children are visited in descending
index order when the input is increasing, as in the program's cut stack. -/
def preorder (vs:List ℕ) : ℕ→List (List ℕ)
  | 0=>[[]]
  | w+1=>[]::(extensions vs).flatMap (fun p=>(preorder p.2 w).map (p.1::·))

def readBack (M:ℕ) : List ℕ→ℕ→Assignment
  | [],_=>[] | v::vs,z=>readBack M vs (z/M)++[(v,z%M)]

def admissible (valid:ℕ→ℕ→Bool) (a:Assignment) := a.all fun q=>valid q.1 q.2

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration


