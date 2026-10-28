-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureData1
-- name    : Sensitivity213981Formal_Endpoint22ClosureData1
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:13:32.650318+00:00
-- url     : https://prove2.me/theorems/c8215cd1-9248-441f-b882-0319452b43bf
-- title:
--   Endpoint22 Closure Data1 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Closure Data1 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Endpoint22.nodes1`, `ThreeBoundMinmaxNumeric.Endpoint22.outputPointers1`, `ThreeBoundMinmaxNumeric.Endpoint22.newNodes1`, `ThreeBoundMinmaxNumeric.Endpoint22.outputIndex1`, `ThreeBoundMinmaxNumeric.Endpoint22.nodeCount1`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ClosureData1.lean, lines 1–143.

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureCoordinates
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile ClosureCertificate
def newNodes1:Table (Node 22):=
(.branch 2744
(.branch 2741
(.branch 2740
(.leaf ⟨(.d 10 10 12),2768124653826881164,.step (.dUp 10 10 12 (by decide) (by decide)) 1903 1903⟩)
(.leaf ⟨(.d 10 10 15),2768124653826881164,.step (.dUp 10 10 15 (by decide) (by decide)) 1906 1906⟩))
(.branch 2742
(.leaf ⟨(.d 9 10 12),2768124653826881164,.step (.dDown 9 10 12 (by decide) (by decide)) 2739 2739⟩)
(.branch 2743
(.leaf ⟨(.d 9 10 15),2768124653826881164,.step (.dDown 9 10 15 (by decide) (by decide)) 2740 2740⟩)
(.leaf ⟨(.d 8 10 12),2768124653826881164,.step (.dDown 8 10 12 (by decide) (by decide)) 2741 2741⟩))))
(.branch 2746
(.branch 2745
(.leaf ⟨(.d 8 10 15),2768124653826881164,.step (.dDown 8 10 15 (by decide) (by decide)) 2742 2742⟩)
(.leaf ⟨(.d 11 11 15),2873183830725104211,.step (.dUp 11 11 15 (by decide) (by decide)) 2026 2026⟩))
(.branch 2747
(.leaf ⟨(.d 12 12 15),3021922124970892808,.step (.dUp 12 12 15 (by decide) (by decide)) 2143 2143⟩)
(.branch 2748
(.leaf ⟨(.d 11 12 15),2731410490885396263,.step (.dUp 11 12 15 (by decide) (by decide)) 2134 2134⟩)
(.leaf ⟨(.d 13 13 15),8944310641383911535,.step (.dUp 13 13 15 (by decide) (by decide)) 2255 2255⟩)))))
def nodes1 (k:ℕ):Node 22:=
  if k< 2739 then ⟨coordOfIndex k,rawProfile1 (coordOfIndex k),.input⟩
  else newNodes1.get k
def outputPointers1:PointerTable:=
(.branch 1369
.identity
(.branch 2054
(.branch 1711
.identity
(.branch 1882
.identity
(.branch 1968
(.branch 1925
(.branch 1903
(.branch 1892
(.branch 1887
(.branch 1884
(.branch 1883
(.fixed 2743)
.identity)
(.branch 1885
.identity
(.branch 1886
(.fixed 2744)
.identity)))
.identity)
(.branch 1897
(.branch 1894
(.branch 1893
.identity
(.fixed 2741))
(.branch 1895
.identity
(.branch 1896
.identity
(.fixed 2742))))
.identity))
(.branch 1914
(.branch 1908
(.branch 1905
(.branch 1904
.identity
(.fixed 2739))
(.branch 1906
.identity
(.branch 1907
.identity
(.fixed 2740))))
.identity)
.identity))
.identity)
(.branch 2011
.identity
(.branch 2032
(.branch 2021
.identity
(.branch 2026
.identity
(.branch 2029
(.branch 2027
.identity
(.branch 2028
(.fixed 2745)
.identity))
.identity)))
.identity)))))
(.branch 2396
(.branch 2225
(.branch 2139
(.branch 2096
.identity
(.branch 2117
.identity
(.branch 2128
.identity
(.branch 2133
.identity
(.branch 2136
(.branch 2134
.identity
(.branch 2135
.identity
(.fixed 2747)))
.identity)))))
(.branch 2182
(.branch 2160
(.branch 2149
(.branch 2144
.identity
(.branch 2146
(.branch 2145
(.fixed 2746)
.identity)
.identity))
.identity)
.identity)
.identity))
(.branch 2310
(.branch 2267
(.branch 2246
.identity
(.branch 2256
.identity
(.branch 2261
(.branch 2258
(.branch 2257
(.fixed 2748)
.identity)
.identity)
.identity)))
.identity)
.identity))
.identity)))
def outputIndex1 (c:Coord 22):ℕ:=outputPointers1.get (flatIndex c)
def nodeCount1:ℕ:=2749
end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal


