-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureData2
-- name    : Sensitivity213981Formal_Endpoint22ClosureData2
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:13:36.437245+00:00
-- url     : https://prove2.me/theorems/c9583079-ccb0-46e0-81ca-87a1d0dff565
-- title:
--   Endpoint22 Closure Data2 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Closure Data2 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Endpoint22.nodes2`, `ThreeBoundMinmaxNumeric.Endpoint22.outputPointers2`, `ThreeBoundMinmaxNumeric.Endpoint22.newNodes2`, `ThreeBoundMinmaxNumeric.Endpoint22.outputIndex2`, `ThreeBoundMinmaxNumeric.Endpoint22.nodeCount2`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ClosureData2.lean, lines 1–153.

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
def newNodes2:Table (Node 22):=
(.branch 2744
(.branch 2741
(.branch 2740
(.leaf ⟨(.d 12 12 14),156281336558105085538,.step (.dUp 12 12 14 (by decide) (by decide)) 2142 2142⟩)
(.leaf ⟨(.d 12 12 17),156281336558105085538,.step (.dUp 12 12 17 (by decide) (by decide)) 2145 2145⟩))
(.branch 2742
(.leaf ⟨(.d 11 12 14),156281336558105085538,.step (.dDown 11 12 14 (by decide) (by decide)) 2739 2739⟩)
(.branch 2743
(.leaf ⟨(.d 11 12 17),156281336558105085538,.step (.dDown 11 12 17 (by decide) (by decide)) 2740 2740⟩)
(.leaf ⟨(.d 10 12 14),156281336558105085538,.step (.dDown 10 12 14 (by decide) (by decide)) 2741 2741⟩))))
(.branch 2747
(.branch 2745
(.leaf ⟨(.d 10 12 17),156281336558105085538,.step (.dDown 10 12 17 (by decide) (by decide)) 2742 2742⟩)
(.branch 2746
(.leaf ⟨(.d 13 13 17),162203725074518104265,.step (.dUp 13 13 17 (by decide) (by decide)) 2257 2257⟩)
(.leaf ⟨(.d 14 14 17),170528926682734431955,.step (.dUp 14 14 17 (by decide) (by decide)) 2362 2362⟩)))
(.branch 2748
(.leaf ⟨(.d 13 14 17),154246077023671510570,.step (.dUp 13 14 17 (by decide) (by decide)) 2355 2355⟩)
(.branch 2749
(.leaf ⟨(.d 15 15 17),504770282732958998715,.step (.dUp 15 15 17 (by decide) (by decide)) 2458 2458⟩)
(.leaf ⟨(.d 13 15 17),4912750682261376137,.step (.dUp 13 15 17 (by decide) (by decide)) 2446 2446⟩)))))
def nodes2 (k:ℕ):Node 22:=
  if k< 2739 then ⟨coordOfIndex k,rawProfile2 (coordOfIndex k),.input⟩
  else newNodes2.get k
def outputPointers2:PointerTable:=
(.branch 1369
.identity
(.branch 2054
.identity
(.branch 2396
(.branch 2225
(.branch 2139
(.branch 2096
.identity
(.branch 2117
.identity
(.branch 2128
(.branch 2122
.identity
(.branch 2125
.identity
(.branch 2126
(.fixed 2743)
.identity)))
(.branch 2133
(.branch 2130
(.branch 2129
(.fixed 2744)
.identity)
.identity)
(.branch 2136
(.branch 2134
.identity
(.branch 2135
(.fixed 2741)
.identity))
(.branch 2137
.identity
(.branch 2138
(.fixed 2742)
.identity)))))))
(.branch 2182
(.branch 2160
(.branch 2149
(.branch 2144
(.branch 2141
.identity
(.branch 2142
.identity
(.branch 2143
.identity
(.fixed 2739))))
(.branch 2146
.identity
(.branch 2147
(.fixed 2740)
.identity)))
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
.identity
(.branch 2259
(.fixed 2745)
.identity))
.identity)))
.identity)
(.branch 2353
.identity
(.branch 2374
(.branch 2363
(.branch 2358
(.branch 2355
.identity
(.branch 2356
.identity
(.branch 2357
(.fixed 2747)
.identity)))
.identity)
(.branch 2368
(.branch 2365
(.branch 2364
(.fixed 2746)
.identity)
.identity)
.identity))
.identity))))
(.branch 2567
(.branch 2481
(.branch 2438
.identity
(.branch 2459
(.branch 2448
(.branch 2443
.identity
(.branch 2445
.identity
(.branch 2446
.identity
(.branch 2447
.identity
(.fixed 2749)))))
.identity)
(.branch 2470
(.branch 2464
(.branch 2461
(.branch 2460
(.fixed 2748)
.identity)
.identity)
.identity)
.identity)))
.identity)
.identity))))
def outputIndex2 (c:Coord 22):ℕ:=outputPointers2.get (flatIndex c)
def nodeCount2:ℕ:=2750
end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal


