-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureData0
-- name    : Sensitivity213981Formal_Endpoint22ClosureData0
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:15:10.267758+00:00
-- url     : https://prove2.me/theorems/c8966f5d-d633-4153-a652-21f77516c885
-- title:
--   Endpoint22 Closure Data0 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Closure Data0 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Endpoint22.nodes0`, `ThreeBoundMinmaxNumeric.Endpoint22.outputPointers0`, `ThreeBoundMinmaxNumeric.Endpoint22.newNodes0`, `ThreeBoundMinmaxNumeric.Endpoint22.outputIndex0`, `ThreeBoundMinmaxNumeric.Endpoint22.nodeCount0`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ClosureData0.lean, lines 1–157.

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
def newNodes0:Table (Node 22):=
(.branch 2745
(.branch 2742
(.branch 2740
(.leaf ⟨(.d 9 9 11),49131381935961194,.step (.dUp 9 9 11 (by decide) (by decide)) 1781 1781⟩)
(.branch 2741
(.leaf ⟨(.d 9 9 12),49131381935961194,.step (.dUp 9 9 12 (by decide) (by decide)) 2739 2739⟩)
(.leaf ⟨(.d 9 9 14),49131381935961194,.step (.dUp 9 9 14 (by decide) (by decide)) 1784 1784⟩)))
(.branch 2743
(.leaf ⟨(.d 8 9 11),49131381935961194,.step (.dDown 8 9 11 (by decide) (by decide)) 2739 2739⟩)
(.branch 2744
(.leaf ⟨(.d 8 9 12),49131381935961194,.step (.dDown 8 9 12 (by decide) (by decide)) 2740 2740⟩)
(.leaf ⟨(.d 8 9 14),49131381935961194,.step (.dDown 8 9 14 (by decide) (by decide)) 2741 2741⟩))))
(.branch 2748
(.branch 2746
(.leaf ⟨(.d 10 10 14),50992917462858289,.step (.dUp 10 10 14 (by decide) (by decide)) 1905 1905⟩)
(.branch 2747
(.leaf ⟨(.d 11 11 14),53564613323890930,.step (.dUp 11 11 14 (by decide) (by decide)) 2025 2025⟩)
(.leaf ⟨(.d 10 11 14),50900890784513969,.step (.dUp 10 11 14 (by decide) (by decide)) 2015 2015⟩)))
(.branch 2749
(.leaf ⟨(.d 12 12 14),53627300001453076,.step (.dUp 12 12 14 (by decide) (by decide)) 2142 2142⟩)
(.branch 2750
(.leaf ⟨(.d 11 12 14),53314058359364884,.step (.dUp 11 12 14 (by decide) (by decide)) 2133 2133⟩)
(.leaf ⟨(.d 10 12 14),48481608315254404,.step (.dUp 10 12 14 (by decide) (by decide)) 2124 2124⟩)))))
def nodes0 (k:ℕ):Node 22:=
  if k< 2739 then ⟨coordOfIndex k,rawProfile0 (coordOfIndex k),.input⟩
  else newNodes0.get k
def outputPointers0:PointerTable:=
(.branch 1369
.identity
(.branch 2054
(.branch 1711
.identity
(.branch 1882
(.branch 1796
(.branch 1753
.identity
(.branch 1774
(.branch 1763
.identity
(.branch 1768
.identity
(.branch 1771
(.branch 1769
.identity
(.branch 1770
.identity
(.fixed 2742)))
(.branch 1772
(.fixed 2743)
(.branch 1773
.identity
(.fixed 2744))))))
(.branch 1785
(.branch 1779
.identity
(.branch 1782
.identity
(.branch 1783
(.fixed 2739)
(.branch 1784
(.fixed 2740)
.identity))))
(.branch 1790
(.branch 1787
(.branch 1786
(.fixed 2741)
.identity)
.identity)
.identity))))
.identity)
(.branch 1968
(.branch 1925
(.branch 1903
.identity
(.branch 1914
(.branch 1908
(.branch 1905
.identity
(.branch 1906
.identity
(.branch 1907
(.fixed 2745)
.identity)))
.identity)
.identity))
.identity)
(.branch 2011
.identity
(.branch 2032
(.branch 2021
(.branch 2016
.identity
(.branch 2018
(.branch 2017
(.fixed 2747)
.identity)
.identity))
(.branch 2026
.identity
(.branch 2029
(.branch 2027
(.fixed 2746)
.identity)
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
(.branch 2122
.identity
(.branch 2125
.identity
(.branch 2126
(.fixed 2750)
.identity)))
(.branch 2133
.identity
(.branch 2136
(.branch 2134
.identity
(.branch 2135
(.fixed 2749)
.identity))
.identity)))))
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
(.fixed 2748))))
.identity)
.identity)
.identity)
.identity))
.identity)
.identity)))
def outputIndex0 (c:Coord 22):ℕ:=outputPointers0.get (flatIndex c)
def nodeCount0:ℕ:=2751
end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal


