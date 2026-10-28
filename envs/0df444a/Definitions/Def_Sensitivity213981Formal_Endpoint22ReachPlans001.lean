-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans001
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:43:16.169817+00:00
-- url     : https://prove2.me/theorems/9bf59f11-0950-4fc0-b7d9-7c4626a5164b
-- title:
--   Endpoint22 Reach Plans001 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans001 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan171`, `ThreeBoundEndpoint22Reachable.plan102`, `ThreeBoundEndpoint22Reachable.plan172`, `ThreeBoundEndpoint22Reachable.plan173`, `ThreeBoundEndpoint22Reachable.plan174`, `ThreeBoundEndpoint22Reachable.plan175`, `ThreeBoundEndpoint22Reachable.plan176`, `ThreeBoundEndpoint22Reachable.plan177`, `ThreeBoundEndpoint22Reachable.plan178`, `ThreeBoundEndpoint22Reachable.plan179`, `ThreeBoundEndpoint22Reachable.plan180`, `ThreeBoundEndpoint22Reachable.plan181`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans001.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
def plan97 : Plan := .step choices132 bits19 plan0

def plan98 : Plan := .step choices134 bits16 plan0

def plan99 : Plan := .step choices135 bits18 plan0

def plan100 : Plan := .step choices139 bits37 plan0

def plan101 : Plan := .step choices141 bits30 plan0

def plan102 : Plan := .step choices142 bits31 plan0

def plan103 : Plan := .step choices143 bits32 plan0

def plan104 : Plan := .step choices145 bits30 plan0

def plan105 : Plan := .step choices146 bits31 plan0

def plan106 : Plan := .step choices150 bits49 plan0

def plan107 : Plan := .step choices152 bits41 plan0

def plan108 : Plan := .step choices153 bits42 plan0

def plan109 : Plan := .step choices154 bits43 plan0

def plan110 : Plan := .step choices156 bits41 plan0

def plan111 : Plan := .step choices157 bits42 plan0

def plan112 : Plan := .step choices159 bits56 plan0

def plan113 : Plan := .step choices160 bits57 plan0

def plan114 : Plan := .step choices161 bits58 plan0

def plan115 : Plan := .step choices163 bits56 plan0

def plan116 : Plan := .step choices164 bits57 plan0

def plan117 : Plan := .step choices168 bits7 plan0

def plan118 : Plan := .step choices172 bits12 plan0

def plan119 : Plan := .step choices175 bits3 plan0

def plan120 : Plan := .step choices176 bits4 plan0

def plan121 : Plan := .step choices179 bits3 plan0

def plan122 : Plan := .step choices183 bits25 plan0

def plan123 : Plan := .step choices186 bits18 plan0

def plan124 : Plan := .step choices187 bits20 plan0

def plan125 : Plan := .step choices190 bits18 plan0

def plan126 : Plan := .step choices194 bits38 plan0

def plan127 : Plan := .step choices197 bits33 plan0

def plan128 : Plan := .step choices198 bits34 plan0

def plan129 : Plan := .step choices201 bits33 plan0

def plan130 : Plan := .step choices208 bits44 plan0

def plan131 : Plan := .step choices209 bits45 plan0

def plan132 : Plan := .step choices212 bits44 plan0

def plan133 : Plan := .step choices219 bits59 plan0

def plan134 : Plan := .step choices220 bits60 plan0

def plan135 : Plan := .step choices223 bits59 plan0

def plan136 : Plan := .step choices226 bits80 plan0

def plan137 : Plan := .step choices227 bits81 plan0

def plan138 : Plan := .step choices230 bits80 plan0

def plan139 : Plan := .step choices231 bits7 plan0

def plan140 : Plan := .step choices234 bits3 plan0

def plan141 : Plan := .step choices235 bits4 plan0

def plan142 : Plan := .step choices236 bits3 plan0

def plan143 : Plan := .step choices241 bits18 plan0

def plan144 : Plan := .step choices242 bits20 plan0

def plan145 : Plan := .step choices244 bits18 plan0

def plan146 : Plan := .step choices251 bits33 plan0

def plan147 : Plan := .step choices252 bits35 plan0

def plan148 : Plan := .step choices255 bits33 plan0

def plan149 : Plan := .step choices262 bits46 plan0

def plan150 : Plan := .step choices263 bits47 plan0

def plan151 : Plan := .step choices266 bits46 plan0

def plan152 : Plan := .step choices273 bits61 plan0

def plan153 : Plan := .step choices274 bits62 plan0

def plan154 : Plan := .step choices277 bits61 plan0

def plan155 : Plan := .step choices284 bits82 plan0

def plan156 : Plan := .step choices285 bits83 plan0

def plan157 : Plan := .step choices288 bits82 plan0

def plan158 : Plan := .step choices291 bits106 plan0

def plan159 : Plan := .step choices292 bits107 plan0

def plan160 : Plan := .step choices295 bits106 plan0

def plan161 : Plan := .step choices297 bits48 plan0

def plan162 : Plan := .step choices301 bits63 plan0

def plan163 : Plan := .step choices308 bits84 plan0

def plan164 : Plan := .step choices318 bits108 plan0

def plan165 : Plan := .step choices325 bits123 plan0

def plan166 : Plan := .step choices329 bits153 plan0

def plan167 : Plan := .step choices11 bits50 plan12

def plan168 : Plan := .step choices11 bits50 plan13

def plan169 : Plan := .step choices11 bits50 plan14

def plan170 : Plan := .step choices12 bits51 plan12

def plan171 : Plan := .step choices12 bits51 plan13

def plan172 : Plan := .step choices12 bits51 plan14

def plan173 : Plan := .step choices13 bits51 plan13

def plan174 : Plan := .step choices13 bits51 plan14

def plan175 : Plan := .step choices14 bits51 plan14

def plan176 : Plan := .step choices15 bits64 plan17

def plan177 : Plan := .step choices15 bits64 plan18

def plan178 : Plan := .step choices15 bits64 plan19

def plan179 : Plan := .step choices15 bits64 plan20

def plan180 : Plan := .step choices15 bits64 plan21

def plan181 : Plan := .step choices15 bits64 plan22

def plan182 : Plan := .step choices15 bits64 plan23

def plan183 : Plan := .step choices16 bits65 plan17

def plan184 : Plan := .step choices16 bits65 plan18

def plan185 : Plan := .step choices16 bits65 plan19

def plan186 : Plan := .step choices16 bits65 plan20

def plan187 : Plan := .step choices16 bits65 plan21

def plan188 : Plan := .step choices16 bits65 plan22

def plan189 : Plan := .step choices16 bits65 plan23

def plan190 : Plan := .step choices17 bits65 plan18

def plan191 : Plan := .step choices17 bits65 plan19

def plan192 : Plan := .step choices17 bits65 plan20

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


