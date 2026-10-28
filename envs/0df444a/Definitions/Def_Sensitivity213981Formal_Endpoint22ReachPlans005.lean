-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans005
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:44:23.388694+00:00
-- url     : https://prove2.me/theorems/510b3b38-7684-4229-b29c-3f0d82539cea
-- title:
--   Endpoint22 Reach Plans005 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans005 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan552`, `ThreeBoundEndpoint22Reachable.plan553`, `ThreeBoundEndpoint22Reachable.plan554`, `ThreeBoundEndpoint22Reachable.plan555`, `ThreeBoundEndpoint22Reachable.plan556`, `ThreeBoundEndpoint22Reachable.plan486`, `ThreeBoundEndpoint22Reachable.plan557`, `ThreeBoundEndpoint22Reachable.plan558`, `ThreeBoundEndpoint22Reachable.plan559`, `ThreeBoundEndpoint22Reachable.plan560`, `ThreeBoundEndpoint22Reachable.plan561`, `ThreeBoundEndpoint22Reachable.plan562`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans005.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
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
def plan481 : Plan := .step choices135 bits102 plan97

def plan482 : Plan := .step choices135 bits101 plan99

def plan483 : Plan := .step choices138 bits159 plan103

def plan484 : Plan := .step choices139 bits175 plan100

def plan485 : Plan := .step choices139 bits161 plan102

def plan486 : Plan := .step choices139 bits162 plan103

def plan487 : Plan := .step choices139 bits161 plan105

def plan488 : Plan := .step choices141 bits160 plan100

def plan489 : Plan := .step choices141 bits143 plan101

def plan490 : Plan := .step choices141 bits144 plan102

def plan491 : Plan := .step choices141 bits145 plan103

def plan492 : Plan := .step choices141 bits143 plan104

def plan493 : Plan := .step choices141 bits144 plan105

def plan494 : Plan := .step choices142 bits145 plan102

def plan495 : Plan := .step choices142 bits146 plan103

def plan496 : Plan := .step choices142 bits145 plan105

def plan497 : Plan := .step choices143 bits147 plan103

def plan498 : Plan := .step choices145 bits160 plan100

def plan499 : Plan := .step choices145 bits144 plan102

def plan500 : Plan := .step choices145 bits145 plan103

def plan501 : Plan := .step choices145 bits143 plan104

def plan502 : Plan := .step choices145 bits144 plan105

def plan503 : Plan := .step choices146 bits146 plan103

def plan504 : Plan := .step choices146 bits145 plan105

def plan505 : Plan := .step choices150 bits222 plan108

def plan506 : Plan := .step choices150 bits223 plan109

def plan507 : Plan := .step choices150 bits222 plan111

def plan508 : Plan := .step choices152 bits221 plan106

def plan509 : Plan := .step choices152 bits201 plan107

def plan510 : Plan := .step choices152 bits202 plan108

def plan511 : Plan := .step choices152 bits203 plan109

def plan512 : Plan := .step choices152 bits201 plan110

def plan513 : Plan := .step choices152 bits202 plan111

def plan514 : Plan := .step choices153 bits204 plan108

def plan515 : Plan := .step choices153 bits205 plan109

def plan516 : Plan := .step choices153 bits204 plan111

def plan517 : Plan := .step choices154 bits206 plan109

def plan518 : Plan := .step choices156 bits221 plan106

def plan519 : Plan := .step choices156 bits202 plan108

def plan520 : Plan := .step choices156 bits203 plan109

def plan521 : Plan := .step choices156 bits201 plan110

def plan522 : Plan := .step choices156 bits202 plan111

def plan523 : Plan := .step choices157 bits205 plan109

def plan524 : Plan := .step choices157 bits204 plan111

def plan525 : Plan := .step choices159 bits274 plan112

def plan526 : Plan := .step choices159 bits275 plan113

def plan527 : Plan := .step choices159 bits276 plan114

def plan528 : Plan := .step choices159 bits274 plan115

def plan529 : Plan := .step choices159 bits275 plan116

def plan530 : Plan := .step choices160 bits276 plan113

def plan531 : Plan := .step choices160 bits277 plan114

def plan532 : Plan := .step choices160 bits276 plan116

def plan533 : Plan := .step choices161 bits278 plan114

def plan534 : Plan := .step choices163 bits275 plan113

def plan535 : Plan := .step choices163 bits276 plan114

def plan536 : Plan := .step choices163 bits274 plan115

def plan537 : Plan := .step choices163 bits275 plan116

def plan538 : Plan := .step choices164 bits277 plan114

def plan539 : Plan := .step choices164 bits276 plan116

def plan540 : Plan := .step choices168 bits55 plan117

def plan541 : Plan := .step choices172 bits90 plan118

def plan542 : Plan := .step choices172 bits78 plan119

def plan543 : Plan := .step choices172 bits79 plan120

def plan544 : Plan := .step choices172 bits78 plan121

def plan545 : Plan := .step choices183 bits132 plan122

def plan546 : Plan := .step choices183 bits121 plan123

def plan547 : Plan := .step choices183 bits122 plan124

def plan548 : Plan := .step choices183 bits121 plan125

def plan549 : Plan := .step choices186 bits101 plan123

def plan550 : Plan := .step choices186 bits104 plan124

def plan551 : Plan := .step choices186 bits101 plan125

def plan552 : Plan := .step choices187 bits105 plan124

def plan553 : Plan := .step choices190 bits104 plan124

def plan554 : Plan := .step choices190 bits101 plan125

def plan555 : Plan := .step choices194 bits184 plan126

def plan556 : Plan := .step choices194 bits163 plan127

def plan557 : Plan := .step choices194 bits164 plan128

def plan558 : Plan := .step choices194 bits163 plan129

def plan559 : Plan := .step choices197 bits148 plan127

def plan560 : Plan := .step choices197 bits149 plan128

def plan561 : Plan := .step choices197 bits148 plan129

def plan562 : Plan := .step choices198 bits150 plan128

def plan563 : Plan := .step choices201 bits149 plan128

def plan564 : Plan := .step choices201 bits148 plan129

def plan565 : Plan := .step choices205 bits224 plan130

def plan566 : Plan := .step choices205 bits225 plan131

def plan567 : Plan := .step choices205 bits224 plan132

def plan568 : Plan := .step choices208 bits207 plan130

def plan569 : Plan := .step choices208 bits208 plan131

def plan570 : Plan := .step choices208 bits207 plan132

def plan571 : Plan := .step choices209 bits209 plan131

def plan572 : Plan := .step choices212 bits208 plan131

def plan573 : Plan := .step choices212 bits207 plan132

def plan574 : Plan := .step choices216 bits305 plan134

def plan575 : Plan := .step choices219 bits279 plan133

def plan576 : Plan := .step choices219 bits280 plan134

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


