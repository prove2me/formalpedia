-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans004
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:44:21.542522+00:00
-- url     : https://prove2.me/theorems/3508f2f3-fcfb-4819-932c-dcf71087f849
-- title:
--   Endpoint22 Reach Plans004 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans004 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan457`, `ThreeBoundEndpoint22Reachable.plan458`, `ThreeBoundEndpoint22Reachable.plan459`, `ThreeBoundEndpoint22Reachable.plan460`, `ThreeBoundEndpoint22Reachable.plan461`, `ThreeBoundEndpoint22Reachable.plan390`, `ThreeBoundEndpoint22Reachable.plan462`, `ThreeBoundEndpoint22Reachable.plan463`, `ThreeBoundEndpoint22Reachable.plan464`, `ThreeBoundEndpoint22Reachable.plan465`, `ThreeBoundEndpoint22Reachable.plan466`, `ThreeBoundEndpoint22Reachable.plan467`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans004.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
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
def plan385 : Plan := .step choices90 bits97 plan72

def plan386 : Plan := .step choices90 bits96 plan73

def plan387 : Plan := .step choices90 bits97 plan74

def plan388 : Plan := .step choices91 bits98 plan72

def plan389 : Plan := .step choices91 bits98 plan74

def plan390 : Plan := .step choices94 bits154 plan76

def plan391 : Plan := .step choices94 bits155 plan77

def plan392 : Plan := .step choices94 bits155 plan78

def plan393 : Plan := .step choices94 bits154 plan79

def plan394 : Plan := .step choices94 bits155 plan80

def plan395 : Plan := .step choices95 bits158 plan77

def plan396 : Plan := .step choices95 bits158 plan78

def plan397 : Plan := .step choices95 bits158 plan80

def plan398 : Plan := .step choices96 bits156 plan75

def plan399 : Plan := .step choices96 bits139 plan77

def plan400 : Plan := .step choices96 bits139 plan78

def plan401 : Plan := .step choices96 bits139 plan80

def plan402 : Plan := .step choices97 bits157 plan75

def plan403 : Plan := .step choices97 bits140 plan76

def plan404 : Plan := .step choices97 bits141 plan77

def plan405 : Plan := .step choices97 bits141 plan78

def plan406 : Plan := .step choices97 bits140 plan79

def plan407 : Plan := .step choices97 bits141 plan80

def plan408 : Plan := .step choices98 bits142 plan77

def plan409 : Plan := .step choices98 bits142 plan78

def plan410 : Plan := .step choices98 bits142 plan80

def plan411 : Plan := .step choices99 bits142 plan78

def plan412 : Plan := .step choices100 bits156 plan75

def plan413 : Plan := .step choices100 bits139 plan77

def plan414 : Plan := .step choices100 bits139 plan78

def plan415 : Plan := .step choices100 bits139 plan80

def plan416 : Plan := .step choices101 bits157 plan75

def plan417 : Plan := .step choices101 bits141 plan77

def plan418 : Plan := .step choices101 bits141 plan78

def plan419 : Plan := .step choices101 bits140 plan79

def plan420 : Plan := .step choices101 bits141 plan80

def plan421 : Plan := .step choices102 bits142 plan78

def plan422 : Plan := .step choices102 bits142 plan80

def plan423 : Plan := .step choices103 bits198 plan82

def plan424 : Plan := .step choices103 bits198 plan83

def plan425 : Plan := .step choices103 bits198 plan85

def plan426 : Plan := .step choices104 bits198 plan81

def plan427 : Plan := .step choices104 bits199 plan82

def plan428 : Plan := .step choices104 bits199 plan83

def plan429 : Plan := .step choices104 bits198 plan84

def plan430 : Plan := .step choices104 bits199 plan85

def plan431 : Plan := .step choices105 bits200 plan82

def plan432 : Plan := .step choices105 bits200 plan83

def plan433 : Plan := .step choices105 bits200 plan85

def plan434 : Plan := .step choices106 bits200 plan83

def plan435 : Plan := .step choices107 bits198 plan82

def plan436 : Plan := .step choices107 bits198 plan83

def plan437 : Plan := .step choices107 bits198 plan85

def plan438 : Plan := .step choices108 bits199 plan82

def plan439 : Plan := .step choices108 bits199 plan83

def plan440 : Plan := .step choices108 bits198 plan84

def plan441 : Plan := .step choices108 bits199 plan85

def plan442 : Plan := .step choices109 bits200 plan83

def plan443 : Plan := .step choices109 bits200 plan85

def plan444 : Plan := .step choices112 bits53 plan86

def plan445 : Plan := .step choices112 bits54 plan87

def plan446 : Plan := .step choices113 bits55 plan87

def plan447 : Plan := .step choices116 bits89 plan88

def plan448 : Plan := .step choices116 bits72 plan89

def plan449 : Plan := .step choices116 bits74 plan90

def plan450 : Plan := .step choices116 bits76 plan91

def plan451 : Plan := .step choices116 bits72 plan92

def plan452 : Plan := .step choices116 bits74 plan93

def plan453 : Plan := .step choices117 bits90 plan88

def plan454 : Plan := .step choices117 bits78 plan90

def plan455 : Plan := .step choices117 bits79 plan91

def plan456 : Plan := .step choices117 bits78 plan93

def plan457 : Plan := .step choices119 bits77 plan88

def plan458 : Plan := .step choices123 bits77 plan88

def plan459 : Plan := .step choices127 bits117 plan96

def plan460 : Plan := .step choices127 bits118 plan97

def plan461 : Plan := .step choices127 bits117 plan99

def plan462 : Plan := .step choices128 bits129 plan94

def plan463 : Plan := .step choices128 bits119 plan96

def plan464 : Plan := .step choices128 bits120 plan97

def plan465 : Plan := .step choices128 bits119 plan99

def plan466 : Plan := .step choices130 bits116 plan94

def plan467 : Plan := .step choices130 bits96 plan95

def plan468 : Plan := .step choices130 bits99 plan96

def plan469 : Plan := .step choices130 bits100 plan97

def plan470 : Plan := .step choices130 bits96 plan98

def plan471 : Plan := .step choices130 bits99 plan99

def plan472 : Plan := .step choices131 bits101 plan96

def plan473 : Plan := .step choices131 bits102 plan97

def plan474 : Plan := .step choices131 bits101 plan99

def plan475 : Plan := .step choices132 bits103 plan97

def plan476 : Plan := .step choices134 bits116 plan94

def plan477 : Plan := .step choices134 bits99 plan96

def plan478 : Plan := .step choices134 bits100 plan97

def plan479 : Plan := .step choices134 bits96 plan98

def plan480 : Plan := .step choices134 bits99 plan99

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


