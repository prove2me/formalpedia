-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans000
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:42:19.371651+00:00
-- url     : https://prove2.me/theorems/6ca105af-0a49-4899-b97d-ff8c1ff0ee0e
-- title:
--   Endpoint22 Reach Plans000 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans000 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan78`, `ThreeBoundEndpoint22Reachable.plan79`, `ThreeBoundEndpoint22Reachable.plan80`, `ThreeBoundEndpoint22Reachable.plan7`, `ThreeBoundEndpoint22Reachable.plan81`, `ThreeBoundEndpoint22Reachable.plan82`, `ThreeBoundEndpoint22Reachable.plan83`, `ThreeBoundEndpoint22Reachable.plan84`, `ThreeBoundEndpoint22Reachable.plan85`, `ThreeBoundEndpoint22Reachable.plan86`, `ThreeBoundEndpoint22Reachable.plan87`, `ThreeBoundEndpoint22Reachable.plan88`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans000.lean, lines 1–202.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
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
def plan1 : Plan := .step choices0 bits0 plan0

def plan2 : Plan := .step choices1 bits0 plan0

def plan3 : Plan := .step choices2 bits0 plan0

def plan4 : Plan := .step choices3 bits0 plan0

def plan5 : Plan := .step choices4 bits0 plan0

def plan6 : Plan := .step choices5 bits0 plan0

def plan7 : Plan := .step choices6 bits0 plan0

def plan8 : Plan := .step choices7 bits0 plan0

def plan9 : Plan := .step choices8 bits0 plan0

def plan10 : Plan := .step choices9 bits0 plan0

def plan11 : Plan := .step choices10 bits0 plan0

def plan12 : Plan := .step choices12 bits5 plan0

def plan13 : Plan := .step choices13 bits5 plan0

def plan14 : Plan := .step choices14 bits5 plan0

def plan15 : Plan := .step choices17 bits8 plan0

def plan16 : Plan := .step choices18 bits8 plan0

def plan17 : Plan := .step choices19 bits1 plan0

def plan18 : Plan := .step choices20 bits1 plan0

def plan19 : Plan := .step choices21 bits1 plan0

def plan20 : Plan := .step choices22 bits1 plan0

def plan21 : Plan := .step choices23 bits1 plan0

def plan22 : Plan := .step choices24 bits1 plan0

def plan23 : Plan := .step choices25 bits1 plan0

def plan24 : Plan := .step choices26 bits13 plan0

def plan25 : Plan := .step choices27 bits13 plan0

def plan26 : Plan := .step choices28 bits13 plan0

def plan27 : Plan := .step choices29 bits13 plan0

def plan28 : Plan := .step choices30 bits13 plan0

def plan29 : Plan := .step choices31 bits13 plan0

def plan30 : Plan := .step choices32 bits13 plan0

def plan31 : Plan := .step choices34 bits5 plan0

def plan32 : Plan := .step choices35 bits6 plan0

def plan33 : Plan := .step choices36 bits6 plan0

def plan34 : Plan := .step choices39 bits9 plan0

def plan35 : Plan := .step choices40 bits9 plan0

def plan36 : Plan := .step choices41 bits1 plan0

def plan37 : Plan := .step choices42 bits2 plan0

def plan38 : Plan := .step choices43 bits2 plan0

def plan39 : Plan := .step choices44 bits2 plan0

def plan40 : Plan := .step choices45 bits1 plan0

def plan41 : Plan := .step choices46 bits2 plan0

def plan42 : Plan := .step choices47 bits2 plan0

def plan43 : Plan := .step choices50 bits21 plan0

def plan44 : Plan := .step choices51 bits21 plan0

def plan45 : Plan := .step choices52 bits14 plan0

def plan46 : Plan := .step choices53 bits15 plan0

def plan47 : Plan := .step choices54 bits15 plan0

def plan48 : Plan := .step choices55 bits15 plan0

def plan49 : Plan := .step choices56 bits14 plan0

def plan50 : Plan := .step choices57 bits15 plan0

def plan51 : Plan := .step choices58 bits15 plan0

def plan52 : Plan := .step choices59 bits26 plan0

def plan53 : Plan := .step choices60 bits27 plan0

def plan54 : Plan := .step choices61 bits27 plan0

def plan55 : Plan := .step choices62 bits27 plan0

def plan56 : Plan := .step choices63 bits26 plan0

def plan57 : Plan := .step choices64 bits27 plan0

def plan58 : Plan := .step choices65 bits27 plan0

def plan59 : Plan := .step choices68 bits6 plan0

def plan60 : Plan := .step choices69 bits7 plan0

def plan61 : Plan := .step choices72 bits10 plan0

def plan62 : Plan := .step choices73 bits11 plan0

def plan63 : Plan := .step choices75 bits2 plan0

def plan64 : Plan := .step choices76 bits3 plan0

def plan65 : Plan := .step choices77 bits3 plan0

def plan66 : Plan := .step choices79 bits2 plan0

def plan67 : Plan := .step choices80 bits3 plan0

def plan68 : Plan := .step choices83 bits22 plan0

def plan69 : Plan := .step choices84 bits23 plan0

def plan70 : Plan := .step choices86 bits16 plan0

def plan71 : Plan := .step choices87 bits17 plan0

def plan72 : Plan := .step choices88 bits17 plan0

def plan73 : Plan := .step choices90 bits16 plan0

def plan74 : Plan := .step choices91 bits17 plan0

def plan75 : Plan := .step choices95 bits36 plan0

def plan76 : Plan := .step choices97 bits28 plan0

def plan77 : Plan := .step choices98 bits29 plan0

def plan78 : Plan := .step choices99 bits29 plan0

def plan79 : Plan := .step choices101 bits28 plan0

def plan80 : Plan := .step choices102 bits29 plan0

def plan81 : Plan := .step choices104 bits39 plan0

def plan82 : Plan := .step choices105 bits40 plan0

def plan83 : Plan := .step choices106 bits40 plan0

def plan84 : Plan := .step choices108 bits39 plan0

def plan85 : Plan := .step choices109 bits40 plan0

def plan86 : Plan := .step choices112 bits6 plan0

def plan87 : Plan := .step choices113 bits7 plan0

def plan88 : Plan := .step choices117 bits12 plan0

def plan89 : Plan := .step choices119 bits2 plan0

def plan90 : Plan := .step choices120 bits3 plan0

def plan91 : Plan := .step choices121 bits4 plan0

def plan92 : Plan := .step choices123 bits2 plan0

def plan93 : Plan := .step choices124 bits3 plan0

def plan94 : Plan := .step choices128 bits24 plan0

def plan95 : Plan := .step choices130 bits16 plan0

def plan96 : Plan := .step choices131 bits18 plan0

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


