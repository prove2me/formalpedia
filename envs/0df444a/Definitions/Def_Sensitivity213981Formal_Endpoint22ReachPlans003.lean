-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans003
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans003
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:43:11.403585+00:00
-- url     : https://prove2.me/theorems/c6a8c9b1-a56f-4943-89d4-a52a3e79da90
-- title:
--   Endpoint22 Reach Plans003 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans003 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan362`, `ThreeBoundEndpoint22Reachable.plan363`, `ThreeBoundEndpoint22Reachable.plan294`, `ThreeBoundEndpoint22Reachable.plan364`, `ThreeBoundEndpoint22Reachable.plan365`, `ThreeBoundEndpoint22Reachable.plan366`, `ThreeBoundEndpoint22Reachable.plan367`, `ThreeBoundEndpoint22Reachable.plan368`, `ThreeBoundEndpoint22Reachable.plan369`, `ThreeBoundEndpoint22Reachable.plan370`, `ThreeBoundEndpoint22Reachable.plan371`, `ThreeBoundEndpoint22Reachable.plan372`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans003.lean, lines 1–204.

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
def plan289 : Plan := .step choices56 bits109 plan43

def plan290 : Plan := .step choices56 bits109 plan44

def plan291 : Plan := .step choices56 bits93 plan46

def plan292 : Plan := .step choices56 bits93 plan47

def plan293 : Plan := .step choices56 bits93 plan48

def plan294 : Plan := .step choices56 bits92 plan49

def plan295 : Plan := .step choices56 bits93 plan50

def plan296 : Plan := .step choices56 bits93 plan51

def plan297 : Plan := .step choices57 bits110 plan44

def plan298 : Plan := .step choices57 bits94 plan47

def plan299 : Plan := .step choices57 bits94 plan48

def plan300 : Plan := .step choices57 bits94 plan50

def plan301 : Plan := .step choices57 bits94 plan51

def plan302 : Plan := .step choices58 bits94 plan48

def plan303 : Plan := .step choices58 bits94 plan51

def plan304 : Plan := .step choices59 bits136 plan52

def plan305 : Plan := .step choices59 bits137 plan53

def plan306 : Plan := .step choices59 bits137 plan54

def plan307 : Plan := .step choices59 bits137 plan55

def plan308 : Plan := .step choices59 bits136 plan56

def plan309 : Plan := .step choices59 bits137 plan57

def plan310 : Plan := .step choices59 bits137 plan58

def plan311 : Plan := .step choices60 bits138 plan53

def plan312 : Plan := .step choices60 bits138 plan54

def plan313 : Plan := .step choices60 bits138 plan55

def plan314 : Plan := .step choices60 bits138 plan57

def plan315 : Plan := .step choices60 bits138 plan58

def plan316 : Plan := .step choices61 bits138 plan54

def plan317 : Plan := .step choices61 bits138 plan55

def plan318 : Plan := .step choices61 bits138 plan58

def plan319 : Plan := .step choices62 bits138 plan55

def plan320 : Plan := .step choices63 bits137 plan53

def plan321 : Plan := .step choices63 bits137 plan54

def plan322 : Plan := .step choices63 bits137 plan55

def plan323 : Plan := .step choices63 bits136 plan56

def plan324 : Plan := .step choices63 bits137 plan57

def plan325 : Plan := .step choices63 bits137 plan58

def plan326 : Plan := .step choices64 bits138 plan54

def plan327 : Plan := .step choices64 bits138 plan55

def plan328 : Plan := .step choices64 bits138 plan57

def plan329 : Plan := .step choices64 bits138 plan58

def plan330 : Plan := .step choices65 bits138 plan55

def plan331 : Plan := .step choices65 bits138 plan58

def plan332 : Plan := .step choices67 bits53 plan60

def plan333 : Plan := .step choices68 bits53 plan59

def plan334 : Plan := .step choices68 bits54 plan60

def plan335 : Plan := .step choices69 bits55 plan60

def plan336 : Plan := .step choices71 bits70 plan64

def plan337 : Plan := .step choices71 bits70 plan65

def plan338 : Plan := .step choices71 bits70 plan67

def plan339 : Plan := .step choices72 bits86 plan61

def plan340 : Plan := .step choices72 bits87 plan62

def plan341 : Plan := .step choices72 bits72 plan63

def plan342 : Plan := .step choices72 bits74 plan64

def plan343 : Plan := .step choices72 bits74 plan65

def plan344 : Plan := .step choices72 bits72 plan66

def plan345 : Plan := .step choices72 bits74 plan67

def plan346 : Plan := .step choices73 bits88 plan62

def plan347 : Plan := .step choices73 bits75 plan64

def plan348 : Plan := .step choices73 bits75 plan65

def plan349 : Plan := .step choices73 bits75 plan67

def plan350 : Plan := .step choices74 bits71 plan62

def plan351 : Plan := .step choices75 bits73 plan62

def plan352 : Plan := .step choices78 bits71 plan62

def plan353 : Plan := .step choices79 bits73 plan62

def plan354 : Plan := .step choices83 bits124 plan68

def plan355 : Plan := .step choices83 bits125 plan69

def plan356 : Plan := .step choices83 bits112 plan70

def plan357 : Plan := .step choices83 bits113 plan71

def plan358 : Plan := .step choices83 bits113 plan72

def plan359 : Plan := .step choices83 bits112 plan73

def plan360 : Plan := .step choices83 bits113 plan74

def plan361 : Plan := .step choices84 bits126 plan69

def plan362 : Plan := .step choices84 bits115 plan71

def plan363 : Plan := .step choices84 bits115 plan72

def plan364 : Plan := .step choices84 bits115 plan74

def plan365 : Plan := .step choices85 bits111 plan69

def plan366 : Plan := .step choices85 bits95 plan71

def plan367 : Plan := .step choices85 bits95 plan72

def plan368 : Plan := .step choices85 bits95 plan74

def plan369 : Plan := .step choices86 bits114 plan69

def plan370 : Plan := .step choices86 bits96 plan70

def plan371 : Plan := .step choices86 bits97 plan71

def plan372 : Plan := .step choices86 bits97 plan72

def plan373 : Plan := .step choices86 bits96 plan73

def plan374 : Plan := .step choices86 bits97 plan74

def plan375 : Plan := .step choices87 bits98 plan71

def plan376 : Plan := .step choices87 bits98 plan72

def plan377 : Plan := .step choices87 bits98 plan74

def plan378 : Plan := .step choices88 bits98 plan72

def plan379 : Plan := .step choices89 bits111 plan69

def plan380 : Plan := .step choices89 bits95 plan71

def plan381 : Plan := .step choices89 bits95 plan72

def plan382 : Plan := .step choices89 bits95 plan74

def plan383 : Plan := .step choices90 bits114 plan69

def plan384 : Plan := .step choices90 bits97 plan71

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


