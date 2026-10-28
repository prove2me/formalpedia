-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks002
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks002
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:14.478992+00:00
-- url     : https://prove2.me/theorems/c5e5b436-6636-427a-867f-05e39a2ca9e8
-- title:
--   Endpoint22 Reach Checks002 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks002 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t4_372jobs`, `ThreeBoundEndpoint22Reachable.t4_373root`, `ThreeBoundEndpoint22Reachable.t4_373jobs0`, `ThreeBoundEndpoint22Reachable.t4_373jobs`, `ThreeBoundEndpoint22Reachable.t4_374root`, `ThreeBoundEndpoint22Reachable.t4_374jobs0`, `ThreeBoundEndpoint22Reachable.t4_374jobs`, `ThreeBoundEndpoint22Reachable.t4_375root`, `ThreeBoundEndpoint22Reachable.t4_375jobs0`, `ThreeBoundEndpoint22Reachable.t4_375jobs`, `ThreeBoundEndpoint22Reachable.t4_360root`, `ThreeBoundEndpoint22Reachable.t4_376root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks002.lean, lines 1–685.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans018
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans020
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans022
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
open ThreeBoundEndpoint22Packed (tree)

def t4_359root : Job := ⟨plan1941,[],none,⟨6,1,0⟩⟩
def t4_359jobs0 : List Job := [⟨plan1941,[],none,⟨6,1,0⟩⟩]

def t4_359jobs : List Job := t4_359jobs0




def t4_360root : Job := ⟨plan1942,[],none,⟨6,1,0⟩⟩
def t4_360jobs0 : List Job := [⟨plan1942,[],none,⟨6,1,0⟩⟩]

def t4_360jobs : List Job := t4_360jobs0




def t4_361root : Job := ⟨plan1943,[],none,⟨6,1,0⟩⟩
def t4_361jobs0 : List Job := [⟨plan1943,[],none,⟨6,1,0⟩⟩]

def t4_361jobs : List Job := t4_361jobs0




def t4_362root : Job := ⟨plan1944,[],none,⟨6,1,0⟩⟩
def t4_362jobs0 : List Job := [⟨plan1944,[],none,⟨6,1,0⟩⟩]

def t4_362jobs : List Job := t4_362jobs0




def t4_363root : Job := ⟨plan1785,[],none,⟨6,0,0⟩⟩
def t4_363jobs0 : List Job := [⟨plan1785,[],none,⟨6,0,0⟩⟩]

def t4_363jobs : List Job := t4_363jobs0




def t4_364root : Job := ⟨plan1945,[],none,⟨6,1,0⟩⟩
def t4_364jobs0 : List Job := [⟨plan1945,[],none,⟨6,1,0⟩⟩]

def t4_364jobs : List Job := t4_364jobs0




def t4_365root : Job := ⟨plan1946,[],none,⟨6,1,0⟩⟩
def t4_365jobs0 : List Job := [⟨plan1946,[],none,⟨6,1,0⟩⟩]

def t4_365jobs : List Job := t4_365jobs0




def t4_366root : Job := ⟨plan1947,[],none,⟨6,1,0⟩⟩
def t4_366jobs0 : List Job := [⟨plan1947,[],none,⟨6,1,0⟩⟩]

def t4_366jobs : List Job := t4_366jobs0




def t4_367root : Job := ⟨plan1948,[],none,⟨6,1,0⟩⟩
def t4_367jobs0 : List Job := [⟨plan1948,[],none,⟨6,1,0⟩⟩]

def t4_367jobs : List Job := t4_367jobs0




def t4_368root : Job := ⟨plan1949,[],none,⟨6,1,0⟩⟩
def t4_368jobs0 : List Job := [⟨plan1949,[],none,⟨6,1,0⟩⟩]

def t4_368jobs : List Job := t4_368jobs0




def t4_369root : Job := ⟨plan1950,[],none,⟨6,1,0⟩⟩
def t4_369jobs0 : List Job := [⟨plan1950,[],none,⟨6,1,0⟩⟩]

def t4_369jobs : List Job := t4_369jobs0




def t4_370root : Job := ⟨plan1711,[],none,⟨6,0,0⟩⟩
def t4_370jobs0 : List Job := [⟨plan1711,[],none,⟨6,0,0⟩⟩]

def t4_370jobs : List Job := t4_370jobs0




def t4_371root : Job := ⟨plan1786,[],none,⟨6,0,0⟩⟩
def t4_371jobs0 : List Job := [⟨plan1786,[],none,⟨6,0,0⟩⟩]

def t4_371jobs : List Job := t4_371jobs0




def t4_372root : Job := ⟨plan1787,[],none,⟨6,0,0⟩⟩
def t4_372jobs0 : List Job := [⟨plan1787,[],none,⟨6,0,0⟩⟩]

def t4_372jobs : List Job := t4_372jobs0




def t4_373root : Job := ⟨plan1788,[],none,⟨6,0,0⟩⟩
def t4_373jobs0 : List Job := [⟨plan1788,[],none,⟨6,0,0⟩⟩]

def t4_373jobs : List Job := t4_373jobs0




def t4_374root : Job := ⟨plan1951,[],none,⟨6,1,0⟩⟩
def t4_374jobs0 : List Job := [⟨plan1951,[],none,⟨6,1,0⟩⟩]

def t4_374jobs : List Job := t4_374jobs0




def t4_375root : Job := ⟨plan1952,[],none,⟨6,1,0⟩⟩
def t4_375jobs0 : List Job := [⟨plan1952,[],none,⟨6,1,0⟩⟩]

def t4_375jobs : List Job := t4_375jobs0




def t4_376root : Job := ⟨plan1953,[],none,⟨6,1,0⟩⟩
def t4_376jobs0 : List Job := [⟨plan1953,[],none,⟨6,1,0⟩⟩]

def t4_376jobs : List Job := t4_376jobs0




def t4_377root : Job := ⟨plan1954,[],none,⟨6,1,0⟩⟩
def t4_377jobs0 : List Job := [⟨plan1954,[],none,⟨6,1,0⟩⟩]

def t4_377jobs : List Job := t4_377jobs0




def t4_378root : Job := ⟨plan1955,[],none,⟨6,1,0⟩⟩
def t4_378jobs0 : List Job := [⟨plan1955,[],none,⟨6,1,0⟩⟩]

def t4_378jobs : List Job := t4_378jobs0




def t4_379root : Job := ⟨plan1956,[],none,⟨6,1,0⟩⟩
def t4_379jobs0 : List Job := [⟨plan1956,[],none,⟨6,1,0⟩⟩]

def t4_379jobs : List Job := t4_379jobs0




def t4_380root : Job := ⟨plan1789,[],none,⟨6,0,0⟩⟩
def t4_380jobs0 : List Job := [⟨plan1789,[],none,⟨6,0,0⟩⟩]

def t4_380jobs : List Job := t4_380jobs0




def t4_381root : Job := ⟨plan1957,[],none,⟨6,1,0⟩⟩
def t4_381jobs0 : List Job := [⟨plan1957,[],none,⟨6,1,0⟩⟩]

def t4_381jobs : List Job := t4_381jobs0




def t4_382root : Job := ⟨plan1958,[],none,⟨6,1,0⟩⟩
def t4_382jobs0 : List Job := [⟨plan1958,[],none,⟨6,1,0⟩⟩]

def t4_382jobs : List Job := t4_382jobs0




def t4_383root : Job := ⟨plan1959,[],none,⟨6,1,0⟩⟩
def t4_383jobs0 : List Job := [⟨plan1959,[],none,⟨6,1,0⟩⟩]

def t4_383jobs : List Job := t4_383jobs0




def t4_384root : Job := ⟨plan1960,[],none,⟨6,1,0⟩⟩
def t4_384jobs0 : List Job := [⟨plan1960,[],none,⟨6,1,0⟩⟩]

def t4_384jobs : List Job := t4_384jobs0




def t4_385root : Job := ⟨plan2153,[],none,⟨6,3,0⟩⟩
def t4_385jobs0 : List Job := [⟨plan2153,[],none,⟨6,3,0⟩⟩]

def t4_385jobs : List Job := t4_385jobs0




def t4_386root : Job := ⟨plan2154,[],none,⟨6,3,0⟩⟩
def t4_386jobs0 : List Job := [⟨plan2154,[],none,⟨6,3,0⟩⟩]

def t4_386jobs : List Job := t4_386jobs0




def t4_387root : Job := ⟨plan2155,[],none,⟨6,3,0⟩⟩
def t4_387jobs0 : List Job := [⟨plan2155,[],none,⟨6,3,0⟩⟩]

def t4_387jobs : List Job := t4_387jobs0




def t4_388root : Job := ⟨plan2156,[],none,⟨6,3,0⟩⟩
def t4_388jobs0 : List Job := [⟨plan2156,[],none,⟨6,3,0⟩⟩]

def t4_388jobs : List Job := t4_388jobs0




def t4_389root : Job := ⟨plan2157,[],none,⟨6,3,0⟩⟩
def t4_389jobs0 : List Job := [⟨plan2157,[],none,⟨6,3,0⟩⟩]

def t4_389jobs : List Job := t4_389jobs0




def t4_390root : Job := ⟨plan2158,[],none,⟨6,3,0⟩⟩
def t4_390jobs0 : List Job := [⟨plan2158,[],none,⟨6,3,0⟩⟩]

def t4_390jobs : List Job := t4_390jobs0




def t4_391root : Job := ⟨plan2159,[],none,⟨6,3,0⟩⟩
def t4_391jobs0 : List Job := [⟨plan2159,[],none,⟨6,3,0⟩⟩]

def t4_391jobs : List Job := t4_391jobs0




def t4_392root : Job := ⟨plan2160,[],none,⟨6,3,0⟩⟩
def t4_392jobs0 : List Job := [⟨plan2160,[],none,⟨6,3,0⟩⟩]

def t4_392jobs : List Job := t4_392jobs0




def t4_393root : Job := ⟨plan2161,[],none,⟨6,3,0⟩⟩
def t4_393jobs0 : List Job := [⟨plan2161,[],none,⟨6,3,0⟩⟩]

def t4_393jobs : List Job := t4_393jobs0




def t4_394root : Job := ⟨plan1961,[],none,⟨6,1,0⟩⟩
def t4_394jobs0 : List Job := [⟨plan1961,[],none,⟨6,1,0⟩⟩]

def t4_394jobs : List Job := t4_394jobs0




def t4_395root : Job := ⟨plan2162,[],none,⟨6,3,0⟩⟩
def t4_395jobs0 : List Job := [⟨plan2162,[],none,⟨6,3,0⟩⟩]

def t4_395jobs : List Job := t4_395jobs0




def t4_396root : Job := ⟨plan2163,[],none,⟨6,3,0⟩⟩
def t4_396jobs0 : List Job := [⟨plan2163,[],none,⟨6,3,0⟩⟩]

def t4_396jobs : List Job := t4_396jobs0




def t4_397root : Job := ⟨plan2164,[],none,⟨6,3,0⟩⟩
def t4_397jobs0 : List Job := [⟨plan2164,[],none,⟨6,3,0⟩⟩]

def t4_397jobs : List Job := t4_397jobs0




def t4_398root : Job := ⟨plan2165,[],none,⟨6,3,0⟩⟩
def t4_398jobs0 : List Job := [⟨plan2165,[],none,⟨6,3,0⟩⟩]

def t4_398jobs : List Job := t4_398jobs0




def t4_399root : Job := ⟨plan2166,[],none,⟨6,3,0⟩⟩
def t4_399jobs0 : List Job := [⟨plan2166,[],none,⟨6,3,0⟩⟩]

def t4_399jobs : List Job := t4_399jobs0




def t4_400root : Job := ⟨plan2167,[],none,⟨6,3,0⟩⟩
def t4_400jobs0 : List Job := [⟨plan2167,[],none,⟨6,3,0⟩⟩]

def t4_400jobs : List Job := t4_400jobs0




def t4_401root : Job := ⟨plan2168,[],none,⟨6,3,0⟩⟩
def t4_401jobs0 : List Job := [⟨plan2168,[],none,⟨6,3,0⟩⟩]

def t4_401jobs : List Job := t4_401jobs0




def t4_402root : Job := ⟨plan2169,[],none,⟨6,3,0⟩⟩
def t4_402jobs0 : List Job := [⟨plan2169,[],none,⟨6,3,0⟩⟩]

def t4_402jobs : List Job := t4_402jobs0




def t4_403root : Job := ⟨plan2170,[],none,⟨6,3,0⟩⟩
def t4_403jobs0 : List Job := [⟨plan2170,[],none,⟨6,3,0⟩⟩]

def t4_403jobs : List Job := t4_403jobs0




def t4_404root : Job := ⟨plan2171,[],none,⟨6,3,0⟩⟩
def t4_404jobs0 : List Job := [⟨plan2171,[],none,⟨6,3,0⟩⟩]

def t4_404jobs : List Job := t4_404jobs0




def t4_405root : Job := ⟨plan2172,[],none,⟨6,3,0⟩⟩
def t4_405jobs0 : List Job := [⟨plan2172,[],none,⟨6,3,0⟩⟩]

def t4_405jobs : List Job := t4_405jobs0




def t4_406root : Job := ⟨plan2173,[],none,⟨6,3,0⟩⟩
def t4_406jobs0 : List Job := [⟨plan2173,[],none,⟨6,3,0⟩⟩]

def t4_406jobs : List Job := t4_406jobs0




def t4_407root : Job := ⟨plan2174,[],none,⟨6,3,0⟩⟩
def t4_407jobs0 : List Job := [⟨plan2174,[],none,⟨6,3,0⟩⟩]

def t4_407jobs : List Job := t4_407jobs0




def t4_408root : Job := ⟨plan1790,[],none,⟨6,0,0⟩⟩
def t4_408jobs0 : List Job := [⟨plan1790,[],none,⟨6,0,0⟩⟩]

def t4_408jobs : List Job := t4_408jobs0




def t4_409root : Job := ⟨plan1962,[],none,⟨6,1,0⟩⟩
def t4_409jobs0 : List Job := [⟨plan1962,[],none,⟨6,1,0⟩⟩]

def t4_409jobs : List Job := t4_409jobs0




def t4_410root : Job := ⟨plan1963,[],none,⟨6,1,0⟩⟩
def t4_410jobs0 : List Job := [⟨plan1963,[],none,⟨6,1,0⟩⟩]

def t4_410jobs : List Job := t4_410jobs0




def t4_411root : Job := ⟨plan1964,[],none,⟨6,1,0⟩⟩
def t4_411jobs0 : List Job := [⟨plan1964,[],none,⟨6,1,0⟩⟩]

def t4_411jobs : List Job := t4_411jobs0




def t4_412root : Job := ⟨plan2175,[],none,⟨6,3,0⟩⟩
def t4_412jobs0 : List Job := [⟨plan2175,[],none,⟨6,3,0⟩⟩]

def t4_412jobs : List Job := t4_412jobs0




def t4_413root : Job := ⟨plan2176,[],none,⟨6,3,0⟩⟩
def t4_413jobs0 : List Job := [⟨plan2176,[],none,⟨6,3,0⟩⟩]

def t4_413jobs : List Job := t4_413jobs0




def t4_414root : Job := ⟨plan2177,[],none,⟨6,3,0⟩⟩
def t4_414jobs0 : List Job := [⟨plan2177,[],none,⟨6,3,0⟩⟩]

def t4_414jobs : List Job := t4_414jobs0




def t4_415root : Job := ⟨plan2178,[],none,⟨6,3,0⟩⟩
def t4_415jobs0 : List Job := [⟨plan2178,[],none,⟨6,3,0⟩⟩]

def t4_415jobs : List Job := t4_415jobs0




def t4_416root : Job := ⟨plan1965,[],none,⟨6,1,0⟩⟩
def t4_416jobs0 : List Job := [⟨plan1965,[],none,⟨6,1,0⟩⟩]

def t4_416jobs : List Job := t4_416jobs0




def t4_417root : Job := ⟨plan2179,[],none,⟨6,3,0⟩⟩
def t4_417jobs0 : List Job := [⟨plan2179,[],none,⟨6,3,0⟩⟩]

def t4_417jobs : List Job := t4_417jobs0




def t4_418root : Job := ⟨plan2180,[],none,⟨6,3,0⟩⟩
def t4_418jobs0 : List Job := [⟨plan2180,[],none,⟨6,3,0⟩⟩]

def t4_418jobs : List Job := t4_418jobs0




def t4_419root : Job := ⟨plan2181,[],none,⟨6,3,0⟩⟩
def t4_419jobs0 : List Job := [⟨plan2181,[],none,⟨6,3,0⟩⟩]

def t4_419jobs : List Job := t4_419jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


