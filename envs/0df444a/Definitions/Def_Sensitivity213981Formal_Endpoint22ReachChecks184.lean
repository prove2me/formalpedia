-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks184
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks184
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:38.608798+00:00
-- url     : https://prove2.me/theorems/2f8cfde3-6d47-47ca-b0f1-a39e3e3c1087
-- title:
--   Endpoint22 Reach Checks184 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks184 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_376root`, `ThreeBoundEndpoint22Reachable.t7_376jobs0`, `ThreeBoundEndpoint22Reachable.t7_376jobs`, `ThreeBoundEndpoint22Reachable.t7_377root`, `ThreeBoundEndpoint22Reachable.t7_377jobs0`, `ThreeBoundEndpoint22Reachable.t7_377jobs`, `ThreeBoundEndpoint22Reachable.t7_378root`, `ThreeBoundEndpoint22Reachable.t7_378jobs0`, `ThreeBoundEndpoint22Reachable.t7_378jobs`, `ThreeBoundEndpoint22Reachable.t7_379root`, `ThreeBoundEndpoint22Reachable.t7_379jobs0`, `ThreeBoundEndpoint22Reachable.t7_379jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks184.lean, lines 1–725.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans093
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

def t7_363root : Job := ⟨plan8663,[],none,⟨21,10,0⟩⟩
def t7_363jobs0 : List Job := [⟨plan8663,[],none,⟨21,10,0⟩⟩]

def t7_363jobs : List Job := t7_363jobs0




def t7_364root : Job := ⟨plan8664,[],none,⟨21,10,0⟩⟩
def t7_364jobs0 : List Job := [⟨plan8664,[],none,⟨21,10,0⟩⟩]

def t7_364jobs : List Job := t7_364jobs0




def t7_365root : Job := ⟨plan8848,[],none,⟨21,15,0⟩⟩
def t7_365jobs0 : List Job := [⟨plan8848,[],none,⟨21,15,0⟩⟩]

def t7_365jobs : List Job := t7_365jobs0




def t7_366root : Job := ⟨plan8849,[],none,⟨21,15,0⟩⟩
def t7_366jobs0 : List Job := [⟨plan8849,[],none,⟨21,15,0⟩⟩]

def t7_366jobs : List Job := t7_366jobs0




def t7_367root : Job := ⟨plan8850,[],none,⟨21,15,0⟩⟩
def t7_367jobs0 : List Job := [⟨plan8850,[],none,⟨21,15,0⟩⟩]

def t7_367jobs : List Job := t7_367jobs0




def t7_368root : Job := ⟨plan8851,[],none,⟨21,15,0⟩⟩
def t7_368jobs0 : List Job := [⟨plan8851,[],none,⟨21,15,0⟩⟩]

def t7_368jobs : List Job := t7_368jobs0




def t7_369root : Job := ⟨plan8852,[],none,⟨21,15,0⟩⟩
def t7_369jobs0 : List Job := [⟨plan8852,[],none,⟨21,15,0⟩⟩]

def t7_369jobs : List Job := t7_369jobs0




def t7_370root : Job := ⟨plan8853,[],none,⟨21,15,0⟩⟩
def t7_370jobs0 : List Job := [⟨plan8853,[],none,⟨21,15,0⟩⟩]

def t7_370jobs : List Job := t7_370jobs0




def t7_371root : Job := ⟨plan8854,[],none,⟨21,15,0⟩⟩
def t7_371jobs0 : List Job := [⟨plan8854,[],none,⟨21,15,0⟩⟩]

def t7_371jobs : List Job := t7_371jobs0




def t7_372root : Job := ⟨plan8855,[],none,⟨21,15,0⟩⟩
def t7_372jobs0 : List Job := [⟨plan8855,[],none,⟨21,15,0⟩⟩]

def t7_372jobs : List Job := t7_372jobs0




def t7_373root : Job := ⟨plan8856,[],none,⟨21,15,0⟩⟩
def t7_373jobs0 : List Job := [⟨plan8856,[],none,⟨21,15,0⟩⟩]

def t7_373jobs : List Job := t7_373jobs0




def t7_374root : Job := ⟨plan8857,[],none,⟨21,15,0⟩⟩
def t7_374jobs0 : List Job := [⟨plan8857,[],none,⟨21,15,0⟩⟩]

def t7_374jobs : List Job := t7_374jobs0




def t7_375root : Job := ⟨plan8858,[],none,⟨21,15,0⟩⟩
def t7_375jobs0 : List Job := [⟨plan8858,[],none,⟨21,15,0⟩⟩]

def t7_375jobs : List Job := t7_375jobs0




def t7_376root : Job := ⟨plan8943,[],none,⟨21,21,0⟩⟩
def t7_376jobs0 : List Job := [⟨plan8943,[],none,⟨21,21,0⟩⟩]

def t7_376jobs : List Job := t7_376jobs0




def t7_377root : Job := ⟨plan8944,[],none,⟨21,21,0⟩⟩
def t7_377jobs0 : List Job := [⟨plan8944,[],none,⟨21,21,0⟩⟩]

def t7_377jobs : List Job := t7_377jobs0




def t7_378root : Job := ⟨plan8945,[],none,⟨21,21,0⟩⟩
def t7_378jobs0 : List Job := [⟨plan8945,[],none,⟨21,21,0⟩⟩]

def t7_378jobs : List Job := t7_378jobs0




def t7_379root : Job := ⟨plan8665,[],none,⟨21,10,0⟩⟩
def t7_379jobs0 : List Job := [⟨plan8665,[],none,⟨21,10,0⟩⟩]

def t7_379jobs : List Job := t7_379jobs0




def t7_380root : Job := ⟨plan8859,[],none,⟨21,15,0⟩⟩
def t7_380jobs0 : List Job := [⟨plan8859,[],none,⟨21,15,0⟩⟩]

def t7_380jobs : List Job := t7_380jobs0




def t7_381root : Job := ⟨plan8860,[],none,⟨21,15,0⟩⟩
def t7_381jobs0 : List Job := [⟨plan8860,[],none,⟨21,15,0⟩⟩]

def t7_381jobs : List Job := t7_381jobs0




def t7_382root : Job := ⟨plan8861,[],none,⟨21,15,0⟩⟩
def t7_382jobs0 : List Job := [⟨plan8861,[],none,⟨21,15,0⟩⟩]

def t7_382jobs : List Job := t7_382jobs0




def t7_383root : Job := ⟨plan8946,[],none,⟨21,21,0⟩⟩
def t7_383jobs0 : List Job := [⟨plan8946,[],none,⟨21,21,0⟩⟩]

def t7_383jobs : List Job := t7_383jobs0




def t7_384root : Job := ⟨plan8947,[],none,⟨21,21,0⟩⟩
def t7_384jobs0 : List Job := [⟨plan8947,[],none,⟨21,21,0⟩⟩]

def t7_384jobs : List Job := t7_384jobs0




def t7_385root : Job := ⟨plan8948,[],none,⟨21,21,0⟩⟩
def t7_385jobs0 : List Job := [⟨plan8948,[],none,⟨21,21,0⟩⟩]

def t7_385jobs : List Job := t7_385jobs0




def t7_386root : Job := ⟨plan8949,[],none,⟨21,21,0⟩⟩
def t7_386jobs0 : List Job := [⟨plan8949,[],none,⟨21,21,0⟩⟩]

def t7_386jobs : List Job := t7_386jobs0




def t7_387root : Job := ⟨plan8950,[],none,⟨21,21,0⟩⟩
def t7_387jobs0 : List Job := [⟨plan8950,[],none,⟨21,21,0⟩⟩]

def t7_387jobs : List Job := t7_387jobs0




def t7_388root : Job := ⟨plan8951,[],none,⟨21,21,0⟩⟩
def t7_388jobs0 : List Job := [⟨plan8951,[],none,⟨21,21,0⟩⟩]

def t7_388jobs : List Job := t7_388jobs0




def t7_389root : Job := ⟨plan8952,[],none,⟨21,21,0⟩⟩
def t7_389jobs0 : List Job := [⟨plan8952,[],none,⟨21,21,0⟩⟩]

def t7_389jobs : List Job := t7_389jobs0




def t7_390root : Job := ⟨plan8953,[],none,⟨21,21,0⟩⟩
def t7_390jobs0 : List Job := [⟨plan8953,[],none,⟨21,21,0⟩⟩]

def t7_390jobs : List Job := t7_390jobs0




def t7_391root : Job := ⟨plan8954,[],none,⟨21,21,0⟩⟩
def t7_391jobs0 : List Job := [⟨plan8954,[],none,⟨21,21,0⟩⟩]

def t7_391jobs : List Job := t7_391jobs0




def t7_392root : Job := ⟨plan8955,[],none,⟨21,21,0⟩⟩
def t7_392jobs0 : List Job := [⟨plan8955,[],none,⟨21,21,0⟩⟩]

def t7_392jobs : List Job := t7_392jobs0




def t7_393root : Job := ⟨plan8956,[],none,⟨21,21,0⟩⟩
def t7_393jobs0 : List Job := [⟨plan8956,[],none,⟨21,21,0⟩⟩]

def t7_393jobs : List Job := t7_393jobs0




def t7_394root : Job := ⟨plan8957,[],none,⟨21,21,0⟩⟩
def t7_394jobs0 : List Job := [⟨plan8957,[],none,⟨21,21,0⟩⟩]

def t7_394jobs : List Job := t7_394jobs0




def t7_395root : Job := ⟨plan8958,[],none,⟨21,21,0⟩⟩
def t7_395jobs0 : List Job := [⟨plan8958,[],none,⟨21,21,0⟩⟩]

def t7_395jobs : List Job := t7_395jobs0




def t7_396root : Job := ⟨plan8959,[],none,⟨21,21,0⟩⟩
def t7_396jobs0 : List Job := [⟨plan8959,[],none,⟨21,21,0⟩⟩]

def t7_396jobs : List Job := t7_396jobs0




def t7_397root : Job := ⟨plan8960,[],none,⟨21,21,0⟩⟩
def t7_397jobs0 : List Job := [⟨plan8960,[],none,⟨21,21,0⟩⟩]

def t7_397jobs : List Job := t7_397jobs0




def t7_398root : Job := ⟨plan8961,[],none,⟨21,21,0⟩⟩
def t7_398jobs0 : List Job := [⟨plan8961,[],none,⟨21,21,0⟩⟩]

def t7_398jobs : List Job := t7_398jobs0




def t7_399root : Job := ⟨plan8962,[],none,⟨21,21,0⟩⟩
def t7_399jobs0 : List Job := [⟨plan8962,[],none,⟨21,21,0⟩⟩]

def t7_399jobs : List Job := t7_399jobs0




def t7_400root : Job := ⟨plan8963,[],none,⟨21,21,0⟩⟩
def t7_400jobs0 : List Job := [⟨plan8963,[],none,⟨21,21,0⟩⟩]

def t7_400jobs : List Job := t7_400jobs0




def t7_401root : Job := ⟨plan8964,[],none,⟨21,21,0⟩⟩
def t7_401jobs0 : List Job := [⟨plan8964,[],none,⟨21,21,0⟩⟩]

def t7_401jobs : List Job := t7_401jobs0




def t7_402root : Job := ⟨plan8862,[],none,⟨21,15,0⟩⟩
def t7_402jobs0 : List Job := [⟨plan8862,[],none,⟨21,15,0⟩⟩]

def t7_402jobs : List Job := t7_402jobs0




def t7_403root : Job := ⟨plan8965,[],none,⟨21,21,0⟩⟩
def t7_403jobs0 : List Job := [⟨plan8965,[],none,⟨21,21,0⟩⟩]

def t7_403jobs : List Job := t7_403jobs0




def t7_404root : Job := ⟨plan8966,[],none,⟨21,21,0⟩⟩
def t7_404jobs0 : List Job := [⟨plan8966,[],none,⟨21,21,0⟩⟩]

def t7_404jobs : List Job := t7_404jobs0




def t7_405root : Job := ⟨plan8967,[],none,⟨21,21,0⟩⟩
def t7_405jobs0 : List Job := [⟨plan8967,[],none,⟨21,21,0⟩⟩]

def t7_405jobs : List Job := t7_405jobs0




def t7_406root : Job := ⟨plan8666,[],none,⟨21,10,0⟩⟩
def t7_406jobs0 : List Job := [⟨plan8666,[],none,⟨21,10,0⟩⟩]

def t7_406jobs : List Job := t7_406jobs0




def t7_407root : Job := ⟨plan8863,[],none,⟨21,15,0⟩⟩
def t7_407jobs0 : List Job := [⟨plan8863,[],none,⟨21,15,0⟩⟩]

def t7_407jobs : List Job := t7_407jobs0




def t7_408root : Job := ⟨plan8864,[],none,⟨21,15,0⟩⟩
def t7_408jobs0 : List Job := [⟨plan8864,[],none,⟨21,15,0⟩⟩]

def t7_408jobs : List Job := t7_408jobs0




def t7_409root : Job := ⟨plan8865,[],none,⟨21,15,0⟩⟩
def t7_409jobs0 : List Job := [⟨plan8865,[],none,⟨21,15,0⟩⟩]

def t7_409jobs : List Job := t7_409jobs0




def t7_410root : Job := ⟨plan8968,[],none,⟨21,21,0⟩⟩
def t7_410jobs0 : List Job := [⟨plan8968,[],none,⟨21,21,0⟩⟩]

def t7_410jobs : List Job := t7_410jobs0




def t7_411root : Job := ⟨plan8969,[],none,⟨21,21,0⟩⟩
def t7_411jobs0 : List Job := [⟨plan8969,[],none,⟨21,21,0⟩⟩]

def t7_411jobs : List Job := t7_411jobs0




def t7_412root : Job := ⟨plan8970,[],none,⟨21,21,0⟩⟩
def t7_412jobs0 : List Job := [⟨plan8970,[],none,⟨21,21,0⟩⟩]

def t7_412jobs : List Job := t7_412jobs0




def t7_413root : Job := ⟨plan8971,[],none,⟨21,21,0⟩⟩
def t7_413jobs0 : List Job := [⟨plan8971,[],none,⟨21,21,0⟩⟩]

def t7_413jobs : List Job := t7_413jobs0




def t7_414root : Job := ⟨plan8972,[],none,⟨21,21,0⟩⟩
def t7_414jobs0 : List Job := [⟨plan8972,[],none,⟨21,21,0⟩⟩]

def t7_414jobs : List Job := t7_414jobs0




def t7_415root : Job := ⟨plan8973,[],none,⟨21,21,0⟩⟩
def t7_415jobs0 : List Job := [⟨plan8973,[],none,⟨21,21,0⟩⟩]

def t7_415jobs : List Job := t7_415jobs0




def t7_416root : Job := ⟨plan8974,[],none,⟨21,21,0⟩⟩
def t7_416jobs0 : List Job := [⟨plan8974,[],none,⟨21,21,0⟩⟩]

def t7_416jobs : List Job := t7_416jobs0




def t7_417root : Job := ⟨plan8975,[],none,⟨21,21,0⟩⟩
def t7_417jobs0 : List Job := [⟨plan8975,[],none,⟨21,21,0⟩⟩]

def t7_417jobs : List Job := t7_417jobs0




def t7_418root : Job := ⟨plan8976,[],none,⟨21,21,0⟩⟩
def t7_418jobs0 : List Job := [⟨plan8976,[],none,⟨21,21,0⟩⟩]

def t7_418jobs : List Job := t7_418jobs0




def t7_419root : Job := ⟨plan8977,[],none,⟨21,21,0⟩⟩
def t7_419jobs0 : List Job := [⟨plan8977,[],none,⟨21,21,0⟩⟩]

def t7_419jobs : List Job := t7_419jobs0




def t7_420root : Job := ⟨plan8978,[],none,⟨21,21,0⟩⟩
def t7_420jobs0 : List Job := [⟨plan8978,[],none,⟨21,21,0⟩⟩]

def t7_420jobs : List Job := t7_420jobs0




def t7_421root : Job := ⟨plan8428,[],none,⟨21,1,0⟩⟩
def t7_421jobs0 : List Job := [⟨plan8428,[],none,⟨21,1,0⟩⟩]

def t7_421jobs : List Job := t7_421jobs0




def t7_422root : Job := ⟨plan8458,[],none,⟨21,3,0⟩⟩
def t7_422jobs0 : List Job := [⟨plan8458,[],none,⟨21,3,0⟩⟩]

def t7_422jobs : List Job := t7_422jobs0




def t7_423root : Job := ⟨plan8459,[],none,⟨21,3,0⟩⟩
def t7_423jobs0 : List Job := [⟨plan8089,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨21,1,(-2)⟩⟩,⟨plan8089,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨20,2,0⟩⟩,⟨plan8089,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨20,1,(-1)⟩⟩,⟨plan8089,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨19,3,2⟩⟩]

def t7_423jobs1 : List Job := [⟨plan8089,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨19,2,1⟩⟩,⟨plan8089,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨19,1,0⟩⟩]

def t7_423jobs : List Job := t7_423jobs0++t7_423jobs1




def t7_424root : Job := ⟨plan8460,[],none,⟨21,3,0⟩⟩
def t7_424jobs0 : List Job := [⟨plan8460,[],none,⟨21,3,0⟩⟩]

def t7_424jobs : List Job := t7_424jobs0




def t7_425root : Job := ⟨plan8528,[],none,⟨21,6,0⟩⟩
def t7_425jobs0 : List Job := [⟨plan8528,[],none,⟨21,6,0⟩⟩]

def t7_425jobs : List Job := t7_425jobs0




def t7_426root : Job := ⟨plan8529,[],none,⟨21,6,0⟩⟩
def t7_426jobs0 : List Job := [⟨plan8117,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8117,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨20,4,(-1)⟩⟩,⟨plan8117,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨20,3,(-2)⟩⟩,⟨plan8117,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨19,5,1⟩⟩]

def t7_426jobs1 : List Job := [⟨plan8117,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨19,4,0⟩⟩]

def t7_426jobs2 : List Job := [⟨plan8117,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨19,3,(-1)⟩⟩]

def t7_426jobs : List Job := t7_426jobs0++t7_426jobs1++t7_426jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


