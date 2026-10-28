-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks058
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks058
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:26.450969+00:00
-- url     : https://prove2.me/theorems/1c2f1987-7d74-401e-9c27-f9d6c418c1b1
-- title:
--   Endpoint22 Reach Checks058 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks058 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_387root`, `ThreeBoundEndpoint22Reachable.t6_387jobs0`, `ThreeBoundEndpoint22Reachable.t6_387jobs`, `ThreeBoundEndpoint22Reachable.t6_388root`, `ThreeBoundEndpoint22Reachable.t6_388jobs0`, `ThreeBoundEndpoint22Reachable.t6_388jobs`, `ThreeBoundEndpoint22Reachable.t6_389root`, `ThreeBoundEndpoint22Reachable.t6_389jobs0`, `ThreeBoundEndpoint22Reachable.t6_389jobs`, `ThreeBoundEndpoint22Reachable.t6_390root`, `ThreeBoundEndpoint22Reachable.t6_375root`, `ThreeBoundEndpoint22Reachable.t6_390jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks058.lean, lines 1–554.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
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

def t6_374root : Job := ⟨plan6523,[],none,⟨15,3,0⟩⟩
def t6_374jobs0 : List Job := [⟨plan6523,[],none,⟨15,3,0⟩⟩]

def t6_374jobs : List Job := t6_374jobs0




def t6_375root : Job := ⟨plan6840,[],none,⟨15,6,0⟩⟩
def t6_375jobs0 : List Job := [⟨plan6840,[],none,⟨15,6,0⟩⟩]

def t6_375jobs : List Job := t6_375jobs0




def t6_376root : Job := ⟨plan6841,[],none,⟨15,6,0⟩⟩
def t6_376jobs0 : List Job := [⟨plan6841,[],none,⟨15,6,0⟩⟩]

def t6_376jobs : List Job := t6_376jobs0




def t6_377root : Job := ⟨plan6842,[],none,⟨15,6,0⟩⟩
def t6_377jobs0 : List Job := [⟨plan6842,[],none,⟨15,6,0⟩⟩]

def t6_377jobs : List Job := t6_377jobs0




def t6_378root : Job := ⟨plan7230,[],none,⟨15,10,0⟩⟩
def t6_378jobs0 : List Job := [⟨plan7230,[],none,⟨15,10,0⟩⟩]

def t6_378jobs : List Job := t6_378jobs0




def t6_379root : Job := ⟨plan7231,[],none,⟨15,10,0⟩⟩
def t6_379jobs0 : List Job := [⟨plan7231,[],none,⟨15,10,0⟩⟩]

def t6_379jobs : List Job := t6_379jobs0




def t6_380root : Job := ⟨plan7232,[],none,⟨15,10,0⟩⟩
def t6_380jobs0 : List Job := [⟨plan7232,[],none,⟨15,10,0⟩⟩]

def t6_380jobs : List Job := t6_380jobs0




def t6_381root : Job := ⟨plan7233,[],none,⟨15,10,0⟩⟩
def t6_381jobs0 : List Job := [⟨plan7233,[],none,⟨15,10,0⟩⟩]

def t6_381jobs : List Job := t6_381jobs0




def t6_382root : Job := ⟨plan7234,[],none,⟨15,10,0⟩⟩
def t6_382jobs0 : List Job := [⟨plan7234,[],none,⟨15,10,0⟩⟩]

def t6_382jobs : List Job := t6_382jobs0




def t6_383root : Job := ⟨plan7235,[],none,⟨15,10,0⟩⟩
def t6_383jobs0 : List Job := [⟨plan7235,[],none,⟨15,10,0⟩⟩]

def t6_383jobs : List Job := t6_383jobs0




def t6_384root : Job := ⟨plan7236,[],none,⟨15,10,0⟩⟩
def t6_384jobs0 : List Job := [⟨plan7236,[],none,⟨15,10,0⟩⟩]

def t6_384jobs : List Job := t6_384jobs0




def t6_385root : Job := ⟨plan7237,[],none,⟨15,10,0⟩⟩
def t6_385jobs0 : List Job := [⟨plan7237,[],none,⟨15,10,0⟩⟩]

def t6_385jobs : List Job := t6_385jobs0




def t6_386root : Job := ⟨plan7238,[],none,⟨15,10,0⟩⟩
def t6_386jobs0 : List Job := [⟨plan7238,[],none,⟨15,10,0⟩⟩]

def t6_386jobs : List Job := t6_386jobs0




def t6_387root : Job := ⟨plan7239,[],none,⟨15,10,0⟩⟩
def t6_387jobs0 : List Job := [⟨plan7239,[],none,⟨15,10,0⟩⟩]

def t6_387jobs : List Job := t6_387jobs0




def t6_388root : Job := ⟨plan7240,[],none,⟨15,10,0⟩⟩
def t6_388jobs0 : List Job := [⟨plan7240,[],none,⟨15,10,0⟩⟩]

def t6_388jobs : List Job := t6_388jobs0




def t6_389root : Job := ⟨plan7241,[],none,⟨15,10,0⟩⟩
def t6_389jobs0 : List Job := [⟨plan7241,[],none,⟨15,10,0⟩⟩]

def t6_389jobs : List Job := t6_389jobs0




def t6_390root : Job := ⟨plan7242,[],none,⟨15,10,0⟩⟩
def t6_390jobs0 : List Job := [⟨plan7242,[],none,⟨15,10,0⟩⟩]

def t6_390jobs : List Job := t6_390jobs0




def t6_391root : Job := ⟨plan7243,[],none,⟨15,10,0⟩⟩
def t6_391jobs0 : List Job := [⟨plan7243,[],none,⟨15,10,0⟩⟩]

def t6_391jobs : List Job := t6_391jobs0




def t6_392root : Job := ⟨plan7244,[],none,⟨15,10,0⟩⟩
def t6_392jobs0 : List Job := [⟨plan7244,[],none,⟨15,10,0⟩⟩]

def t6_392jobs : List Job := t6_392jobs0




def t6_393root : Job := ⟨plan7245,[],none,⟨15,10,0⟩⟩
def t6_393jobs0 : List Job := [⟨plan7245,[],none,⟨15,10,0⟩⟩]

def t6_393jobs : List Job := t6_393jobs0




def t6_394root : Job := ⟨plan7246,[],none,⟨15,10,0⟩⟩
def t6_394jobs0 : List Job := [⟨plan7246,[],none,⟨15,10,0⟩⟩]

def t6_394jobs : List Job := t6_394jobs0




def t6_395root : Job := ⟨plan7247,[],none,⟨15,10,0⟩⟩
def t6_395jobs0 : List Job := [⟨plan7247,[],none,⟨15,10,0⟩⟩]

def t6_395jobs : List Job := t6_395jobs0




def t6_396root : Job := ⟨plan7248,[],none,⟨15,10,0⟩⟩
def t6_396jobs0 : List Job := [⟨plan7248,[],none,⟨15,10,0⟩⟩]

def t6_396jobs : List Job := t6_396jobs0




def t6_397root : Job := ⟨plan6524,[],none,⟨15,3,0⟩⟩
def t6_397jobs0 : List Job := [⟨plan6524,[],none,⟨15,3,0⟩⟩]

def t6_397jobs : List Job := t6_397jobs0




def t6_398root : Job := ⟨plan6843,[],none,⟨15,6,0⟩⟩
def t6_398jobs0 : List Job := [⟨plan6843,[],none,⟨15,6,0⟩⟩]

def t6_398jobs : List Job := t6_398jobs0




def t6_399root : Job := ⟨plan6844,[],none,⟨15,6,0⟩⟩
def t6_399jobs0 : List Job := [⟨plan5695,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5695,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_399jobs1 : List Job := [⟨plan5695,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_399jobs : List Job := t6_399jobs0++t6_399jobs1




def t6_400root : Job := ⟨plan6845,[],none,⟨15,6,0⟩⟩
def t6_400jobs0 : List Job := [⟨plan6845,[],none,⟨15,6,0⟩⟩]

def t6_400jobs : List Job := t6_400jobs0




def t6_401root : Job := ⟨plan7249,[],none,⟨15,10,0⟩⟩
def t6_401jobs0 : List Job := [⟨plan7249,[],none,⟨15,10,0⟩⟩]

def t6_401jobs : List Job := t6_401jobs0




def t6_402root : Job := ⟨plan7250,[],none,⟨15,10,0⟩⟩
def t6_402jobs0 : List Job := [⟨plan7250,[],none,⟨15,10,0⟩⟩]

def t6_402jobs : List Job := t6_402jobs0




def t6_403root : Job := ⟨plan7251,[],none,⟨15,10,0⟩⟩
def t6_403jobs0 : List Job := [⟨plan7251,[],none,⟨15,10,0⟩⟩]

def t6_403jobs : List Job := t6_403jobs0




def t6_404root : Job := ⟨plan7252,[],none,⟨15,10,0⟩⟩
def t6_404jobs0 : List Job := [⟨plan7252,[],none,⟨15,10,0⟩⟩]

def t6_404jobs : List Job := t6_404jobs0




def t6_405root : Job := ⟨plan7253,[],none,⟨15,10,0⟩⟩
def t6_405jobs0 : List Job := [⟨plan7253,[],none,⟨15,10,0⟩⟩]

def t6_405jobs : List Job := t6_405jobs0




def t6_406root : Job := ⟨plan7254,[],none,⟨15,10,0⟩⟩
def t6_406jobs0 : List Job := [⟨plan7254,[],none,⟨15,10,0⟩⟩]

def t6_406jobs : List Job := t6_406jobs0




def t6_407root : Job := ⟨plan7255,[],none,⟨15,10,0⟩⟩
def t6_407jobs0 : List Job := [⟨plan7255,[],none,⟨15,10,0⟩⟩]

def t6_407jobs : List Job := t6_407jobs0




def t6_408root : Job := ⟨plan7256,[],none,⟨15,10,0⟩⟩
def t6_408jobs0 : List Job := [⟨plan7256,[],none,⟨15,10,0⟩⟩]

def t6_408jobs : List Job := t6_408jobs0




def t6_409root : Job := ⟨plan7257,[],none,⟨15,10,0⟩⟩
def t6_409jobs0 : List Job := [⟨plan7257,[],none,⟨15,10,0⟩⟩]

def t6_409jobs : List Job := t6_409jobs0




def t6_410root : Job := ⟨plan7258,[],none,⟨15,10,0⟩⟩
def t6_410jobs0 : List Job := [⟨plan7258,[],none,⟨15,10,0⟩⟩]

def t6_410jobs : List Job := t6_410jobs0




def t6_411root : Job := ⟨plan7259,[],none,⟨15,10,0⟩⟩
def t6_411jobs0 : List Job := [⟨plan7259,[],none,⟨15,10,0⟩⟩]

def t6_411jobs : List Job := t6_411jobs0




def t6_412root : Job := ⟨plan7260,[],none,⟨15,10,0⟩⟩
def t6_412jobs0 : List Job := [⟨plan7260,[],none,⟨15,10,0⟩⟩]

def t6_412jobs : List Job := t6_412jobs0




def t6_413root : Job := ⟨plan7261,[],none,⟨15,10,0⟩⟩
def t6_413jobs0 : List Job := [⟨plan7261,[],none,⟨15,10,0⟩⟩]

def t6_413jobs : List Job := t6_413jobs0




def t6_414root : Job := ⟨plan7262,[],none,⟨15,10,0⟩⟩
def t6_414jobs0 : List Job := [⟨plan7262,[],none,⟨15,10,0⟩⟩]

def t6_414jobs : List Job := t6_414jobs0




def t6_415root : Job := ⟨plan7263,[],none,⟨15,10,0⟩⟩
def t6_415jobs0 : List Job := [⟨plan7263,[],none,⟨15,10,0⟩⟩]

def t6_415jobs : List Job := t6_415jobs0




def t6_416root : Job := ⟨plan7264,[],none,⟨15,10,0⟩⟩
def t6_416jobs0 : List Job := [⟨plan7264,[],none,⟨15,10,0⟩⟩]

def t6_416jobs : List Job := t6_416jobs0




def t6_417root : Job := ⟨plan7265,[],none,⟨15,10,0⟩⟩
def t6_417jobs0 : List Job := [⟨plan7265,[],none,⟨15,10,0⟩⟩]

def t6_417jobs : List Job := t6_417jobs0




def t6_418root : Job := ⟨plan7266,[],none,⟨15,10,0⟩⟩
def t6_418jobs0 : List Job := [⟨plan7266,[],none,⟨15,10,0⟩⟩]

def t6_418jobs : List Job := t6_418jobs0




def t6_419root : Job := ⟨plan7267,[],none,⟨15,10,0⟩⟩
def t6_419jobs0 : List Job := [⟨plan7267,[],none,⟨15,10,0⟩⟩]

def t6_419jobs : List Job := t6_419jobs0




def t6_420root : Job := ⟨plan7268,[],none,⟨15,10,0⟩⟩
def t6_420jobs0 : List Job := [⟨plan7268,[],none,⟨15,10,0⟩⟩]

def t6_420jobs : List Job := t6_420jobs0




def t6_421root : Job := ⟨plan7269,[],none,⟨15,10,0⟩⟩
def t6_421jobs0 : List Job := [⟨plan7269,[],none,⟨15,10,0⟩⟩]

def t6_421jobs : List Job := t6_421jobs0




def t6_422root : Job := ⟨plan7270,[],none,⟨15,10,0⟩⟩
def t6_422jobs0 : List Job := [⟨plan7270,[],none,⟨15,10,0⟩⟩]

def t6_422jobs : List Job := t6_422jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


