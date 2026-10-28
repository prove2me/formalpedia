-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks010
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks010
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:23:34.24237+00:00
-- url     : https://prove2.me/theorems/96b8f046-62ad-420f-86f1-8571ad0bda77
-- title:
--   Endpoint22 Reach Checks010 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks010 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_427root`, `ThreeBoundEndpoint22Reachable.t5_427jobs0`, `ThreeBoundEndpoint22Reachable.t5_427jobs`, `ThreeBoundEndpoint22Reachable.t5_428root`, `ThreeBoundEndpoint22Reachable.t5_428jobs0`, `ThreeBoundEndpoint22Reachable.t5_428jobs`, `ThreeBoundEndpoint22Reachable.t5_429root`, `ThreeBoundEndpoint22Reachable.t5_429jobs0`, `ThreeBoundEndpoint22Reachable.t5_429jobs`, `ThreeBoundEndpoint22Reachable.t5_430root`, `ThreeBoundEndpoint22Reachable.t5_430jobs0`, `ThreeBoundEndpoint22Reachable.t5_430jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks010.lean, lines 1–563.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans047
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

def t5_417root : Job := ⟨plan4160,[],none,⟨10,3,0⟩⟩
def t5_417jobs0 : List Job := [⟨plan1374,[⟨1,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-6)⟩⟩,⟨plan1374,[⟨1,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-5)⟩⟩,⟨plan1374,[⟨1,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1374,[⟨1,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-4)⟩⟩,⟨plan1374,[⟨1,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-5)⟩⟩,⟨plan1374,[⟨1,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,(-3)⟩⟩,⟨plan1374,[⟨1,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-4)⟩⟩,⟨plan1374,[⟨1,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨9,3,(-5)⟩⟩,⟨plan1374,[⟨1,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨8,3,(-4)⟩⟩,⟨plan1374,[⟨1,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1374,[⟨1,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨7,3,(-3)⟩⟩]

def t5_417jobs1 : List Job := [⟨plan1374,[⟨1,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨7,3,(-4)⟩⟩,⟨plan1374,[⟨1,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨6,3,(-2)⟩⟩,⟨plan1374,[⟨1,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨6,3,(-3)⟩⟩,⟨plan1374,[⟨1,1,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨9,3,(-6)⟩⟩]

def t5_417jobs2 : List Job := [⟨plan1374,[⟨1,1,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨8,3,(-5)⟩⟩,⟨plan1374,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨8,3,(-6)⟩⟩,⟨plan1374,[⟨1,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨7,3,(-4)⟩⟩,⟨plan1374,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨7,3,(-5)⟩⟩,⟨plan1374,[⟨1,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨6,3,(-3)⟩⟩,⟨plan1374,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨6,3,(-4)⟩⟩]

def t5_417jobs : List Job := t5_417jobs0++t5_417jobs1++t5_417jobs2




def t5_418root : Job := ⟨plan4161,[],none,⟨10,3,0⟩⟩
def t5_418jobs0 : List Job := [⟨plan2773,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2773,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_418jobs1 : List Job := [⟨plan2773,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_418jobs : List Job := t5_418jobs0++t5_418jobs1




def t5_419root : Job := ⟨plan4162,[],none,⟨10,3,0⟩⟩
def t5_419jobs0 : List Job := [⟨plan4162,[],none,⟨10,3,0⟩⟩]

def t5_419jobs : List Job := t5_419jobs0




def t5_420root : Job := ⟨plan4163,[],none,⟨10,3,0⟩⟩
def t5_420jobs0 : List Job := [⟨plan2775,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2775,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_420jobs1 : List Job := [⟨plan2775,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_420jobs : List Job := t5_420jobs0++t5_420jobs1




def t5_421root : Job := ⟨plan4164,[],none,⟨10,3,0⟩⟩
def t5_421jobs0 : List Job := [⟨plan2776,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2776,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_421jobs1 : List Job := [⟨plan2776,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_421jobs : List Job := t5_421jobs0++t5_421jobs1




def t5_422root : Job := ⟨plan4165,[],none,⟨10,3,0⟩⟩
def t5_422jobs0 : List Job := [⟨plan4165,[],none,⟨10,3,0⟩⟩]

def t5_422jobs : List Job := t5_422jobs0




def t5_423root : Job := ⟨plan3871,[],none,⟨10,1,0⟩⟩
def t5_423jobs0 : List Job := [⟨plan3871,[],none,⟨10,1,0⟩⟩]

def t5_423jobs : List Job := t5_423jobs0




def t5_424root : Job := ⟨plan3720,[],none,⟨10,0,0⟩⟩
def t5_424jobs0 : List Job := [⟨plan3720,[],none,⟨10,0,0⟩⟩]

def t5_424jobs : List Job := t5_424jobs0




def t5_425root : Job := ⟨plan3872,[],none,⟨10,1,0⟩⟩
def t5_425jobs0 : List Job := [⟨plan3872,[],none,⟨10,1,0⟩⟩]

def t5_425jobs : List Job := t5_425jobs0




def t5_426root : Job := ⟨plan3873,[],none,⟨10,1,0⟩⟩
def t5_426jobs0 : List Job := [⟨plan3873,[],none,⟨10,1,0⟩⟩]

def t5_426jobs : List Job := t5_426jobs0




def t5_427root : Job := ⟨plan3874,[],none,⟨10,1,0⟩⟩
def t5_427jobs0 : List Job := [⟨plan3874,[],none,⟨10,1,0⟩⟩]

def t5_427jobs : List Job := t5_427jobs0




def t5_428root : Job := ⟨plan4166,[],none,⟨10,3,0⟩⟩
def t5_428jobs0 : List Job := [⟨plan4166,[],none,⟨10,3,0⟩⟩]

def t5_428jobs : List Job := t5_428jobs0




def t5_429root : Job := ⟨plan4167,[],none,⟨10,3,0⟩⟩
def t5_429jobs0 : List Job := [⟨plan4167,[],none,⟨10,3,0⟩⟩]

def t5_429jobs : List Job := t5_429jobs0




def t5_430root : Job := ⟨plan4168,[],none,⟨10,3,0⟩⟩
def t5_430jobs0 : List Job := [⟨plan4168,[],none,⟨10,3,0⟩⟩]

def t5_430jobs : List Job := t5_430jobs0




def t5_431root : Job := ⟨plan4169,[],none,⟨10,3,0⟩⟩
def t5_431jobs0 : List Job := [⟨plan4169,[],none,⟨10,3,0⟩⟩]

def t5_431jobs : List Job := t5_431jobs0




def t5_432root : Job := ⟨plan4170,[],none,⟨10,3,0⟩⟩
def t5_432jobs0 : List Job := [⟨plan4170,[],none,⟨10,3,0⟩⟩]

def t5_432jobs : List Job := t5_432jobs0




def t5_433root : Job := ⟨plan4171,[],none,⟨10,3,0⟩⟩
def t5_433jobs0 : List Job := [⟨plan4171,[],none,⟨10,3,0⟩⟩]

def t5_433jobs : List Job := t5_433jobs0




def t5_434root : Job := ⟨plan4172,[],none,⟨10,3,0⟩⟩
def t5_434jobs0 : List Job := [⟨plan4172,[],none,⟨10,3,0⟩⟩]

def t5_434jobs : List Job := t5_434jobs0




def t5_435root : Job := ⟨plan4173,[],none,⟨10,3,0⟩⟩
def t5_435jobs0 : List Job := [⟨plan4173,[],none,⟨10,3,0⟩⟩]

def t5_435jobs : List Job := t5_435jobs0




def t5_436root : Job := ⟨plan3721,[],none,⟨10,0,0⟩⟩
def t5_436jobs0 : List Job := [⟨plan3721,[],none,⟨10,0,0⟩⟩]

def t5_436jobs : List Job := t5_436jobs0




def t5_437root : Job := ⟨plan3875,[],none,⟨10,1,0⟩⟩
def t5_437jobs0 : List Job := [⟨plan3875,[],none,⟨10,1,0⟩⟩]

def t5_437jobs : List Job := t5_437jobs0




def t5_438root : Job := ⟨plan3876,[],none,⟨10,1,0⟩⟩
def t5_438jobs0 : List Job := [⟨plan3876,[],none,⟨10,1,0⟩⟩]

def t5_438jobs : List Job := t5_438jobs0




def t5_439root : Job := ⟨plan3877,[],none,⟨10,1,0⟩⟩
def t5_439jobs0 : List Job := [⟨plan3877,[],none,⟨10,1,0⟩⟩]

def t5_439jobs : List Job := t5_439jobs0




def t5_440root : Job := ⟨plan4174,[],none,⟨10,3,0⟩⟩
def t5_440jobs0 : List Job := [⟨plan4174,[],none,⟨10,3,0⟩⟩]

def t5_440jobs : List Job := t5_440jobs0




def t5_441root : Job := ⟨plan4175,[],none,⟨10,3,0⟩⟩
def t5_441jobs0 : List Job := [⟨plan4175,[],none,⟨10,3,0⟩⟩]

def t5_441jobs : List Job := t5_441jobs0




def t5_442root : Job := ⟨plan4176,[],none,⟨10,3,0⟩⟩
def t5_442jobs0 : List Job := [⟨plan4176,[],none,⟨10,3,0⟩⟩]

def t5_442jobs : List Job := t5_442jobs0




def t5_443root : Job := ⟨plan4177,[],none,⟨10,3,0⟩⟩
def t5_443jobs0 : List Job := [⟨plan4177,[],none,⟨10,3,0⟩⟩]

def t5_443jobs : List Job := t5_443jobs0




def t5_444root : Job := ⟨plan4178,[],none,⟨10,3,0⟩⟩
def t5_444jobs0 : List Job := [⟨plan4178,[],none,⟨10,3,0⟩⟩]

def t5_444jobs : List Job := t5_444jobs0




def t5_445root : Job := ⟨plan4179,[],none,⟨10,3,0⟩⟩
def t5_445jobs0 : List Job := [⟨plan4179,[],none,⟨10,3,0⟩⟩]

def t5_445jobs : List Job := t5_445jobs0




def t5_446root : Job := ⟨plan4180,[],none,⟨10,3,0⟩⟩
def t5_446jobs0 : List Job := [⟨plan4180,[],none,⟨10,3,0⟩⟩]

def t5_446jobs : List Job := t5_446jobs0




def t5_447root : Job := ⟨plan4539,[],none,⟨10,6,0⟩⟩
def t5_447jobs0 : List Job := [⟨plan4539,[],none,⟨10,6,0⟩⟩]

def t5_447jobs : List Job := t5_447jobs0




def t5_448root : Job := ⟨plan4540,[],none,⟨10,6,0⟩⟩
def t5_448jobs0 : List Job := [⟨plan4540,[],none,⟨10,6,0⟩⟩]

def t5_448jobs : List Job := t5_448jobs0




def t5_449root : Job := ⟨plan4541,[],none,⟨10,6,0⟩⟩
def t5_449jobs0 : List Job := [⟨plan4541,[],none,⟨10,6,0⟩⟩]

def t5_449jobs : List Job := t5_449jobs0




def t5_450root : Job := ⟨plan3878,[],none,⟨10,1,0⟩⟩
def t5_450jobs0 : List Job := [⟨plan3878,[],none,⟨10,1,0⟩⟩]

def t5_450jobs : List Job := t5_450jobs0




def t5_451root : Job := ⟨plan4181,[],none,⟨10,3,0⟩⟩
def t5_451jobs0 : List Job := [⟨plan4181,[],none,⟨10,3,0⟩⟩]

def t5_451jobs : List Job := t5_451jobs0




def t5_452root : Job := ⟨plan4182,[],none,⟨10,3,0⟩⟩
def t5_452jobs0 : List Job := [⟨plan4182,[],none,⟨10,3,0⟩⟩]

def t5_452jobs : List Job := t5_452jobs0




def t5_453root : Job := ⟨plan4183,[],none,⟨10,3,0⟩⟩
def t5_453jobs0 : List Job := [⟨plan4183,[],none,⟨10,3,0⟩⟩]

def t5_453jobs : List Job := t5_453jobs0




def t5_454root : Job := ⟨plan4542,[],none,⟨10,6,0⟩⟩
def t5_454jobs0 : List Job := [⟨plan4542,[],none,⟨10,6,0⟩⟩]

def t5_454jobs : List Job := t5_454jobs0




def t5_455root : Job := ⟨plan4543,[],none,⟨10,6,0⟩⟩
def t5_455jobs0 : List Job := [⟨plan4543,[],none,⟨10,6,0⟩⟩]

def t5_455jobs : List Job := t5_455jobs0




def t5_456root : Job := ⟨plan4544,[],none,⟨10,6,0⟩⟩
def t5_456jobs0 : List Job := [⟨plan4544,[],none,⟨10,6,0⟩⟩]

def t5_456jobs : List Job := t5_456jobs0




def t5_457root : Job := ⟨plan4545,[],none,⟨10,6,0⟩⟩
def t5_457jobs0 : List Job := [⟨plan4545,[],none,⟨10,6,0⟩⟩]

def t5_457jobs : List Job := t5_457jobs0




def t5_458root : Job := ⟨plan4546,[],none,⟨10,6,0⟩⟩
def t5_458jobs0 : List Job := [⟨plan4546,[],none,⟨10,6,0⟩⟩]

def t5_458jobs : List Job := t5_458jobs0




def t5_459root : Job := ⟨plan4547,[],none,⟨10,6,0⟩⟩
def t5_459jobs0 : List Job := [⟨plan4547,[],none,⟨10,6,0⟩⟩]

def t5_459jobs : List Job := t5_459jobs0




def t5_460root : Job := ⟨plan4548,[],none,⟨10,6,0⟩⟩
def t5_460jobs0 : List Job := [⟨plan4548,[],none,⟨10,6,0⟩⟩]

def t5_460jobs : List Job := t5_460jobs0




def t5_461root : Job := ⟨plan4549,[],none,⟨10,6,0⟩⟩
def t5_461jobs0 : List Job := [⟨plan4549,[],none,⟨10,6,0⟩⟩]

def t5_461jobs : List Job := t5_461jobs0




def t5_462root : Job := ⟨plan4550,[],none,⟨10,6,0⟩⟩
def t5_462jobs0 : List Job := [⟨plan4550,[],none,⟨10,6,0⟩⟩]

def t5_462jobs : List Job := t5_462jobs0




def t5_463root : Job := ⟨plan4551,[],none,⟨10,6,0⟩⟩
def t5_463jobs0 : List Job := [⟨plan4551,[],none,⟨10,6,0⟩⟩]

def t5_463jobs : List Job := t5_463jobs0




def t5_464root : Job := ⟨plan4552,[],none,⟨10,6,0⟩⟩
def t5_464jobs0 : List Job := [⟨plan4552,[],none,⟨10,6,0⟩⟩]

def t5_464jobs : List Job := t5_464jobs0




def t5_465root : Job := ⟨plan4553,[],none,⟨10,6,0⟩⟩
def t5_465jobs0 : List Job := [⟨plan4553,[],none,⟨10,6,0⟩⟩]

def t5_465jobs : List Job := t5_465jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


