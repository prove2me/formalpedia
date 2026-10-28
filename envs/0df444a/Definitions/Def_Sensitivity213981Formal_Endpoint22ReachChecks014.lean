-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks014
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks014
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:23:56.427578+00:00
-- url     : https://prove2.me/theorems/be3a0953-8d6b-4618-8926-265116577b4b
-- title:
--   Endpoint22 Reach Checks014 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks014 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_631root`, `ThreeBoundEndpoint22Reachable.t5_631jobs0`, `ThreeBoundEndpoint22Reachable.t5_631jobs`, `ThreeBoundEndpoint22Reachable.t5_632root`, `ThreeBoundEndpoint22Reachable.t5_632jobs0`, `ThreeBoundEndpoint22Reachable.t5_632jobs`, `ThreeBoundEndpoint22Reachable.t5_633root`, `ThreeBoundEndpoint22Reachable.t5_633jobs0`, `ThreeBoundEndpoint22Reachable.t5_633jobs`, `ThreeBoundEndpoint22Reachable.t5_634root`, `ThreeBoundEndpoint22Reachable.t5_634jobs0`, `ThreeBoundEndpoint22Reachable.t5_634jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks014.lean, lines 1–676.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans048
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

def t5_618root : Job := ⟨plan4228,[],none,⟨10,3,0⟩⟩
def t5_618jobs0 : List Job := [⟨plan2866,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2866,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_618jobs1 : List Job := [⟨plan2866,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_618jobs : List Job := t5_618jobs0++t5_618jobs1




def t5_619root : Job := ⟨plan4229,[],none,⟨10,3,0⟩⟩
def t5_619jobs0 : List Job := [⟨plan4229,[],none,⟨10,3,0⟩⟩]

def t5_619jobs : List Job := t5_619jobs0




def t5_620root : Job := ⟨plan4640,[],none,⟨10,6,0⟩⟩
def t5_620jobs0 : List Job := [⟨plan4640,[],none,⟨10,6,0⟩⟩]

def t5_620jobs : List Job := t5_620jobs0




def t5_621root : Job := ⟨plan4641,[],none,⟨10,6,0⟩⟩
def t5_621jobs0 : List Job := [⟨plan4641,[],none,⟨10,6,0⟩⟩]

def t5_621jobs : List Job := t5_621jobs0




def t5_622root : Job := ⟨plan4642,[],none,⟨10,6,0⟩⟩
def t5_622jobs0 : List Job := [⟨plan4642,[],none,⟨10,6,0⟩⟩]

def t5_622jobs : List Job := t5_622jobs0




def t5_623root : Job := ⟨plan4643,[],none,⟨10,6,0⟩⟩
def t5_623jobs0 : List Job := [⟨plan4643,[],none,⟨10,6,0⟩⟩]

def t5_623jobs : List Job := t5_623jobs0




def t5_624root : Job := ⟨plan4644,[],none,⟨10,6,0⟩⟩
def t5_624jobs0 : List Job := [⟨plan4644,[],none,⟨10,6,0⟩⟩]

def t5_624jobs : List Job := t5_624jobs0




def t5_625root : Job := ⟨plan4645,[],none,⟨10,6,0⟩⟩
def t5_625jobs0 : List Job := [⟨plan4645,[],none,⟨10,6,0⟩⟩]

def t5_625jobs : List Job := t5_625jobs0




def t5_626root : Job := ⟨plan4646,[],none,⟨10,6,0⟩⟩
def t5_626jobs0 : List Job := [⟨plan4646,[],none,⟨10,6,0⟩⟩]

def t5_626jobs : List Job := t5_626jobs0




def t5_627root : Job := ⟨plan3897,[],none,⟨10,1,0⟩⟩
def t5_627jobs0 : List Job := [⟨plan3897,[],none,⟨10,1,0⟩⟩]

def t5_627jobs : List Job := t5_627jobs0




def t5_628root : Job := ⟨plan4230,[],none,⟨10,3,0⟩⟩
def t5_628jobs0 : List Job := [⟨plan4230,[],none,⟨10,3,0⟩⟩]

def t5_628jobs : List Job := t5_628jobs0




def t5_629root : Job := ⟨plan4231,[],none,⟨10,3,0⟩⟩
def t5_629jobs0 : List Job := [⟨plan4231,[],none,⟨10,3,0⟩⟩]

def t5_629jobs : List Job := t5_629jobs0




def t5_630root : Job := ⟨plan4232,[],none,⟨10,3,0⟩⟩
def t5_630jobs0 : List Job := [⟨plan4232,[],none,⟨10,3,0⟩⟩]

def t5_630jobs : List Job := t5_630jobs0




def t5_631root : Job := ⟨plan4647,[],none,⟨10,6,0⟩⟩
def t5_631jobs0 : List Job := [⟨plan4647,[],none,⟨10,6,0⟩⟩]

def t5_631jobs : List Job := t5_631jobs0




def t5_632root : Job := ⟨plan4648,[],none,⟨10,6,0⟩⟩
def t5_632jobs0 : List Job := [⟨plan4648,[],none,⟨10,6,0⟩⟩]

def t5_632jobs : List Job := t5_632jobs0




def t5_633root : Job := ⟨plan4649,[],none,⟨10,6,0⟩⟩
def t5_633jobs0 : List Job := [⟨plan4649,[],none,⟨10,6,0⟩⟩]

def t5_633jobs : List Job := t5_633jobs0




def t5_634root : Job := ⟨plan4650,[],none,⟨10,6,0⟩⟩
def t5_634jobs0 : List Job := [⟨plan4650,[],none,⟨10,6,0⟩⟩]

def t5_634jobs : List Job := t5_634jobs0




def t5_635root : Job := ⟨plan4233,[],none,⟨10,3,0⟩⟩
def t5_635jobs0 : List Job := [⟨plan4233,[],none,⟨10,3,0⟩⟩]

def t5_635jobs : List Job := t5_635jobs0




def t5_636root : Job := ⟨plan4651,[],none,⟨10,6,0⟩⟩
def t5_636jobs0 : List Job := [⟨plan4651,[],none,⟨10,6,0⟩⟩]

def t5_636jobs : List Job := t5_636jobs0




def t5_637root : Job := ⟨plan4652,[],none,⟨10,6,0⟩⟩
def t5_637jobs0 : List Job := [⟨plan4652,[],none,⟨10,6,0⟩⟩]

def t5_637jobs : List Job := t5_637jobs0




def t5_638root : Job := ⟨plan4653,[],none,⟨10,6,0⟩⟩
def t5_638jobs0 : List Job := [⟨plan4653,[],none,⟨10,6,0⟩⟩]

def t5_638jobs : List Job := t5_638jobs0




def t5_639root : Job := ⟨plan4654,[],none,⟨10,6,0⟩⟩
def t5_639jobs0 : List Job := [⟨plan4654,[],none,⟨10,6,0⟩⟩]

def t5_639jobs : List Job := t5_639jobs0




def t5_640root : Job := ⟨plan4655,[],none,⟨10,6,0⟩⟩
def t5_640jobs0 : List Job := [⟨plan4655,[],none,⟨10,6,0⟩⟩]

def t5_640jobs : List Job := t5_640jobs0




def t5_641root : Job := ⟨plan4656,[],none,⟨10,6,0⟩⟩
def t5_641jobs0 : List Job := [⟨plan4656,[],none,⟨10,6,0⟩⟩]

def t5_641jobs : List Job := t5_641jobs0




def t5_642root : Job := ⟨plan4657,[],none,⟨10,6,0⟩⟩
def t5_642jobs0 : List Job := [⟨plan4657,[],none,⟨10,6,0⟩⟩]

def t5_642jobs : List Job := t5_642jobs0




def t5_643root : Job := ⟨plan4658,[],none,⟨10,6,0⟩⟩
def t5_643jobs0 : List Job := [⟨plan4658,[],none,⟨10,6,0⟩⟩]

def t5_643jobs : List Job := t5_643jobs0




def t5_644root : Job := ⟨plan4659,[],none,⟨10,6,0⟩⟩
def t5_644jobs0 : List Job := [⟨plan4659,[],none,⟨10,6,0⟩⟩]

def t5_644jobs : List Job := t5_644jobs0




def t5_645root : Job := ⟨plan4660,[],none,⟨10,6,0⟩⟩
def t5_645jobs0 : List Job := [⟨plan4660,[],none,⟨10,6,0⟩⟩]

def t5_645jobs : List Job := t5_645jobs0




def t5_646root : Job := ⟨plan4661,[],none,⟨10,6,0⟩⟩
def t5_646jobs0 : List Job := [⟨plan4661,[],none,⟨10,6,0⟩⟩]

def t5_646jobs : List Job := t5_646jobs0




def t5_647root : Job := ⟨plan4662,[],none,⟨10,6,0⟩⟩
def t5_647jobs0 : List Job := [⟨plan4662,[],none,⟨10,6,0⟩⟩]

def t5_647jobs : List Job := t5_647jobs0




def t5_648root : Job := ⟨plan3668,[],none,⟨10,0,0⟩⟩
def t5_648jobs0 : List Job := [⟨plan3668,[],none,⟨10,0,0⟩⟩]

def t5_648jobs : List Job := t5_648jobs0




def t5_649root : Job := ⟨plan3669,[],none,⟨10,0,0⟩⟩
def t5_649jobs0 : List Job := [⟨plan3669,[],none,⟨10,0,0⟩⟩]

def t5_649jobs : List Job := t5_649jobs0




def t5_650root : Job := ⟨plan3726,[],none,⟨10,0,0⟩⟩
def t5_650jobs0 : List Job := [⟨plan3726,[],none,⟨10,0,0⟩⟩]

def t5_650jobs : List Job := t5_650jobs0




def t5_651root : Job := ⟨plan3727,[],none,⟨10,0,0⟩⟩
def t5_651jobs0 : List Job := [⟨plan3727,[],none,⟨10,0,0⟩⟩]

def t5_651jobs : List Job := t5_651jobs0




def t5_652root : Job := ⟨plan3728,[],none,⟨10,0,0⟩⟩
def t5_652jobs0 : List Job := [⟨plan3728,[],none,⟨10,0,0⟩⟩]

def t5_652jobs : List Job := t5_652jobs0




def t5_653root : Job := ⟨plan3729,[],none,⟨10,0,0⟩⟩
def t5_653jobs0 : List Job := [⟨plan3729,[],none,⟨10,0,0⟩⟩]

def t5_653jobs : List Job := t5_653jobs0




def t5_654root : Job := ⟨plan3730,[],none,⟨10,0,0⟩⟩
def t5_654jobs0 : List Job := [⟨plan3730,[],none,⟨10,0,0⟩⟩]

def t5_654jobs : List Job := t5_654jobs0




def t5_655root : Job := ⟨plan3670,[],none,⟨10,0,0⟩⟩
def t5_655jobs0 : List Job := [⟨plan3670,[],none,⟨10,0,0⟩⟩]

def t5_655jobs : List Job := t5_655jobs0




def t5_656root : Job := ⟨plan3731,[],none,⟨10,0,0⟩⟩
def t5_656jobs0 : List Job := [⟨plan3731,[],none,⟨10,0,0⟩⟩]

def t5_656jobs : List Job := t5_656jobs0




def t5_657root : Job := ⟨plan3732,[],none,⟨10,0,0⟩⟩
def t5_657jobs0 : List Job := [⟨plan3732,[],none,⟨10,0,0⟩⟩]

def t5_657jobs : List Job := t5_657jobs0




def t5_658root : Job := ⟨plan3733,[],none,⟨10,0,0⟩⟩
def t5_658jobs0 : List Job := [⟨plan3733,[],none,⟨10,0,0⟩⟩]

def t5_658jobs : List Job := t5_658jobs0




def t5_659root : Job := ⟨plan3734,[],none,⟨10,0,0⟩⟩
def t5_659jobs0 : List Job := [⟨plan3734,[],none,⟨10,0,0⟩⟩]

def t5_659jobs : List Job := t5_659jobs0




def t5_660root : Job := ⟨plan3898,[],none,⟨10,1,0⟩⟩
def t5_660jobs0 : List Job := [⟨plan3898,[],none,⟨10,1,0⟩⟩]

def t5_660jobs : List Job := t5_660jobs0




def t5_661root : Job := ⟨plan3899,[],none,⟨10,1,0⟩⟩
def t5_661jobs0 : List Job := [⟨plan3899,[],none,⟨10,1,0⟩⟩]

def t5_661jobs : List Job := t5_661jobs0




def t5_662root : Job := ⟨plan3900,[],none,⟨10,1,0⟩⟩
def t5_662jobs0 : List Job := [⟨plan3900,[],none,⟨10,1,0⟩⟩]

def t5_662jobs : List Job := t5_662jobs0




def t5_663root : Job := ⟨plan3901,[],none,⟨10,1,0⟩⟩
def t5_663jobs0 : List Job := [⟨plan3901,[],none,⟨10,1,0⟩⟩]

def t5_663jobs : List Job := t5_663jobs0




def t5_664root : Job := ⟨plan3902,[],none,⟨10,1,0⟩⟩
def t5_664jobs0 : List Job := [⟨plan3902,[],none,⟨10,1,0⟩⟩]

def t5_664jobs : List Job := t5_664jobs0




def t5_665root : Job := ⟨plan3903,[],none,⟨10,1,0⟩⟩
def t5_665jobs0 : List Job := [⟨plan3903,[],none,⟨10,1,0⟩⟩]

def t5_665jobs : List Job := t5_665jobs0




def t5_666root : Job := ⟨plan3904,[],none,⟨10,1,0⟩⟩
def t5_666jobs0 : List Job := [⟨plan3904,[],none,⟨10,1,0⟩⟩]

def t5_666jobs : List Job := t5_666jobs0




def t5_667root : Job := ⟨plan3905,[],none,⟨10,1,0⟩⟩
def t5_667jobs0 : List Job := [⟨plan3905,[],none,⟨10,1,0⟩⟩]

def t5_667jobs : List Job := t5_667jobs0




def t5_668root : Job := ⟨plan3906,[],none,⟨10,1,0⟩⟩
def t5_668jobs0 : List Job := [⟨plan3906,[],none,⟨10,1,0⟩⟩]

def t5_668jobs : List Job := t5_668jobs0




def t5_669root : Job := ⟨plan3735,[],none,⟨10,0,0⟩⟩
def t5_669jobs0 : List Job := [⟨plan3735,[],none,⟨10,0,0⟩⟩]

def t5_669jobs : List Job := t5_669jobs0




def t5_670root : Job := ⟨plan3907,[],none,⟨10,1,0⟩⟩
def t5_670jobs0 : List Job := [⟨plan3907,[],none,⟨10,1,0⟩⟩]

def t5_670jobs : List Job := t5_670jobs0




def t5_671root : Job := ⟨plan3908,[],none,⟨10,1,0⟩⟩
def t5_671jobs0 : List Job := [⟨plan3908,[],none,⟨10,1,0⟩⟩]

def t5_671jobs : List Job := t5_671jobs0




def t5_672root : Job := ⟨plan3909,[],none,⟨10,1,0⟩⟩
def t5_672jobs0 : List Job := [⟨plan3909,[],none,⟨10,1,0⟩⟩]

def t5_672jobs : List Job := t5_672jobs0




def t5_673root : Job := ⟨plan3910,[],none,⟨10,1,0⟩⟩
def t5_673jobs0 : List Job := [⟨plan3910,[],none,⟨10,1,0⟩⟩]

def t5_673jobs : List Job := t5_673jobs0




def t5_674root : Job := ⟨plan3911,[],none,⟨10,1,0⟩⟩
def t5_674jobs0 : List Job := [⟨plan3911,[],none,⟨10,1,0⟩⟩]

def t5_674jobs : List Job := t5_674jobs0




def t5_675root : Job := ⟨plan3912,[],none,⟨10,1,0⟩⟩
def t5_675jobs0 : List Job := [⟨plan3912,[],none,⟨10,1,0⟩⟩]

def t5_675jobs : List Job := t5_675jobs0




def t5_676root : Job := ⟨plan3671,[],none,⟨10,0,0⟩⟩
def t5_676jobs0 : List Job := [⟨plan3671,[],none,⟨10,0,0⟩⟩]

def t5_676jobs : List Job := t5_676jobs0




def t5_677root : Job := ⟨plan3736,[],none,⟨10,0,0⟩⟩
def t5_677jobs0 : List Job := [⟨plan3736,[],none,⟨10,0,0⟩⟩]

def t5_677jobs : List Job := t5_677jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


