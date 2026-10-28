-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks031
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks031
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:22:42.73699+00:00
-- url     : https://prove2.me/theorems/484a3e90-40ff-4673-85a1-ec7eb9040962
-- title:
--   Endpoint22 Reach Checks031 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks031 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_942jobs0`, `ThreeBoundEndpoint22Reachable.t5_942jobs`, `ThreeBoundEndpoint22Reachable.t5_943root`, `ThreeBoundEndpoint22Reachable.t5_943jobs0`, `ThreeBoundEndpoint22Reachable.t5_943jobs`, `ThreeBoundEndpoint22Reachable.t5_944root`, `ThreeBoundEndpoint22Reachable.t5_944jobs0`, `ThreeBoundEndpoint22Reachable.t5_944jobs`, `ThreeBoundEndpoint22Reachable.t5_945root`, `ThreeBoundEndpoint22Reachable.t5_945jobs0`, `ThreeBoundEndpoint22Reachable.t5_945jobs`, `ThreeBoundEndpoint22Reachable.t5_930root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks031.lean, lines 1–487.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
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

def t5_929root : Job := ⟨plan4335,[],none,⟨10,3,0⟩⟩
def t5_929jobs0 : List Job := [⟨plan4335,[],none,⟨10,3,0⟩⟩]

def t5_929jobs : List Job := t5_929jobs0




def t5_930root : Job := ⟨plan4748,[],none,⟨10,6,0⟩⟩
def t5_930jobs0 : List Job := [⟨plan4748,[],none,⟨10,6,0⟩⟩]

def t5_930jobs : List Job := t5_930jobs0




def t5_931root : Job := ⟨plan4749,[],none,⟨10,6,0⟩⟩
def t5_931jobs0 : List Job := [⟨plan4749,[],none,⟨10,6,0⟩⟩]

def t5_931jobs : List Job := t5_931jobs0




def t5_932root : Job := ⟨plan4750,[],none,⟨10,6,0⟩⟩
def t5_932jobs0 : List Job := [⟨plan4750,[],none,⟨10,6,0⟩⟩]

def t5_932jobs : List Job := t5_932jobs0




def t5_933root : Job := ⟨plan4751,[],none,⟨10,6,0⟩⟩
def t5_933jobs0 : List Job := [⟨plan4751,[],none,⟨10,6,0⟩⟩]

def t5_933jobs : List Job := t5_933jobs0




def t5_934root : Job := ⟨plan4752,[],none,⟨10,6,0⟩⟩
def t5_934jobs0 : List Job := [⟨plan4752,[],none,⟨10,6,0⟩⟩]

def t5_934jobs : List Job := t5_934jobs0




def t5_935root : Job := ⟨plan4753,[],none,⟨10,6,0⟩⟩
def t5_935jobs0 : List Job := [⟨plan4753,[],none,⟨10,6,0⟩⟩]

def t5_935jobs : List Job := t5_935jobs0




def t5_936root : Job := ⟨plan4754,[],none,⟨10,6,0⟩⟩
def t5_936jobs0 : List Job := [⟨plan4754,[],none,⟨10,6,0⟩⟩]

def t5_936jobs : List Job := t5_936jobs0




def t5_937root : Job := ⟨plan4336,[],none,⟨10,3,0⟩⟩
def t5_937jobs0 : List Job := [⟨plan4336,[],none,⟨10,3,0⟩⟩]

def t5_937jobs : List Job := t5_937jobs0




def t5_938root : Job := ⟨plan4755,[],none,⟨10,6,0⟩⟩
def t5_938jobs0 : List Job := [⟨plan4755,[],none,⟨10,6,0⟩⟩]

def t5_938jobs : List Job := t5_938jobs0




def t5_939root : Job := ⟨plan4756,[],none,⟨10,6,0⟩⟩
def t5_939jobs0 : List Job := [⟨plan4756,[],none,⟨10,6,0⟩⟩]

def t5_939jobs : List Job := t5_939jobs0




def t5_940root : Job := ⟨plan4757,[],none,⟨10,6,0⟩⟩
def t5_940jobs0 : List Job := [⟨plan4757,[],none,⟨10,6,0⟩⟩]

def t5_940jobs : List Job := t5_940jobs0




def t5_941root : Job := ⟨plan4758,[],none,⟨10,6,0⟩⟩
def t5_941jobs0 : List Job := [⟨plan4758,[],none,⟨10,6,0⟩⟩]

def t5_941jobs : List Job := t5_941jobs0




def t5_942root : Job := ⟨plan4759,[],none,⟨10,6,0⟩⟩
def t5_942jobs0 : List Job := [⟨plan4759,[],none,⟨10,6,0⟩⟩]

def t5_942jobs : List Job := t5_942jobs0




def t5_943root : Job := ⟨plan4760,[],none,⟨10,6,0⟩⟩
def t5_943jobs0 : List Job := [⟨plan4760,[],none,⟨10,6,0⟩⟩]

def t5_943jobs : List Job := t5_943jobs0




def t5_944root : Job := ⟨plan4761,[],none,⟨10,6,0⟩⟩
def t5_944jobs0 : List Job := [⟨plan4761,[],none,⟨10,6,0⟩⟩]

def t5_944jobs : List Job := t5_944jobs0




def t5_945root : Job := ⟨plan4762,[],none,⟨10,6,0⟩⟩
def t5_945jobs0 : List Job := [⟨plan4762,[],none,⟨10,6,0⟩⟩]

def t5_945jobs : List Job := t5_945jobs0




def t5_946root : Job := ⟨plan4763,[],none,⟨10,6,0⟩⟩
def t5_946jobs0 : List Job := [⟨plan4763,[],none,⟨10,6,0⟩⟩]

def t5_946jobs : List Job := t5_946jobs0




def t5_947root : Job := ⟨plan4764,[],none,⟨10,6,0⟩⟩
def t5_947jobs0 : List Job := [⟨plan4764,[],none,⟨10,6,0⟩⟩]

def t5_947jobs : List Job := t5_947jobs0




def t5_948root : Job := ⟨plan4765,[],none,⟨10,6,0⟩⟩
def t5_948jobs0 : List Job := [⟨plan4765,[],none,⟨10,6,0⟩⟩]

def t5_948jobs : List Job := t5_948jobs0




def t5_949root : Job := ⟨plan4766,[],none,⟨10,6,0⟩⟩
def t5_949jobs0 : List Job := [⟨plan4766,[],none,⟨10,6,0⟩⟩]

def t5_949jobs : List Job := t5_949jobs0




def t5_950root : Job := ⟨plan3961,[],none,⟨10,1,0⟩⟩
def t5_950jobs0 : List Job := [⟨plan3961,[],none,⟨10,1,0⟩⟩]

def t5_950jobs : List Job := t5_950jobs0




def t5_951root : Job := ⟨plan4337,[],none,⟨10,3,0⟩⟩
def t5_951jobs0 : List Job := [⟨plan4337,[],none,⟨10,3,0⟩⟩]

def t5_951jobs : List Job := t5_951jobs0




def t5_952root : Job := ⟨plan4338,[],none,⟨10,3,0⟩⟩
def t5_952jobs0 : List Job := [⟨plan4338,[],none,⟨10,3,0⟩⟩]

def t5_952jobs : List Job := t5_952jobs0




def t5_953root : Job := ⟨plan4339,[],none,⟨10,3,0⟩⟩
def t5_953jobs0 : List Job := [⟨plan4339,[],none,⟨10,3,0⟩⟩]

def t5_953jobs : List Job := t5_953jobs0




def t5_954root : Job := ⟨plan4767,[],none,⟨10,6,0⟩⟩
def t5_954jobs0 : List Job := [⟨plan4767,[],none,⟨10,6,0⟩⟩]

def t5_954jobs : List Job := t5_954jobs0




def t5_955root : Job := ⟨plan4768,[],none,⟨10,6,0⟩⟩
def t5_955jobs0 : List Job := [⟨plan4768,[],none,⟨10,6,0⟩⟩]

def t5_955jobs : List Job := t5_955jobs0




def t5_956root : Job := ⟨plan4769,[],none,⟨10,6,0⟩⟩
def t5_956jobs0 : List Job := [⟨plan4769,[],none,⟨10,6,0⟩⟩]

def t5_956jobs : List Job := t5_956jobs0




def t5_957root : Job := ⟨plan4770,[],none,⟨10,6,0⟩⟩
def t5_957jobs0 : List Job := [⟨plan4770,[],none,⟨10,6,0⟩⟩]

def t5_957jobs : List Job := t5_957jobs0




def t5_958root : Job := ⟨plan4340,[],none,⟨10,3,0⟩⟩
def t5_958jobs0 : List Job := [⟨plan4340,[],none,⟨10,3,0⟩⟩]

def t5_958jobs : List Job := t5_958jobs0




def t5_959root : Job := ⟨plan4771,[],none,⟨10,6,0⟩⟩
def t5_959jobs0 : List Job := [⟨plan4771,[],none,⟨10,6,0⟩⟩]

def t5_959jobs : List Job := t5_959jobs0




def t5_960root : Job := ⟨plan4772,[],none,⟨10,6,0⟩⟩
def t5_960jobs0 : List Job := [⟨plan4772,[],none,⟨10,6,0⟩⟩]

def t5_960jobs : List Job := t5_960jobs0




def t5_961root : Job := ⟨plan4773,[],none,⟨10,6,0⟩⟩
def t5_961jobs0 : List Job := [⟨plan4773,[],none,⟨10,6,0⟩⟩]

def t5_961jobs : List Job := t5_961jobs0




def t5_962root : Job := ⟨plan4774,[],none,⟨10,6,0⟩⟩
def t5_962jobs0 : List Job := [⟨plan4774,[],none,⟨10,6,0⟩⟩]

def t5_962jobs : List Job := t5_962jobs0




def t5_963root : Job := ⟨plan4775,[],none,⟨10,6,0⟩⟩
def t5_963jobs0 : List Job := [⟨plan4775,[],none,⟨10,6,0⟩⟩]

def t5_963jobs : List Job := t5_963jobs0




def t5_964root : Job := ⟨plan4776,[],none,⟨10,6,0⟩⟩
def t5_964jobs0 : List Job := [⟨plan4776,[],none,⟨10,6,0⟩⟩]

def t5_964jobs : List Job := t5_964jobs0




def t5_965root : Job := ⟨plan4777,[],none,⟨10,6,0⟩⟩
def t5_965jobs0 : List Job := [⟨plan4777,[],none,⟨10,6,0⟩⟩]

def t5_965jobs : List Job := t5_965jobs0




def t5_966root : Job := ⟨plan4778,[],none,⟨10,6,0⟩⟩
def t5_966jobs0 : List Job := [⟨plan4778,[],none,⟨10,6,0⟩⟩]

def t5_966jobs : List Job := t5_966jobs0




def t5_967root : Job := ⟨plan3752,[],none,⟨10,0,0⟩⟩
def t5_967jobs0 : List Job := [⟨plan3752,[],none,⟨10,0,0⟩⟩]

def t5_967jobs : List Job := t5_967jobs0




def t5_968root : Job := ⟨plan3962,[],none,⟨10,1,0⟩⟩
def t5_968jobs0 : List Job := [⟨plan3962,[],none,⟨10,1,0⟩⟩]

def t5_968jobs : List Job := t5_968jobs0




def t5_969root : Job := ⟨plan3963,[],none,⟨10,1,0⟩⟩
def t5_969jobs0 : List Job := [⟨plan3963,[],none,⟨10,1,0⟩⟩]

def t5_969jobs : List Job := t5_969jobs0




def t5_970root : Job := ⟨plan3964,[],none,⟨10,1,0⟩⟩
def t5_970jobs0 : List Job := [⟨plan3964,[],none,⟨10,1,0⟩⟩]

def t5_970jobs : List Job := t5_970jobs0




def t5_971root : Job := ⟨plan4341,[],none,⟨10,3,0⟩⟩
def t5_971jobs0 : List Job := [⟨plan4341,[],none,⟨10,3,0⟩⟩]

def t5_971jobs : List Job := t5_971jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


