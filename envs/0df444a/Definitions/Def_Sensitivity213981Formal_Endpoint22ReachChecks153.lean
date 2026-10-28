-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks153
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks153
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:01.421441+00:00
-- url     : https://prove2.me/theorems/e8ecfc2b-7916-46b6-8426-65f3728b4daa
-- title:
--   Endpoint22 Reach Checks153 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks153 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1720root`, `ThreeBoundEndpoint22Reachable.t6_1720jobs0`, `ThreeBoundEndpoint22Reachable.t6_1720jobs`, `ThreeBoundEndpoint22Reachable.t6_1721root`, `ThreeBoundEndpoint22Reachable.t6_1721jobs0`, `ThreeBoundEndpoint22Reachable.t6_1721jobs`, `ThreeBoundEndpoint22Reachable.t6_1722root`, `ThreeBoundEndpoint22Reachable.t6_1722jobs0`, `ThreeBoundEndpoint22Reachable.t6_1708jobs`, `ThreeBoundEndpoint22Reachable.t6_1722jobs`, `ThreeBoundEndpoint22Reachable.t6_1723root`, `ThreeBoundEndpoint22Reachable.t6_1723jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks153.lean, lines 1–315.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans080
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans083
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

def t6_1708root : Job := ⟨plan7685,[],none,⟨15,10,0⟩⟩
def t6_1708jobs0 : List Job := [⟨plan5783,[⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5783,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5783,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1708jobs1 : List Job := [⟨plan5783,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,0⟩⟩,⟨plan5783,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1708jobs : List Job := t6_1708jobs0++t6_1708jobs1




def t6_1709root : Job := ⟨plan7686,[],none,⟨15,10,0⟩⟩
def t6_1709jobs0 : List Job := [⟨plan7686,[],none,⟨15,10,0⟩⟩]

def t6_1709jobs : List Job := t6_1709jobs0




def t6_1710root : Job := ⟨plan8017,[],none,⟨15,15,0⟩⟩
def t6_1710jobs0 : List Job := [⟨plan8017,[],none,⟨15,15,0⟩⟩]

def t6_1710jobs : List Job := t6_1710jobs0




def t6_1711root : Job := ⟨plan8018,[],none,⟨15,15,0⟩⟩
def t6_1711jobs0 : List Job := [⟨plan8018,[],none,⟨15,15,0⟩⟩]

def t6_1711jobs : List Job := t6_1711jobs0




def t6_1712root : Job := ⟨plan8019,[],none,⟨15,15,0⟩⟩
def t6_1712jobs0 : List Job := [⟨plan8019,[],none,⟨15,15,0⟩⟩]

def t6_1712jobs : List Job := t6_1712jobs0




def t6_1713root : Job := ⟨plan8020,[],none,⟨15,15,0⟩⟩
def t6_1713jobs0 : List Job := [⟨plan8020,[],none,⟨15,15,0⟩⟩]

def t6_1713jobs : List Job := t6_1713jobs0




def t6_1714root : Job := ⟨plan8021,[],none,⟨15,15,0⟩⟩
def t6_1714jobs0 : List Job := [⟨plan8021,[],none,⟨15,15,0⟩⟩]

def t6_1714jobs : List Job := t6_1714jobs0




def t6_1715root : Job := ⟨plan8022,[],none,⟨15,15,0⟩⟩
def t6_1715jobs0 : List Job := [⟨plan8022,[],none,⟨15,15,0⟩⟩]

def t6_1715jobs : List Job := t6_1715jobs0




def t6_1716root : Job := ⟨plan8023,[],none,⟨15,15,0⟩⟩
def t6_1716jobs0 : List Job := [⟨plan8023,[],none,⟨15,15,0⟩⟩]

def t6_1716jobs : List Job := t6_1716jobs0




def t6_1717root : Job := ⟨plan8024,[],none,⟨15,15,0⟩⟩
def t6_1717jobs0 : List Job := [⟨plan8024,[],none,⟨15,15,0⟩⟩]

def t6_1717jobs : List Job := t6_1717jobs0




def t6_1718root : Job := ⟨plan8025,[],none,⟨15,15,0⟩⟩
def t6_1718jobs0 : List Job := [⟨plan8025,[],none,⟨15,15,0⟩⟩]

def t6_1718jobs : List Job := t6_1718jobs0




def t6_1719root : Job := ⟨plan8026,[],none,⟨15,15,0⟩⟩
def t6_1719jobs0 : List Job := [⟨plan8026,[],none,⟨15,15,0⟩⟩]

def t6_1719jobs : List Job := t6_1719jobs0




def t6_1720root : Job := ⟨plan8027,[],none,⟨15,15,0⟩⟩
def t6_1720jobs0 : List Job := [⟨plan8027,[],none,⟨15,15,0⟩⟩]

def t6_1720jobs : List Job := t6_1720jobs0




def t6_1721root : Job := ⟨plan8028,[],none,⟨15,15,0⟩⟩
def t6_1721jobs0 : List Job := [⟨plan8028,[],none,⟨15,15,0⟩⟩]

def t6_1721jobs : List Job := t6_1721jobs0




def t6_1722root : Job := ⟨plan8029,[],none,⟨15,15,0⟩⟩
def t6_1722jobs0 : List Job := [⟨plan8029,[],none,⟨15,15,0⟩⟩]

def t6_1722jobs : List Job := t6_1722jobs0




def t6_1723root : Job := ⟨plan8030,[],none,⟨15,15,0⟩⟩
def t6_1723jobs0 : List Job := [⟨plan8030,[],none,⟨15,15,0⟩⟩]

def t6_1723jobs : List Job := t6_1723jobs0




def t6_1724root : Job := ⟨plan8031,[],none,⟨15,15,0⟩⟩
def t6_1724jobs0 : List Job := [⟨plan8031,[],none,⟨15,15,0⟩⟩]

def t6_1724jobs : List Job := t6_1724jobs0




def t6_1725root : Job := ⟨plan8032,[],none,⟨15,15,0⟩⟩
def t6_1725jobs0 : List Job := [⟨plan8032,[],none,⟨15,15,0⟩⟩]

def t6_1725jobs : List Job := t6_1725jobs0




def t6_1726root : Job := ⟨plan6433,[],none,⟨15,1,0⟩⟩
def t6_1726jobs0 : List Job := [⟨plan6433,[],none,⟨15,1,0⟩⟩]

def t6_1726jobs : List Job := t6_1726jobs0




def t6_1727root : Job := ⟨plan6690,[],none,⟨15,3,0⟩⟩
def t6_1727jobs0 : List Job := [⟨plan6690,[],none,⟨15,3,0⟩⟩]

def t6_1727jobs : List Job := t6_1727jobs0




def t6_1728root : Job := ⟨plan6691,[],none,⟨15,3,0⟩⟩
def t6_1728jobs0 : List Job := [⟨plan5524,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5524,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨14,2,0⟩⟩,⟨plan5524,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1728jobs1 : List Job := [⟨plan5524,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨13,3,2⟩⟩,⟨plan5524,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,2,1⟩⟩,⟨plan5524,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,1,0⟩⟩]

def t6_1728jobs : List Job := t6_1728jobs0++t6_1728jobs1




def t6_1729root : Job := ⟨plan6692,[],none,⟨15,3,0⟩⟩
def t6_1729jobs0 : List Job := [⟨plan6692,[],none,⟨15,3,0⟩⟩]

def t6_1729jobs : List Job := t6_1729jobs0




def t6_1730root : Job := ⟨plan7137,[],none,⟨15,6,0⟩⟩
def t6_1730jobs0 : List Job := [⟨plan7137,[],none,⟨15,6,0⟩⟩]

def t6_1730jobs : List Job := t6_1730jobs0




def t6_1731root : Job := ⟨plan7138,[],none,⟨15,6,0⟩⟩
def t6_1731jobs0 : List Job := [⟨plan5715,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5715,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,4,(-1)⟩⟩,⟨plan5715,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1731jobs1 : List Job := [⟨plan5715,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,5,1⟩⟩]

def t6_1731jobs2 : List Job := [⟨plan5715,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,0⟩⟩,⟨plan5715,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-1)⟩⟩]

def t6_1731jobs : List Job := t6_1731jobs0++t6_1731jobs1++t6_1731jobs2




def t6_1732root : Job := ⟨plan7139,[],none,⟨15,6,0⟩⟩
def t6_1732jobs0 : List Job := [⟨plan7139,[],none,⟨15,6,0⟩⟩]

def t6_1732jobs : List Job := t6_1732jobs0




def t6_1733root : Job := ⟨plan7140,[],none,⟨15,6,0⟩⟩
def t6_1733jobs0 : List Job := [⟨plan5717,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5717,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1733jobs1 : List Job := [⟨plan5717,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1733jobs2 : List Job := [⟨plan5717,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,5,1⟩⟩]

def t6_1733jobs3 : List Job := [⟨plan5717,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,0⟩⟩,⟨plan5717,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-1)⟩⟩]

def t6_1733jobs : List Job := t6_1733jobs0++t6_1733jobs1++t6_1733jobs2++t6_1733jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


