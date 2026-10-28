-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks154
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks154
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:59.050983+00:00
-- url     : https://prove2.me/theorems/f04a2ac5-52ea-4e2a-a133-37bffa7661c6
-- title:
--   Endpoint22 Reach Checks154 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks154 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1743jobs1`, `ThreeBoundEndpoint22Reachable.t6_1743jobs2`, `ThreeBoundEndpoint22Reachable.t6_1743jobs`, `ThreeBoundEndpoint22Reachable.t6_1734jobs2`, `ThreeBoundEndpoint22Reachable.t6_1744root`, `ThreeBoundEndpoint22Reachable.t6_1744jobs0`, `ThreeBoundEndpoint22Reachable.t6_1744jobs1`, `ThreeBoundEndpoint22Reachable.t6_1744jobs`, `ThreeBoundEndpoint22Reachable.t6_1745root`, `ThreeBoundEndpoint22Reachable.t6_1745jobs0`, `ThreeBoundEndpoint22Reachable.t6_1745jobs`, `ThreeBoundEndpoint22Reachable.t6_1746root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks154.lean, lines 1–364.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_1734root : Job := ⟨plan7141,[],none,⟨15,6,0⟩⟩
def t6_1734jobs0 : List Job := [⟨plan5718,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5718,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,4,(-1)⟩⟩,⟨plan5718,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1734jobs1 : List Job := [⟨plan5718,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,5,1⟩⟩]

def t6_1734jobs2 : List Job := [⟨plan5718,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,0⟩⟩,⟨plan5718,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-1)⟩⟩]

def t6_1734jobs : List Job := t6_1734jobs0++t6_1734jobs1++t6_1734jobs2




def t6_1735root : Job := ⟨plan7142,[],none,⟨15,6,0⟩⟩
def t6_1735jobs0 : List Job := [⟨plan7142,[],none,⟨15,6,0⟩⟩]

def t6_1735jobs : List Job := t6_1735jobs0




def t6_1736root : Job := ⟨plan7687,[],none,⟨15,10,0⟩⟩
def t6_1736jobs0 : List Job := [⟨plan7687,[],none,⟨15,10,0⟩⟩]

def t6_1736jobs : List Job := t6_1736jobs0




def t6_1737root : Job := ⟨plan7688,[],none,⟨15,10,0⟩⟩
def t6_1737jobs0 : List Job := [⟨plan5928,[⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5928,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5928,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5928,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,0⟩⟩]

def t6_1737jobs1 : List Job := [⟨plan5928,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1737jobs : List Job := t6_1737jobs0++t6_1737jobs1




def t6_1738root : Job := ⟨plan7689,[],none,⟨15,10,0⟩⟩
def t6_1738jobs0 : List Job := [⟨plan7689,[],none,⟨15,10,0⟩⟩]

def t6_1738jobs : List Job := t6_1738jobs0




def t6_1739root : Job := ⟨plan7690,[],none,⟨15,10,0⟩⟩
def t6_1739jobs0 : List Job := [⟨plan5930,[⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5930,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1739jobs1 : List Job := [⟨plan5930,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5930,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,0⟩⟩]

def t6_1739jobs2 : List Job := [⟨plan5930,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1739jobs : List Job := t6_1739jobs0++t6_1739jobs1++t6_1739jobs2




def t6_1740root : Job := ⟨plan7691,[],none,⟨15,10,0⟩⟩
def t6_1740jobs0 : List Job := [⟨plan5931,[⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5931,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5931,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1740jobs1 : List Job := [⟨plan5931,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,0⟩⟩,⟨plan5931,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1740jobs : List Job := t6_1740jobs0++t6_1740jobs1




def t6_1741root : Job := ⟨plan7692,[],none,⟨15,10,0⟩⟩
def t6_1741jobs0 : List Job := [⟨plan7692,[],none,⟨15,10,0⟩⟩]

def t6_1741jobs : List Job := t6_1741jobs0




def t6_1742root : Job := ⟨plan7693,[],none,⟨15,10,0⟩⟩
def t6_1742jobs0 : List Job := [⟨plan5933,[⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5933,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1742jobs1 : List Job := [⟨plan5933,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5933,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,0⟩⟩,⟨plan5933,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1742jobs : List Job := t6_1742jobs0++t6_1742jobs1




def t6_1743root : Job := ⟨plan7694,[],none,⟨15,10,0⟩⟩
def t6_1743jobs0 : List Job := [⟨plan5934,[⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5934,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1743jobs1 : List Job := [⟨plan5934,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5934,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,0⟩⟩]

def t6_1743jobs2 : List Job := [⟨plan5934,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1743jobs : List Job := t6_1743jobs0++t6_1743jobs1++t6_1743jobs2




def t6_1744root : Job := ⟨plan7695,[],none,⟨15,10,0⟩⟩
def t6_1744jobs0 : List Job := [⟨plan5935,[⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5935,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5935,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5935,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,0⟩⟩]

def t6_1744jobs1 : List Job := [⟨plan5935,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1744jobs : List Job := t6_1744jobs0++t6_1744jobs1




def t6_1745root : Job := ⟨plan7696,[],none,⟨15,10,0⟩⟩
def t6_1745jobs0 : List Job := [⟨plan7696,[],none,⟨15,10,0⟩⟩]

def t6_1745jobs : List Job := t6_1745jobs0




def t6_1746root : Job := ⟨plan8033,[],none,⟨15,15,0⟩⟩
def t6_1746jobs0 : List Job := [⟨plan8033,[],none,⟨15,15,0⟩⟩]

def t6_1746jobs : List Job := t6_1746jobs0




def t6_1747root : Job := ⟨plan8034,[],none,⟨15,15,0⟩⟩
def t6_1747jobs0 : List Job := [⟨plan8034,[],none,⟨15,15,0⟩⟩]

def t6_1747jobs : List Job := t6_1747jobs0




def t6_1748root : Job := ⟨plan8035,[],none,⟨15,15,0⟩⟩
def t6_1748jobs0 : List Job := [⟨plan8035,[],none,⟨15,15,0⟩⟩]

def t6_1748jobs : List Job := t6_1748jobs0




def t6_1749root : Job := ⟨plan8036,[],none,⟨15,15,0⟩⟩
def t6_1749jobs0 : List Job := [⟨plan8036,[],none,⟨15,15,0⟩⟩]

def t6_1749jobs : List Job := t6_1749jobs0




def t6_1750root : Job := ⟨plan8037,[],none,⟨15,15,0⟩⟩
def t6_1750jobs0 : List Job := [⟨plan8037,[],none,⟨15,15,0⟩⟩]

def t6_1750jobs : List Job := t6_1750jobs0




def t6_1751root : Job := ⟨plan8038,[],none,⟨15,15,0⟩⟩
def t6_1751jobs0 : List Job := [⟨plan8038,[],none,⟨15,15,0⟩⟩]

def t6_1751jobs : List Job := t6_1751jobs0




def t6_1752root : Job := ⟨plan8039,[],none,⟨15,15,0⟩⟩
def t6_1752jobs0 : List Job := [⟨plan8039,[],none,⟨15,15,0⟩⟩]

def t6_1752jobs : List Job := t6_1752jobs0




def t6_1753root : Job := ⟨plan8040,[],none,⟨15,15,0⟩⟩
def t6_1753jobs0 : List Job := [⟨plan8040,[],none,⟨15,15,0⟩⟩]

def t6_1753jobs : List Job := t6_1753jobs0




def t6_1754root : Job := ⟨plan8041,[],none,⟨15,15,0⟩⟩
def t6_1754jobs0 : List Job := [⟨plan8041,[],none,⟨15,15,0⟩⟩]

def t6_1754jobs : List Job := t6_1754jobs0




def t6_1755root : Job := ⟨plan8042,[],none,⟨15,15,0⟩⟩
def t6_1755jobs0 : List Job := [⟨plan8042,[],none,⟨15,15,0⟩⟩]

def t6_1755jobs : List Job := t6_1755jobs0




def t6_1756root : Job := ⟨plan8043,[],none,⟨15,15,0⟩⟩
def t6_1756jobs0 : List Job := [⟨plan8043,[],none,⟨15,15,0⟩⟩]

def t6_1756jobs : List Job := t6_1756jobs0




def t6_1757root : Job := ⟨plan6693,[],none,⟨15,3,0⟩⟩
def t6_1757jobs0 : List Job := [⟨plan6693,[],none,⟨15,3,0⟩⟩]

def t6_1757jobs : List Job := t6_1757jobs0




def t6_1758root : Job := ⟨plan7143,[],none,⟨15,6,0⟩⟩
def t6_1758jobs0 : List Job := [⟨plan7143,[],none,⟨15,6,0⟩⟩]

def t6_1758jobs : List Job := t6_1758jobs0




def t6_1759root : Job := ⟨plan7144,[],none,⟨15,6,0⟩⟩
def t6_1759jobs0 : List Job := [⟨plan7144,[],none,⟨15,6,0⟩⟩]

def t6_1759jobs : List Job := t6_1759jobs0




def t6_1760root : Job := ⟨plan7145,[],none,⟨15,6,0⟩⟩
def t6_1760jobs0 : List Job := [⟨plan7145,[],none,⟨15,6,0⟩⟩]

def t6_1760jobs : List Job := t6_1760jobs0




def t6_1761root : Job := ⟨plan7697,[],none,⟨15,10,0⟩⟩
def t6_1761jobs0 : List Job := [⟨plan7697,[],none,⟨15,10,0⟩⟩]

def t6_1761jobs : List Job := t6_1761jobs0




def t6_1762root : Job := ⟨plan7698,[],none,⟨15,10,0⟩⟩
def t6_1762jobs0 : List Job := [⟨plan7698,[],none,⟨15,10,0⟩⟩]

def t6_1762jobs : List Job := t6_1762jobs0




def t6_1763root : Job := ⟨plan7699,[],none,⟨15,10,0⟩⟩
def t6_1763jobs0 : List Job := [⟨plan7699,[],none,⟨15,10,0⟩⟩]

def t6_1763jobs : List Job := t6_1763jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


