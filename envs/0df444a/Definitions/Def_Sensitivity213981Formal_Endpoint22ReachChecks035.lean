-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks035
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks035
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:10.603185+00:00
-- url     : https://prove2.me/theorems/fe682757-cc6b-46ea-956b-8e5395a72ac4
-- title:
--   Endpoint22 Reach Checks035 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks035 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1220jobs3`, `ThreeBoundEndpoint22Reachable.t5_1220jobs`, `ThreeBoundEndpoint22Reachable.t5_1213jobs`, `ThreeBoundEndpoint22Reachable.t5_1221root`, `ThreeBoundEndpoint22Reachable.t5_1221jobs0`, `ThreeBoundEndpoint22Reachable.t5_1221jobs1`, `ThreeBoundEndpoint22Reachable.t5_1221jobs`, `ThreeBoundEndpoint22Reachable.t5_1214root`, `ThreeBoundEndpoint22Reachable.t5_1214jobs0`, `ThreeBoundEndpoint22Reachable.t5_1214jobs1`, `ThreeBoundEndpoint22Reachable.t5_1214jobs`, `ThreeBoundEndpoint22Reachable.t5_1215root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks035.lean, lines 1–141.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
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

def t5_1213root : Job := ⟨plan3971,[],none,⟨10,1,0⟩⟩
def t5_1213jobs0 : List Job := [⟨plan2627,[⟨5,0,1⟩],(some ⟨5,0,1⟩),⟨10,0,(-1)⟩⟩,⟨plan2627,[⟨5,1,0⟩],(some ⟨5,1,0⟩),⟨9,1,1⟩⟩,⟨plan2627,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,0,0⟩⟩,⟨plan2627,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,1,2⟩⟩]

def t5_1213jobs1 : List Job := [⟨plan2627,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,0,1⟩⟩]

def t5_1213jobs : List Job := t5_1213jobs0++t5_1213jobs1




def t5_1214root : Job := ⟨plan3972,[],none,⟨10,1,0⟩⟩
def t5_1214jobs0 : List Job := [⟨plan2628,[⟨5,0,1⟩],(some ⟨5,0,1⟩),⟨10,0,(-1)⟩⟩,⟨plan2628,[⟨5,1,0⟩],(some ⟨5,1,0⟩),⟨9,1,1⟩⟩,⟨plan2628,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,0,0⟩⟩,⟨plan2628,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,1,2⟩⟩]

def t5_1214jobs1 : List Job := [⟨plan2628,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,0,1⟩⟩]

def t5_1214jobs : List Job := t5_1214jobs0++t5_1214jobs1




def t5_1215root : Job := ⟨plan3973,[],none,⟨10,1,0⟩⟩
def t5_1215jobs0 : List Job := [⟨plan2629,[⟨5,0,1⟩],(some ⟨5,0,1⟩),⟨10,0,(-1)⟩⟩,⟨plan2629,[⟨5,1,0⟩],(some ⟨5,1,0⟩),⟨9,1,1⟩⟩,⟨plan2629,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,0,0⟩⟩,⟨plan2629,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,1,2⟩⟩]

def t5_1215jobs1 : List Job := [⟨plan2629,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,0,1⟩⟩]

def t5_1215jobs : List Job := t5_1215jobs0++t5_1215jobs1




def t5_1216root : Job := ⟨plan4374,[],none,⟨10,3,0⟩⟩
def t5_1216jobs0 : List Job := [⟨plan2762,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2762,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩,⟨plan2762,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2762,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩]

def t5_1216jobs1 : List Job := [⟨plan2762,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩,⟨plan2762,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1216jobs : List Job := t5_1216jobs0++t5_1216jobs1




def t5_1217root : Job := ⟨plan4375,[],none,⟨10,3,0⟩⟩
def t5_1217jobs0 : List Job := [⟨plan2763,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2763,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩]

def t5_1217jobs1 : List Job := [⟨plan2763,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2763,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩]

def t5_1217jobs2 : List Job := [⟨plan2763,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩]

def t5_1217jobs3 : List Job := [⟨plan2763,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1217jobs : List Job := t5_1217jobs0++t5_1217jobs1++t5_1217jobs2++t5_1217jobs3




def t5_1218root : Job := ⟨plan4376,[],none,⟨10,3,0⟩⟩
def t5_1218jobs0 : List Job := [⟨plan2764,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2764,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩,⟨plan2764,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1218jobs1 : List Job := [⟨plan2764,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩,⟨plan2764,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩]

def t5_1218jobs2 : List Job := [⟨plan2764,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1218jobs : List Job := t5_1218jobs0++t5_1218jobs1++t5_1218jobs2




def t5_1219root : Job := ⟨plan4377,[],none,⟨10,3,0⟩⟩
def t5_1219jobs0 : List Job := [⟨plan2765,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2765,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩,⟨plan2765,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1219jobs1 : List Job := [⟨plan2765,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩,⟨plan2765,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩]

def t5_1219jobs2 : List Job := [⟨plan2765,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1219jobs : List Job := t5_1219jobs0++t5_1219jobs1++t5_1219jobs2




def t5_1220root : Job := ⟨plan4378,[],none,⟨10,3,0⟩⟩
def t5_1220jobs0 : List Job := [⟨plan2766,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2766,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩]

def t5_1220jobs1 : List Job := [⟨plan2766,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2766,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩]

def t5_1220jobs2 : List Job := [⟨plan2766,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩]

def t5_1220jobs3 : List Job := [⟨plan2766,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1220jobs : List Job := t5_1220jobs0++t5_1220jobs1++t5_1220jobs2++t5_1220jobs3




def t5_1221root : Job := ⟨plan4379,[],none,⟨10,3,0⟩⟩
def t5_1221jobs0 : List Job := [⟨plan2767,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2767,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩,⟨plan2767,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2767,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩]

def t5_1221jobs1 : List Job := [⟨plan2767,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩,⟨plan2767,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1221jobs : List Job := t5_1221jobs0++t5_1221jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


