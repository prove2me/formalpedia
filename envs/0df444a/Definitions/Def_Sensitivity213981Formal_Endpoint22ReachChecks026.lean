-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks026
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks026
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:07.541664+00:00
-- url     : https://prove2.me/theorems/c8cf544c-c42f-4c1c-92c1-18ca95eceb68
-- title:
--   Endpoint22 Reach Checks026 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks026 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_852root`, `ThreeBoundEndpoint22Reachable.t5_852jobs0`, `ThreeBoundEndpoint22Reachable.t5_852jobs1`, `ThreeBoundEndpoint22Reachable.t5_852jobs`, `ThreeBoundEndpoint22Reachable.t5_853root`, `ThreeBoundEndpoint22Reachable.t5_853jobs0`, `ThreeBoundEndpoint22Reachable.t5_853jobs`, `ThreeBoundEndpoint22Reachable.t5_854root`, `ThreeBoundEndpoint22Reachable.t5_854jobs0`, `ThreeBoundEndpoint22Reachable.t5_854jobs1`, `ThreeBoundEndpoint22Reachable.t5_854jobs`, `ThreeBoundEndpoint22Reachable.t5_840root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks026.lean, lines 1–313.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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

def t5_839root : Job := ⟨plan4302,[],none,⟨10,3,0⟩⟩
def t5_839jobs0 : List Job := [⟨plan4302,[],none,⟨10,3,0⟩⟩]

def t5_839jobs : List Job := t5_839jobs0




def t5_840root : Job := ⟨plan4716,[],none,⟨10,6,0⟩⟩
def t5_840jobs0 : List Job := [⟨plan4716,[],none,⟨10,6,0⟩⟩]

def t5_840jobs : List Job := t5_840jobs0




def t5_841root : Job := ⟨plan4717,[],none,⟨10,6,0⟩⟩
def t5_841jobs0 : List Job := [⟨plan4717,[],none,⟨10,6,0⟩⟩]

def t5_841jobs : List Job := t5_841jobs0




def t5_842root : Job := ⟨plan4718,[],none,⟨10,6,0⟩⟩
def t5_842jobs0 : List Job := [⟨plan4718,[],none,⟨10,6,0⟩⟩]

def t5_842jobs : List Job := t5_842jobs0




def t5_843root : Job := ⟨plan4719,[],none,⟨10,6,0⟩⟩
def t5_843jobs0 : List Job := [⟨plan4719,[],none,⟨10,6,0⟩⟩]

def t5_843jobs : List Job := t5_843jobs0




def t5_844root : Job := ⟨plan4303,[],none,⟨10,3,0⟩⟩
def t5_844jobs0 : List Job := [⟨plan4303,[],none,⟨10,3,0⟩⟩]

def t5_844jobs : List Job := t5_844jobs0




def t5_845root : Job := ⟨plan4720,[],none,⟨10,6,0⟩⟩
def t5_845jobs0 : List Job := [⟨plan4720,[],none,⟨10,6,0⟩⟩]

def t5_845jobs : List Job := t5_845jobs0




def t5_846root : Job := ⟨plan4721,[],none,⟨10,6,0⟩⟩
def t5_846jobs0 : List Job := [⟨plan4721,[],none,⟨10,6,0⟩⟩]

def t5_846jobs : List Job := t5_846jobs0




def t5_847root : Job := ⟨plan4722,[],none,⟨10,6,0⟩⟩
def t5_847jobs0 : List Job := [⟨plan4722,[],none,⟨10,6,0⟩⟩]

def t5_847jobs : List Job := t5_847jobs0




def t5_848root : Job := ⟨plan4723,[],none,⟨10,6,0⟩⟩
def t5_848jobs0 : List Job := [⟨plan4723,[],none,⟨10,6,0⟩⟩]

def t5_848jobs : List Job := t5_848jobs0




def t5_849root : Job := ⟨plan4724,[],none,⟨10,6,0⟩⟩
def t5_849jobs0 : List Job := [⟨plan4724,[],none,⟨10,6,0⟩⟩]

def t5_849jobs : List Job := t5_849jobs0




def t5_850root : Job := ⟨plan4725,[],none,⟨10,6,0⟩⟩
def t5_850jobs0 : List Job := [⟨plan4725,[],none,⟨10,6,0⟩⟩]

def t5_850jobs : List Job := t5_850jobs0




def t5_851root : Job := ⟨plan4726,[],none,⟨10,6,0⟩⟩
def t5_851jobs0 : List Job := [⟨plan3104,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3104,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_851jobs1 : List Job := [⟨plan3104,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_851jobs : List Job := t5_851jobs0++t5_851jobs1




def t5_852root : Job := ⟨plan4727,[],none,⟨10,6,0⟩⟩
def t5_852jobs0 : List Job := [⟨plan3105,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3105,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_852jobs1 : List Job := [⟨plan3105,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_852jobs : List Job := t5_852jobs0++t5_852jobs1




def t5_853root : Job := ⟨plan4728,[],none,⟨10,6,0⟩⟩
def t5_853jobs0 : List Job := [⟨plan4728,[],none,⟨10,6,0⟩⟩]

def t5_853jobs : List Job := t5_853jobs0




def t5_854root : Job := ⟨plan4729,[],none,⟨10,6,0⟩⟩
def t5_854jobs0 : List Job := [⟨plan3107,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3107,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_854jobs1 : List Job := [⟨plan3107,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_854jobs : List Job := t5_854jobs0++t5_854jobs1




def t5_855root : Job := ⟨plan4730,[],none,⟨10,6,0⟩⟩
def t5_855jobs0 : List Job := [⟨plan3108,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3108,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_855jobs1 : List Job := [⟨plan3108,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_855jobs : List Job := t5_855jobs0++t5_855jobs1




def t5_856root : Job := ⟨plan4731,[],none,⟨10,6,0⟩⟩
def t5_856jobs0 : List Job := [⟨plan4731,[],none,⟨10,6,0⟩⟩]

def t5_856jobs : List Job := t5_856jobs0




def t5_857root : Job := ⟨plan4732,[],none,⟨10,6,0⟩⟩
def t5_857jobs0 : List Job := [⟨plan4732,[],none,⟨10,6,0⟩⟩]

def t5_857jobs : List Job := t5_857jobs0




def t5_858root : Job := ⟨plan3673,[],none,⟨10,0,0⟩⟩
def t5_858jobs0 : List Job := [⟨plan3673,[],none,⟨10,0,0⟩⟩]

def t5_858jobs : List Job := t5_858jobs0




def t5_859root : Job := ⟨plan3746,[],none,⟨10,0,0⟩⟩
def t5_859jobs0 : List Job := [⟨plan3746,[],none,⟨10,0,0⟩⟩]

def t5_859jobs : List Job := t5_859jobs0




def t5_860root : Job := ⟨plan3747,[],none,⟨10,0,0⟩⟩
def t5_860jobs0 : List Job := [⟨plan3747,[],none,⟨10,0,0⟩⟩]

def t5_860jobs : List Job := t5_860jobs0




def t5_861root : Job := ⟨plan3748,[],none,⟨10,0,0⟩⟩
def t5_861jobs0 : List Job := [⟨plan3748,[],none,⟨10,0,0⟩⟩]

def t5_861jobs : List Job := t5_861jobs0




def t5_862root : Job := ⟨plan3943,[],none,⟨10,1,0⟩⟩
def t5_862jobs0 : List Job := [⟨plan3943,[],none,⟨10,1,0⟩⟩]

def t5_862jobs : List Job := t5_862jobs0




def t5_863root : Job := ⟨plan3944,[],none,⟨10,1,0⟩⟩
def t5_863jobs0 : List Job := [⟨plan2631,[⟨3,0,2⟩],(some ⟨3,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2631,[⟨3,1,1⟩],(some ⟨3,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2631,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_863jobs1 : List Job := [⟨plan2631,[⟨3,2,0⟩],(some ⟨3,2,0⟩),⟨8,1,0⟩⟩,⟨plan2631,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2631,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,1,(-2)⟩⟩,⟨plan2631,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,1,0⟩⟩,⟨plan2631,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,1,(-1)⟩⟩]

def t5_863jobs : List Job := t5_863jobs0++t5_863jobs1




def t5_864root : Job := ⟨plan3945,[],none,⟨10,1,0⟩⟩
def t5_864jobs0 : List Job := [⟨plan2632,[⟨3,0,2⟩],(some ⟨3,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2632,[⟨3,1,1⟩],(some ⟨3,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2632,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2632,[⟨3,2,0⟩],(some ⟨3,2,0⟩),⟨8,1,0⟩⟩]

def t5_864jobs1 : List Job := [⟨plan2632,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2632,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,1,(-2)⟩⟩,⟨plan2632,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,1,0⟩⟩,⟨plan2632,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,1,(-1)⟩⟩]

def t5_864jobs : List Job := t5_864jobs0++t5_864jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


