-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks030
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks030
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:10.267318+00:00
-- url     : https://prove2.me/theorems/4bfceb77-5760-4da7-9d19-dda6fc490fa2
-- title:
--   Endpoint22 Reach Checks030 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks030 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_905root`, `ThreeBoundEndpoint22Reachable.t5_905jobs0`, `ThreeBoundEndpoint22Reachable.t5_905jobs`, `ThreeBoundEndpoint22Reachable.t5_906root`, `ThreeBoundEndpoint22Reachable.t5_906jobs0`, `ThreeBoundEndpoint22Reachable.t5_906jobs`, `ThreeBoundEndpoint22Reachable.t5_907root`, `ThreeBoundEndpoint22Reachable.t5_907jobs0`, `ThreeBoundEndpoint22Reachable.t5_907jobs`, `ThreeBoundEndpoint22Reachable.t5_908root`, `ThreeBoundEndpoint22Reachable.t5_908jobs0`, `ThreeBoundEndpoint22Reachable.t5_908jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks030.lean, lines 1–430.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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

def t5_892root : Job := ⟨plan4747,[],none,⟨10,6,0⟩⟩
def t5_892jobs0 : List Job := [⟨plan4747,[],none,⟨10,6,0⟩⟩]

def t5_892jobs : List Job := t5_892jobs0




def t5_893root : Job := ⟨plan3749,[],none,⟨10,0,0⟩⟩
def t5_893jobs0 : List Job := [⟨plan3749,[],none,⟨10,0,0⟩⟩]

def t5_893jobs : List Job := t5_893jobs0




def t5_894root : Job := ⟨plan3949,[],none,⟨10,1,0⟩⟩
def t5_894jobs0 : List Job := [⟨plan3949,[],none,⟨10,1,0⟩⟩]

def t5_894jobs : List Job := t5_894jobs0




def t5_895root : Job := ⟨plan3950,[],none,⟨10,1,0⟩⟩
def t5_895jobs0 : List Job := [⟨plan3950,[],none,⟨10,1,0⟩⟩]

def t5_895jobs : List Job := t5_895jobs0




def t5_896root : Job := ⟨plan3951,[],none,⟨10,1,0⟩⟩
def t5_896jobs0 : List Job := [⟨plan3951,[],none,⟨10,1,0⟩⟩]

def t5_896jobs : List Job := t5_896jobs0




def t5_897root : Job := ⟨plan3750,[],none,⟨10,0,0⟩⟩
def t5_897jobs0 : List Job := [⟨plan3750,[],none,⟨10,0,0⟩⟩]

def t5_897jobs : List Job := t5_897jobs0




def t5_898root : Job := ⟨plan3952,[],none,⟨10,1,0⟩⟩
def t5_898jobs0 : List Job := [⟨plan3952,[],none,⟨10,1,0⟩⟩]

def t5_898jobs : List Job := t5_898jobs0




def t5_899root : Job := ⟨plan3953,[],none,⟨10,1,0⟩⟩
def t5_899jobs0 : List Job := [⟨plan3953,[],none,⟨10,1,0⟩⟩]

def t5_899jobs : List Job := t5_899jobs0




def t5_900root : Job := ⟨plan3954,[],none,⟨10,1,0⟩⟩
def t5_900jobs0 : List Job := [⟨plan3954,[],none,⟨10,1,0⟩⟩]

def t5_900jobs : List Job := t5_900jobs0




def t5_901root : Job := ⟨plan3955,[],none,⟨10,1,0⟩⟩
def t5_901jobs0 : List Job := [⟨plan3955,[],none,⟨10,1,0⟩⟩]

def t5_901jobs : List Job := t5_901jobs0




def t5_902root : Job := ⟨plan4314,[],none,⟨10,3,0⟩⟩
def t5_902jobs0 : List Job := [⟨plan4314,[],none,⟨10,3,0⟩⟩]

def t5_902jobs : List Job := t5_902jobs0




def t5_903root : Job := ⟨plan4315,[],none,⟨10,3,0⟩⟩
def t5_903jobs0 : List Job := [⟨plan4315,[],none,⟨10,3,0⟩⟩]

def t5_903jobs : List Job := t5_903jobs0




def t5_904root : Job := ⟨plan4316,[],none,⟨10,3,0⟩⟩
def t5_904jobs0 : List Job := [⟨plan4316,[],none,⟨10,3,0⟩⟩]

def t5_904jobs : List Job := t5_904jobs0




def t5_905root : Job := ⟨plan4317,[],none,⟨10,3,0⟩⟩
def t5_905jobs0 : List Job := [⟨plan4317,[],none,⟨10,3,0⟩⟩]

def t5_905jobs : List Job := t5_905jobs0




def t5_906root : Job := ⟨plan4318,[],none,⟨10,3,0⟩⟩
def t5_906jobs0 : List Job := [⟨plan4318,[],none,⟨10,3,0⟩⟩]

def t5_906jobs : List Job := t5_906jobs0




def t5_907root : Job := ⟨plan4319,[],none,⟨10,3,0⟩⟩
def t5_907jobs0 : List Job := [⟨plan4319,[],none,⟨10,3,0⟩⟩]

def t5_907jobs : List Job := t5_907jobs0




def t5_908root : Job := ⟨plan4320,[],none,⟨10,3,0⟩⟩
def t5_908jobs0 : List Job := [⟨plan4320,[],none,⟨10,3,0⟩⟩]

def t5_908jobs : List Job := t5_908jobs0




def t5_909root : Job := ⟨plan3956,[],none,⟨10,1,0⟩⟩
def t5_909jobs0 : List Job := [⟨plan3956,[],none,⟨10,1,0⟩⟩]

def t5_909jobs : List Job := t5_909jobs0




def t5_910root : Job := ⟨plan4321,[],none,⟨10,3,0⟩⟩
def t5_910jobs0 : List Job := [⟨plan4321,[],none,⟨10,3,0⟩⟩]

def t5_910jobs : List Job := t5_910jobs0




def t5_911root : Job := ⟨plan4322,[],none,⟨10,3,0⟩⟩
def t5_911jobs0 : List Job := [⟨plan4322,[],none,⟨10,3,0⟩⟩]

def t5_911jobs : List Job := t5_911jobs0




def t5_912root : Job := ⟨plan4323,[],none,⟨10,3,0⟩⟩
def t5_912jobs0 : List Job := [⟨plan4323,[],none,⟨10,3,0⟩⟩]

def t5_912jobs : List Job := t5_912jobs0




def t5_913root : Job := ⟨plan4324,[],none,⟨10,3,0⟩⟩
def t5_913jobs0 : List Job := [⟨plan4324,[],none,⟨10,3,0⟩⟩]

def t5_913jobs : List Job := t5_913jobs0




def t5_914root : Job := ⟨plan4325,[],none,⟨10,3,0⟩⟩
def t5_914jobs0 : List Job := [⟨plan4325,[],none,⟨10,3,0⟩⟩]

def t5_914jobs : List Job := t5_914jobs0




def t5_915root : Job := ⟨plan3751,[],none,⟨10,0,0⟩⟩
def t5_915jobs0 : List Job := [⟨plan3751,[],none,⟨10,0,0⟩⟩]

def t5_915jobs : List Job := t5_915jobs0




def t5_916root : Job := ⟨plan3957,[],none,⟨10,1,0⟩⟩
def t5_916jobs0 : List Job := [⟨plan3957,[],none,⟨10,1,0⟩⟩]

def t5_916jobs : List Job := t5_916jobs0




def t5_917root : Job := ⟨plan3958,[],none,⟨10,1,0⟩⟩
def t5_917jobs0 : List Job := [⟨plan2608,[⟨4,0,1⟩],(some ⟨4,0,1⟩),⟨10,0,(-1)⟩⟩,⟨plan2608,[⟨4,1,0⟩],(some ⟨4,1,0⟩),⟨9,1,1⟩⟩]

def t5_917jobs1 : List Job := [⟨plan2608,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨9,0,0⟩⟩]

def t5_917jobs : List Job := t5_917jobs0++t5_917jobs1




def t5_918root : Job := ⟨plan3959,[],none,⟨10,1,0⟩⟩
def t5_918jobs0 : List Job := [⟨plan3959,[],none,⟨10,1,0⟩⟩]

def t5_918jobs : List Job := t5_918jobs0




def t5_919root : Job := ⟨plan4326,[],none,⟨10,3,0⟩⟩
def t5_919jobs0 : List Job := [⟨plan4326,[],none,⟨10,3,0⟩⟩]

def t5_919jobs : List Job := t5_919jobs0




def t5_920root : Job := ⟨plan4327,[],none,⟨10,3,0⟩⟩
def t5_920jobs0 : List Job := [⟨plan2713,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2713,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨9,2,0⟩⟩]

def t5_920jobs1 : List Job := [⟨plan2713,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_920jobs : List Job := t5_920jobs0++t5_920jobs1




def t5_921root : Job := ⟨plan4328,[],none,⟨10,3,0⟩⟩
def t5_921jobs0 : List Job := [⟨plan2714,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2714,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨9,2,0⟩⟩]

def t5_921jobs1 : List Job := [⟨plan2714,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_921jobs : List Job := t5_921jobs0++t5_921jobs1




def t5_922root : Job := ⟨plan4329,[],none,⟨10,3,0⟩⟩
def t5_922jobs0 : List Job := [⟨plan4329,[],none,⟨10,3,0⟩⟩]

def t5_922jobs : List Job := t5_922jobs0




def t5_923root : Job := ⟨plan4330,[],none,⟨10,3,0⟩⟩
def t5_923jobs0 : List Job := [⟨plan2716,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2716,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨9,2,0⟩⟩]

def t5_923jobs1 : List Job := [⟨plan2716,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_923jobs : List Job := t5_923jobs0++t5_923jobs1




def t5_924root : Job := ⟨plan4331,[],none,⟨10,3,0⟩⟩
def t5_924jobs0 : List Job := [⟨plan4331,[],none,⟨10,3,0⟩⟩]

def t5_924jobs : List Job := t5_924jobs0




def t5_925root : Job := ⟨plan3960,[],none,⟨10,1,0⟩⟩
def t5_925jobs0 : List Job := [⟨plan3960,[],none,⟨10,1,0⟩⟩]

def t5_925jobs : List Job := t5_925jobs0




def t5_926root : Job := ⟨plan4332,[],none,⟨10,3,0⟩⟩
def t5_926jobs0 : List Job := [⟨plan4332,[],none,⟨10,3,0⟩⟩]

def t5_926jobs : List Job := t5_926jobs0




def t5_927root : Job := ⟨plan4333,[],none,⟨10,3,0⟩⟩
def t5_927jobs0 : List Job := [⟨plan4333,[],none,⟨10,3,0⟩⟩]

def t5_927jobs : List Job := t5_927jobs0




def t5_928root : Job := ⟨plan4334,[],none,⟨10,3,0⟩⟩
def t5_928jobs0 : List Job := [⟨plan4334,[],none,⟨10,3,0⟩⟩]

def t5_928jobs : List Job := t5_928jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


