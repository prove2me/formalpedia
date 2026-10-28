-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks157
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks157
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:30:36.193644+00:00
-- url     : https://prove2.me/theorems/43f6791e-1bd8-4be5-ba3a-b69931712226
-- title:
--   Endpoint22 Reach Checks157 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks157 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_84jobs`, `ThreeBoundEndpoint22Reachable.t7_85root`, `ThreeBoundEndpoint22Reachable.t7_85jobs0`, `ThreeBoundEndpoint22Reachable.t7_85jobs`, `ThreeBoundEndpoint22Reachable.t7_86root`, `ThreeBoundEndpoint22Reachable.t7_86jobs0`, `ThreeBoundEndpoint22Reachable.t7_86jobs`, `ThreeBoundEndpoint22Reachable.t7_87root`, `ThreeBoundEndpoint22Reachable.t7_87jobs0`, `ThreeBoundEndpoint22Reachable.t7_87jobs`, `ThreeBoundEndpoint22Reachable.t7_88root`, `ThreeBoundEndpoint22Reachable.t7_72root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks157.lean, lines 1–633.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans091
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

def t7_71root : Job := ⟨plan8579,[],none,⟨21,10,0⟩⟩
def t7_71jobs0 : List Job := [⟨plan8579,[],none,⟨21,10,0⟩⟩]

def t7_71jobs : List Job := t7_71jobs0




def t7_72root : Job := ⟨plan8580,[],none,⟨21,10,0⟩⟩
def t7_72jobs0 : List Job := [⟨plan8580,[],none,⟨21,10,0⟩⟩]

def t7_72jobs : List Job := t7_72jobs0




def t7_73root : Job := ⟨plan8726,[],none,⟨21,15,0⟩⟩
def t7_73jobs0 : List Job := [⟨plan8726,[],none,⟨21,15,0⟩⟩]

def t7_73jobs : List Job := t7_73jobs0




def t7_74root : Job := ⟨plan8727,[],none,⟨21,15,0⟩⟩
def t7_74jobs0 : List Job := [⟨plan8727,[],none,⟨21,15,0⟩⟩]

def t7_74jobs : List Job := t7_74jobs0




def t7_75root : Job := ⟨plan8728,[],none,⟨21,15,0⟩⟩
def t7_75jobs0 : List Job := [⟨plan8728,[],none,⟨21,15,0⟩⟩]

def t7_75jobs : List Job := t7_75jobs0




def t7_76root : Job := ⟨plan8480,[],none,⟨21,6,0⟩⟩
def t7_76jobs0 : List Job := [⟨plan8480,[],none,⟨21,6,0⟩⟩]

def t7_76jobs : List Job := t7_76jobs0




def t7_77root : Job := ⟨plan8581,[],none,⟨21,10,0⟩⟩
def t7_77jobs0 : List Job := [⟨plan8581,[],none,⟨21,10,0⟩⟩]

def t7_77jobs : List Job := t7_77jobs0




def t7_78root : Job := ⟨plan8582,[],none,⟨21,10,0⟩⟩
def t7_78jobs0 : List Job := [⟨plan8582,[],none,⟨21,10,0⟩⟩]

def t7_78jobs : List Job := t7_78jobs0




def t7_79root : Job := ⟨plan8583,[],none,⟨21,10,0⟩⟩
def t7_79jobs0 : List Job := [⟨plan8583,[],none,⟨21,10,0⟩⟩]

def t7_79jobs : List Job := t7_79jobs0




def t7_80root : Job := ⟨plan8729,[],none,⟨21,15,0⟩⟩
def t7_80jobs0 : List Job := [⟨plan8729,[],none,⟨21,15,0⟩⟩]

def t7_80jobs : List Job := t7_80jobs0




def t7_81root : Job := ⟨plan8730,[],none,⟨21,15,0⟩⟩
def t7_81jobs0 : List Job := [⟨plan8730,[],none,⟨21,15,0⟩⟩]

def t7_81jobs : List Job := t7_81jobs0




def t7_82root : Job := ⟨plan8731,[],none,⟨21,15,0⟩⟩
def t7_82jobs0 : List Job := [⟨plan8731,[],none,⟨21,15,0⟩⟩]

def t7_82jobs : List Job := t7_82jobs0




def t7_83root : Job := ⟨plan8732,[],none,⟨21,15,0⟩⟩
def t7_83jobs0 : List Job := [⟨plan8732,[],none,⟨21,15,0⟩⟩]

def t7_83jobs : List Job := t7_83jobs0




def t7_84root : Job := ⟨plan8733,[],none,⟨21,15,0⟩⟩
def t7_84jobs0 : List Job := [⟨plan8733,[],none,⟨21,15,0⟩⟩]

def t7_84jobs : List Job := t7_84jobs0




def t7_85root : Job := ⟨plan8734,[],none,⟨21,15,0⟩⟩
def t7_85jobs0 : List Job := [⟨plan8734,[],none,⟨21,15,0⟩⟩]

def t7_85jobs : List Job := t7_85jobs0




def t7_86root : Job := ⟨plan8735,[],none,⟨21,15,0⟩⟩
def t7_86jobs0 : List Job := [⟨plan8735,[],none,⟨21,15,0⟩⟩]

def t7_86jobs : List Job := t7_86jobs0




def t7_87root : Job := ⟨plan8736,[],none,⟨21,15,0⟩⟩
def t7_87jobs0 : List Job := [⟨plan8736,[],none,⟨21,15,0⟩⟩]

def t7_87jobs : List Job := t7_87jobs0




def t7_88root : Job := ⟨plan8737,[],none,⟨21,15,0⟩⟩
def t7_88jobs0 : List Job := [⟨plan8737,[],none,⟨21,15,0⟩⟩]

def t7_88jobs : List Job := t7_88jobs0




def t7_89root : Job := ⟨plan8738,[],none,⟨21,15,0⟩⟩
def t7_89jobs0 : List Job := [⟨plan8738,[],none,⟨21,15,0⟩⟩]

def t7_89jobs : List Job := t7_89jobs0




def t7_90root : Job := ⟨plan8739,[],none,⟨21,15,0⟩⟩
def t7_90jobs0 : List Job := [⟨plan8739,[],none,⟨21,15,0⟩⟩]

def t7_90jobs : List Job := t7_90jobs0




def t7_91root : Job := ⟨plan8740,[],none,⟨21,15,0⟩⟩
def t7_91jobs0 : List Job := [⟨plan8740,[],none,⟨21,15,0⟩⟩]

def t7_91jobs : List Job := t7_91jobs0




def t7_92root : Job := ⟨plan8741,[],none,⟨21,15,0⟩⟩
def t7_92jobs0 : List Job := [⟨plan8741,[],none,⟨21,15,0⟩⟩]

def t7_92jobs : List Job := t7_92jobs0




def t7_93root : Job := ⟨plan8742,[],none,⟨21,15,0⟩⟩
def t7_93jobs0 : List Job := [⟨plan8742,[],none,⟨21,15,0⟩⟩]

def t7_93jobs : List Job := t7_93jobs0




def t7_94root : Job := ⟨plan8743,[],none,⟨21,15,0⟩⟩
def t7_94jobs0 : List Job := [⟨plan8743,[],none,⟨21,15,0⟩⟩]

def t7_94jobs : List Job := t7_94jobs0




def t7_95root : Job := ⟨plan8744,[],none,⟨21,15,0⟩⟩
def t7_95jobs0 : List Job := [⟨plan8744,[],none,⟨21,15,0⟩⟩]

def t7_95jobs : List Job := t7_95jobs0




def t7_96root : Job := ⟨plan8745,[],none,⟨21,15,0⟩⟩
def t7_96jobs0 : List Job := [⟨plan8745,[],none,⟨21,15,0⟩⟩]

def t7_96jobs : List Job := t7_96jobs0




def t7_97root : Job := ⟨plan8746,[],none,⟨21,15,0⟩⟩
def t7_97jobs0 : List Job := [⟨plan8746,[],none,⟨21,15,0⟩⟩]

def t7_97jobs : List Job := t7_97jobs0




def t7_98root : Job := ⟨plan8747,[],none,⟨21,15,0⟩⟩
def t7_98jobs0 : List Job := [⟨plan8747,[],none,⟨21,15,0⟩⟩]

def t7_98jobs : List Job := t7_98jobs0




def t7_99root : Job := ⟨plan8584,[],none,⟨21,10,0⟩⟩
def t7_99jobs0 : List Job := [⟨plan8584,[],none,⟨21,10,0⟩⟩]

def t7_99jobs : List Job := t7_99jobs0




def t7_100root : Job := ⟨plan8748,[],none,⟨21,15,0⟩⟩
def t7_100jobs0 : List Job := [⟨plan8748,[],none,⟨21,15,0⟩⟩]

def t7_100jobs : List Job := t7_100jobs0




def t7_101root : Job := ⟨plan8749,[],none,⟨21,15,0⟩⟩
def t7_101jobs0 : List Job := [⟨plan8749,[],none,⟨21,15,0⟩⟩]

def t7_101jobs : List Job := t7_101jobs0




def t7_102root : Job := ⟨plan8750,[],none,⟨21,15,0⟩⟩
def t7_102jobs0 : List Job := [⟨plan8750,[],none,⟨21,15,0⟩⟩]

def t7_102jobs : List Job := t7_102jobs0




def t7_103root : Job := ⟨plan8481,[],none,⟨21,6,0⟩⟩
def t7_103jobs0 : List Job := [⟨plan8481,[],none,⟨21,6,0⟩⟩]

def t7_103jobs : List Job := t7_103jobs0




def t7_104root : Job := ⟨plan8585,[],none,⟨21,10,0⟩⟩
def t7_104jobs0 : List Job := [⟨plan8585,[],none,⟨21,10,0⟩⟩]

def t7_104jobs : List Job := t7_104jobs0




def t7_105root : Job := ⟨plan8586,[],none,⟨21,10,0⟩⟩
def t7_105jobs0 : List Job := [⟨plan8586,[],none,⟨21,10,0⟩⟩]

def t7_105jobs : List Job := t7_105jobs0




def t7_106root : Job := ⟨plan8587,[],none,⟨21,10,0⟩⟩
def t7_106jobs0 : List Job := [⟨plan8587,[],none,⟨21,10,0⟩⟩]

def t7_106jobs : List Job := t7_106jobs0




def t7_107root : Job := ⟨plan8751,[],none,⟨21,15,0⟩⟩
def t7_107jobs0 : List Job := [⟨plan8751,[],none,⟨21,15,0⟩⟩]

def t7_107jobs : List Job := t7_107jobs0




def t7_108root : Job := ⟨plan8752,[],none,⟨21,15,0⟩⟩
def t7_108jobs0 : List Job := [⟨plan8752,[],none,⟨21,15,0⟩⟩]

def t7_108jobs : List Job := t7_108jobs0




def t7_109root : Job := ⟨plan8753,[],none,⟨21,15,0⟩⟩
def t7_109jobs0 : List Job := [⟨plan8753,[],none,⟨21,15,0⟩⟩]

def t7_109jobs : List Job := t7_109jobs0




def t7_110root : Job := ⟨plan8754,[],none,⟨21,15,0⟩⟩
def t7_110jobs0 : List Job := [⟨plan8754,[],none,⟨21,15,0⟩⟩]

def t7_110jobs : List Job := t7_110jobs0




def t7_111root : Job := ⟨plan8755,[],none,⟨21,15,0⟩⟩
def t7_111jobs0 : List Job := [⟨plan8755,[],none,⟨21,15,0⟩⟩]

def t7_111jobs : List Job := t7_111jobs0




def t7_112root : Job := ⟨plan8756,[],none,⟨21,15,0⟩⟩
def t7_112jobs0 : List Job := [⟨plan8756,[],none,⟨21,15,0⟩⟩]

def t7_112jobs : List Job := t7_112jobs0




def t7_113root : Job := ⟨plan8757,[],none,⟨21,15,0⟩⟩
def t7_113jobs0 : List Job := [⟨plan8757,[],none,⟨21,15,0⟩⟩]

def t7_113jobs : List Job := t7_113jobs0




def t7_114root : Job := ⟨plan8758,[],none,⟨21,15,0⟩⟩
def t7_114jobs0 : List Job := [⟨plan8758,[],none,⟨21,15,0⟩⟩]

def t7_114jobs : List Job := t7_114jobs0




def t7_115root : Job := ⟨plan8759,[],none,⟨21,15,0⟩⟩
def t7_115jobs0 : List Job := [⟨plan8759,[],none,⟨21,15,0⟩⟩]

def t7_115jobs : List Job := t7_115jobs0




def t7_116root : Job := ⟨plan8760,[],none,⟨21,15,0⟩⟩
def t7_116jobs0 : List Job := [⟨plan8760,[],none,⟨21,15,0⟩⟩]

def t7_116jobs : List Job := t7_116jobs0




def t7_117root : Job := ⟨plan8761,[],none,⟨21,15,0⟩⟩
def t7_117jobs0 : List Job := [⟨plan8761,[],none,⟨21,15,0⟩⟩]

def t7_117jobs : List Job := t7_117jobs0




def t7_118root : Job := ⟨plan8435,[],none,⟨21,3,0⟩⟩
def t7_118jobs0 : List Job := [⟨plan8435,[],none,⟨21,3,0⟩⟩]

def t7_118jobs : List Job := t7_118jobs0




def t7_119root : Job := ⟨plan8482,[],none,⟨21,6,0⟩⟩
def t7_119jobs0 : List Job := [⟨plan8482,[],none,⟨21,6,0⟩⟩]

def t7_119jobs : List Job := t7_119jobs0




def t7_120root : Job := ⟨plan8483,[],none,⟨21,6,0⟩⟩
def t7_120jobs0 : List Job := [⟨plan8483,[],none,⟨21,6,0⟩⟩]

def t7_120jobs : List Job := t7_120jobs0




def t7_121root : Job := ⟨plan8484,[],none,⟨21,6,0⟩⟩
def t7_121jobs0 : List Job := [⟨plan8484,[],none,⟨21,6,0⟩⟩]

def t7_121jobs : List Job := t7_121jobs0




def t7_122root : Job := ⟨plan8418,[],none,⟨21,1,0⟩⟩
def t7_122jobs0 : List Job := [⟨plan8418,[],none,⟨21,1,0⟩⟩]

def t7_122jobs : List Job := t7_122jobs0




def t7_123root : Job := ⟨plan8436,[],none,⟨21,3,0⟩⟩
def t7_123jobs0 : List Job := [⟨plan8436,[],none,⟨21,3,0⟩⟩]

def t7_123jobs : List Job := t7_123jobs0




def t7_124root : Job := ⟨plan8437,[],none,⟨21,3,0⟩⟩
def t7_124jobs0 : List Job := [⟨plan8086,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8086,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8086,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,3,(-3)⟩⟩,⟨plan8086,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨19,3,(-1)⟩⟩]

def t7_124jobs1 : List Job := [⟨plan8086,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,3,(-2)⟩⟩,⟨plan8086,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_124jobs : List Job := t7_124jobs0++t7_124jobs1




def t7_125root : Job := ⟨plan8438,[],none,⟨21,3,0⟩⟩
def t7_125jobs0 : List Job := [⟨plan8438,[],none,⟨21,3,0⟩⟩]

def t7_125jobs : List Job := t7_125jobs0




def t7_126root : Job := ⟨plan8485,[],none,⟨21,6,0⟩⟩
def t7_126jobs0 : List Job := [⟨plan8485,[],none,⟨21,6,0⟩⟩]

def t7_126jobs : List Job := t7_126jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


