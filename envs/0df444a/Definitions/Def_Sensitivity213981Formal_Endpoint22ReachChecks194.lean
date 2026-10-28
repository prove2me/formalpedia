-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks194
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks194
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:35:55.404627+00:00
-- url     : https://prove2.me/theorems/2f865f24-4bf3-4a3e-84f5-9bdf7e51e9ec
-- title:
--   Endpoint22 Reach Checks194 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks194 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t8_23jobs`, `ThreeBoundEndpoint22Reachable.t8_24root`, `ThreeBoundEndpoint22Reachable.t8_24jobs0`, `ThreeBoundEndpoint22Reachable.t8_24jobs`, `ThreeBoundEndpoint22Reachable.t8_25root`, `ThreeBoundEndpoint22Reachable.t8_25jobs0`, `ThreeBoundEndpoint22Reachable.t8_25jobs`, `ThreeBoundEndpoint22Reachable.t8_11root`, `ThreeBoundEndpoint22Reachable.t8_26root`, `ThreeBoundEndpoint22Reachable.t8_26jobs0`, `ThreeBoundEndpoint22Reachable.t8_26jobs`, `ThreeBoundEndpoint22Reachable.t8_11jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks194.lean, lines 1–837.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans095
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans096
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

def t8_10root : Job := ⟨plan9194,[],none,⟨28,21,0⟩⟩
def t8_10jobs0 : List Job := [⟨plan9194,[],none,⟨28,21,0⟩⟩]

def t8_10jobs : List Job := t8_10jobs0




def t8_11root : Job := ⟨plan9195,[],none,⟨28,21,0⟩⟩
def t8_11jobs0 : List Job := [⟨plan9195,[],none,⟨28,21,0⟩⟩]

def t8_11jobs : List Job := t8_11jobs0




def t8_12root : Job := ⟨plan9196,[],none,⟨28,21,0⟩⟩
def t8_12jobs0 : List Job := [⟨plan9196,[],none,⟨28,21,0⟩⟩]

def t8_12jobs : List Job := t8_12jobs0




def t8_13root : Job := ⟨plan9197,[],none,⟨28,21,0⟩⟩
def t8_13jobs0 : List Job := [⟨plan9197,[],none,⟨28,21,0⟩⟩]

def t8_13jobs : List Job := t8_13jobs0




def t8_14root : Job := ⟨plan9198,[],none,⟨28,21,0⟩⟩
def t8_14jobs0 : List Job := [⟨plan9198,[],none,⟨28,21,0⟩⟩]

def t8_14jobs : List Job := t8_14jobs0




def t8_15root : Job := ⟨plan9199,[],none,⟨28,21,0⟩⟩
def t8_15jobs0 : List Job := [⟨plan9199,[],none,⟨28,21,0⟩⟩]

def t8_15jobs : List Job := t8_15jobs0




def t8_16root : Job := ⟨plan9200,[],none,⟨28,21,0⟩⟩
def t8_16jobs0 : List Job := [⟨plan9200,[],none,⟨28,21,0⟩⟩]

def t8_16jobs : List Job := t8_16jobs0




def t8_17root : Job := ⟨plan9201,[],none,⟨28,21,0⟩⟩
def t8_17jobs0 : List Job := [⟨plan9201,[],none,⟨28,21,0⟩⟩]

def t8_17jobs : List Job := t8_17jobs0




def t8_18root : Job := ⟨plan9172,[],none,⟨28,6,0⟩⟩
def t8_18jobs0 : List Job := [⟨plan9172,[],none,⟨28,6,0⟩⟩]

def t8_18jobs : List Job := t8_18jobs0




def t8_19root : Job := ⟨plan9174,[],none,⟨28,10,0⟩⟩
def t8_19jobs0 : List Job := [⟨plan9174,[],none,⟨28,10,0⟩⟩]

def t8_19jobs : List Job := t8_19jobs0




def t8_20root : Job := ⟨plan9175,[],none,⟨28,10,0⟩⟩
def t8_20jobs0 : List Job := [⟨plan9175,[],none,⟨28,10,0⟩⟩]

def t8_20jobs : List Job := t8_20jobs0




def t8_21root : Job := ⟨plan9176,[],none,⟨28,10,0⟩⟩
def t8_21jobs0 : List Job := [⟨plan9176,[],none,⟨28,10,0⟩⟩]

def t8_21jobs : List Job := t8_21jobs0




def t8_22root : Job := ⟨plan9182,[],none,⟨28,15,0⟩⟩
def t8_22jobs0 : List Job := [⟨plan9182,[],none,⟨28,15,0⟩⟩]

def t8_22jobs : List Job := t8_22jobs0




def t8_23root : Job := ⟨plan9183,[],none,⟨28,15,0⟩⟩
def t8_23jobs0 : List Job := [⟨plan9183,[],none,⟨28,15,0⟩⟩]

def t8_23jobs : List Job := t8_23jobs0




def t8_24root : Job := ⟨plan9184,[],none,⟨28,15,0⟩⟩
def t8_24jobs0 : List Job := [⟨plan9184,[],none,⟨28,15,0⟩⟩]

def t8_24jobs : List Job := t8_24jobs0




def t8_25root : Job := ⟨plan9185,[],none,⟨28,15,0⟩⟩
def t8_25jobs0 : List Job := [⟨plan9185,[],none,⟨28,15,0⟩⟩]

def t8_25jobs : List Job := t8_25jobs0




def t8_26root : Job := ⟨plan9186,[],none,⟨28,15,0⟩⟩
def t8_26jobs0 : List Job := [⟨plan9186,[],none,⟨28,15,0⟩⟩]

def t8_26jobs : List Job := t8_26jobs0




def t8_27root : Job := ⟨plan9187,[],none,⟨28,15,0⟩⟩
def t8_27jobs0 : List Job := [⟨plan9187,[],none,⟨28,15,0⟩⟩]

def t8_27jobs : List Job := t8_27jobs0




def t8_28root : Job := ⟨plan9202,[],none,⟨28,21,0⟩⟩
def t8_28jobs0 : List Job := [⟨plan9202,[],none,⟨28,21,0⟩⟩]

def t8_28jobs : List Job := t8_28jobs0




def t8_29root : Job := ⟨plan9203,[],none,⟨28,21,0⟩⟩
def t8_29jobs0 : List Job := [⟨plan9203,[],none,⟨28,21,0⟩⟩]

def t8_29jobs : List Job := t8_29jobs0




def t8_30root : Job := ⟨plan9204,[],none,⟨28,21,0⟩⟩
def t8_30jobs0 : List Job := [⟨plan9204,[],none,⟨28,21,0⟩⟩]

def t8_30jobs : List Job := t8_30jobs0




def t8_31root : Job := ⟨plan9205,[],none,⟨28,21,0⟩⟩
def t8_31jobs0 : List Job := [⟨plan9205,[],none,⟨28,21,0⟩⟩]

def t8_31jobs : List Job := t8_31jobs0




def t8_32root : Job := ⟨plan9206,[],none,⟨28,21,0⟩⟩
def t8_32jobs0 : List Job := [⟨plan9206,[],none,⟨28,21,0⟩⟩]

def t8_32jobs : List Job := t8_32jobs0




def t8_33root : Job := ⟨plan9207,[],none,⟨28,21,0⟩⟩
def t8_33jobs0 : List Job := [⟨plan9207,[],none,⟨28,21,0⟩⟩]

def t8_33jobs : List Job := t8_33jobs0




def t8_34root : Job := ⟨plan9208,[],none,⟨28,21,0⟩⟩
def t8_34jobs0 : List Job := [⟨plan9208,[],none,⟨28,21,0⟩⟩]

def t8_34jobs : List Job := t8_34jobs0




def t8_35root : Job := ⟨plan9209,[],none,⟨28,21,0⟩⟩
def t8_35jobs0 : List Job := [⟨plan9209,[],none,⟨28,21,0⟩⟩]

def t8_35jobs : List Job := t8_35jobs0




def t8_36root : Job := ⟨plan9210,[],none,⟨28,21,0⟩⟩
def t8_36jobs0 : List Job := [⟨plan9210,[],none,⟨28,21,0⟩⟩]

def t8_36jobs : List Job := t8_36jobs0




def t8_37root : Job := ⟨plan9211,[],none,⟨28,21,0⟩⟩
def t8_37jobs0 : List Job := [⟨plan9211,[],none,⟨28,21,0⟩⟩]

def t8_37jobs : List Job := t8_37jobs0




def t8_38root : Job := ⟨plan9212,[],none,⟨28,21,0⟩⟩
def t8_38jobs0 : List Job := [⟨plan9212,[],none,⟨28,21,0⟩⟩]

def t8_38jobs : List Job := t8_38jobs0




def t8_39root : Job := ⟨plan9220,[],none,⟨28,28,0⟩⟩
def t8_39jobs0 : List Job := [⟨plan9220,[],none,⟨28,28,0⟩⟩]

def t8_39jobs : List Job := t8_39jobs0




def t8_40root : Job := ⟨plan9221,[],none,⟨28,28,0⟩⟩
def t8_40jobs0 : List Job := [⟨plan9221,[],none,⟨28,28,0⟩⟩]

def t8_40jobs : List Job := t8_40jobs0




def t8_41root : Job := ⟨plan9222,[],none,⟨28,28,0⟩⟩
def t8_41jobs0 : List Job := [⟨plan9222,[],none,⟨28,28,0⟩⟩]

def t8_41jobs : List Job := t8_41jobs0




def t8_42root : Job := ⟨plan9188,[],none,⟨28,15,0⟩⟩
def t8_42jobs0 : List Job := [⟨plan9188,[],none,⟨28,15,0⟩⟩]

def t8_42jobs : List Job := t8_42jobs0




def t8_43root : Job := ⟨plan9213,[],none,⟨28,21,0⟩⟩
def t8_43jobs0 : List Job := [⟨plan9213,[],none,⟨28,21,0⟩⟩]

def t8_43jobs : List Job := t8_43jobs0




def t8_44root : Job := ⟨plan9214,[],none,⟨28,21,0⟩⟩
def t8_44jobs0 : List Job := [⟨plan9214,[],none,⟨28,21,0⟩⟩]

def t8_44jobs : List Job := t8_44jobs0




def t8_45root : Job := ⟨plan9215,[],none,⟨28,21,0⟩⟩
def t8_45jobs0 : List Job := [⟨plan9215,[],none,⟨28,21,0⟩⟩]

def t8_45jobs : List Job := t8_45jobs0




def t8_46root : Job := ⟨plan9223,[],none,⟨28,28,0⟩⟩
def t8_46jobs0 : List Job := [⟨plan9223,[],none,⟨28,28,0⟩⟩]

def t8_46jobs : List Job := t8_46jobs0




def t8_47root : Job := ⟨plan9224,[],none,⟨28,28,0⟩⟩
def t8_47jobs0 : List Job := [⟨plan9224,[],none,⟨28,28,0⟩⟩]

def t8_47jobs : List Job := t8_47jobs0




def t8_48root : Job := ⟨plan9225,[],none,⟨28,28,0⟩⟩
def t8_48jobs0 : List Job := [⟨plan9225,[],none,⟨28,28,0⟩⟩]

def t8_48jobs : List Job := t8_48jobs0




def t8_49root : Job := ⟨plan9226,[],none,⟨28,28,0⟩⟩
def t8_49jobs0 : List Job := [⟨plan9226,[],none,⟨28,28,0⟩⟩]

def t8_49jobs : List Job := t8_49jobs0




def t8_50root : Job := ⟨plan9227,[],none,⟨28,28,0⟩⟩
def t8_50jobs0 : List Job := [⟨plan9227,[],none,⟨28,28,0⟩⟩]

def t8_50jobs : List Job := t8_50jobs0




def t8_51root : Job := ⟨plan9228,[],none,⟨28,28,0⟩⟩
def t8_51jobs0 : List Job := [⟨plan9228,[],none,⟨28,28,0⟩⟩]

def t8_51jobs : List Job := t8_51jobs0




def t8_52root : Job := ⟨plan9229,[],none,⟨28,28,0⟩⟩
def t8_52jobs0 : List Job := [⟨plan9229,[],none,⟨28,28,0⟩⟩]

def t8_52jobs : List Job := t8_52jobs0




def t8_53root : Job := ⟨plan9230,[],none,⟨28,28,0⟩⟩
def t8_53jobs0 : List Job := [⟨plan9230,[],none,⟨28,28,0⟩⟩]

def t8_53jobs : List Job := t8_53jobs0




def t8_54root : Job := ⟨plan9231,[],none,⟨28,28,0⟩⟩
def t8_54jobs0 : List Job := [⟨plan9231,[],none,⟨28,28,0⟩⟩]

def t8_54jobs : List Job := t8_54jobs0




def t8_55root : Job := ⟨plan9232,[],none,⟨28,28,0⟩⟩
def t8_55jobs0 : List Job := [⟨plan9232,[],none,⟨28,28,0⟩⟩]

def t8_55jobs : List Job := t8_55jobs0




def t8_56root : Job := ⟨plan9233,[],none,⟨28,28,0⟩⟩
def t8_56jobs0 : List Job := [⟨plan9233,[],none,⟨28,28,0⟩⟩]

def t8_56jobs : List Job := t8_56jobs0




def t8_57root : Job := ⟨plan9234,[],none,⟨28,28,0⟩⟩
def t8_57jobs0 : List Job := [⟨plan9234,[],none,⟨28,28,0⟩⟩]

def t8_57jobs : List Job := t8_57jobs0




def t8_58root : Job := ⟨plan9235,[],none,⟨28,28,0⟩⟩
def t8_58jobs0 : List Job := [⟨plan9235,[],none,⟨28,28,0⟩⟩]

def t8_58jobs : List Job := t8_58jobs0




def t8_59root : Job := ⟨plan9236,[],none,⟨28,28,0⟩⟩
def t8_59jobs0 : List Job := [⟨plan9236,[],none,⟨28,28,0⟩⟩]

def t8_59jobs : List Job := t8_59jobs0




def t8_60root : Job := ⟨plan9237,[],none,⟨28,28,0⟩⟩
def t8_60jobs0 : List Job := [⟨plan9237,[],none,⟨28,28,0⟩⟩]

def t8_60jobs : List Job := t8_60jobs0




def t8_61root : Job := ⟨plan9238,[],none,⟨28,28,0⟩⟩
def t8_61jobs0 : List Job := [⟨plan9238,[],none,⟨28,28,0⟩⟩]

def t8_61jobs : List Job := t8_61jobs0




def t8_62root : Job := ⟨plan9239,[],none,⟨28,28,0⟩⟩
def t8_62jobs0 : List Job := [⟨plan9239,[],none,⟨28,28,0⟩⟩]

def t8_62jobs : List Job := t8_62jobs0




def t8_63root : Job := ⟨plan9240,[],none,⟨28,28,0⟩⟩
def t8_63jobs0 : List Job := [⟨plan9240,[],none,⟨28,28,0⟩⟩]

def t8_63jobs : List Job := t8_63jobs0




def t8_64root : Job := ⟨plan9241,[],none,⟨28,28,0⟩⟩
def t8_64jobs0 : List Job := [⟨plan9241,[],none,⟨28,28,0⟩⟩]

def t8_64jobs : List Job := t8_64jobs0




def t8_65root : Job := ⟨plan9216,[],none,⟨28,21,0⟩⟩
def t8_65jobs0 : List Job := [⟨plan9216,[],none,⟨28,21,0⟩⟩]

def t8_65jobs : List Job := t8_65jobs0




def t8_66root : Job := ⟨plan9242,[],none,⟨28,28,0⟩⟩
def t8_66jobs0 : List Job := [⟨plan9242,[],none,⟨28,28,0⟩⟩]

def t8_66jobs : List Job := t8_66jobs0




def t8_67root : Job := ⟨plan9243,[],none,⟨28,28,0⟩⟩
def t8_67jobs0 : List Job := [⟨plan9243,[],none,⟨28,28,0⟩⟩]

def t8_67jobs : List Job := t8_67jobs0




def t8_68root : Job := ⟨plan9244,[],none,⟨28,28,0⟩⟩
def t8_68jobs0 : List Job := [⟨plan9244,[],none,⟨28,28,0⟩⟩]

def t8_68jobs : List Job := t8_68jobs0




def t8_69root : Job := ⟨plan9189,[],none,⟨28,15,0⟩⟩
def t8_69jobs0 : List Job := [⟨plan9189,[],none,⟨28,15,0⟩⟩]

def t8_69jobs : List Job := t8_69jobs0




def t8_70root : Job := ⟨plan9217,[],none,⟨28,21,0⟩⟩
def t8_70jobs0 : List Job := [⟨plan9217,[],none,⟨28,21,0⟩⟩]

def t8_70jobs : List Job := t8_70jobs0




def t8_71root : Job := ⟨plan9218,[],none,⟨28,21,0⟩⟩
def t8_71jobs0 : List Job := [⟨plan9218,[],none,⟨28,21,0⟩⟩]

def t8_71jobs : List Job := t8_71jobs0




def t8_72root : Job := ⟨plan9219,[],none,⟨28,21,0⟩⟩
def t8_72jobs0 : List Job := [⟨plan9219,[],none,⟨28,21,0⟩⟩]

def t8_72jobs : List Job := t8_72jobs0




def t8_73root : Job := ⟨plan9245,[],none,⟨28,28,0⟩⟩
def t8_73jobs0 : List Job := [⟨plan9245,[],none,⟨28,28,0⟩⟩]

def t8_73jobs : List Job := t8_73jobs0




def t8_74root : Job := ⟨plan9246,[],none,⟨28,28,0⟩⟩
def t8_74jobs0 : List Job := [⟨plan9246,[],none,⟨28,28,0⟩⟩]

def t8_74jobs : List Job := t8_74jobs0




def t8_75root : Job := ⟨plan9247,[],none,⟨28,28,0⟩⟩
def t8_75jobs0 : List Job := [⟨plan9247,[],none,⟨28,28,0⟩⟩]

def t8_75jobs : List Job := t8_75jobs0




def t8_76root : Job := ⟨plan9248,[],none,⟨28,28,0⟩⟩
def t8_76jobs0 : List Job := [⟨plan9248,[],none,⟨28,28,0⟩⟩]

def t8_76jobs : List Job := t8_76jobs0




def t8_77root : Job := ⟨plan9249,[],none,⟨28,28,0⟩⟩
def t8_77jobs0 : List Job := [⟨plan9249,[],none,⟨28,28,0⟩⟩]

def t8_77jobs : List Job := t8_77jobs0




def t8_78root : Job := ⟨plan9250,[],none,⟨28,28,0⟩⟩
def t8_78jobs0 : List Job := [⟨plan9250,[],none,⟨28,28,0⟩⟩]

def t8_78jobs : List Job := t8_78jobs0




def t8_79root : Job := ⟨plan9251,[],none,⟨28,28,0⟩⟩
def t8_79jobs0 : List Job := [⟨plan9251,[],none,⟨28,28,0⟩⟩]

def t8_79jobs : List Job := t8_79jobs0




def t8_80root : Job := ⟨plan9252,[],none,⟨28,28,0⟩⟩
def t8_80jobs0 : List Job := [⟨plan9252,[],none,⟨28,28,0⟩⟩]

def t8_80jobs : List Job := t8_80jobs0




def t8_81root : Job := ⟨plan9253,[],none,⟨28,28,0⟩⟩
def t8_81jobs0 : List Job := [⟨plan9253,[],none,⟨28,28,0⟩⟩]

def t8_81jobs : List Job := t8_81jobs0




def t8_82root : Job := ⟨plan9254,[],none,⟨28,28,0⟩⟩
def t8_82jobs0 : List Job := [⟨plan9254,[],none,⟨28,28,0⟩⟩]

def t8_82jobs : List Job := t8_82jobs0




def t8_83root : Job := ⟨plan9255,[],none,⟨28,28,0⟩⟩
def t8_83jobs0 : List Job := [⟨plan9255,[],none,⟨28,28,0⟩⟩]

def t8_83jobs : List Job := t8_83jobs0




def t9_0root : Job := ⟨plan9257,[],none,⟨36,36,0⟩⟩
def t9_0jobs0 : List Job := [⟨plan9257,[],none,⟨36,36,0⟩⟩]

def t9_0jobs : List Job := t9_0jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


