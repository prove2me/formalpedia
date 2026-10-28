-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks000
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks000
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:59.870102+00:00
-- url     : https://prove2.me/theorems/a98796be-a732-4cc4-aa2d-dfc430621af3
-- title:
--   Endpoint22 Reach Checks000 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks000 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t3_68root`, `ThreeBoundEndpoint22Reachable.t3_68jobs0`, `ThreeBoundEndpoint22Reachable.t3_68jobs`, `ThreeBoundEndpoint22Reachable.t2_2jobs0`, `ThreeBoundEndpoint22Reachable.t3_69root`, `ThreeBoundEndpoint22Reachable.t3_69jobs0`, `ThreeBoundEndpoint22Reachable.t3_69jobs`, `ThreeBoundEndpoint22Reachable.t3_70root`, `ThreeBoundEndpoint22Reachable.t3_70jobs0`, `ThreeBoundEndpoint22Reachable.t3_70jobs`, `ThreeBoundEndpoint22Reachable.t2_2jobs`, `ThreeBoundEndpoint22Reachable.t3_71root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks000.lean, lines 1–6171.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans018
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans019
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans021
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

def t0_0root : Job := ⟨plan0,[],none,⟨0,0,0⟩⟩
def t0_0jobs0 : List Job := [⟨plan0,[],none,⟨0,0,0⟩⟩]

def t0_0jobs : List Job := t0_0jobs0




def t1_0root : Job := ⟨plan1,[],none,⟨0,0,0⟩⟩
def t1_0jobs0 : List Job := [⟨plan1,[],none,⟨0,0,0⟩⟩]

def t1_0jobs : List Job := t1_0jobs0




def t1_1root : Job := ⟨plan2,[],none,⟨0,0,0⟩⟩
def t1_1jobs0 : List Job := [⟨plan2,[],none,⟨0,0,0⟩⟩]

def t1_1jobs : List Job := t1_1jobs0




def t1_2root : Job := ⟨plan3,[],none,⟨0,0,0⟩⟩
def t1_2jobs0 : List Job := [⟨plan3,[],none,⟨0,0,0⟩⟩]

def t1_2jobs : List Job := t1_2jobs0




def t1_3root : Job := ⟨plan4,[],none,⟨0,0,0⟩⟩
def t1_3jobs0 : List Job := [⟨plan4,[],none,⟨0,0,0⟩⟩]

def t1_3jobs : List Job := t1_3jobs0




def t1_4root : Job := ⟨plan5,[],none,⟨0,0,0⟩⟩
def t1_4jobs0 : List Job := [⟨plan5,[],none,⟨0,0,0⟩⟩]

def t1_4jobs : List Job := t1_4jobs0




def t1_5root : Job := ⟨plan6,[],none,⟨0,0,0⟩⟩
def t1_5jobs0 : List Job := [⟨plan6,[],none,⟨0,0,0⟩⟩]

def t1_5jobs : List Job := t1_5jobs0




def t1_6root : Job := ⟨plan7,[],none,⟨0,0,0⟩⟩
def t1_6jobs0 : List Job := [⟨plan7,[],none,⟨0,0,0⟩⟩]

def t1_6jobs : List Job := t1_6jobs0




def t1_7root : Job := ⟨plan8,[],none,⟨0,0,0⟩⟩
def t1_7jobs0 : List Job := [⟨plan8,[],none,⟨0,0,0⟩⟩]

def t1_7jobs : List Job := t1_7jobs0




def t1_8root : Job := ⟨plan9,[],none,⟨0,0,0⟩⟩
def t1_8jobs0 : List Job := [⟨plan9,[],none,⟨0,0,0⟩⟩]

def t1_8jobs : List Job := t1_8jobs0




def t1_9root : Job := ⟨plan10,[],none,⟨0,0,0⟩⟩
def t1_9jobs0 : List Job := [⟨plan10,[],none,⟨0,0,0⟩⟩]

def t1_9jobs : List Job := t1_9jobs0




def t1_10root : Job := ⟨plan11,[],none,⟨0,0,0⟩⟩
def t1_10jobs0 : List Job := [⟨plan11,[],none,⟨0,0,0⟩⟩]

def t1_10jobs : List Job := t1_10jobs0




def t2_0root : Job := ⟨plan167,[],none,⟨1,0,0⟩⟩
def t2_0jobs0 : List Job := [⟨plan167,[],none,⟨1,0,0⟩⟩]

def t2_0jobs : List Job := t2_0jobs0




def t2_1root : Job := ⟨plan168,[],none,⟨1,0,0⟩⟩
def t2_1jobs0 : List Job := [⟨plan168,[],none,⟨1,0,0⟩⟩]

def t2_1jobs : List Job := t2_1jobs0




def t2_2root : Job := ⟨plan169,[],none,⟨1,0,0⟩⟩
def t2_2jobs0 : List Job := [⟨plan169,[],none,⟨1,0,0⟩⟩]

def t2_2jobs : List Job := t2_2jobs0




def t2_3root : Job := ⟨plan176,[],none,⟨1,0,0⟩⟩
def t2_3jobs0 : List Job := [⟨plan176,[],none,⟨1,0,0⟩⟩]

def t2_3jobs : List Job := t2_3jobs0




def t2_4root : Job := ⟨plan177,[],none,⟨1,0,0⟩⟩
def t2_4jobs0 : List Job := [⟨plan177,[],none,⟨1,0,0⟩⟩]

def t2_4jobs : List Job := t2_4jobs0




def t2_5root : Job := ⟨plan178,[],none,⟨1,0,0⟩⟩
def t2_5jobs0 : List Job := [⟨plan178,[],none,⟨1,0,0⟩⟩]

def t2_5jobs : List Job := t2_5jobs0




def t2_6root : Job := ⟨plan179,[],none,⟨1,0,0⟩⟩
def t2_6jobs0 : List Job := [⟨plan179,[],none,⟨1,0,0⟩⟩]

def t2_6jobs : List Job := t2_6jobs0




def t2_7root : Job := ⟨plan180,[],none,⟨1,0,0⟩⟩
def t2_7jobs0 : List Job := [⟨plan180,[],none,⟨1,0,0⟩⟩]

def t2_7jobs : List Job := t2_7jobs0




def t2_8root : Job := ⟨plan181,[],none,⟨1,0,0⟩⟩
def t2_8jobs0 : List Job := [⟨plan181,[],none,⟨1,0,0⟩⟩]

def t2_8jobs : List Job := t2_8jobs0




def t2_9root : Job := ⟨plan182,[],none,⟨1,0,0⟩⟩
def t2_9jobs0 : List Job := [⟨plan182,[],none,⟨1,0,0⟩⟩]

def t2_9jobs : List Job := t2_9jobs0




def t2_10root : Job := ⟨plan170,[],none,⟨1,0,0⟩⟩
def t2_10jobs0 : List Job := [⟨plan170,[],none,⟨1,0,0⟩⟩]

def t2_10jobs : List Job := t2_10jobs0




def t2_11root : Job := ⟨plan171,[],none,⟨1,0,0⟩⟩
def t2_11jobs0 : List Job := [⟨plan171,[],none,⟨1,0,0⟩⟩]

def t2_11jobs : List Job := t2_11jobs0




def t2_12root : Job := ⟨plan172,[],none,⟨1,0,0⟩⟩
def t2_12jobs0 : List Job := [⟨plan172,[],none,⟨1,0,0⟩⟩]

def t2_12jobs : List Job := t2_12jobs0




def t2_13root : Job := ⟨plan183,[],none,⟨1,0,0⟩⟩
def t2_13jobs0 : List Job := [⟨plan183,[],none,⟨1,0,0⟩⟩]

def t2_13jobs : List Job := t2_13jobs0




def t2_14root : Job := ⟨plan184,[],none,⟨1,0,0⟩⟩
def t2_14jobs0 : List Job := [⟨plan184,[],none,⟨1,0,0⟩⟩]

def t2_14jobs : List Job := t2_14jobs0




def t2_15root : Job := ⟨plan185,[],none,⟨1,0,0⟩⟩
def t2_15jobs0 : List Job := [⟨plan185,[],none,⟨1,0,0⟩⟩]

def t2_15jobs : List Job := t2_15jobs0




def t2_16root : Job := ⟨plan186,[],none,⟨1,0,0⟩⟩
def t2_16jobs0 : List Job := [⟨plan186,[],none,⟨1,0,0⟩⟩]

def t2_16jobs : List Job := t2_16jobs0




def t2_17root : Job := ⟨plan187,[],none,⟨1,0,0⟩⟩
def t2_17jobs0 : List Job := [⟨plan187,[],none,⟨1,0,0⟩⟩]

def t2_17jobs : List Job := t2_17jobs0




def t2_18root : Job := ⟨plan188,[],none,⟨1,0,0⟩⟩
def t2_18jobs0 : List Job := [⟨plan188,[],none,⟨1,0,0⟩⟩]

def t2_18jobs : List Job := t2_18jobs0




def t2_19root : Job := ⟨plan189,[],none,⟨1,0,0⟩⟩
def t2_19jobs0 : List Job := [⟨plan189,[],none,⟨1,0,0⟩⟩]

def t2_19jobs : List Job := t2_19jobs0




def t2_20root : Job := ⟨plan173,[],none,⟨1,0,0⟩⟩
def t2_20jobs0 : List Job := [⟨plan173,[],none,⟨1,0,0⟩⟩]

def t2_20jobs : List Job := t2_20jobs0




def t2_21root : Job := ⟨plan174,[],none,⟨1,0,0⟩⟩
def t2_21jobs0 : List Job := [⟨plan174,[],none,⟨1,0,0⟩⟩]

def t2_21jobs : List Job := t2_21jobs0




def t2_22root : Job := ⟨plan190,[],none,⟨1,0,0⟩⟩
def t2_22jobs0 : List Job := [⟨plan190,[],none,⟨1,0,0⟩⟩]

def t2_22jobs : List Job := t2_22jobs0




def t2_23root : Job := ⟨plan191,[],none,⟨1,0,0⟩⟩
def t2_23jobs0 : List Job := [⟨plan191,[],none,⟨1,0,0⟩⟩]

def t2_23jobs : List Job := t2_23jobs0




def t2_24root : Job := ⟨plan192,[],none,⟨1,0,0⟩⟩
def t2_24jobs0 : List Job := [⟨plan192,[],none,⟨1,0,0⟩⟩]

def t2_24jobs : List Job := t2_24jobs0




def t2_25root : Job := ⟨plan193,[],none,⟨1,0,0⟩⟩
def t2_25jobs0 : List Job := [⟨plan193,[],none,⟨1,0,0⟩⟩]

def t2_25jobs : List Job := t2_25jobs0




def t2_26root : Job := ⟨plan194,[],none,⟨1,0,0⟩⟩
def t2_26jobs0 : List Job := [⟨plan194,[],none,⟨1,0,0⟩⟩]

def t2_26jobs : List Job := t2_26jobs0




def t2_27root : Job := ⟨plan175,[],none,⟨1,0,0⟩⟩
def t2_27jobs0 : List Job := [⟨plan175,[],none,⟨1,0,0⟩⟩]

def t2_27jobs : List Job := t2_27jobs0




def t2_28root : Job := ⟨plan195,[],none,⟨1,0,0⟩⟩
def t2_28jobs0 : List Job := [⟨plan195,[],none,⟨1,0,0⟩⟩]

def t2_28jobs : List Job := t2_28jobs0




def t2_29root : Job := ⟨plan196,[],none,⟨1,0,0⟩⟩
def t2_29jobs0 : List Job := [⟨plan196,[],none,⟨1,0,0⟩⟩]

def t2_29jobs : List Job := t2_29jobs0




def t2_30root : Job := ⟨plan197,[],none,⟨1,0,0⟩⟩
def t2_30jobs0 : List Job := [⟨plan197,[],none,⟨1,0,0⟩⟩]

def t2_30jobs : List Job := t2_30jobs0




def t2_31root : Job := ⟨plan198,[],none,⟨1,0,0⟩⟩
def t2_31jobs0 : List Job := [⟨plan198,[],none,⟨1,0,0⟩⟩]

def t2_31jobs : List Job := t2_31jobs0




def t2_32root : Job := ⟨plan199,[],none,⟨1,0,0⟩⟩
def t2_32jobs0 : List Job := [⟨plan199,[],none,⟨1,0,0⟩⟩]

def t2_32jobs : List Job := t2_32jobs0




def t2_33root : Job := ⟨plan204,[],none,⟨1,1,0⟩⟩
def t2_33jobs0 : List Job := [⟨plan204,[],none,⟨1,1,0⟩⟩]

def t2_33jobs : List Job := t2_33jobs0




def t2_34root : Job := ⟨plan205,[],none,⟨1,1,0⟩⟩
def t2_34jobs0 : List Job := [⟨plan205,[],none,⟨1,1,0⟩⟩]

def t2_34jobs : List Job := t2_34jobs0




def t2_35root : Job := ⟨plan206,[],none,⟨1,1,0⟩⟩
def t2_35jobs0 : List Job := [⟨plan206,[],none,⟨1,1,0⟩⟩]

def t2_35jobs : List Job := t2_35jobs0




def t2_36root : Job := ⟨plan207,[],none,⟨1,1,0⟩⟩
def t2_36jobs0 : List Job := [⟨plan207,[],none,⟨1,1,0⟩⟩]

def t2_36jobs : List Job := t2_36jobs0




def t2_37root : Job := ⟨plan208,[],none,⟨1,1,0⟩⟩
def t2_37jobs0 : List Job := [⟨plan208,[],none,⟨1,1,0⟩⟩]

def t2_37jobs : List Job := t2_37jobs0




def t2_38root : Job := ⟨plan209,[],none,⟨1,1,0⟩⟩
def t2_38jobs0 : List Job := [⟨plan209,[],none,⟨1,1,0⟩⟩]

def t2_38jobs : List Job := t2_38jobs0




def t2_39root : Job := ⟨plan210,[],none,⟨1,1,0⟩⟩
def t2_39jobs0 : List Job := [⟨plan210,[],none,⟨1,1,0⟩⟩]

def t2_39jobs : List Job := t2_39jobs0




def t2_40root : Job := ⟨plan200,[],none,⟨1,0,0⟩⟩
def t2_40jobs0 : List Job := [⟨plan200,[],none,⟨1,0,0⟩⟩]

def t2_40jobs : List Job := t2_40jobs0




def t2_41root : Job := ⟨plan211,[],none,⟨1,1,0⟩⟩
def t2_41jobs0 : List Job := [⟨plan211,[],none,⟨1,1,0⟩⟩]

def t2_41jobs : List Job := t2_41jobs0




def t2_42root : Job := ⟨plan212,[],none,⟨1,1,0⟩⟩
def t2_42jobs0 : List Job := [⟨plan212,[],none,⟨1,1,0⟩⟩]

def t2_42jobs : List Job := t2_42jobs0




def t2_43root : Job := ⟨plan213,[],none,⟨1,1,0⟩⟩
def t2_43jobs0 : List Job := [⟨plan213,[],none,⟨1,1,0⟩⟩]

def t2_43jobs : List Job := t2_43jobs0




def t2_44root : Job := ⟨plan214,[],none,⟨1,1,0⟩⟩
def t2_44jobs0 : List Job := [⟨plan214,[],none,⟨1,1,0⟩⟩]

def t2_44jobs : List Job := t2_44jobs0




def t2_45root : Job := ⟨plan215,[],none,⟨1,1,0⟩⟩
def t2_45jobs0 : List Job := [⟨plan215,[],none,⟨1,1,0⟩⟩]

def t2_45jobs : List Job := t2_45jobs0




def t2_46root : Job := ⟨plan216,[],none,⟨1,1,0⟩⟩
def t2_46jobs0 : List Job := [⟨plan216,[],none,⟨1,1,0⟩⟩]

def t2_46jobs : List Job := t2_46jobs0




def t2_47root : Job := ⟨plan217,[],none,⟨1,1,0⟩⟩
def t2_47jobs0 : List Job := [⟨plan217,[],none,⟨1,1,0⟩⟩]

def t2_47jobs : List Job := t2_47jobs0




def t2_48root : Job := ⟨plan218,[],none,⟨1,1,0⟩⟩
def t2_48jobs0 : List Job := [⟨plan218,[],none,⟨1,1,0⟩⟩]

def t2_48jobs : List Job := t2_48jobs0




def t2_49root : Job := ⟨plan219,[],none,⟨1,1,0⟩⟩
def t2_49jobs0 : List Job := [⟨plan219,[],none,⟨1,1,0⟩⟩]

def t2_49jobs : List Job := t2_49jobs0




def t2_50root : Job := ⟨plan201,[],none,⟨1,0,0⟩⟩
def t2_50jobs0 : List Job := [⟨plan201,[],none,⟨1,0,0⟩⟩]

def t2_50jobs : List Job := t2_50jobs0




def t2_51root : Job := ⟨plan202,[],none,⟨1,0,0⟩⟩
def t2_51jobs0 : List Job := [⟨plan202,[],none,⟨1,0,0⟩⟩]

def t2_51jobs : List Job := t2_51jobs0




def t2_52root : Job := ⟨plan220,[],none,⟨1,1,0⟩⟩
def t2_52jobs0 : List Job := [⟨plan220,[],none,⟨1,1,0⟩⟩]

def t2_52jobs : List Job := t2_52jobs0




def t2_53root : Job := ⟨plan221,[],none,⟨1,1,0⟩⟩
def t2_53jobs0 : List Job := [⟨plan221,[],none,⟨1,1,0⟩⟩]

def t2_53jobs : List Job := t2_53jobs0




def t2_54root : Job := ⟨plan222,[],none,⟨1,1,0⟩⟩
def t2_54jobs0 : List Job := [⟨plan222,[],none,⟨1,1,0⟩⟩]

def t2_54jobs : List Job := t2_54jobs0




def t2_55root : Job := ⟨plan223,[],none,⟨1,1,0⟩⟩
def t2_55jobs0 : List Job := [⟨plan223,[],none,⟨1,1,0⟩⟩]

def t2_55jobs : List Job := t2_55jobs0




def t2_56root : Job := ⟨plan224,[],none,⟨1,1,0⟩⟩
def t2_56jobs0 : List Job := [⟨plan224,[],none,⟨1,1,0⟩⟩]

def t2_56jobs : List Job := t2_56jobs0




def t2_57root : Job := ⟨plan225,[],none,⟨1,1,0⟩⟩
def t2_57jobs0 : List Job := [⟨plan225,[],none,⟨1,1,0⟩⟩]

def t2_57jobs : List Job := t2_57jobs0




def t2_58root : Job := ⟨plan203,[],none,⟨1,0,0⟩⟩
def t2_58jobs0 : List Job := [⟨plan203,[],none,⟨1,0,0⟩⟩]

def t2_58jobs : List Job := t2_58jobs0




def t2_59root : Job := ⟨plan226,[],none,⟨1,1,0⟩⟩
def t2_59jobs0 : List Job := [⟨plan226,[],none,⟨1,1,0⟩⟩]

def t2_59jobs : List Job := t2_59jobs0




def t2_60root : Job := ⟨plan227,[],none,⟨1,1,0⟩⟩
def t2_60jobs0 : List Job := [⟨plan227,[],none,⟨1,1,0⟩⟩]

def t2_60jobs : List Job := t2_60jobs0




def t2_61root : Job := ⟨plan228,[],none,⟨1,1,0⟩⟩
def t2_61jobs0 : List Job := [⟨plan228,[],none,⟨1,1,0⟩⟩]

def t2_61jobs : List Job := t2_61jobs0




def t2_62root : Job := ⟨plan229,[],none,⟨1,1,0⟩⟩
def t2_62jobs0 : List Job := [⟨plan229,[],none,⟨1,1,0⟩⟩]

def t2_62jobs : List Job := t2_62jobs0




def t2_63root : Job := ⟨plan230,[],none,⟨1,1,0⟩⟩
def t2_63jobs0 : List Job := [⟨plan230,[],none,⟨1,1,0⟩⟩]

def t2_63jobs : List Job := t2_63jobs0




def t2_64root : Job := ⟨plan231,[],none,⟨1,1,0⟩⟩
def t2_64jobs0 : List Job := [⟨plan231,[],none,⟨1,1,0⟩⟩]

def t2_64jobs : List Job := t2_64jobs0




def t3_0root : Job := ⟨plan634,[],none,⟨3,0,0⟩⟩
def t3_0jobs0 : List Job := [⟨plan634,[],none,⟨3,0,0⟩⟩]

def t3_0jobs : List Job := t3_0jobs0




def t3_1root : Job := ⟨plan635,[],none,⟨3,0,0⟩⟩
def t3_1jobs0 : List Job := [⟨plan635,[],none,⟨3,0,0⟩⟩]

def t3_1jobs : List Job := t3_1jobs0




def t3_2root : Job := ⟨plan649,[],none,⟨3,0,0⟩⟩
def t3_2jobs0 : List Job := [⟨plan649,[],none,⟨3,0,0⟩⟩]

def t3_2jobs : List Job := t3_2jobs0




def t3_3root : Job := ⟨plan650,[],none,⟨3,0,0⟩⟩
def t3_3jobs0 : List Job := [⟨plan650,[],none,⟨3,0,0⟩⟩]

def t3_3jobs : List Job := t3_3jobs0




def t3_4root : Job := ⟨plan651,[],none,⟨3,0,0⟩⟩
def t3_4jobs0 : List Job := [⟨plan651,[],none,⟨3,0,0⟩⟩]

def t3_4jobs : List Job := t3_4jobs0




def t3_5root : Job := ⟨plan652,[],none,⟨3,0,0⟩⟩
def t3_5jobs0 : List Job := [⟨plan652,[],none,⟨3,0,0⟩⟩]

def t3_5jobs : List Job := t3_5jobs0




def t3_6root : Job := ⟨plan653,[],none,⟨3,0,0⟩⟩
def t3_6jobs0 : List Job := [⟨plan653,[],none,⟨3,0,0⟩⟩]

def t3_6jobs : List Job := t3_6jobs0




def t3_7root : Job := ⟨plan636,[],none,⟨3,0,0⟩⟩
def t3_7jobs0 : List Job := [⟨plan636,[],none,⟨3,0,0⟩⟩]

def t3_7jobs : List Job := t3_7jobs0




def t3_8root : Job := ⟨plan637,[],none,⟨3,0,0⟩⟩
def t3_8jobs0 : List Job := [⟨plan637,[],none,⟨3,0,0⟩⟩]

def t3_8jobs : List Job := t3_8jobs0




def t3_9root : Job := ⟨plan654,[],none,⟨3,0,0⟩⟩
def t3_9jobs0 : List Job := [⟨plan654,[],none,⟨3,0,0⟩⟩]

def t3_9jobs : List Job := t3_9jobs0




def t3_10root : Job := ⟨plan655,[],none,⟨3,0,0⟩⟩
def t3_10jobs0 : List Job := [⟨plan655,[],none,⟨3,0,0⟩⟩]

def t3_10jobs : List Job := t3_10jobs0




def t3_11root : Job := ⟨plan656,[],none,⟨3,0,0⟩⟩
def t3_11jobs0 : List Job := [⟨plan656,[],none,⟨3,0,0⟩⟩]

def t3_11jobs : List Job := t3_11jobs0




def t3_12root : Job := ⟨plan657,[],none,⟨3,0,0⟩⟩
def t3_12jobs0 : List Job := [⟨plan657,[],none,⟨3,0,0⟩⟩]

def t3_12jobs : List Job := t3_12jobs0




def t3_13root : Job := ⟨plan658,[],none,⟨3,0,0⟩⟩
def t3_13jobs0 : List Job := [⟨plan658,[],none,⟨3,0,0⟩⟩]

def t3_13jobs : List Job := t3_13jobs0




def t3_14root : Job := ⟨plan638,[],none,⟨3,0,0⟩⟩
def t3_14jobs0 : List Job := [⟨plan638,[],none,⟨3,0,0⟩⟩]

def t3_14jobs : List Job := t3_14jobs0




def t3_15root : Job := ⟨plan659,[],none,⟨3,0,0⟩⟩
def t3_15jobs0 : List Job := [⟨plan659,[],none,⟨3,0,0⟩⟩]

def t3_15jobs : List Job := t3_15jobs0




def t3_16root : Job := ⟨plan660,[],none,⟨3,0,0⟩⟩
def t3_16jobs0 : List Job := [⟨plan660,[],none,⟨3,0,0⟩⟩]

def t3_16jobs : List Job := t3_16jobs0




def t3_17root : Job := ⟨plan661,[],none,⟨3,0,0⟩⟩
def t3_17jobs0 : List Job := [⟨plan661,[],none,⟨3,0,0⟩⟩]

def t3_17jobs : List Job := t3_17jobs0




def t3_18root : Job := ⟨plan662,[],none,⟨3,0,0⟩⟩
def t3_18jobs0 : List Job := [⟨plan662,[],none,⟨3,0,0⟩⟩]

def t3_18jobs : List Job := t3_18jobs0




def t3_19root : Job := ⟨plan663,[],none,⟨3,0,0⟩⟩
def t3_19jobs0 : List Job := [⟨plan663,[],none,⟨3,0,0⟩⟩]

def t3_19jobs : List Job := t3_19jobs0




def t3_20root : Job := ⟨plan710,[],none,⟨3,1,0⟩⟩
def t3_20jobs0 : List Job := [⟨plan710,[],none,⟨3,1,0⟩⟩]

def t3_20jobs : List Job := t3_20jobs0




def t3_21root : Job := ⟨plan711,[],none,⟨3,1,0⟩⟩
def t3_21jobs0 : List Job := [⟨plan711,[],none,⟨3,1,0⟩⟩]

def t3_21jobs : List Job := t3_21jobs0




def t3_22root : Job := ⟨plan712,[],none,⟨3,1,0⟩⟩
def t3_22jobs0 : List Job := [⟨plan712,[],none,⟨3,1,0⟩⟩]

def t3_22jobs : List Job := t3_22jobs0




def t3_23root : Job := ⟨plan713,[],none,⟨3,1,0⟩⟩
def t3_23jobs0 : List Job := [⟨plan713,[],none,⟨3,1,0⟩⟩]

def t3_23jobs : List Job := t3_23jobs0




def t3_24root : Job := ⟨plan714,[],none,⟨3,1,0⟩⟩
def t3_24jobs0 : List Job := [⟨plan714,[],none,⟨3,1,0⟩⟩]

def t3_24jobs : List Job := t3_24jobs0




def t3_25root : Job := ⟨plan664,[],none,⟨3,0,0⟩⟩
def t3_25jobs0 : List Job := [⟨plan664,[],none,⟨3,0,0⟩⟩]

def t3_25jobs : List Job := t3_25jobs0




def t3_26root : Job := ⟨plan715,[],none,⟨3,1,0⟩⟩
def t3_26jobs0 : List Job := [⟨plan715,[],none,⟨3,1,0⟩⟩]

def t3_26jobs : List Job := t3_26jobs0




def t3_27root : Job := ⟨plan716,[],none,⟨3,1,0⟩⟩
def t3_27jobs0 : List Job := [⟨plan716,[],none,⟨3,1,0⟩⟩]

def t3_27jobs : List Job := t3_27jobs0




def t3_28root : Job := ⟨plan717,[],none,⟨3,1,0⟩⟩
def t3_28jobs0 : List Job := [⟨plan717,[],none,⟨3,1,0⟩⟩]

def t3_28jobs : List Job := t3_28jobs0




def t3_29root : Job := ⟨plan718,[],none,⟨3,1,0⟩⟩
def t3_29jobs0 : List Job := [⟨plan718,[],none,⟨3,1,0⟩⟩]

def t3_29jobs : List Job := t3_29jobs0




def t3_30root : Job := ⟨plan719,[],none,⟨3,1,0⟩⟩
def t3_30jobs0 : List Job := [⟨plan719,[],none,⟨3,1,0⟩⟩]

def t3_30jobs : List Job := t3_30jobs0




def t3_31root : Job := ⟨plan720,[],none,⟨3,1,0⟩⟩
def t3_31jobs0 : List Job := [⟨plan720,[],none,⟨3,1,0⟩⟩]

def t3_31jobs : List Job := t3_31jobs0




def t3_32root : Job := ⟨plan721,[],none,⟨3,1,0⟩⟩
def t3_32jobs0 : List Job := [⟨plan721,[],none,⟨3,1,0⟩⟩]

def t3_32jobs : List Job := t3_32jobs0




def t3_33root : Job := ⟨plan722,[],none,⟨3,1,0⟩⟩
def t3_33jobs0 : List Job := [⟨plan722,[],none,⟨3,1,0⟩⟩]

def t3_33jobs : List Job := t3_33jobs0




def t3_34root : Job := ⟨plan723,[],none,⟨3,1,0⟩⟩
def t3_34jobs0 : List Job := [⟨plan723,[],none,⟨3,1,0⟩⟩]

def t3_34jobs : List Job := t3_34jobs0




def t3_35root : Job := ⟨plan665,[],none,⟨3,0,0⟩⟩
def t3_35jobs0 : List Job := [⟨plan665,[],none,⟨3,0,0⟩⟩]

def t3_35jobs : List Job := t3_35jobs0




def t3_36root : Job := ⟨plan666,[],none,⟨3,0,0⟩⟩
def t3_36jobs0 : List Job := [⟨plan666,[],none,⟨3,0,0⟩⟩]

def t3_36jobs : List Job := t3_36jobs0




def t3_37root : Job := ⟨plan724,[],none,⟨3,1,0⟩⟩
def t3_37jobs0 : List Job := [⟨plan724,[],none,⟨3,1,0⟩⟩]

def t3_37jobs : List Job := t3_37jobs0




def t3_38root : Job := ⟨plan725,[],none,⟨3,1,0⟩⟩
def t3_38jobs0 : List Job := [⟨plan725,[],none,⟨3,1,0⟩⟩]

def t3_38jobs : List Job := t3_38jobs0




def t3_39root : Job := ⟨plan726,[],none,⟨3,1,0⟩⟩
def t3_39jobs0 : List Job := [⟨plan726,[],none,⟨3,1,0⟩⟩]

def t3_39jobs : List Job := t3_39jobs0




def t3_40root : Job := ⟨plan727,[],none,⟨3,1,0⟩⟩
def t3_40jobs0 : List Job := [⟨plan727,[],none,⟨3,1,0⟩⟩]

def t3_40jobs : List Job := t3_40jobs0




def t3_41root : Job := ⟨plan728,[],none,⟨3,1,0⟩⟩
def t3_41jobs0 : List Job := [⟨plan728,[],none,⟨3,1,0⟩⟩]

def t3_41jobs : List Job := t3_41jobs0




def t3_42root : Job := ⟨plan667,[],none,⟨3,0,0⟩⟩
def t3_42jobs0 : List Job := [⟨plan667,[],none,⟨3,0,0⟩⟩]

def t3_42jobs : List Job := t3_42jobs0




def t3_43root : Job := ⟨plan729,[],none,⟨3,1,0⟩⟩
def t3_43jobs0 : List Job := [⟨plan729,[],none,⟨3,1,0⟩⟩]

def t3_43jobs : List Job := t3_43jobs0




def t3_44root : Job := ⟨plan730,[],none,⟨3,1,0⟩⟩
def t3_44jobs0 : List Job := [⟨plan730,[],none,⟨3,1,0⟩⟩]

def t3_44jobs : List Job := t3_44jobs0




def t3_45root : Job := ⟨plan731,[],none,⟨3,1,0⟩⟩
def t3_45jobs0 : List Job := [⟨plan731,[],none,⟨3,1,0⟩⟩]

def t3_45jobs : List Job := t3_45jobs0




def t3_46root : Job := ⟨plan732,[],none,⟨3,1,0⟩⟩
def t3_46jobs0 : List Job := [⟨plan732,[],none,⟨3,1,0⟩⟩]

def t3_46jobs : List Job := t3_46jobs0




def t3_47root : Job := ⟨plan733,[],none,⟨3,1,0⟩⟩
def t3_47jobs0 : List Job := [⟨plan733,[],none,⟨3,1,0⟩⟩]

def t3_47jobs : List Job := t3_47jobs0




def t3_48root : Job := ⟨plan734,[],none,⟨3,1,0⟩⟩
def t3_48jobs0 : List Job := [⟨plan734,[],none,⟨3,1,0⟩⟩]

def t3_48jobs : List Job := t3_48jobs0




def t3_49root : Job := ⟨plan639,[],none,⟨3,0,0⟩⟩
def t3_49jobs0 : List Job := [⟨plan639,[],none,⟨3,0,0⟩⟩]

def t3_49jobs : List Job := t3_49jobs0




def t3_50root : Job := ⟨plan640,[],none,⟨3,0,0⟩⟩
def t3_50jobs0 : List Job := [⟨plan640,[],none,⟨3,0,0⟩⟩]

def t3_50jobs : List Job := t3_50jobs0




def t3_51root : Job := ⟨plan641,[],none,⟨3,0,0⟩⟩
def t3_51jobs0 : List Job := [⟨plan641,[],none,⟨3,0,0⟩⟩]

def t3_51jobs : List Job := t3_51jobs0




def t3_52root : Job := ⟨plan668,[],none,⟨3,0,0⟩⟩
def t3_52jobs0 : List Job := [⟨plan668,[],none,⟨3,0,0⟩⟩]

def t3_52jobs : List Job := t3_52jobs0




def t3_53root : Job := ⟨plan669,[],none,⟨3,0,0⟩⟩
def t3_53jobs0 : List Job := [⟨plan669,[],none,⟨3,0,0⟩⟩]

def t3_53jobs : List Job := t3_53jobs0




def t3_54root : Job := ⟨plan670,[],none,⟨3,0,0⟩⟩
def t3_54jobs0 : List Job := [⟨plan670,[],none,⟨3,0,0⟩⟩]

def t3_54jobs : List Job := t3_54jobs0




def t3_55root : Job := ⟨plan671,[],none,⟨3,0,0⟩⟩
def t3_55jobs0 : List Job := [⟨plan671,[],none,⟨3,0,0⟩⟩]

def t3_55jobs : List Job := t3_55jobs0




def t3_56root : Job := ⟨plan672,[],none,⟨3,0,0⟩⟩
def t3_56jobs0 : List Job := [⟨plan672,[],none,⟨3,0,0⟩⟩]

def t3_56jobs : List Job := t3_56jobs0




def t3_57root : Job := ⟨plan673,[],none,⟨3,0,0⟩⟩
def t3_57jobs0 : List Job := [⟨plan673,[],none,⟨3,0,0⟩⟩]

def t3_57jobs : List Job := t3_57jobs0




def t3_58root : Job := ⟨plan674,[],none,⟨3,0,0⟩⟩
def t3_58jobs0 : List Job := [⟨plan674,[],none,⟨3,0,0⟩⟩]

def t3_58jobs : List Job := t3_58jobs0




def t3_59root : Job := ⟨plan642,[],none,⟨3,0,0⟩⟩
def t3_59jobs0 : List Job := [⟨plan642,[],none,⟨3,0,0⟩⟩]

def t3_59jobs : List Job := t3_59jobs0




def t3_60root : Job := ⟨plan643,[],none,⟨3,0,0⟩⟩
def t3_60jobs0 : List Job := [⟨plan643,[],none,⟨3,0,0⟩⟩]

def t3_60jobs : List Job := t3_60jobs0




def t3_61root : Job := ⟨plan675,[],none,⟨3,0,0⟩⟩
def t3_61jobs0 : List Job := [⟨plan675,[],none,⟨3,0,0⟩⟩]

def t3_61jobs : List Job := t3_61jobs0




def t3_62root : Job := ⟨plan676,[],none,⟨3,0,0⟩⟩
def t3_62jobs0 : List Job := [⟨plan676,[],none,⟨3,0,0⟩⟩]

def t3_62jobs : List Job := t3_62jobs0




def t3_63root : Job := ⟨plan677,[],none,⟨3,0,0⟩⟩
def t3_63jobs0 : List Job := [⟨plan677,[],none,⟨3,0,0⟩⟩]

def t3_63jobs : List Job := t3_63jobs0




def t3_64root : Job := ⟨plan678,[],none,⟨3,0,0⟩⟩
def t3_64jobs0 : List Job := [⟨plan678,[],none,⟨3,0,0⟩⟩]

def t3_64jobs : List Job := t3_64jobs0




def t3_65root : Job := ⟨plan679,[],none,⟨3,0,0⟩⟩
def t3_65jobs0 : List Job := [⟨plan679,[],none,⟨3,0,0⟩⟩]

def t3_65jobs : List Job := t3_65jobs0




def t3_66root : Job := ⟨plan644,[],none,⟨3,0,0⟩⟩
def t3_66jobs0 : List Job := [⟨plan644,[],none,⟨3,0,0⟩⟩]

def t3_66jobs : List Job := t3_66jobs0




def t3_67root : Job := ⟨plan680,[],none,⟨3,0,0⟩⟩
def t3_67jobs0 : List Job := [⟨plan680,[],none,⟨3,0,0⟩⟩]

def t3_67jobs : List Job := t3_67jobs0




def t3_68root : Job := ⟨plan681,[],none,⟨3,0,0⟩⟩
def t3_68jobs0 : List Job := [⟨plan681,[],none,⟨3,0,0⟩⟩]

def t3_68jobs : List Job := t3_68jobs0




def t3_69root : Job := ⟨plan682,[],none,⟨3,0,0⟩⟩
def t3_69jobs0 : List Job := [⟨plan682,[],none,⟨3,0,0⟩⟩]

def t3_69jobs : List Job := t3_69jobs0




def t3_70root : Job := ⟨plan683,[],none,⟨3,0,0⟩⟩
def t3_70jobs0 : List Job := [⟨plan683,[],none,⟨3,0,0⟩⟩]

def t3_70jobs : List Job := t3_70jobs0




def t3_71root : Job := ⟨plan684,[],none,⟨3,0,0⟩⟩
def t3_71jobs0 : List Job := [⟨plan684,[],none,⟨3,0,0⟩⟩]

def t3_71jobs : List Job := t3_71jobs0




def t3_72root : Job := ⟨plan735,[],none,⟨3,1,0⟩⟩
def t3_72jobs0 : List Job := [⟨plan735,[],none,⟨3,1,0⟩⟩]

def t3_72jobs : List Job := t3_72jobs0




def t3_73root : Job := ⟨plan736,[],none,⟨3,1,0⟩⟩
def t3_73jobs0 : List Job := [⟨plan736,[],none,⟨3,1,0⟩⟩]

def t3_73jobs : List Job := t3_73jobs0




def t3_74root : Job := ⟨plan737,[],none,⟨3,1,0⟩⟩
def t3_74jobs0 : List Job := [⟨plan737,[],none,⟨3,1,0⟩⟩]

def t3_74jobs : List Job := t3_74jobs0




def t3_75root : Job := ⟨plan738,[],none,⟨3,1,0⟩⟩
def t3_75jobs0 : List Job := [⟨plan738,[],none,⟨3,1,0⟩⟩]

def t3_75jobs : List Job := t3_75jobs0




def t3_76root : Job := ⟨plan739,[],none,⟨3,1,0⟩⟩
def t3_76jobs0 : List Job := [⟨plan739,[],none,⟨3,1,0⟩⟩]

def t3_76jobs : List Job := t3_76jobs0




def t3_77root : Job := ⟨plan740,[],none,⟨3,1,0⟩⟩
def t3_77jobs0 : List Job := [⟨plan740,[],none,⟨3,1,0⟩⟩]

def t3_77jobs : List Job := t3_77jobs0




def t3_78root : Job := ⟨plan741,[],none,⟨3,1,0⟩⟩
def t3_78jobs0 : List Job := [⟨plan741,[],none,⟨3,1,0⟩⟩]

def t3_78jobs : List Job := t3_78jobs0




def t3_79root : Job := ⟨plan685,[],none,⟨3,0,0⟩⟩
def t3_79jobs0 : List Job := [⟨plan685,[],none,⟨3,0,0⟩⟩]

def t3_79jobs : List Job := t3_79jobs0




def t3_80root : Job := ⟨plan742,[],none,⟨3,1,0⟩⟩
def t3_80jobs0 : List Job := [⟨plan742,[],none,⟨3,1,0⟩⟩]

def t3_80jobs : List Job := t3_80jobs0




def t3_81root : Job := ⟨plan743,[],none,⟨3,1,0⟩⟩
def t3_81jobs0 : List Job := [⟨plan743,[],none,⟨3,1,0⟩⟩]

def t3_81jobs : List Job := t3_81jobs0




def t3_82root : Job := ⟨plan744,[],none,⟨3,1,0⟩⟩
def t3_82jobs0 : List Job := [⟨plan744,[],none,⟨3,1,0⟩⟩]

def t3_82jobs : List Job := t3_82jobs0




def t3_83root : Job := ⟨plan745,[],none,⟨3,1,0⟩⟩
def t3_83jobs0 : List Job := [⟨plan745,[],none,⟨3,1,0⟩⟩]

def t3_83jobs : List Job := t3_83jobs0




def t3_84root : Job := ⟨plan746,[],none,⟨3,1,0⟩⟩
def t3_84jobs0 : List Job := [⟨plan746,[],none,⟨3,1,0⟩⟩]

def t3_84jobs : List Job := t3_84jobs0




def t3_85root : Job := ⟨plan747,[],none,⟨3,1,0⟩⟩
def t3_85jobs0 : List Job := [⟨plan747,[],none,⟨3,1,0⟩⟩]

def t3_85jobs : List Job := t3_85jobs0




def t3_86root : Job := ⟨plan748,[],none,⟨3,1,0⟩⟩
def t3_86jobs0 : List Job := [⟨plan748,[],none,⟨3,1,0⟩⟩]

def t3_86jobs : List Job := t3_86jobs0




def t3_87root : Job := ⟨plan749,[],none,⟨3,1,0⟩⟩
def t3_87jobs0 : List Job := [⟨plan749,[],none,⟨3,1,0⟩⟩]

def t3_87jobs : List Job := t3_87jobs0




def t3_88root : Job := ⟨plan750,[],none,⟨3,1,0⟩⟩
def t3_88jobs0 : List Job := [⟨plan750,[],none,⟨3,1,0⟩⟩]

def t3_88jobs : List Job := t3_88jobs0




def t3_89root : Job := ⟨plan686,[],none,⟨3,0,0⟩⟩
def t3_89jobs0 : List Job := [⟨plan686,[],none,⟨3,0,0⟩⟩]

def t3_89jobs : List Job := t3_89jobs0




def t3_90root : Job := ⟨plan687,[],none,⟨3,0,0⟩⟩
def t3_90jobs0 : List Job := [⟨plan687,[],none,⟨3,0,0⟩⟩]

def t3_90jobs : List Job := t3_90jobs0




def t3_91root : Job := ⟨plan751,[],none,⟨3,1,0⟩⟩
def t3_91jobs0 : List Job := [⟨plan751,[],none,⟨3,1,0⟩⟩]

def t3_91jobs : List Job := t3_91jobs0




def t3_92root : Job := ⟨plan752,[],none,⟨3,1,0⟩⟩
def t3_92jobs0 : List Job := [⟨plan752,[],none,⟨3,1,0⟩⟩]

def t3_92jobs : List Job := t3_92jobs0




def t3_93root : Job := ⟨plan753,[],none,⟨3,1,0⟩⟩
def t3_93jobs0 : List Job := [⟨plan753,[],none,⟨3,1,0⟩⟩]

def t3_93jobs : List Job := t3_93jobs0




def t3_94root : Job := ⟨plan754,[],none,⟨3,1,0⟩⟩
def t3_94jobs0 : List Job := [⟨plan754,[],none,⟨3,1,0⟩⟩]

def t3_94jobs : List Job := t3_94jobs0




def t3_95root : Job := ⟨plan755,[],none,⟨3,1,0⟩⟩
def t3_95jobs0 : List Job := [⟨plan755,[],none,⟨3,1,0⟩⟩]

def t3_95jobs : List Job := t3_95jobs0




def t3_96root : Job := ⟨plan756,[],none,⟨3,1,0⟩⟩
def t3_96jobs0 : List Job := [⟨plan756,[],none,⟨3,1,0⟩⟩]

def t3_96jobs : List Job := t3_96jobs0




def t3_97root : Job := ⟨plan688,[],none,⟨3,0,0⟩⟩
def t3_97jobs0 : List Job := [⟨plan688,[],none,⟨3,0,0⟩⟩]

def t3_97jobs : List Job := t3_97jobs0




def t3_98root : Job := ⟨plan757,[],none,⟨3,1,0⟩⟩
def t3_98jobs0 : List Job := [⟨plan757,[],none,⟨3,1,0⟩⟩]

def t3_98jobs : List Job := t3_98jobs0




def t3_99root : Job := ⟨plan758,[],none,⟨3,1,0⟩⟩
def t3_99jobs0 : List Job := [⟨plan758,[],none,⟨3,1,0⟩⟩]

def t3_99jobs : List Job := t3_99jobs0




def t3_100root : Job := ⟨plan759,[],none,⟨3,1,0⟩⟩
def t3_100jobs0 : List Job := [⟨plan759,[],none,⟨3,1,0⟩⟩]

def t3_100jobs : List Job := t3_100jobs0




def t3_101root : Job := ⟨plan760,[],none,⟨3,1,0⟩⟩
def t3_101jobs0 : List Job := [⟨plan760,[],none,⟨3,1,0⟩⟩]

def t3_101jobs : List Job := t3_101jobs0




def t3_102root : Job := ⟨plan761,[],none,⟨3,1,0⟩⟩
def t3_102jobs0 : List Job := [⟨plan761,[],none,⟨3,1,0⟩⟩]

def t3_102jobs : List Job := t3_102jobs0




def t3_103root : Job := ⟨plan762,[],none,⟨3,1,0⟩⟩
def t3_103jobs0 : List Job := [⟨plan762,[],none,⟨3,1,0⟩⟩]

def t3_103jobs : List Job := t3_103jobs0




def t3_104root : Job := ⟨plan645,[],none,⟨3,0,0⟩⟩
def t3_104jobs0 : List Job := [⟨plan645,[],none,⟨3,0,0⟩⟩]

def t3_104jobs : List Job := t3_104jobs0




def t3_105root : Job := ⟨plan646,[],none,⟨3,0,0⟩⟩
def t3_105jobs0 : List Job := [⟨plan646,[],none,⟨3,0,0⟩⟩]

def t3_105jobs : List Job := t3_105jobs0




def t3_106root : Job := ⟨plan689,[],none,⟨3,0,0⟩⟩
def t3_106jobs0 : List Job := [⟨plan689,[],none,⟨3,0,0⟩⟩]

def t3_106jobs : List Job := t3_106jobs0




def t3_107root : Job := ⟨plan690,[],none,⟨3,0,0⟩⟩
def t3_107jobs0 : List Job := [⟨plan690,[],none,⟨3,0,0⟩⟩]

def t3_107jobs : List Job := t3_107jobs0




def t3_108root : Job := ⟨plan691,[],none,⟨3,0,0⟩⟩
def t3_108jobs0 : List Job := [⟨plan691,[],none,⟨3,0,0⟩⟩]

def t3_108jobs : List Job := t3_108jobs0




def t3_109root : Job := ⟨plan692,[],none,⟨3,0,0⟩⟩
def t3_109jobs0 : List Job := [⟨plan692,[],none,⟨3,0,0⟩⟩]

def t3_109jobs : List Job := t3_109jobs0




def t3_110root : Job := ⟨plan693,[],none,⟨3,0,0⟩⟩
def t3_110jobs0 : List Job := [⟨plan693,[],none,⟨3,0,0⟩⟩]

def t3_110jobs : List Job := t3_110jobs0




def t3_111root : Job := ⟨plan647,[],none,⟨3,0,0⟩⟩
def t3_111jobs0 : List Job := [⟨plan647,[],none,⟨3,0,0⟩⟩]

def t3_111jobs : List Job := t3_111jobs0




def t3_112root : Job := ⟨plan694,[],none,⟨3,0,0⟩⟩
def t3_112jobs0 : List Job := [⟨plan694,[],none,⟨3,0,0⟩⟩]

def t3_112jobs : List Job := t3_112jobs0




def t3_113root : Job := ⟨plan695,[],none,⟨3,0,0⟩⟩
def t3_113jobs0 : List Job := [⟨plan695,[],none,⟨3,0,0⟩⟩]

def t3_113jobs : List Job := t3_113jobs0




def t3_114root : Job := ⟨plan696,[],none,⟨3,0,0⟩⟩
def t3_114jobs0 : List Job := [⟨plan696,[],none,⟨3,0,0⟩⟩]

def t3_114jobs : List Job := t3_114jobs0




def t3_115root : Job := ⟨plan697,[],none,⟨3,0,0⟩⟩
def t3_115jobs0 : List Job := [⟨plan697,[],none,⟨3,0,0⟩⟩]

def t3_115jobs : List Job := t3_115jobs0




def t3_116root : Job := ⟨plan763,[],none,⟨3,1,0⟩⟩
def t3_116jobs0 : List Job := [⟨plan763,[],none,⟨3,1,0⟩⟩]

def t3_116jobs : List Job := t3_116jobs0




def t3_117root : Job := ⟨plan764,[],none,⟨3,1,0⟩⟩
def t3_117jobs0 : List Job := [⟨plan764,[],none,⟨3,1,0⟩⟩]

def t3_117jobs : List Job := t3_117jobs0




def t3_118root : Job := ⟨plan765,[],none,⟨3,1,0⟩⟩
def t3_118jobs0 : List Job := [⟨plan765,[],none,⟨3,1,0⟩⟩]

def t3_118jobs : List Job := t3_118jobs0




def t3_119root : Job := ⟨plan766,[],none,⟨3,1,0⟩⟩
def t3_119jobs0 : List Job := [⟨plan766,[],none,⟨3,1,0⟩⟩]

def t3_119jobs : List Job := t3_119jobs0




def t3_120root : Job := ⟨plan767,[],none,⟨3,1,0⟩⟩
def t3_120jobs0 : List Job := [⟨plan767,[],none,⟨3,1,0⟩⟩]

def t3_120jobs : List Job := t3_120jobs0




def t3_121root : Job := ⟨plan768,[],none,⟨3,1,0⟩⟩
def t3_121jobs0 : List Job := [⟨plan768,[],none,⟨3,1,0⟩⟩]

def t3_121jobs : List Job := t3_121jobs0




def t3_122root : Job := ⟨plan769,[],none,⟨3,1,0⟩⟩
def t3_122jobs0 : List Job := [⟨plan769,[],none,⟨3,1,0⟩⟩]

def t3_122jobs : List Job := t3_122jobs0




def t3_123root : Job := ⟨plan770,[],none,⟨3,1,0⟩⟩
def t3_123jobs0 : List Job := [⟨plan770,[],none,⟨3,1,0⟩⟩]

def t3_123jobs : List Job := t3_123jobs0




def t3_124root : Job := ⟨plan771,[],none,⟨3,1,0⟩⟩
def t3_124jobs0 : List Job := [⟨plan771,[],none,⟨3,1,0⟩⟩]

def t3_124jobs : List Job := t3_124jobs0




def t3_125root : Job := ⟨plan698,[],none,⟨3,0,0⟩⟩
def t3_125jobs0 : List Job := [⟨plan698,[],none,⟨3,0,0⟩⟩]

def t3_125jobs : List Job := t3_125jobs0




def t3_126root : Job := ⟨plan772,[],none,⟨3,1,0⟩⟩
def t3_126jobs0 : List Job := [⟨plan772,[],none,⟨3,1,0⟩⟩]

def t3_126jobs : List Job := t3_126jobs0




def t3_127root : Job := ⟨plan773,[],none,⟨3,1,0⟩⟩
def t3_127jobs0 : List Job := [⟨plan773,[],none,⟨3,1,0⟩⟩]

def t3_127jobs : List Job := t3_127jobs0




def t3_128root : Job := ⟨plan774,[],none,⟨3,1,0⟩⟩
def t3_128jobs0 : List Job := [⟨plan774,[],none,⟨3,1,0⟩⟩]

def t3_128jobs : List Job := t3_128jobs0




def t3_129root : Job := ⟨plan775,[],none,⟨3,1,0⟩⟩
def t3_129jobs0 : List Job := [⟨plan775,[],none,⟨3,1,0⟩⟩]

def t3_129jobs : List Job := t3_129jobs0




def t3_130root : Job := ⟨plan776,[],none,⟨3,1,0⟩⟩
def t3_130jobs0 : List Job := [⟨plan776,[],none,⟨3,1,0⟩⟩]

def t3_130jobs : List Job := t3_130jobs0




def t3_131root : Job := ⟨plan777,[],none,⟨3,1,0⟩⟩
def t3_131jobs0 : List Job := [⟨plan777,[],none,⟨3,1,0⟩⟩]

def t3_131jobs : List Job := t3_131jobs0




def t3_132root : Job := ⟨plan648,[],none,⟨3,0,0⟩⟩
def t3_132jobs0 : List Job := [⟨plan648,[],none,⟨3,0,0⟩⟩]

def t3_132jobs : List Job := t3_132jobs0




def t3_133root : Job := ⟨plan699,[],none,⟨3,0,0⟩⟩
def t3_133jobs0 : List Job := [⟨plan699,[],none,⟨3,0,0⟩⟩]

def t3_133jobs : List Job := t3_133jobs0




def t3_134root : Job := ⟨plan700,[],none,⟨3,0,0⟩⟩
def t3_134jobs0 : List Job := [⟨plan700,[],none,⟨3,0,0⟩⟩]

def t3_134jobs : List Job := t3_134jobs0




def t3_135root : Job := ⟨plan701,[],none,⟨3,0,0⟩⟩
def t3_135jobs0 : List Job := [⟨plan701,[],none,⟨3,0,0⟩⟩]

def t3_135jobs : List Job := t3_135jobs0




def t3_136root : Job := ⟨plan778,[],none,⟨3,1,0⟩⟩
def t3_136jobs0 : List Job := [⟨plan778,[],none,⟨3,1,0⟩⟩]

def t3_136jobs : List Job := t3_136jobs0




def t3_137root : Job := ⟨plan779,[],none,⟨3,1,0⟩⟩
def t3_137jobs0 : List Job := [⟨plan779,[],none,⟨3,1,0⟩⟩]

def t3_137jobs : List Job := t3_137jobs0




def t3_138root : Job := ⟨plan780,[],none,⟨3,1,0⟩⟩
def t3_138jobs0 : List Job := [⟨plan780,[],none,⟨3,1,0⟩⟩]

def t3_138jobs : List Job := t3_138jobs0




def t3_139root : Job := ⟨plan781,[],none,⟨3,1,0⟩⟩
def t3_139jobs0 : List Job := [⟨plan781,[],none,⟨3,1,0⟩⟩]

def t3_139jobs : List Job := t3_139jobs0




def t3_140root : Job := ⟨plan782,[],none,⟨3,1,0⟩⟩
def t3_140jobs0 : List Job := [⟨plan782,[],none,⟨3,1,0⟩⟩]

def t3_140jobs : List Job := t3_140jobs0




def t3_141root : Job := ⟨plan783,[],none,⟨3,1,0⟩⟩
def t3_141jobs0 : List Job := [⟨plan783,[],none,⟨3,1,0⟩⟩]

def t3_141jobs : List Job := t3_141jobs0




def t3_142root : Job := ⟨plan702,[],none,⟨3,0,0⟩⟩
def t3_142jobs0 : List Job := [⟨plan702,[],none,⟨3,0,0⟩⟩]

def t3_142jobs : List Job := t3_142jobs0




def t3_143root : Job := ⟨plan703,[],none,⟨3,0,0⟩⟩
def t3_143jobs0 : List Job := [⟨plan703,[],none,⟨3,0,0⟩⟩]

def t3_143jobs : List Job := t3_143jobs0




def t3_144root : Job := ⟨plan784,[],none,⟨3,1,0⟩⟩
def t3_144jobs0 : List Job := [⟨plan784,[],none,⟨3,1,0⟩⟩]

def t3_144jobs : List Job := t3_144jobs0




def t3_145root : Job := ⟨plan785,[],none,⟨3,1,0⟩⟩
def t3_145jobs0 : List Job := [⟨plan785,[],none,⟨3,1,0⟩⟩]

def t3_145jobs : List Job := t3_145jobs0




def t3_146root : Job := ⟨plan786,[],none,⟨3,1,0⟩⟩
def t3_146jobs0 : List Job := [⟨plan786,[],none,⟨3,1,0⟩⟩]

def t3_146jobs : List Job := t3_146jobs0




def t3_147root : Job := ⟨plan787,[],none,⟨3,1,0⟩⟩
def t3_147jobs0 : List Job := [⟨plan787,[],none,⟨3,1,0⟩⟩]

def t3_147jobs : List Job := t3_147jobs0




def t3_148root : Job := ⟨plan788,[],none,⟨3,1,0⟩⟩
def t3_148jobs0 : List Job := [⟨plan788,[],none,⟨3,1,0⟩⟩]

def t3_148jobs : List Job := t3_148jobs0




def t3_149root : Job := ⟨plan704,[],none,⟨3,0,0⟩⟩
def t3_149jobs0 : List Job := [⟨plan704,[],none,⟨3,0,0⟩⟩]

def t3_149jobs : List Job := t3_149jobs0




def t3_150root : Job := ⟨plan789,[],none,⟨3,1,0⟩⟩
def t3_150jobs0 : List Job := [⟨plan789,[],none,⟨3,1,0⟩⟩]

def t3_150jobs : List Job := t3_150jobs0




def t3_151root : Job := ⟨plan790,[],none,⟨3,1,0⟩⟩
def t3_151jobs0 : List Job := [⟨plan790,[],none,⟨3,1,0⟩⟩]

def t3_151jobs : List Job := t3_151jobs0




def t3_152root : Job := ⟨plan791,[],none,⟨3,1,0⟩⟩
def t3_152jobs0 : List Job := [⟨plan791,[],none,⟨3,1,0⟩⟩]

def t3_152jobs : List Job := t3_152jobs0




def t3_153root : Job := ⟨plan792,[],none,⟨3,1,0⟩⟩
def t3_153jobs0 : List Job := [⟨plan792,[],none,⟨3,1,0⟩⟩]

def t3_153jobs : List Job := t3_153jobs0




def t3_154root : Job := ⟨plan793,[],none,⟨3,1,0⟩⟩
def t3_154jobs0 : List Job := [⟨plan793,[],none,⟨3,1,0⟩⟩]

def t3_154jobs : List Job := t3_154jobs0




def t3_155root : Job := ⟨plan819,[],none,⟨3,3,0⟩⟩
def t3_155jobs0 : List Job := [⟨plan819,[],none,⟨3,3,0⟩⟩]

def t3_155jobs : List Job := t3_155jobs0




def t3_156root : Job := ⟨plan820,[],none,⟨3,3,0⟩⟩
def t3_156jobs0 : List Job := [⟨plan820,[],none,⟨3,3,0⟩⟩]

def t3_156jobs : List Job := t3_156jobs0




def t3_157root : Job := ⟨plan821,[],none,⟨3,3,0⟩⟩
def t3_157jobs0 : List Job := [⟨plan821,[],none,⟨3,3,0⟩⟩]

def t3_157jobs : List Job := t3_157jobs0




def t3_158root : Job := ⟨plan822,[],none,⟨3,3,0⟩⟩
def t3_158jobs0 : List Job := [⟨plan822,[],none,⟨3,3,0⟩⟩]

def t3_158jobs : List Job := t3_158jobs0




def t3_159root : Job := ⟨plan823,[],none,⟨3,3,0⟩⟩
def t3_159jobs0 : List Job := [⟨plan823,[],none,⟨3,3,0⟩⟩]

def t3_159jobs : List Job := t3_159jobs0




def t3_160root : Job := ⟨plan824,[],none,⟨3,3,0⟩⟩
def t3_160jobs0 : List Job := [⟨plan824,[],none,⟨3,3,0⟩⟩]

def t3_160jobs : List Job := t3_160jobs0




def t3_161root : Job := ⟨plan825,[],none,⟨3,3,0⟩⟩
def t3_161jobs0 : List Job := [⟨plan825,[],none,⟨3,3,0⟩⟩]

def t3_161jobs : List Job := t3_161jobs0




def t3_162root : Job := ⟨plan794,[],none,⟨3,1,0⟩⟩
def t3_162jobs0 : List Job := [⟨plan794,[],none,⟨3,1,0⟩⟩]

def t3_162jobs : List Job := t3_162jobs0




def t3_163root : Job := ⟨plan826,[],none,⟨3,3,0⟩⟩
def t3_163jobs0 : List Job := [⟨plan826,[],none,⟨3,3,0⟩⟩]

def t3_163jobs : List Job := t3_163jobs0




def t3_164root : Job := ⟨plan827,[],none,⟨3,3,0⟩⟩
def t3_164jobs0 : List Job := [⟨plan827,[],none,⟨3,3,0⟩⟩]

def t3_164jobs : List Job := t3_164jobs0




def t3_165root : Job := ⟨plan828,[],none,⟨3,3,0⟩⟩
def t3_165jobs0 : List Job := [⟨plan828,[],none,⟨3,3,0⟩⟩]

def t3_165jobs : List Job := t3_165jobs0




def t3_166root : Job := ⟨plan829,[],none,⟨3,3,0⟩⟩
def t3_166jobs0 : List Job := [⟨plan829,[],none,⟨3,3,0⟩⟩]

def t3_166jobs : List Job := t3_166jobs0




def t3_167root : Job := ⟨plan830,[],none,⟨3,3,0⟩⟩
def t3_167jobs0 : List Job := [⟨plan830,[],none,⟨3,3,0⟩⟩]

def t3_167jobs : List Job := t3_167jobs0




def t3_168root : Job := ⟨plan831,[],none,⟨3,3,0⟩⟩
def t3_168jobs0 : List Job := [⟨plan831,[],none,⟨3,3,0⟩⟩]

def t3_168jobs : List Job := t3_168jobs0




def t3_169root : Job := ⟨plan832,[],none,⟨3,3,0⟩⟩
def t3_169jobs0 : List Job := [⟨plan832,[],none,⟨3,3,0⟩⟩]

def t3_169jobs : List Job := t3_169jobs0




def t3_170root : Job := ⟨plan833,[],none,⟨3,3,0⟩⟩
def t3_170jobs0 : List Job := [⟨plan833,[],none,⟨3,3,0⟩⟩]

def t3_170jobs : List Job := t3_170jobs0




def t3_171root : Job := ⟨plan834,[],none,⟨3,3,0⟩⟩
def t3_171jobs0 : List Job := [⟨plan834,[],none,⟨3,3,0⟩⟩]

def t3_171jobs : List Job := t3_171jobs0




def t3_172root : Job := ⟨plan795,[],none,⟨3,1,0⟩⟩
def t3_172jobs0 : List Job := [⟨plan795,[],none,⟨3,1,0⟩⟩]

def t3_172jobs : List Job := t3_172jobs0




def t3_173root : Job := ⟨plan796,[],none,⟨3,1,0⟩⟩
def t3_173jobs0 : List Job := [⟨plan796,[],none,⟨3,1,0⟩⟩]

def t3_173jobs : List Job := t3_173jobs0




def t3_174root : Job := ⟨plan835,[],none,⟨3,3,0⟩⟩
def t3_174jobs0 : List Job := [⟨plan835,[],none,⟨3,3,0⟩⟩]

def t3_174jobs : List Job := t3_174jobs0




def t3_175root : Job := ⟨plan836,[],none,⟨3,3,0⟩⟩
def t3_175jobs0 : List Job := [⟨plan836,[],none,⟨3,3,0⟩⟩]

def t3_175jobs : List Job := t3_175jobs0




def t3_176root : Job := ⟨plan837,[],none,⟨3,3,0⟩⟩
def t3_176jobs0 : List Job := [⟨plan837,[],none,⟨3,3,0⟩⟩]

def t3_176jobs : List Job := t3_176jobs0




def t3_177root : Job := ⟨plan838,[],none,⟨3,3,0⟩⟩
def t3_177jobs0 : List Job := [⟨plan838,[],none,⟨3,3,0⟩⟩]

def t3_177jobs : List Job := t3_177jobs0




def t3_178root : Job := ⟨plan839,[],none,⟨3,3,0⟩⟩
def t3_178jobs0 : List Job := [⟨plan839,[],none,⟨3,3,0⟩⟩]

def t3_178jobs : List Job := t3_178jobs0




def t3_179root : Job := ⟨plan840,[],none,⟨3,3,0⟩⟩
def t3_179jobs0 : List Job := [⟨plan840,[],none,⟨3,3,0⟩⟩]

def t3_179jobs : List Job := t3_179jobs0




def t3_180root : Job := ⟨plan797,[],none,⟨3,1,0⟩⟩
def t3_180jobs0 : List Job := [⟨plan797,[],none,⟨3,1,0⟩⟩]

def t3_180jobs : List Job := t3_180jobs0




def t3_181root : Job := ⟨plan841,[],none,⟨3,3,0⟩⟩
def t3_181jobs0 : List Job := [⟨plan841,[],none,⟨3,3,0⟩⟩]

def t3_181jobs : List Job := t3_181jobs0




def t3_182root : Job := ⟨plan842,[],none,⟨3,3,0⟩⟩
def t3_182jobs0 : List Job := [⟨plan842,[],none,⟨3,3,0⟩⟩]

def t3_182jobs : List Job := t3_182jobs0




def t3_183root : Job := ⟨plan843,[],none,⟨3,3,0⟩⟩
def t3_183jobs0 : List Job := [⟨plan843,[],none,⟨3,3,0⟩⟩]

def t3_183jobs : List Job := t3_183jobs0




def t3_184root : Job := ⟨plan844,[],none,⟨3,3,0⟩⟩
def t3_184jobs0 : List Job := [⟨plan844,[],none,⟨3,3,0⟩⟩]

def t3_184jobs : List Job := t3_184jobs0




def t3_185root : Job := ⟨plan845,[],none,⟨3,3,0⟩⟩
def t3_185jobs0 : List Job := [⟨plan845,[],none,⟨3,3,0⟩⟩]

def t3_185jobs : List Job := t3_185jobs0




def t3_186root : Job := ⟨plan846,[],none,⟨3,3,0⟩⟩
def t3_186jobs0 : List Job := [⟨plan846,[],none,⟨3,3,0⟩⟩]

def t3_186jobs : List Job := t3_186jobs0




def t3_187root : Job := ⟨plan705,[],none,⟨3,0,0⟩⟩
def t3_187jobs0 : List Job := [⟨plan705,[],none,⟨3,0,0⟩⟩]

def t3_187jobs : List Job := t3_187jobs0




def t3_188root : Job := ⟨plan798,[],none,⟨3,1,0⟩⟩
def t3_188jobs0 : List Job := [⟨plan798,[],none,⟨3,1,0⟩⟩]

def t3_188jobs : List Job := t3_188jobs0




def t3_189root : Job := ⟨plan799,[],none,⟨3,1,0⟩⟩
def t3_189jobs0 : List Job := [⟨plan799,[],none,⟨3,1,0⟩⟩]

def t3_189jobs : List Job := t3_189jobs0




def t3_190root : Job := ⟨plan800,[],none,⟨3,1,0⟩⟩
def t3_190jobs0 : List Job := [⟨plan800,[],none,⟨3,1,0⟩⟩]

def t3_190jobs : List Job := t3_190jobs0




def t3_191root : Job := ⟨plan801,[],none,⟨3,1,0⟩⟩
def t3_191jobs0 : List Job := [⟨plan801,[],none,⟨3,1,0⟩⟩]

def t3_191jobs : List Job := t3_191jobs0




def t3_192root : Job := ⟨plan847,[],none,⟨3,3,0⟩⟩
def t3_192jobs0 : List Job := [⟨plan847,[],none,⟨3,3,0⟩⟩]

def t3_192jobs : List Job := t3_192jobs0




def t3_193root : Job := ⟨plan848,[],none,⟨3,3,0⟩⟩
def t3_193jobs0 : List Job := [⟨plan848,[],none,⟨3,3,0⟩⟩]

def t3_193jobs : List Job := t3_193jobs0




def t3_194root : Job := ⟨plan849,[],none,⟨3,3,0⟩⟩
def t3_194jobs0 : List Job := [⟨plan849,[],none,⟨3,3,0⟩⟩]

def t3_194jobs : List Job := t3_194jobs0




def t3_195root : Job := ⟨plan850,[],none,⟨3,3,0⟩⟩
def t3_195jobs0 : List Job := [⟨plan850,[],none,⟨3,3,0⟩⟩]

def t3_195jobs : List Job := t3_195jobs0




def t3_196root : Job := ⟨plan851,[],none,⟨3,3,0⟩⟩
def t3_196jobs0 : List Job := [⟨plan851,[],none,⟨3,3,0⟩⟩]

def t3_196jobs : List Job := t3_196jobs0




def t3_197root : Job := ⟨plan852,[],none,⟨3,3,0⟩⟩
def t3_197jobs0 : List Job := [⟨plan852,[],none,⟨3,3,0⟩⟩]

def t3_197jobs : List Job := t3_197jobs0




def t3_198root : Job := ⟨plan853,[],none,⟨3,3,0⟩⟩
def t3_198jobs0 : List Job := [⟨plan853,[],none,⟨3,3,0⟩⟩]

def t3_198jobs : List Job := t3_198jobs0




def t3_199root : Job := ⟨plan854,[],none,⟨3,3,0⟩⟩
def t3_199jobs0 : List Job := [⟨plan854,[],none,⟨3,3,0⟩⟩]

def t3_199jobs : List Job := t3_199jobs0




def t3_200root : Job := ⟨plan855,[],none,⟨3,3,0⟩⟩
def t3_200jobs0 : List Job := [⟨plan855,[],none,⟨3,3,0⟩⟩]

def t3_200jobs : List Job := t3_200jobs0




def t3_201root : Job := ⟨plan802,[],none,⟨3,1,0⟩⟩
def t3_201jobs0 : List Job := [⟨plan802,[],none,⟨3,1,0⟩⟩]

def t3_201jobs : List Job := t3_201jobs0




def t3_202root : Job := ⟨plan856,[],none,⟨3,3,0⟩⟩
def t3_202jobs0 : List Job := [⟨plan856,[],none,⟨3,3,0⟩⟩]

def t3_202jobs : List Job := t3_202jobs0




def t3_203root : Job := ⟨plan857,[],none,⟨3,3,0⟩⟩
def t3_203jobs0 : List Job := [⟨plan857,[],none,⟨3,3,0⟩⟩]

def t3_203jobs : List Job := t3_203jobs0




def t3_204root : Job := ⟨plan858,[],none,⟨3,3,0⟩⟩
def t3_204jobs0 : List Job := [⟨plan858,[],none,⟨3,3,0⟩⟩]

def t3_204jobs : List Job := t3_204jobs0




def t3_205root : Job := ⟨plan859,[],none,⟨3,3,0⟩⟩
def t3_205jobs0 : List Job := [⟨plan859,[],none,⟨3,3,0⟩⟩]

def t3_205jobs : List Job := t3_205jobs0




def t3_206root : Job := ⟨plan860,[],none,⟨3,3,0⟩⟩
def t3_206jobs0 : List Job := [⟨plan860,[],none,⟨3,3,0⟩⟩]

def t3_206jobs : List Job := t3_206jobs0




def t3_207root : Job := ⟨plan861,[],none,⟨3,3,0⟩⟩
def t3_207jobs0 : List Job := [⟨plan861,[],none,⟨3,3,0⟩⟩]

def t3_207jobs : List Job := t3_207jobs0




def t3_208root : Job := ⟨plan862,[],none,⟨3,3,0⟩⟩
def t3_208jobs0 : List Job := [⟨plan862,[],none,⟨3,3,0⟩⟩]

def t3_208jobs : List Job := t3_208jobs0




def t3_209root : Job := ⟨plan863,[],none,⟨3,3,0⟩⟩
def t3_209jobs0 : List Job := [⟨plan863,[],none,⟨3,3,0⟩⟩]

def t3_209jobs : List Job := t3_209jobs0




def t3_210root : Job := ⟨plan864,[],none,⟨3,3,0⟩⟩
def t3_210jobs0 : List Job := [⟨plan864,[],none,⟨3,3,0⟩⟩]

def t3_210jobs : List Job := t3_210jobs0




def t3_211root : Job := ⟨plan865,[],none,⟨3,3,0⟩⟩
def t3_211jobs0 : List Job := [⟨plan865,[],none,⟨3,3,0⟩⟩]

def t3_211jobs : List Job := t3_211jobs0




def t3_212root : Job := ⟨plan866,[],none,⟨3,3,0⟩⟩
def t3_212jobs0 : List Job := [⟨plan866,[],none,⟨3,3,0⟩⟩]

def t3_212jobs : List Job := t3_212jobs0




def t3_213root : Job := ⟨plan867,[],none,⟨3,3,0⟩⟩
def t3_213jobs0 : List Job := [⟨plan867,[],none,⟨3,3,0⟩⟩]

def t3_213jobs : List Job := t3_213jobs0




def t3_214root : Job := ⟨plan868,[],none,⟨3,3,0⟩⟩
def t3_214jobs0 : List Job := [⟨plan868,[],none,⟨3,3,0⟩⟩]

def t3_214jobs : List Job := t3_214jobs0




def t3_215root : Job := ⟨plan706,[],none,⟨3,0,0⟩⟩
def t3_215jobs0 : List Job := [⟨plan706,[],none,⟨3,0,0⟩⟩]

def t3_215jobs : List Job := t3_215jobs0




def t3_216root : Job := ⟨plan707,[],none,⟨3,0,0⟩⟩
def t3_216jobs0 : List Job := [⟨plan707,[],none,⟨3,0,0⟩⟩]

def t3_216jobs : List Job := t3_216jobs0




def t3_217root : Job := ⟨plan803,[],none,⟨3,1,0⟩⟩
def t3_217jobs0 : List Job := [⟨plan803,[],none,⟨3,1,0⟩⟩]

def t3_217jobs : List Job := t3_217jobs0




def t3_218root : Job := ⟨plan804,[],none,⟨3,1,0⟩⟩
def t3_218jobs0 : List Job := [⟨plan804,[],none,⟨3,1,0⟩⟩]

def t3_218jobs : List Job := t3_218jobs0




def t3_219root : Job := ⟨plan805,[],none,⟨3,1,0⟩⟩
def t3_219jobs0 : List Job := [⟨plan805,[],none,⟨3,1,0⟩⟩]

def t3_219jobs : List Job := t3_219jobs0




def t3_220root : Job := ⟨plan806,[],none,⟨3,1,0⟩⟩
def t3_220jobs0 : List Job := [⟨plan806,[],none,⟨3,1,0⟩⟩]

def t3_220jobs : List Job := t3_220jobs0




def t3_221root : Job := ⟨plan807,[],none,⟨3,1,0⟩⟩
def t3_221jobs0 : List Job := [⟨plan807,[],none,⟨3,1,0⟩⟩]

def t3_221jobs : List Job := t3_221jobs0




def t3_222root : Job := ⟨plan708,[],none,⟨3,0,0⟩⟩
def t3_222jobs0 : List Job := [⟨plan708,[],none,⟨3,0,0⟩⟩]

def t3_222jobs : List Job := t3_222jobs0




def t3_223root : Job := ⟨plan808,[],none,⟨3,1,0⟩⟩
def t3_223jobs0 : List Job := [⟨plan808,[],none,⟨3,1,0⟩⟩]

def t3_223jobs : List Job := t3_223jobs0




def t3_224root : Job := ⟨plan809,[],none,⟨3,1,0⟩⟩
def t3_224jobs0 : List Job := [⟨plan809,[],none,⟨3,1,0⟩⟩]

def t3_224jobs : List Job := t3_224jobs0




def t3_225root : Job := ⟨plan810,[],none,⟨3,1,0⟩⟩
def t3_225jobs0 : List Job := [⟨plan810,[],none,⟨3,1,0⟩⟩]

def t3_225jobs : List Job := t3_225jobs0




def t3_226root : Job := ⟨plan811,[],none,⟨3,1,0⟩⟩
def t3_226jobs0 : List Job := [⟨plan811,[],none,⟨3,1,0⟩⟩]

def t3_226jobs : List Job := t3_226jobs0




def t3_227root : Job := ⟨plan869,[],none,⟨3,3,0⟩⟩
def t3_227jobs0 : List Job := [⟨plan869,[],none,⟨3,3,0⟩⟩]

def t3_227jobs : List Job := t3_227jobs0




def t3_228root : Job := ⟨plan870,[],none,⟨3,3,0⟩⟩
def t3_228jobs0 : List Job := [⟨plan870,[],none,⟨3,3,0⟩⟩]

def t3_228jobs : List Job := t3_228jobs0




def t3_229root : Job := ⟨plan871,[],none,⟨3,3,0⟩⟩
def t3_229jobs0 : List Job := [⟨plan871,[],none,⟨3,3,0⟩⟩]

def t3_229jobs : List Job := t3_229jobs0




def t3_230root : Job := ⟨plan872,[],none,⟨3,3,0⟩⟩
def t3_230jobs0 : List Job := [⟨plan872,[],none,⟨3,3,0⟩⟩]

def t3_230jobs : List Job := t3_230jobs0




def t3_231root : Job := ⟨plan873,[],none,⟨3,3,0⟩⟩
def t3_231jobs0 : List Job := [⟨plan873,[],none,⟨3,3,0⟩⟩]

def t3_231jobs : List Job := t3_231jobs0




def t3_232root : Job := ⟨plan874,[],none,⟨3,3,0⟩⟩
def t3_232jobs0 : List Job := [⟨plan874,[],none,⟨3,3,0⟩⟩]

def t3_232jobs : List Job := t3_232jobs0




def t3_233root : Job := ⟨plan875,[],none,⟨3,3,0⟩⟩
def t3_233jobs0 : List Job := [⟨plan875,[],none,⟨3,3,0⟩⟩]

def t3_233jobs : List Job := t3_233jobs0




def t3_234root : Job := ⟨plan876,[],none,⟨3,3,0⟩⟩
def t3_234jobs0 : List Job := [⟨plan876,[],none,⟨3,3,0⟩⟩]

def t3_234jobs : List Job := t3_234jobs0




def t3_235root : Job := ⟨plan877,[],none,⟨3,3,0⟩⟩
def t3_235jobs0 : List Job := [⟨plan877,[],none,⟨3,3,0⟩⟩]

def t3_235jobs : List Job := t3_235jobs0




def t3_236root : Job := ⟨plan812,[],none,⟨3,1,0⟩⟩
def t3_236jobs0 : List Job := [⟨plan812,[],none,⟨3,1,0⟩⟩]

def t3_236jobs : List Job := t3_236jobs0




def t3_237root : Job := ⟨plan813,[],none,⟨3,1,0⟩⟩
def t3_237jobs0 : List Job := [⟨plan813,[],none,⟨3,1,0⟩⟩]

def t3_237jobs : List Job := t3_237jobs0




def t3_238root : Job := ⟨plan878,[],none,⟨3,3,0⟩⟩
def t3_238jobs0 : List Job := [⟨plan878,[],none,⟨3,3,0⟩⟩]

def t3_238jobs : List Job := t3_238jobs0




def t3_239root : Job := ⟨plan879,[],none,⟨3,3,0⟩⟩
def t3_239jobs0 : List Job := [⟨plan879,[],none,⟨3,3,0⟩⟩]

def t3_239jobs : List Job := t3_239jobs0




def t3_240root : Job := ⟨plan880,[],none,⟨3,3,0⟩⟩
def t3_240jobs0 : List Job := [⟨plan880,[],none,⟨3,3,0⟩⟩]

def t3_240jobs : List Job := t3_240jobs0




def t3_241root : Job := ⟨plan881,[],none,⟨3,3,0⟩⟩
def t3_241jobs0 : List Job := [⟨plan881,[],none,⟨3,3,0⟩⟩]

def t3_241jobs : List Job := t3_241jobs0




def t3_242root : Job := ⟨plan882,[],none,⟨3,3,0⟩⟩
def t3_242jobs0 : List Job := [⟨plan882,[],none,⟨3,3,0⟩⟩]

def t3_242jobs : List Job := t3_242jobs0




def t3_243root : Job := ⟨plan883,[],none,⟨3,3,0⟩⟩
def t3_243jobs0 : List Job := [⟨plan883,[],none,⟨3,3,0⟩⟩]

def t3_243jobs : List Job := t3_243jobs0




def t3_244root : Job := ⟨plan814,[],none,⟨3,1,0⟩⟩
def t3_244jobs0 : List Job := [⟨plan814,[],none,⟨3,1,0⟩⟩]

def t3_244jobs : List Job := t3_244jobs0




def t3_245root : Job := ⟨plan884,[],none,⟨3,3,0⟩⟩
def t3_245jobs0 : List Job := [⟨plan884,[],none,⟨3,3,0⟩⟩]

def t3_245jobs : List Job := t3_245jobs0




def t3_246root : Job := ⟨plan885,[],none,⟨3,3,0⟩⟩
def t3_246jobs0 : List Job := [⟨plan885,[],none,⟨3,3,0⟩⟩]

def t3_246jobs : List Job := t3_246jobs0




def t3_247root : Job := ⟨plan886,[],none,⟨3,3,0⟩⟩
def t3_247jobs0 : List Job := [⟨plan886,[],none,⟨3,3,0⟩⟩]

def t3_247jobs : List Job := t3_247jobs0




def t3_248root : Job := ⟨plan887,[],none,⟨3,3,0⟩⟩
def t3_248jobs0 : List Job := [⟨plan887,[],none,⟨3,3,0⟩⟩]

def t3_248jobs : List Job := t3_248jobs0




def t3_249root : Job := ⟨plan888,[],none,⟨3,3,0⟩⟩
def t3_249jobs0 : List Job := [⟨plan888,[],none,⟨3,3,0⟩⟩]

def t3_249jobs : List Job := t3_249jobs0




def t3_250root : Job := ⟨plan889,[],none,⟨3,3,0⟩⟩
def t3_250jobs0 : List Job := [⟨plan889,[],none,⟨3,3,0⟩⟩]

def t3_250jobs : List Job := t3_250jobs0




def t3_251root : Job := ⟨plan709,[],none,⟨3,0,0⟩⟩
def t3_251jobs0 : List Job := [⟨plan709,[],none,⟨3,0,0⟩⟩]

def t3_251jobs : List Job := t3_251jobs0




def t3_252root : Job := ⟨plan815,[],none,⟨3,1,0⟩⟩
def t3_252jobs0 : List Job := [⟨plan815,[],none,⟨3,1,0⟩⟩]

def t3_252jobs : List Job := t3_252jobs0




def t3_253root : Job := ⟨plan816,[],none,⟨3,1,0⟩⟩
def t3_253jobs0 : List Job := [⟨plan816,[],none,⟨3,1,0⟩⟩]

def t3_253jobs : List Job := t3_253jobs0




def t3_254root : Job := ⟨plan817,[],none,⟨3,1,0⟩⟩
def t3_254jobs0 : List Job := [⟨plan817,[],none,⟨3,1,0⟩⟩]

def t3_254jobs : List Job := t3_254jobs0




def t3_255root : Job := ⟨plan890,[],none,⟨3,3,0⟩⟩
def t3_255jobs0 : List Job := [⟨plan890,[],none,⟨3,3,0⟩⟩]

def t3_255jobs : List Job := t3_255jobs0




def t3_256root : Job := ⟨plan891,[],none,⟨3,3,0⟩⟩
def t3_256jobs0 : List Job := [⟨plan891,[],none,⟨3,3,0⟩⟩]

def t3_256jobs : List Job := t3_256jobs0




def t3_257root : Job := ⟨plan892,[],none,⟨3,3,0⟩⟩
def t3_257jobs0 : List Job := [⟨plan892,[],none,⟨3,3,0⟩⟩]

def t3_257jobs : List Job := t3_257jobs0




def t3_258root : Job := ⟨plan893,[],none,⟨3,3,0⟩⟩
def t3_258jobs0 : List Job := [⟨plan893,[],none,⟨3,3,0⟩⟩]

def t3_258jobs : List Job := t3_258jobs0




def t3_259root : Job := ⟨plan818,[],none,⟨3,1,0⟩⟩
def t3_259jobs0 : List Job := [⟨plan818,[],none,⟨3,1,0⟩⟩]

def t3_259jobs : List Job := t3_259jobs0




def t3_260root : Job := ⟨plan894,[],none,⟨3,3,0⟩⟩
def t3_260jobs0 : List Job := [⟨plan894,[],none,⟨3,3,0⟩⟩]

def t3_260jobs : List Job := t3_260jobs0




def t3_261root : Job := ⟨plan895,[],none,⟨3,3,0⟩⟩
def t3_261jobs0 : List Job := [⟨plan895,[],none,⟨3,3,0⟩⟩]

def t3_261jobs : List Job := t3_261jobs0




def t3_262root : Job := ⟨plan896,[],none,⟨3,3,0⟩⟩
def t3_262jobs0 : List Job := [⟨plan896,[],none,⟨3,3,0⟩⟩]

def t3_262jobs : List Job := t3_262jobs0




def t3_263root : Job := ⟨plan897,[],none,⟨3,3,0⟩⟩
def t3_263jobs0 : List Job := [⟨plan897,[],none,⟨3,3,0⟩⟩]

def t3_263jobs : List Job := t3_263jobs0




def t3_264root : Job := ⟨plan898,[],none,⟨3,3,0⟩⟩
def t3_264jobs0 : List Job := [⟨plan898,[],none,⟨3,3,0⟩⟩]

def t3_264jobs : List Job := t3_264jobs0




def t3_265root : Job := ⟨plan899,[],none,⟨3,3,0⟩⟩
def t3_265jobs0 : List Job := [⟨plan899,[],none,⟨3,3,0⟩⟩]

def t3_265jobs : List Job := t3_265jobs0




def t3_266root : Job := ⟨plan900,[],none,⟨3,3,0⟩⟩
def t3_266jobs0 : List Job := [⟨plan900,[],none,⟨3,3,0⟩⟩]

def t3_266jobs : List Job := t3_266jobs0




def t3_267root : Job := ⟨plan901,[],none,⟨3,3,0⟩⟩
def t3_267jobs0 : List Job := [⟨plan901,[],none,⟨3,3,0⟩⟩]

def t3_267jobs : List Job := t3_267jobs0




def t3_268root : Job := ⟨plan902,[],none,⟨3,3,0⟩⟩
def t3_268jobs0 : List Job := [⟨plan902,[],none,⟨3,3,0⟩⟩]

def t3_268jobs : List Job := t3_268jobs0




def t4_0root : Job := ⟨plan1694,[],none,⟨6,0,0⟩⟩
def t4_0jobs0 : List Job := [⟨plan1694,[],none,⟨6,0,0⟩⟩]

def t4_0jobs : List Job := t4_0jobs0




def t4_1root : Job := ⟨plan1713,[],none,⟨6,0,0⟩⟩
def t4_1jobs0 : List Job := [⟨plan1713,[],none,⟨6,0,0⟩⟩]

def t4_1jobs : List Job := t4_1jobs0




def t4_2root : Job := ⟨plan1714,[],none,⟨6,0,0⟩⟩
def t4_2jobs0 : List Job := [⟨plan1714,[],none,⟨6,0,0⟩⟩]

def t4_2jobs : List Job := t4_2jobs0




def t4_3root : Job := ⟨plan1715,[],none,⟨6,0,0⟩⟩
def t4_3jobs0 : List Job := [⟨plan1715,[],none,⟨6,0,0⟩⟩]

def t4_3jobs : List Job := t4_3jobs0




def t4_4root : Job := ⟨plan1695,[],none,⟨6,0,0⟩⟩
def t4_4jobs0 : List Job := [⟨plan1695,[],none,⟨6,0,0⟩⟩]

def t4_4jobs : List Job := t4_4jobs0




def t4_5root : Job := ⟨plan1716,[],none,⟨6,0,0⟩⟩
def t4_5jobs0 : List Job := [⟨plan1716,[],none,⟨6,0,0⟩⟩]

def t4_5jobs : List Job := t4_5jobs0




def t4_6root : Job := ⟨plan1717,[],none,⟨6,0,0⟩⟩
def t4_6jobs0 : List Job := [⟨plan1717,[],none,⟨6,0,0⟩⟩]

def t4_6jobs : List Job := t4_6jobs0




def t4_7root : Job := ⟨plan1718,[],none,⟨6,0,0⟩⟩
def t4_7jobs0 : List Job := [⟨plan1718,[],none,⟨6,0,0⟩⟩]

def t4_7jobs : List Job := t4_7jobs0




def t4_8root : Job := ⟨plan1719,[],none,⟨6,0,0⟩⟩
def t4_8jobs0 : List Job := [⟨plan1719,[],none,⟨6,0,0⟩⟩]

def t4_8jobs : List Job := t4_8jobs0




def t4_9root : Job := ⟨plan1804,[],none,⟨6,1,0⟩⟩
def t4_9jobs0 : List Job := [⟨plan1804,[],none,⟨6,1,0⟩⟩]

def t4_9jobs : List Job := t4_9jobs0




def t4_10root : Job := ⟨plan1805,[],none,⟨6,1,0⟩⟩
def t4_10jobs0 : List Job := [⟨plan1805,[],none,⟨6,1,0⟩⟩]

def t4_10jobs : List Job := t4_10jobs0




def t4_11root : Job := ⟨plan1806,[],none,⟨6,1,0⟩⟩
def t4_11jobs0 : List Job := [⟨plan1806,[],none,⟨6,1,0⟩⟩]

def t4_11jobs : List Job := t4_11jobs0




def t4_12root : Job := ⟨plan1807,[],none,⟨6,1,0⟩⟩
def t4_12jobs0 : List Job := [⟨plan1807,[],none,⟨6,1,0⟩⟩]

def t4_12jobs : List Job := t4_12jobs0




def t4_13root : Job := ⟨plan1808,[],none,⟨6,1,0⟩⟩
def t4_13jobs0 : List Job := [⟨plan1808,[],none,⟨6,1,0⟩⟩]

def t4_13jobs : List Job := t4_13jobs0




def t4_14root : Job := ⟨plan1809,[],none,⟨6,1,0⟩⟩
def t4_14jobs0 : List Job := [⟨plan1809,[],none,⟨6,1,0⟩⟩]

def t4_14jobs : List Job := t4_14jobs0




def t4_15root : Job := ⟨plan1810,[],none,⟨6,1,0⟩⟩
def t4_15jobs0 : List Job := [⟨plan1810,[],none,⟨6,1,0⟩⟩]

def t4_15jobs : List Job := t4_15jobs0




def t4_16root : Job := ⟨plan1720,[],none,⟨6,0,0⟩⟩
def t4_16jobs0 : List Job := [⟨plan1720,[],none,⟨6,0,0⟩⟩]

def t4_16jobs : List Job := t4_16jobs0




def t4_17root : Job := ⟨plan1811,[],none,⟨6,1,0⟩⟩
def t4_17jobs0 : List Job := [⟨plan1811,[],none,⟨6,1,0⟩⟩]

def t4_17jobs : List Job := t4_17jobs0




def t4_18root : Job := ⟨plan1812,[],none,⟨6,1,0⟩⟩
def t4_18jobs0 : List Job := [⟨plan1812,[],none,⟨6,1,0⟩⟩]

def t4_18jobs : List Job := t4_18jobs0




def t4_19root : Job := ⟨plan1813,[],none,⟨6,1,0⟩⟩
def t4_19jobs0 : List Job := [⟨plan1813,[],none,⟨6,1,0⟩⟩]

def t4_19jobs : List Job := t4_19jobs0




def t4_20root : Job := ⟨plan1814,[],none,⟨6,1,0⟩⟩
def t4_20jobs0 : List Job := [⟨plan1814,[],none,⟨6,1,0⟩⟩]

def t4_20jobs : List Job := t4_20jobs0




def t4_21root : Job := ⟨plan1815,[],none,⟨6,1,0⟩⟩
def t4_21jobs0 : List Job := [⟨plan1815,[],none,⟨6,1,0⟩⟩]

def t4_21jobs : List Job := t4_21jobs0




def t4_22root : Job := ⟨plan1696,[],none,⟨6,0,0⟩⟩
def t4_22jobs0 : List Job := [⟨plan1696,[],none,⟨6,0,0⟩⟩]

def t4_22jobs : List Job := t4_22jobs0




def t4_23root : Job := ⟨plan1697,[],none,⟨6,0,0⟩⟩
def t4_23jobs0 : List Job := [⟨plan1697,[],none,⟨6,0,0⟩⟩]

def t4_23jobs : List Job := t4_23jobs0




def t4_24root : Job := ⟨plan1721,[],none,⟨6,0,0⟩⟩
def t4_24jobs0 : List Job := [⟨plan1721,[],none,⟨6,0,0⟩⟩]

def t4_24jobs : List Job := t4_24jobs0




def t4_25root : Job := ⟨plan1722,[],none,⟨6,0,0⟩⟩
def t4_25jobs0 : List Job := [⟨plan1722,[],none,⟨6,0,0⟩⟩]

def t4_25jobs : List Job := t4_25jobs0




def t4_26root : Job := ⟨plan1723,[],none,⟨6,0,0⟩⟩
def t4_26jobs0 : List Job := [⟨plan1723,[],none,⟨6,0,0⟩⟩]

def t4_26jobs : List Job := t4_26jobs0




def t4_27root : Job := ⟨plan1724,[],none,⟨6,0,0⟩⟩
def t4_27jobs0 : List Job := [⟨plan1724,[],none,⟨6,0,0⟩⟩]

def t4_27jobs : List Job := t4_27jobs0




def t4_28root : Job := ⟨plan1725,[],none,⟨6,0,0⟩⟩
def t4_28jobs0 : List Job := [⟨plan1725,[],none,⟨6,0,0⟩⟩]

def t4_28jobs : List Job := t4_28jobs0




def t4_29root : Job := ⟨plan1698,[],none,⟨6,0,0⟩⟩
def t4_29jobs0 : List Job := [⟨plan1698,[],none,⟨6,0,0⟩⟩]

def t4_29jobs : List Job := t4_29jobs0




def t4_30root : Job := ⟨plan1726,[],none,⟨6,0,0⟩⟩
def t4_30jobs0 : List Job := [⟨plan1726,[],none,⟨6,0,0⟩⟩]

def t4_30jobs : List Job := t4_30jobs0




def t4_31root : Job := ⟨plan1727,[],none,⟨6,0,0⟩⟩
def t4_31jobs0 : List Job := [⟨plan1727,[],none,⟨6,0,0⟩⟩]

def t4_31jobs : List Job := t4_31jobs0




def t4_32root : Job := ⟨plan1728,[],none,⟨6,0,0⟩⟩
def t4_32jobs0 : List Job := [⟨plan1728,[],none,⟨6,0,0⟩⟩]

def t4_32jobs : List Job := t4_32jobs0




def t4_33root : Job := ⟨plan1729,[],none,⟨6,0,0⟩⟩
def t4_33jobs0 : List Job := [⟨plan1729,[],none,⟨6,0,0⟩⟩]

def t4_33jobs : List Job := t4_33jobs0




def t4_34root : Job := ⟨plan1816,[],none,⟨6,1,0⟩⟩
def t4_34jobs0 : List Job := [⟨plan1816,[],none,⟨6,1,0⟩⟩]

def t4_34jobs : List Job := t4_34jobs0




def t4_35root : Job := ⟨plan1817,[],none,⟨6,1,0⟩⟩
def t4_35jobs0 : List Job := [⟨plan1817,[],none,⟨6,1,0⟩⟩]

def t4_35jobs : List Job := t4_35jobs0




def t4_36root : Job := ⟨plan1818,[],none,⟨6,1,0⟩⟩
def t4_36jobs0 : List Job := [⟨plan1818,[],none,⟨6,1,0⟩⟩]

def t4_36jobs : List Job := t4_36jobs0




def t4_37root : Job := ⟨plan1819,[],none,⟨6,1,0⟩⟩
def t4_37jobs0 : List Job := [⟨plan1819,[],none,⟨6,1,0⟩⟩]

def t4_37jobs : List Job := t4_37jobs0




def t4_38root : Job := ⟨plan1820,[],none,⟨6,1,0⟩⟩
def t4_38jobs0 : List Job := [⟨plan1820,[],none,⟨6,1,0⟩⟩]

def t4_38jobs : List Job := t4_38jobs0




def t4_39root : Job := ⟨plan1821,[],none,⟨6,1,0⟩⟩
def t4_39jobs0 : List Job := [⟨plan1821,[],none,⟨6,1,0⟩⟩]

def t4_39jobs : List Job := t4_39jobs0




def t4_40root : Job := ⟨plan1822,[],none,⟨6,1,0⟩⟩
def t4_40jobs0 : List Job := [⟨plan1822,[],none,⟨6,1,0⟩⟩]

def t4_40jobs : List Job := t4_40jobs0




def t4_41root : Job := ⟨plan1823,[],none,⟨6,1,0⟩⟩
def t4_41jobs0 : List Job := [⟨plan1823,[],none,⟨6,1,0⟩⟩]

def t4_41jobs : List Job := t4_41jobs0




def t4_42root : Job := ⟨plan1824,[],none,⟨6,1,0⟩⟩
def t4_42jobs0 : List Job := [⟨plan1824,[],none,⟨6,1,0⟩⟩]

def t4_42jobs : List Job := t4_42jobs0




def t4_43root : Job := ⟨plan1730,[],none,⟨6,0,0⟩⟩
def t4_43jobs0 : List Job := [⟨plan1730,[],none,⟨6,0,0⟩⟩]

def t4_43jobs : List Job := t4_43jobs0




def t4_44root : Job := ⟨plan1825,[],none,⟨6,1,0⟩⟩
def t4_44jobs0 : List Job := [⟨plan1825,[],none,⟨6,1,0⟩⟩]

def t4_44jobs : List Job := t4_44jobs0




def t4_45root : Job := ⟨plan1826,[],none,⟨6,1,0⟩⟩
def t4_45jobs0 : List Job := [⟨plan1826,[],none,⟨6,1,0⟩⟩]

def t4_45jobs : List Job := t4_45jobs0




def t4_46root : Job := ⟨plan1827,[],none,⟨6,1,0⟩⟩
def t4_46jobs0 : List Job := [⟨plan1827,[],none,⟨6,1,0⟩⟩]

def t4_46jobs : List Job := t4_46jobs0




def t4_47root : Job := ⟨plan1828,[],none,⟨6,1,0⟩⟩
def t4_47jobs0 : List Job := [⟨plan1828,[],none,⟨6,1,0⟩⟩]

def t4_47jobs : List Job := t4_47jobs0




def t4_48root : Job := ⟨plan1829,[],none,⟨6,1,0⟩⟩
def t4_48jobs0 : List Job := [⟨plan1829,[],none,⟨6,1,0⟩⟩]

def t4_48jobs : List Job := t4_48jobs0




def t4_49root : Job := ⟨plan1830,[],none,⟨6,1,0⟩⟩
def t4_49jobs0 : List Job := [⟨plan1830,[],none,⟨6,1,0⟩⟩]

def t4_49jobs : List Job := t4_49jobs0




def t4_50root : Job := ⟨plan1699,[],none,⟨6,0,0⟩⟩
def t4_50jobs0 : List Job := [⟨plan1699,[],none,⟨6,0,0⟩⟩]

def t4_50jobs : List Job := t4_50jobs0




def t4_51root : Job := ⟨plan1731,[],none,⟨6,0,0⟩⟩
def t4_51jobs0 : List Job := [⟨plan1731,[],none,⟨6,0,0⟩⟩]

def t4_51jobs : List Job := t4_51jobs0




def t4_52root : Job := ⟨plan1732,[],none,⟨6,0,0⟩⟩
def t4_52jobs0 : List Job := [⟨plan1732,[],none,⟨6,0,0⟩⟩]

def t4_52jobs : List Job := t4_52jobs0




def t4_53root : Job := ⟨plan1733,[],none,⟨6,0,0⟩⟩
def t4_53jobs0 : List Job := [⟨plan1733,[],none,⟨6,0,0⟩⟩]

def t4_53jobs : List Job := t4_53jobs0




def t4_54root : Job := ⟨plan1831,[],none,⟨6,1,0⟩⟩
def t4_54jobs0 : List Job := [⟨plan1831,[],none,⟨6,1,0⟩⟩]

def t4_54jobs : List Job := t4_54jobs0




def t4_55root : Job := ⟨plan1832,[],none,⟨6,1,0⟩⟩
def t4_55jobs0 : List Job := [⟨plan1832,[],none,⟨6,1,0⟩⟩]

def t4_55jobs : List Job := t4_55jobs0




def t4_56root : Job := ⟨plan1833,[],none,⟨6,1,0⟩⟩
def t4_56jobs0 : List Job := [⟨plan1833,[],none,⟨6,1,0⟩⟩]

def t4_56jobs : List Job := t4_56jobs0




def t4_57root : Job := ⟨plan1834,[],none,⟨6,1,0⟩⟩
def t4_57jobs0 : List Job := [⟨plan1834,[],none,⟨6,1,0⟩⟩]

def t4_57jobs : List Job := t4_57jobs0




def t4_58root : Job := ⟨plan1835,[],none,⟨6,1,0⟩⟩
def t4_58jobs0 : List Job := [⟨plan1835,[],none,⟨6,1,0⟩⟩]

def t4_58jobs : List Job := t4_58jobs0




def t4_59root : Job := ⟨plan1836,[],none,⟨6,1,0⟩⟩
def t4_59jobs0 : List Job := [⟨plan1836,[],none,⟨6,1,0⟩⟩]

def t4_59jobs : List Job := t4_59jobs0




def t4_60root : Job := ⟨plan1734,[],none,⟨6,0,0⟩⟩
def t4_60jobs0 : List Job := [⟨plan1734,[],none,⟨6,0,0⟩⟩]

def t4_60jobs : List Job := t4_60jobs0




def t4_61root : Job := ⟨plan1837,[],none,⟨6,1,0⟩⟩
def t4_61jobs0 : List Job := [⟨plan1837,[],none,⟨6,1,0⟩⟩]

def t4_61jobs : List Job := t4_61jobs0




def t4_62root : Job := ⟨plan1838,[],none,⟨6,1,0⟩⟩
def t4_62jobs0 : List Job := [⟨plan1838,[],none,⟨6,1,0⟩⟩]

def t4_62jobs : List Job := t4_62jobs0




def t4_63root : Job := ⟨plan1839,[],none,⟨6,1,0⟩⟩
def t4_63jobs0 : List Job := [⟨plan1839,[],none,⟨6,1,0⟩⟩]

def t4_63jobs : List Job := t4_63jobs0




def t4_64root : Job := ⟨plan1735,[],none,⟨6,0,0⟩⟩
def t4_64jobs0 : List Job := [⟨plan1735,[],none,⟨6,0,0⟩⟩]

def t4_64jobs : List Job := t4_64jobs0




def t4_65root : Job := ⟨plan1840,[],none,⟨6,1,0⟩⟩
def t4_65jobs0 : List Job := [⟨plan1840,[],none,⟨6,1,0⟩⟩]

def t4_65jobs : List Job := t4_65jobs0




def t4_66root : Job := ⟨plan1841,[],none,⟨6,1,0⟩⟩
def t4_66jobs0 : List Job := [⟨plan1841,[],none,⟨6,1,0⟩⟩]

def t4_66jobs : List Job := t4_66jobs0




def t4_67root : Job := ⟨plan1842,[],none,⟨6,1,0⟩⟩
def t4_67jobs0 : List Job := [⟨plan1842,[],none,⟨6,1,0⟩⟩]

def t4_67jobs : List Job := t4_67jobs0




def t4_68root : Job := ⟨plan1843,[],none,⟨6,1,0⟩⟩
def t4_68jobs0 : List Job := [⟨plan1843,[],none,⟨6,1,0⟩⟩]

def t4_68jobs : List Job := t4_68jobs0




def t4_69root : Job := ⟨plan2020,[],none,⟨6,3,0⟩⟩
def t4_69jobs0 : List Job := [⟨plan2020,[],none,⟨6,3,0⟩⟩]

def t4_69jobs : List Job := t4_69jobs0




def t4_70root : Job := ⟨plan2021,[],none,⟨6,3,0⟩⟩
def t4_70jobs0 : List Job := [⟨plan2021,[],none,⟨6,3,0⟩⟩]

def t4_70jobs : List Job := t4_70jobs0




def t4_71root : Job := ⟨plan2022,[],none,⟨6,3,0⟩⟩
def t4_71jobs0 : List Job := [⟨plan2022,[],none,⟨6,3,0⟩⟩]

def t4_71jobs : List Job := t4_71jobs0




def t4_72root : Job := ⟨plan2023,[],none,⟨6,3,0⟩⟩
def t4_72jobs0 : List Job := [⟨plan2023,[],none,⟨6,3,0⟩⟩]

def t4_72jobs : List Job := t4_72jobs0




def t4_73root : Job := ⟨plan2024,[],none,⟨6,3,0⟩⟩
def t4_73jobs0 : List Job := [⟨plan2024,[],none,⟨6,3,0⟩⟩]

def t4_73jobs : List Job := t4_73jobs0




def t4_74root : Job := ⟨plan2025,[],none,⟨6,3,0⟩⟩
def t4_74jobs0 : List Job := [⟨plan2025,[],none,⟨6,3,0⟩⟩]

def t4_74jobs : List Job := t4_74jobs0




def t4_75root : Job := ⟨plan2026,[],none,⟨6,3,0⟩⟩
def t4_75jobs0 : List Job := [⟨plan2026,[],none,⟨6,3,0⟩⟩]

def t4_75jobs : List Job := t4_75jobs0




def t4_76root : Job := ⟨plan1844,[],none,⟨6,1,0⟩⟩
def t4_76jobs0 : List Job := [⟨plan1844,[],none,⟨6,1,0⟩⟩]

def t4_76jobs : List Job := t4_76jobs0




def t4_77root : Job := ⟨plan2027,[],none,⟨6,3,0⟩⟩
def t4_77jobs0 : List Job := [⟨plan2027,[],none,⟨6,3,0⟩⟩]

def t4_77jobs : List Job := t4_77jobs0




def t4_78root : Job := ⟨plan2028,[],none,⟨6,3,0⟩⟩
def t4_78jobs0 : List Job := [⟨plan2028,[],none,⟨6,3,0⟩⟩]

def t4_78jobs : List Job := t4_78jobs0




def t4_79root : Job := ⟨plan2029,[],none,⟨6,3,0⟩⟩
def t4_79jobs0 : List Job := [⟨plan2029,[],none,⟨6,3,0⟩⟩]

def t4_79jobs : List Job := t4_79jobs0




def t4_80root : Job := ⟨plan2030,[],none,⟨6,3,0⟩⟩
def t4_80jobs0 : List Job := [⟨plan2030,[],none,⟨6,3,0⟩⟩]

def t4_80jobs : List Job := t4_80jobs0




def t4_81root : Job := ⟨plan2031,[],none,⟨6,3,0⟩⟩
def t4_81jobs0 : List Job := [⟨plan2031,[],none,⟨6,3,0⟩⟩]

def t4_81jobs : List Job := t4_81jobs0




def t4_82root : Job := ⟨plan1736,[],none,⟨6,0,0⟩⟩
def t4_82jobs0 : List Job := [⟨plan1736,[],none,⟨6,0,0⟩⟩]

def t4_82jobs : List Job := t4_82jobs0




def t4_83root : Job := ⟨plan1845,[],none,⟨6,1,0⟩⟩
def t4_83jobs0 : List Job := [⟨plan1845,[],none,⟨6,1,0⟩⟩]

def t4_83jobs : List Job := t4_83jobs0




def t4_84root : Job := ⟨plan1846,[],none,⟨6,1,0⟩⟩
def t4_84jobs0 : List Job := [⟨plan1846,[],none,⟨6,1,0⟩⟩]

def t4_84jobs : List Job := t4_84jobs0




def t4_85root : Job := ⟨plan1847,[],none,⟨6,1,0⟩⟩
def t4_85jobs0 : List Job := [⟨plan1847,[],none,⟨6,1,0⟩⟩]

def t4_85jobs : List Job := t4_85jobs0




def t4_86root : Job := ⟨plan1848,[],none,⟨6,1,0⟩⟩
def t4_86jobs0 : List Job := [⟨plan1848,[],none,⟨6,1,0⟩⟩]

def t4_86jobs : List Job := t4_86jobs0




def t4_87root : Job := ⟨plan2032,[],none,⟨6,3,0⟩⟩
def t4_87jobs0 : List Job := [⟨plan2032,[],none,⟨6,3,0⟩⟩]

def t4_87jobs : List Job := t4_87jobs0




def t4_88root : Job := ⟨plan2033,[],none,⟨6,3,0⟩⟩
def t4_88jobs0 : List Job := [⟨plan2033,[],none,⟨6,3,0⟩⟩]

def t4_88jobs : List Job := t4_88jobs0




def t4_89root : Job := ⟨plan2034,[],none,⟨6,3,0⟩⟩
def t4_89jobs0 : List Job := [⟨plan2034,[],none,⟨6,3,0⟩⟩]

def t4_89jobs : List Job := t4_89jobs0




def t4_90root : Job := ⟨plan2035,[],none,⟨6,3,0⟩⟩
def t4_90jobs0 : List Job := [⟨plan2035,[],none,⟨6,3,0⟩⟩]

def t4_90jobs : List Job := t4_90jobs0




def t4_91root : Job := ⟨plan2036,[],none,⟨6,3,0⟩⟩
def t4_91jobs0 : List Job := [⟨plan2036,[],none,⟨6,3,0⟩⟩]

def t4_91jobs : List Job := t4_91jobs0




def t4_92root : Job := ⟨plan2037,[],none,⟨6,3,0⟩⟩
def t4_92jobs0 : List Job := [⟨plan2037,[],none,⟨6,3,0⟩⟩]

def t4_92jobs : List Job := t4_92jobs0




def t4_93root : Job := ⟨plan2038,[],none,⟨6,3,0⟩⟩
def t4_93jobs0 : List Job := [⟨plan2038,[],none,⟨6,3,0⟩⟩]

def t4_93jobs : List Job := t4_93jobs0




def t4_94root : Job := ⟨plan2039,[],none,⟨6,3,0⟩⟩
def t4_94jobs0 : List Job := [⟨plan2039,[],none,⟨6,3,0⟩⟩]

def t4_94jobs : List Job := t4_94jobs0




def t4_95root : Job := ⟨plan2040,[],none,⟨6,3,0⟩⟩
def t4_95jobs0 : List Job := [⟨plan2040,[],none,⟨6,3,0⟩⟩]

def t4_95jobs : List Job := t4_95jobs0




def t4_96root : Job := ⟨plan1849,[],none,⟨6,1,0⟩⟩
def t4_96jobs0 : List Job := [⟨plan1849,[],none,⟨6,1,0⟩⟩]

def t4_96jobs : List Job := t4_96jobs0




def t4_97root : Job := ⟨plan2041,[],none,⟨6,3,0⟩⟩
def t4_97jobs0 : List Job := [⟨plan2041,[],none,⟨6,3,0⟩⟩]

def t4_97jobs : List Job := t4_97jobs0




def t4_98root : Job := ⟨plan2042,[],none,⟨6,3,0⟩⟩
def t4_98jobs0 : List Job := [⟨plan2042,[],none,⟨6,3,0⟩⟩]

def t4_98jobs : List Job := t4_98jobs0




def t4_99root : Job := ⟨plan2043,[],none,⟨6,3,0⟩⟩
def t4_99jobs0 : List Job := [⟨plan2043,[],none,⟨6,3,0⟩⟩]

def t4_99jobs : List Job := t4_99jobs0




def t4_100root : Job := ⟨plan2044,[],none,⟨6,3,0⟩⟩
def t4_100jobs0 : List Job := [⟨plan2044,[],none,⟨6,3,0⟩⟩]

def t4_100jobs : List Job := t4_100jobs0




def t4_101root : Job := ⟨plan2045,[],none,⟨6,3,0⟩⟩
def t4_101jobs0 : List Job := [⟨plan2045,[],none,⟨6,3,0⟩⟩]

def t4_101jobs : List Job := t4_101jobs0




def t4_102root : Job := ⟨plan2046,[],none,⟨6,3,0⟩⟩
def t4_102jobs0 : List Job := [⟨plan2046,[],none,⟨6,3,0⟩⟩]

def t4_102jobs : List Job := t4_102jobs0




def t4_103root : Job := ⟨plan2047,[],none,⟨6,3,0⟩⟩
def t4_103jobs0 : List Job := [⟨plan2047,[],none,⟨6,3,0⟩⟩]

def t4_103jobs : List Job := t4_103jobs0




def t4_104root : Job := ⟨plan2048,[],none,⟨6,3,0⟩⟩
def t4_104jobs0 : List Job := [⟨plan2048,[],none,⟨6,3,0⟩⟩]

def t4_104jobs : List Job := t4_104jobs0




def t4_105root : Job := ⟨plan2049,[],none,⟨6,3,0⟩⟩
def t4_105jobs0 : List Job := [⟨plan2049,[],none,⟨6,3,0⟩⟩]

def t4_105jobs : List Job := t4_105jobs0




def t4_106root : Job := ⟨plan2050,[],none,⟨6,3,0⟩⟩
def t4_106jobs0 : List Job := [⟨plan2050,[],none,⟨6,3,0⟩⟩]

def t4_106jobs : List Job := t4_106jobs0




def t4_107root : Job := ⟨plan2051,[],none,⟨6,3,0⟩⟩
def t4_107jobs0 : List Job := [⟨plan2051,[],none,⟨6,3,0⟩⟩]

def t4_107jobs : List Job := t4_107jobs0




def t4_108root : Job := ⟨plan2052,[],none,⟨6,3,0⟩⟩
def t4_108jobs0 : List Job := [⟨plan2052,[],none,⟨6,3,0⟩⟩]

def t4_108jobs : List Job := t4_108jobs0




def t4_109root : Job := ⟨plan2053,[],none,⟨6,3,0⟩⟩
def t4_109jobs0 : List Job := [⟨plan2053,[],none,⟨6,3,0⟩⟩]

def t4_109jobs : List Job := t4_109jobs0




def t4_110root : Job := ⟨plan1737,[],none,⟨6,0,0⟩⟩
def t4_110jobs0 : List Job := [⟨plan1737,[],none,⟨6,0,0⟩⟩]

def t4_110jobs : List Job := t4_110jobs0




def t4_111root : Job := ⟨plan1850,[],none,⟨6,1,0⟩⟩
def t4_111jobs0 : List Job := [⟨plan1850,[],none,⟨6,1,0⟩⟩]

def t4_111jobs : List Job := t4_111jobs0




def t4_112root : Job := ⟨plan1851,[],none,⟨6,1,0⟩⟩
def t4_112jobs0 : List Job := [⟨plan1851,[],none,⟨6,1,0⟩⟩]

def t4_112jobs : List Job := t4_112jobs0




def t4_113root : Job := ⟨plan1852,[],none,⟨6,1,0⟩⟩
def t4_113jobs0 : List Job := [⟨plan1852,[],none,⟨6,1,0⟩⟩]

def t4_113jobs : List Job := t4_113jobs0




def t4_114root : Job := ⟨plan1738,[],none,⟨6,0,0⟩⟩
def t4_114jobs0 : List Job := [⟨plan1738,[],none,⟨6,0,0⟩⟩]

def t4_114jobs : List Job := t4_114jobs0




def t4_115root : Job := ⟨plan1853,[],none,⟨6,1,0⟩⟩
def t4_115jobs0 : List Job := [⟨plan1853,[],none,⟨6,1,0⟩⟩]

def t4_115jobs : List Job := t4_115jobs0




def t4_116root : Job := ⟨plan1854,[],none,⟨6,1,0⟩⟩
def t4_116jobs0 : List Job := [⟨plan1854,[],none,⟨6,1,0⟩⟩]

def t4_116jobs : List Job := t4_116jobs0




def t4_117root : Job := ⟨plan1855,[],none,⟨6,1,0⟩⟩
def t4_117jobs0 : List Job := [⟨plan1855,[],none,⟨6,1,0⟩⟩]

def t4_117jobs : List Job := t4_117jobs0




def t4_118root : Job := ⟨plan1856,[],none,⟨6,1,0⟩⟩
def t4_118jobs0 : List Job := [⟨plan1856,[],none,⟨6,1,0⟩⟩]

def t4_118jobs : List Job := t4_118jobs0




def t4_119root : Job := ⟨plan2054,[],none,⟨6,3,0⟩⟩
def t4_119jobs0 : List Job := [⟨plan2054,[],none,⟨6,3,0⟩⟩]

def t4_119jobs : List Job := t4_119jobs0




def t4_120root : Job := ⟨plan2055,[],none,⟨6,3,0⟩⟩
def t4_120jobs0 : List Job := [⟨plan2055,[],none,⟨6,3,0⟩⟩]

def t4_120jobs : List Job := t4_120jobs0




def t4_121root : Job := ⟨plan2056,[],none,⟨6,3,0⟩⟩
def t4_121jobs0 : List Job := [⟨plan2056,[],none,⟨6,3,0⟩⟩]

def t4_121jobs : List Job := t4_121jobs0




def t4_122root : Job := ⟨plan2057,[],none,⟨6,3,0⟩⟩
def t4_122jobs0 : List Job := [⟨plan2057,[],none,⟨6,3,0⟩⟩]

def t4_122jobs : List Job := t4_122jobs0




def t4_123root : Job := ⟨plan2058,[],none,⟨6,3,0⟩⟩
def t4_123jobs0 : List Job := [⟨plan2058,[],none,⟨6,3,0⟩⟩]

def t4_123jobs : List Job := t4_123jobs0




def t4_124root : Job := ⟨plan2059,[],none,⟨6,3,0⟩⟩
def t4_124jobs0 : List Job := [⟨plan2059,[],none,⟨6,3,0⟩⟩]

def t4_124jobs : List Job := t4_124jobs0




def t4_125root : Job := ⟨plan2060,[],none,⟨6,3,0⟩⟩
def t4_125jobs0 : List Job := [⟨plan2060,[],none,⟨6,3,0⟩⟩]

def t4_125jobs : List Job := t4_125jobs0




def t4_126root : Job := ⟨plan1857,[],none,⟨6,1,0⟩⟩
def t4_126jobs0 : List Job := [⟨plan1857,[],none,⟨6,1,0⟩⟩]

def t4_126jobs : List Job := t4_126jobs0




def t4_127root : Job := ⟨plan2061,[],none,⟨6,3,0⟩⟩
def t4_127jobs0 : List Job := [⟨plan2061,[],none,⟨6,3,0⟩⟩]

def t4_127jobs : List Job := t4_127jobs0




def t4_128root : Job := ⟨plan2062,[],none,⟨6,3,0⟩⟩
def t4_128jobs0 : List Job := [⟨plan2062,[],none,⟨6,3,0⟩⟩]

def t4_128jobs : List Job := t4_128jobs0




def t4_129root : Job := ⟨plan2063,[],none,⟨6,3,0⟩⟩
def t4_129jobs0 : List Job := [⟨plan2063,[],none,⟨6,3,0⟩⟩]

def t4_129jobs : List Job := t4_129jobs0




def t4_130root : Job := ⟨plan2064,[],none,⟨6,3,0⟩⟩
def t4_130jobs0 : List Job := [⟨plan2064,[],none,⟨6,3,0⟩⟩]

def t4_130jobs : List Job := t4_130jobs0




def t4_131root : Job := ⟨plan2065,[],none,⟨6,3,0⟩⟩
def t4_131jobs0 : List Job := [⟨plan2065,[],none,⟨6,3,0⟩⟩]

def t4_131jobs : List Job := t4_131jobs0




def t4_132root : Job := ⟨plan1739,[],none,⟨6,0,0⟩⟩
def t4_132jobs0 : List Job := [⟨plan1739,[],none,⟨6,0,0⟩⟩]

def t4_132jobs : List Job := t4_132jobs0




def t4_133root : Job := ⟨plan1858,[],none,⟨6,1,0⟩⟩
def t4_133jobs0 : List Job := [⟨plan1858,[],none,⟨6,1,0⟩⟩]

def t4_133jobs : List Job := t4_133jobs0




def t4_134root : Job := ⟨plan1859,[],none,⟨6,1,0⟩⟩
def t4_134jobs0 : List Job := [⟨plan1859,[],none,⟨6,1,0⟩⟩]

def t4_134jobs : List Job := t4_134jobs0




def t4_135root : Job := ⟨plan1860,[],none,⟨6,1,0⟩⟩
def t4_135jobs0 : List Job := [⟨plan1860,[],none,⟨6,1,0⟩⟩]

def t4_135jobs : List Job := t4_135jobs0




def t4_136root : Job := ⟨plan2066,[],none,⟨6,3,0⟩⟩
def t4_136jobs0 : List Job := [⟨plan2066,[],none,⟨6,3,0⟩⟩]

def t4_136jobs : List Job := t4_136jobs0




def t4_137root : Job := ⟨plan2067,[],none,⟨6,3,0⟩⟩
def t4_137jobs0 : List Job := [⟨plan2067,[],none,⟨6,3,0⟩⟩]

def t4_137jobs : List Job := t4_137jobs0




def t4_138root : Job := ⟨plan2068,[],none,⟨6,3,0⟩⟩
def t4_138jobs0 : List Job := [⟨plan2068,[],none,⟨6,3,0⟩⟩]

def t4_138jobs : List Job := t4_138jobs0




def t4_139root : Job := ⟨plan2069,[],none,⟨6,3,0⟩⟩
def t4_139jobs0 : List Job := [⟨plan2069,[],none,⟨6,3,0⟩⟩]

def t4_139jobs : List Job := t4_139jobs0




def t4_140root : Job := ⟨plan1861,[],none,⟨6,1,0⟩⟩
def t4_140jobs0 : List Job := [⟨plan1861,[],none,⟨6,1,0⟩⟩]

def t4_140jobs : List Job := t4_140jobs0




def t4_141root : Job := ⟨plan2070,[],none,⟨6,3,0⟩⟩
def t4_141jobs0 : List Job := [⟨plan2070,[],none,⟨6,3,0⟩⟩]

def t4_141jobs : List Job := t4_141jobs0




def t4_142root : Job := ⟨plan2071,[],none,⟨6,3,0⟩⟩
def t4_142jobs0 : List Job := [⟨plan2071,[],none,⟨6,3,0⟩⟩]

def t4_142jobs : List Job := t4_142jobs0




def t4_143root : Job := ⟨plan2072,[],none,⟨6,3,0⟩⟩
def t4_143jobs0 : List Job := [⟨plan2072,[],none,⟨6,3,0⟩⟩]

def t4_143jobs : List Job := t4_143jobs0




def t4_144root : Job := ⟨plan2073,[],none,⟨6,3,0⟩⟩
def t4_144jobs0 : List Job := [⟨plan2073,[],none,⟨6,3,0⟩⟩]

def t4_144jobs : List Job := t4_144jobs0




def t4_145root : Job := ⟨plan2074,[],none,⟨6,3,0⟩⟩
def t4_145jobs0 : List Job := [⟨plan2074,[],none,⟨6,3,0⟩⟩]

def t4_145jobs : List Job := t4_145jobs0




def t4_146root : Job := ⟨plan2075,[],none,⟨6,3,0⟩⟩
def t4_146jobs0 : List Job := [⟨plan2075,[],none,⟨6,3,0⟩⟩]

def t4_146jobs : List Job := t4_146jobs0




def t4_147root : Job := ⟨plan2076,[],none,⟨6,3,0⟩⟩
def t4_147jobs0 : List Job := [⟨plan2076,[],none,⟨6,3,0⟩⟩]

def t4_147jobs : List Job := t4_147jobs0




def t4_148root : Job := ⟨plan2077,[],none,⟨6,3,0⟩⟩
def t4_148jobs0 : List Job := [⟨plan2077,[],none,⟨6,3,0⟩⟩]

def t4_148jobs : List Job := t4_148jobs0




def t4_149root : Job := ⟨plan2078,[],none,⟨6,3,0⟩⟩
def t4_149jobs0 : List Job := [⟨plan2078,[],none,⟨6,3,0⟩⟩]

def t4_149jobs : List Job := t4_149jobs0




def t4_150root : Job := ⟨plan1700,[],none,⟨6,0,0⟩⟩
def t4_150jobs0 : List Job := [⟨plan1700,[],none,⟨6,0,0⟩⟩]

def t4_150jobs : List Job := t4_150jobs0




def t4_151root : Job := ⟨plan1740,[],none,⟨6,0,0⟩⟩
def t4_151jobs0 : List Job := [⟨plan1740,[],none,⟨6,0,0⟩⟩]

def t4_151jobs : List Job := t4_151jobs0




def t4_152root : Job := ⟨plan1741,[],none,⟨6,0,0⟩⟩
def t4_152jobs0 : List Job := [⟨plan1741,[],none,⟨6,0,0⟩⟩]

def t4_152jobs : List Job := t4_152jobs0




def t4_153root : Job := ⟨plan1742,[],none,⟨6,0,0⟩⟩
def t4_153jobs0 : List Job := [⟨plan1742,[],none,⟨6,0,0⟩⟩]

def t4_153jobs : List Job := t4_153jobs0




def t4_154root : Job := ⟨plan1701,[],none,⟨6,0,0⟩⟩
def t4_154jobs0 : List Job := [⟨plan1701,[],none,⟨6,0,0⟩⟩]

def t4_154jobs : List Job := t4_154jobs0




def t4_155root : Job := ⟨plan1702,[],none,⟨6,0,0⟩⟩
def t4_155jobs0 : List Job := [⟨plan1702,[],none,⟨6,0,0⟩⟩]

def t4_155jobs : List Job := t4_155jobs0




def t4_156root : Job := ⟨plan1743,[],none,⟨6,0,0⟩⟩
def t4_156jobs0 : List Job := [⟨plan1743,[],none,⟨6,0,0⟩⟩]

def t4_156jobs : List Job := t4_156jobs0




def t4_157root : Job := ⟨plan1744,[],none,⟨6,0,0⟩⟩
def t4_157jobs0 : List Job := [⟨plan1744,[],none,⟨6,0,0⟩⟩]

def t4_157jobs : List Job := t4_157jobs0




def t4_158root : Job := ⟨plan1745,[],none,⟨6,0,0⟩⟩
def t4_158jobs0 : List Job := [⟨plan1745,[],none,⟨6,0,0⟩⟩]

def t4_158jobs : List Job := t4_158jobs0




def t4_159root : Job := ⟨plan1746,[],none,⟨6,0,0⟩⟩
def t4_159jobs0 : List Job := [⟨plan1746,[],none,⟨6,0,0⟩⟩]

def t4_159jobs : List Job := t4_159jobs0




def t4_160root : Job := ⟨plan1747,[],none,⟨6,0,0⟩⟩
def t4_160jobs0 : List Job := [⟨plan1747,[],none,⟨6,0,0⟩⟩]

def t4_160jobs : List Job := t4_160jobs0




def t4_161root : Job := ⟨plan1703,[],none,⟨6,0,0⟩⟩
def t4_161jobs0 : List Job := [⟨plan1703,[],none,⟨6,0,0⟩⟩]

def t4_161jobs : List Job := t4_161jobs0




def t4_162root : Job := ⟨plan1748,[],none,⟨6,0,0⟩⟩
def t4_162jobs0 : List Job := [⟨plan1748,[],none,⟨6,0,0⟩⟩]

def t4_162jobs : List Job := t4_162jobs0




def t4_163root : Job := ⟨plan1749,[],none,⟨6,0,0⟩⟩
def t4_163jobs0 : List Job := [⟨plan1749,[],none,⟨6,0,0⟩⟩]

def t4_163jobs : List Job := t4_163jobs0




def t4_164root : Job := ⟨plan1750,[],none,⟨6,0,0⟩⟩
def t4_164jobs0 : List Job := [⟨plan1750,[],none,⟨6,0,0⟩⟩]

def t4_164jobs : List Job := t4_164jobs0




def t4_165root : Job := ⟨plan1751,[],none,⟨6,0,0⟩⟩
def t4_165jobs0 : List Job := [⟨plan1751,[],none,⟨6,0,0⟩⟩]

def t4_165jobs : List Job := t4_165jobs0




def t4_166root : Job := ⟨plan1862,[],none,⟨6,1,0⟩⟩
def t4_166jobs0 : List Job := [⟨plan1862,[],none,⟨6,1,0⟩⟩]

def t4_166jobs : List Job := t4_166jobs0




def t4_167root : Job := ⟨plan1863,[],none,⟨6,1,0⟩⟩
def t4_167jobs0 : List Job := [⟨plan1863,[],none,⟨6,1,0⟩⟩]

def t4_167jobs : List Job := t4_167jobs0




def t4_168root : Job := ⟨plan1864,[],none,⟨6,1,0⟩⟩
def t4_168jobs0 : List Job := [⟨plan1864,[],none,⟨6,1,0⟩⟩]

def t4_168jobs : List Job := t4_168jobs0




def t4_169root : Job := ⟨plan1752,[],none,⟨6,0,0⟩⟩
def t4_169jobs0 : List Job := [⟨plan1752,[],none,⟨6,0,0⟩⟩]

def t4_169jobs : List Job := t4_169jobs0




def t4_170root : Job := ⟨plan1865,[],none,⟨6,1,0⟩⟩
def t4_170jobs0 : List Job := [⟨plan1865,[],none,⟨6,1,0⟩⟩]

def t4_170jobs : List Job := t4_170jobs0




def t4_171root : Job := ⟨plan1866,[],none,⟨6,1,0⟩⟩
def t4_171jobs0 : List Job := [⟨plan1866,[],none,⟨6,1,0⟩⟩]

def t4_171jobs : List Job := t4_171jobs0




def t4_172root : Job := ⟨plan1867,[],none,⟨6,1,0⟩⟩
def t4_172jobs0 : List Job := [⟨plan1867,[],none,⟨6,1,0⟩⟩]

def t4_172jobs : List Job := t4_172jobs0




def t4_173root : Job := ⟨plan1868,[],none,⟨6,1,0⟩⟩
def t4_173jobs0 : List Job := [⟨plan1868,[],none,⟨6,1,0⟩⟩]

def t4_173jobs : List Job := t4_173jobs0




def t4_174root : Job := ⟨plan1869,[],none,⟨6,1,0⟩⟩
def t4_174jobs0 : List Job := [⟨plan1869,[],none,⟨6,1,0⟩⟩]

def t4_174jobs : List Job := t4_174jobs0




def t4_175root : Job := ⟨plan1870,[],none,⟨6,1,0⟩⟩
def t4_175jobs0 : List Job := [⟨plan1870,[],none,⟨6,1,0⟩⟩]

def t4_175jobs : List Job := t4_175jobs0




def t4_176root : Job := ⟨plan1871,[],none,⟨6,1,0⟩⟩
def t4_176jobs0 : List Job := [⟨plan1871,[],none,⟨6,1,0⟩⟩]

def t4_176jobs : List Job := t4_176jobs0




def t4_177root : Job := ⟨plan1872,[],none,⟨6,1,0⟩⟩
def t4_177jobs0 : List Job := [⟨plan1872,[],none,⟨6,1,0⟩⟩]

def t4_177jobs : List Job := t4_177jobs0




def t4_178root : Job := ⟨plan1873,[],none,⟨6,1,0⟩⟩
def t4_178jobs0 : List Job := [⟨plan1873,[],none,⟨6,1,0⟩⟩]

def t4_178jobs : List Job := t4_178jobs0




def t4_179root : Job := ⟨plan1753,[],none,⟨6,0,0⟩⟩
def t4_179jobs0 : List Job := [⟨plan1753,[],none,⟨6,0,0⟩⟩]

def t4_179jobs : List Job := t4_179jobs0




def t4_180root : Job := ⟨plan1874,[],none,⟨6,1,0⟩⟩
def t4_180jobs0 : List Job := [⟨plan1874,[],none,⟨6,1,0⟩⟩]

def t4_180jobs : List Job := t4_180jobs0




def t4_181root : Job := ⟨plan1875,[],none,⟨6,1,0⟩⟩
def t4_181jobs0 : List Job := [⟨plan1875,[],none,⟨6,1,0⟩⟩]

def t4_181jobs : List Job := t4_181jobs0




def t4_182root : Job := ⟨plan1876,[],none,⟨6,1,0⟩⟩
def t4_182jobs0 : List Job := [⟨plan1876,[],none,⟨6,1,0⟩⟩]

def t4_182jobs : List Job := t4_182jobs0




def t4_183root : Job := ⟨plan1754,[],none,⟨6,0,0⟩⟩
def t4_183jobs0 : List Job := [⟨plan1754,[],none,⟨6,0,0⟩⟩]

def t4_183jobs : List Job := t4_183jobs0




def t4_184root : Job := ⟨plan1877,[],none,⟨6,1,0⟩⟩
def t4_184jobs0 : List Job := [⟨plan1877,[],none,⟨6,1,0⟩⟩]

def t4_184jobs : List Job := t4_184jobs0




def t4_185root : Job := ⟨plan1878,[],none,⟨6,1,0⟩⟩
def t4_185jobs0 : List Job := [⟨plan1878,[],none,⟨6,1,0⟩⟩]

def t4_185jobs : List Job := t4_185jobs0




def t4_186root : Job := ⟨plan1879,[],none,⟨6,1,0⟩⟩
def t4_186jobs0 : List Job := [⟨plan1879,[],none,⟨6,1,0⟩⟩]

def t4_186jobs : List Job := t4_186jobs0




def t4_187root : Job := ⟨plan1880,[],none,⟨6,1,0⟩⟩
def t4_187jobs0 : List Job := [⟨plan1880,[],none,⟨6,1,0⟩⟩]

def t4_187jobs : List Job := t4_187jobs0




def t4_188root : Job := ⟨plan1881,[],none,⟨6,1,0⟩⟩
def t4_188jobs0 : List Job := [⟨plan1881,[],none,⟨6,1,0⟩⟩]

def t4_188jobs : List Job := t4_188jobs0




def t4_189root : Job := ⟨plan1882,[],none,⟨6,1,0⟩⟩
def t4_189jobs0 : List Job := [⟨plan1882,[],none,⟨6,1,0⟩⟩]

def t4_189jobs : List Job := t4_189jobs0




def t4_190root : Job := ⟨plan1704,[],none,⟨6,0,0⟩⟩
def t4_190jobs0 : List Job := [⟨plan1704,[],none,⟨6,0,0⟩⟩]

def t4_190jobs : List Job := t4_190jobs0




def t4_191root : Job := ⟨plan1705,[],none,⟨6,0,0⟩⟩
def t4_191jobs0 : List Job := [⟨plan1705,[],none,⟨6,0,0⟩⟩]

def t4_191jobs : List Job := t4_191jobs0




def t4_192root : Job := ⟨plan1755,[],none,⟨6,0,0⟩⟩
def t4_192jobs0 : List Job := [⟨plan1755,[],none,⟨6,0,0⟩⟩]

def t4_192jobs : List Job := t4_192jobs0




def t4_193root : Job := ⟨plan1756,[],none,⟨6,0,0⟩⟩
def t4_193jobs0 : List Job := [⟨plan1756,[],none,⟨6,0,0⟩⟩]

def t4_193jobs : List Job := t4_193jobs0




def t4_194root : Job := ⟨plan1757,[],none,⟨6,0,0⟩⟩
def t4_194jobs0 : List Job := [⟨plan1757,[],none,⟨6,0,0⟩⟩]

def t4_194jobs : List Job := t4_194jobs0




def t4_195root : Job := ⟨plan1758,[],none,⟨6,0,0⟩⟩
def t4_195jobs0 : List Job := [⟨plan1758,[],none,⟨6,0,0⟩⟩]

def t4_195jobs : List Job := t4_195jobs0




def t4_196root : Job := ⟨plan1759,[],none,⟨6,0,0⟩⟩
def t4_196jobs0 : List Job := [⟨plan1759,[],none,⟨6,0,0⟩⟩]

def t4_196jobs : List Job := t4_196jobs0




def t4_197root : Job := ⟨plan1706,[],none,⟨6,0,0⟩⟩
def t4_197jobs0 : List Job := [⟨plan1706,[],none,⟨6,0,0⟩⟩]

def t4_197jobs : List Job := t4_197jobs0




def t4_198root : Job := ⟨plan1760,[],none,⟨6,0,0⟩⟩
def t4_198jobs0 : List Job := [⟨plan1760,[],none,⟨6,0,0⟩⟩]

def t4_198jobs : List Job := t4_198jobs0




def t4_199root : Job := ⟨plan1761,[],none,⟨6,0,0⟩⟩
def t4_199jobs0 : List Job := [⟨plan1761,[],none,⟨6,0,0⟩⟩]

def t4_199jobs : List Job := t4_199jobs0




def t4_200root : Job := ⟨plan1762,[],none,⟨6,0,0⟩⟩
def t4_200jobs0 : List Job := [⟨plan1762,[],none,⟨6,0,0⟩⟩]

def t4_200jobs : List Job := t4_200jobs0




def t4_201root : Job := ⟨plan1763,[],none,⟨6,0,0⟩⟩
def t4_201jobs0 : List Job := [⟨plan1763,[],none,⟨6,0,0⟩⟩]

def t4_201jobs : List Job := t4_201jobs0




def t4_202root : Job := ⟨plan1883,[],none,⟨6,1,0⟩⟩
def t4_202jobs0 : List Job := [⟨plan1883,[],none,⟨6,1,0⟩⟩]

def t4_202jobs : List Job := t4_202jobs0




def t4_203root : Job := ⟨plan1884,[],none,⟨6,1,0⟩⟩
def t4_203jobs0 : List Job := [⟨plan1884,[],none,⟨6,1,0⟩⟩]

def t4_203jobs : List Job := t4_203jobs0




def t4_204root : Job := ⟨plan1885,[],none,⟨6,1,0⟩⟩
def t4_204jobs0 : List Job := [⟨plan1885,[],none,⟨6,1,0⟩⟩]

def t4_204jobs : List Job := t4_204jobs0




def t4_205root : Job := ⟨plan1886,[],none,⟨6,1,0⟩⟩
def t4_205jobs0 : List Job := [⟨plan1886,[],none,⟨6,1,0⟩⟩]

def t4_205jobs : List Job := t4_205jobs0




def t4_206root : Job := ⟨plan1887,[],none,⟨6,1,0⟩⟩
def t4_206jobs0 : List Job := [⟨plan1887,[],none,⟨6,1,0⟩⟩]

def t4_206jobs : List Job := t4_206jobs0




def t4_207root : Job := ⟨plan1888,[],none,⟨6,1,0⟩⟩
def t4_207jobs0 : List Job := [⟨plan1888,[],none,⟨6,1,0⟩⟩]

def t4_207jobs : List Job := t4_207jobs0




def t4_208root : Job := ⟨plan1889,[],none,⟨6,1,0⟩⟩
def t4_208jobs0 : List Job := [⟨plan1889,[],none,⟨6,1,0⟩⟩]

def t4_208jobs : List Job := t4_208jobs0




def t4_209root : Job := ⟨plan1890,[],none,⟨6,1,0⟩⟩
def t4_209jobs0 : List Job := [⟨plan1890,[],none,⟨6,1,0⟩⟩]

def t4_209jobs : List Job := t4_209jobs0




def t4_210root : Job := ⟨plan1891,[],none,⟨6,1,0⟩⟩
def t4_210jobs0 : List Job := [⟨plan1891,[],none,⟨6,1,0⟩⟩]

def t4_210jobs : List Job := t4_210jobs0




def t4_211root : Job := ⟨plan1764,[],none,⟨6,0,0⟩⟩
def t4_211jobs0 : List Job := [⟨plan1764,[],none,⟨6,0,0⟩⟩]

def t4_211jobs : List Job := t4_211jobs0




def t4_212root : Job := ⟨plan1892,[],none,⟨6,1,0⟩⟩
def t4_212jobs0 : List Job := [⟨plan1892,[],none,⟨6,1,0⟩⟩]

def t4_212jobs : List Job := t4_212jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


