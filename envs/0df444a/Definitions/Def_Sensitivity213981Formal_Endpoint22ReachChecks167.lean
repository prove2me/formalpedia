-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks167
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks167
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:53.877992+00:00
-- url     : https://prove2.me/theorems/e35f523a-315f-45ca-a7cc-c83892b4ad90
-- title:
--   Endpoint22 Reach Checks167 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks167 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_218root`, `ThreeBoundEndpoint22Reachable.t7_218jobs0`, `ThreeBoundEndpoint22Reachable.t7_218jobs`, `ThreeBoundEndpoint22Reachable.t7_219root`, `ThreeBoundEndpoint22Reachable.t7_219jobs0`, `ThreeBoundEndpoint22Reachable.t7_219jobs1`, `ThreeBoundEndpoint22Reachable.t7_219jobs`, `ThreeBoundEndpoint22Reachable.t7_220root`, `ThreeBoundEndpoint22Reachable.t7_220jobs0`, `ThreeBoundEndpoint22Reachable.t7_220jobs1`, `ThreeBoundEndpoint22Reachable.t7_220jobs`, `ThreeBoundEndpoint22Reachable.t7_206root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks167.lean, lines 1–312.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
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

def t7_205root : Job := ⟨plan8771,[],none,⟨21,15,0⟩⟩
def t7_205jobs0 : List Job := [⟨plan8771,[],none,⟨21,15,0⟩⟩]

def t7_205jobs : List Job := t7_205jobs0




def t7_206root : Job := ⟨plan8626,[],none,⟨21,10,0⟩⟩
def t7_206jobs0 : List Job := [⟨plan8626,[],none,⟨21,10,0⟩⟩]

def t7_206jobs : List Job := t7_206jobs0




def t7_207root : Job := ⟨plan8772,[],none,⟨21,15,0⟩⟩
def t7_207jobs0 : List Job := [⟨plan8772,[],none,⟨21,15,0⟩⟩]

def t7_207jobs : List Job := t7_207jobs0




def t7_208root : Job := ⟨plan8773,[],none,⟨21,15,0⟩⟩
def t7_208jobs0 : List Job := [⟨plan8773,[],none,⟨21,15,0⟩⟩]

def t7_208jobs : List Job := t7_208jobs0




def t7_209root : Job := ⟨plan8774,[],none,⟨21,15,0⟩⟩
def t7_209jobs0 : List Job := [⟨plan8774,[],none,⟨21,15,0⟩⟩]

def t7_209jobs : List Job := t7_209jobs0




def t7_210root : Job := ⟨plan8775,[],none,⟨21,15,0⟩⟩
def t7_210jobs0 : List Job := [⟨plan8775,[],none,⟨21,15,0⟩⟩]

def t7_210jobs : List Job := t7_210jobs0




def t7_211root : Job := ⟨plan8776,[],none,⟨21,15,0⟩⟩
def t7_211jobs0 : List Job := [⟨plan8776,[],none,⟨21,15,0⟩⟩]

def t7_211jobs : List Job := t7_211jobs0




def t7_212root : Job := ⟨plan8777,[],none,⟨21,15,0⟩⟩
def t7_212jobs0 : List Job := [⟨plan8777,[],none,⟨21,15,0⟩⟩]

def t7_212jobs : List Job := t7_212jobs0




def t7_213root : Job := ⟨plan8778,[],none,⟨21,15,0⟩⟩
def t7_213jobs0 : List Job := [⟨plan8778,[],none,⟨21,15,0⟩⟩]

def t7_213jobs : List Job := t7_213jobs0




def t7_214root : Job := ⟨plan8779,[],none,⟨21,15,0⟩⟩
def t7_214jobs0 : List Job := [⟨plan8779,[],none,⟨21,15,0⟩⟩]

def t7_214jobs : List Job := t7_214jobs0




def t7_215root : Job := ⟨plan8780,[],none,⟨21,15,0⟩⟩
def t7_215jobs0 : List Job := [⟨plan8780,[],none,⟨21,15,0⟩⟩]

def t7_215jobs : List Job := t7_215jobs0




def t7_216root : Job := ⟨plan8781,[],none,⟨21,15,0⟩⟩
def t7_216jobs0 : List Job := [⟨plan8781,[],none,⟨21,15,0⟩⟩]

def t7_216jobs : List Job := t7_216jobs0




def t7_217root : Job := ⟨plan8782,[],none,⟨21,15,0⟩⟩
def t7_217jobs0 : List Job := [⟨plan8782,[],none,⟨21,15,0⟩⟩]

def t7_217jobs : List Job := t7_217jobs0




def t7_218root : Job := ⟨plan8783,[],none,⟨21,15,0⟩⟩
def t7_218jobs0 : List Job := [⟨plan8783,[],none,⟨21,15,0⟩⟩]

def t7_218jobs : List Job := t7_218jobs0




def t7_219root : Job := ⟨plan8784,[],none,⟨21,15,0⟩⟩
def t7_219jobs0 : List Job := [⟨plan8283,[⟨2,0,6⟩],(some ⟨2,0,6⟩),⟨21,15,(-6)⟩⟩,⟨plan8283,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,15,(-5)⟩⟩]

def t7_219jobs1 : List Job := [⟨plan8283,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,15,(-4)⟩⟩]

def t7_219jobs : List Job := t7_219jobs0++t7_219jobs1




def t7_220root : Job := ⟨plan8785,[],none,⟨21,15,0⟩⟩
def t7_220jobs0 : List Job := [⟨plan8284,[⟨2,0,6⟩],(some ⟨2,0,6⟩),⟨21,15,(-6)⟩⟩,⟨plan8284,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,15,(-5)⟩⟩]

def t7_220jobs1 : List Job := [⟨plan8284,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,15,(-4)⟩⟩]

def t7_220jobs : List Job := t7_220jobs0++t7_220jobs1




def t7_221root : Job := ⟨plan8786,[],none,⟨21,15,0⟩⟩
def t7_221jobs0 : List Job := [⟨plan8786,[],none,⟨21,15,0⟩⟩]

def t7_221jobs : List Job := t7_221jobs0




def t7_222root : Job := ⟨plan8787,[],none,⟨21,15,0⟩⟩
def t7_222jobs0 : List Job := [⟨plan8787,[],none,⟨21,15,0⟩⟩]

def t7_222jobs : List Job := t7_222jobs0




def t7_223root : Job := ⟨plan8788,[],none,⟨21,15,0⟩⟩
def t7_223jobs0 : List Job := [⟨plan8288,[⟨2,0,6⟩],(some ⟨2,0,6⟩),⟨21,15,(-6)⟩⟩,⟨plan8288,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,15,(-5)⟩⟩]

def t7_223jobs1 : List Job := [⟨plan8288,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,15,(-4)⟩⟩]

def t7_223jobs : List Job := t7_223jobs0++t7_223jobs1




def t7_224root : Job := ⟨plan8789,[],none,⟨21,15,0⟩⟩
def t7_224jobs0 : List Job := [⟨plan6230,[⟨2,0,6⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6230,[⟨2,0,6⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6230,[⟨2,0,6⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6230,[⟨2,0,6⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6230,[⟨2,0,6⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6230,[⟨2,0,6⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6230,[⟨2,0,6⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6230,[⟨2,1,5⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6230,[⟨2,1,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6230,[⟨2,1,5⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6230,[⟨2,1,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6230,[⟨2,1,5⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6230,[⟨2,1,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6230,[⟨2,1,5⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6230,[⟨2,2,4⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6230,[⟨2,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6230,[⟨2,2,4⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6230,[⟨2,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,12,(-5)⟩⟩]

def t7_224jobs1 : List Job := [⟨plan6230,[⟨2,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6230,[⟨2,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,13,(-3)⟩⟩,⟨plan6230,[⟨2,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,12,(-4)⟩⟩]

def t7_224jobs : List Job := t7_224jobs0++t7_224jobs1




def t7_225root : Job := ⟨plan8790,[],none,⟨21,15,0⟩⟩
def t7_225jobs0 : List Job := [⟨plan8290,[⟨2,0,6⟩],(some ⟨2,0,6⟩),⟨21,15,(-6)⟩⟩,⟨plan8290,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,15,(-5)⟩⟩]

def t7_225jobs1 : List Job := [⟨plan8290,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,15,(-4)⟩⟩]

def t7_225jobs : List Job := t7_225jobs0++t7_225jobs1




def t7_226root : Job := ⟨plan8791,[],none,⟨21,15,0⟩⟩
def t7_226jobs0 : List Job := [⟨plan8791,[],none,⟨21,15,0⟩⟩]

def t7_226jobs : List Job := t7_226jobs0




def t7_227root : Job := ⟨plan8792,[],none,⟨21,15,0⟩⟩
def t7_227jobs0 : List Job := [⟨plan8792,[],none,⟨21,15,0⟩⟩]

def t7_227jobs : List Job := t7_227jobs0




def t7_228root : Job := ⟨plan8793,[],none,⟨21,15,0⟩⟩
def t7_228jobs0 : List Job := [⟨plan8793,[],none,⟨21,15,0⟩⟩]

def t7_228jobs : List Job := t7_228jobs0




def t7_229root : Job := ⟨plan8446,[],none,⟨21,3,0⟩⟩
def t7_229jobs0 : List Job := [⟨plan8446,[],none,⟨21,3,0⟩⟩]

def t7_229jobs : List Job := t7_229jobs0




def t7_230root : Job := ⟨plan8506,[],none,⟨21,6,0⟩⟩
def t7_230jobs0 : List Job := [⟨plan8142,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8142,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8142,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩,⟨plan8142,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩,⟨plan8142,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩]

def t7_230jobs1 : List Job := [⟨plan8142,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_230jobs : List Job := t7_230jobs0++t7_230jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


