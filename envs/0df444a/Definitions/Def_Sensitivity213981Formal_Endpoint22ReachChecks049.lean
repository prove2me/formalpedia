-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks049
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks049
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:58.812882+00:00
-- url     : https://prove2.me/theorems/8051d251-577d-4f58-9c41-225cf242f3f8
-- title:
--   Endpoint22 Reach Checks049 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks049 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_168root`, `ThreeBoundEndpoint22Reachable.t6_168jobs0`, `ThreeBoundEndpoint22Reachable.t6_168jobs`, `ThreeBoundEndpoint22Reachable.t6_169root`, `ThreeBoundEndpoint22Reachable.t6_169jobs0`, `ThreeBoundEndpoint22Reachable.t6_169jobs`, `ThreeBoundEndpoint22Reachable.t6_170root`, `ThreeBoundEndpoint22Reachable.t6_170jobs0`, `ThreeBoundEndpoint22Reachable.t6_170jobs`, `ThreeBoundEndpoint22Reachable.t6_171root`, `ThreeBoundEndpoint22Reachable.t6_171jobs0`, `ThreeBoundEndpoint22Reachable.t6_171jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks049.lean, lines 1–959.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
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

def t6_155root : Job := ⟨plan6750,[],none,⟨15,6,0⟩⟩
def t6_155jobs0 : List Job := [⟨plan6750,[],none,⟨15,6,0⟩⟩]

def t6_155jobs : List Job := t6_155jobs0




def t6_156root : Job := ⟨plan6751,[],none,⟨15,6,0⟩⟩
def t6_156jobs0 : List Job := [⟨plan6751,[],none,⟨15,6,0⟩⟩]

def t6_156jobs : List Job := t6_156jobs0




def t6_157root : Job := ⟨plan6752,[],none,⟨15,6,0⟩⟩
def t6_157jobs0 : List Job := [⟨plan6752,[],none,⟨15,6,0⟩⟩]

def t6_157jobs : List Job := t6_157jobs0




def t6_158root : Job := ⟨plan6753,[],none,⟨15,6,0⟩⟩
def t6_158jobs0 : List Job := [⟨plan6753,[],none,⟨15,6,0⟩⟩]

def t6_158jobs : List Job := t6_158jobs0




def t6_159root : Job := ⟨plan6754,[],none,⟨15,6,0⟩⟩
def t6_159jobs0 : List Job := [⟨plan6754,[],none,⟨15,6,0⟩⟩]

def t6_159jobs : List Job := t6_159jobs0




def t6_160root : Job := ⟨plan7194,[],none,⟨15,10,0⟩⟩
def t6_160jobs0 : List Job := [⟨plan7194,[],none,⟨15,10,0⟩⟩]

def t6_160jobs : List Job := t6_160jobs0




def t6_161root : Job := ⟨plan7195,[],none,⟨15,10,0⟩⟩
def t6_161jobs0 : List Job := [⟨plan7195,[],none,⟨15,10,0⟩⟩]

def t6_161jobs : List Job := t6_161jobs0




def t6_162root : Job := ⟨plan7196,[],none,⟨15,10,0⟩⟩
def t6_162jobs0 : List Job := [⟨plan7196,[],none,⟨15,10,0⟩⟩]

def t6_162jobs : List Job := t6_162jobs0




def t6_163root : Job := ⟨plan7197,[],none,⟨15,10,0⟩⟩
def t6_163jobs0 : List Job := [⟨plan7197,[],none,⟨15,10,0⟩⟩]

def t6_163jobs : List Job := t6_163jobs0




def t6_164root : Job := ⟨plan7198,[],none,⟨15,10,0⟩⟩
def t6_164jobs0 : List Job := [⟨plan7198,[],none,⟨15,10,0⟩⟩]

def t6_164jobs : List Job := t6_164jobs0




def t6_165root : Job := ⟨plan7199,[],none,⟨15,10,0⟩⟩
def t6_165jobs0 : List Job := [⟨plan7199,[],none,⟨15,10,0⟩⟩]

def t6_165jobs : List Job := t6_165jobs0




def t6_166root : Job := ⟨plan7200,[],none,⟨15,10,0⟩⟩
def t6_166jobs0 : List Job := [⟨plan7200,[],none,⟨15,10,0⟩⟩]

def t6_166jobs : List Job := t6_166jobs0




def t6_167root : Job := ⟨plan6755,[],none,⟨15,6,0⟩⟩
def t6_167jobs0 : List Job := [⟨plan6755,[],none,⟨15,6,0⟩⟩]

def t6_167jobs : List Job := t6_167jobs0




def t6_168root : Job := ⟨plan7201,[],none,⟨15,10,0⟩⟩
def t6_168jobs0 : List Job := [⟨plan7201,[],none,⟨15,10,0⟩⟩]

def t6_168jobs : List Job := t6_168jobs0




def t6_169root : Job := ⟨plan7202,[],none,⟨15,10,0⟩⟩
def t6_169jobs0 : List Job := [⟨plan7202,[],none,⟨15,10,0⟩⟩]

def t6_169jobs : List Job := t6_169jobs0




def t6_170root : Job := ⟨plan7203,[],none,⟨15,10,0⟩⟩
def t6_170jobs0 : List Job := [⟨plan7203,[],none,⟨15,10,0⟩⟩]

def t6_170jobs : List Job := t6_170jobs0




def t6_171root : Job := ⟨plan7204,[],none,⟨15,10,0⟩⟩
def t6_171jobs0 : List Job := [⟨plan7204,[],none,⟨15,10,0⟩⟩]

def t6_171jobs : List Job := t6_171jobs0




def t6_172root : Job := ⟨plan7205,[],none,⟨15,10,0⟩⟩
def t6_172jobs0 : List Job := [⟨plan7205,[],none,⟨15,10,0⟩⟩]

def t6_172jobs : List Job := t6_172jobs0




def t6_173root : Job := ⟨plan7206,[],none,⟨15,10,0⟩⟩
def t6_173jobs0 : List Job := [⟨plan7206,[],none,⟨15,10,0⟩⟩]

def t6_173jobs : List Job := t6_173jobs0




def t6_174root : Job := ⟨plan7207,[],none,⟨15,10,0⟩⟩
def t6_174jobs0 : List Job := [⟨plan7207,[],none,⟨15,10,0⟩⟩]

def t6_174jobs : List Job := t6_174jobs0




def t6_175root : Job := ⟨plan7208,[],none,⟨15,10,0⟩⟩
def t6_175jobs0 : List Job := [⟨plan7208,[],none,⟨15,10,0⟩⟩]

def t6_175jobs : List Job := t6_175jobs0




def t6_176root : Job := ⟨plan7209,[],none,⟨15,10,0⟩⟩
def t6_176jobs0 : List Job := [⟨plan7209,[],none,⟨15,10,0⟩⟩]

def t6_176jobs : List Job := t6_176jobs0




def t6_177root : Job := ⟨plan7210,[],none,⟨15,10,0⟩⟩
def t6_177jobs0 : List Job := [⟨plan7210,[],none,⟨15,10,0⟩⟩]

def t6_177jobs : List Job := t6_177jobs0




def t6_178root : Job := ⟨plan7211,[],none,⟨15,10,0⟩⟩
def t6_178jobs0 : List Job := [⟨plan7211,[],none,⟨15,10,0⟩⟩]

def t6_178jobs : List Job := t6_178jobs0




def t6_179root : Job := ⟨plan6467,[],none,⟨15,3,0⟩⟩
def t6_179jobs0 : List Job := [⟨plan6467,[],none,⟨15,3,0⟩⟩]

def t6_179jobs : List Job := t6_179jobs0




def t6_180root : Job := ⟨plan6333,[],none,⟨15,1,0⟩⟩
def t6_180jobs0 : List Job := [⟨plan6333,[],none,⟨15,1,0⟩⟩]

def t6_180jobs : List Job := t6_180jobs0




def t6_181root : Job := ⟨plan6468,[],none,⟨15,3,0⟩⟩
def t6_181jobs0 : List Job := [⟨plan6468,[],none,⟨15,3,0⟩⟩]

def t6_181jobs : List Job := t6_181jobs0




def t6_182root : Job := ⟨plan6469,[],none,⟨15,3,0⟩⟩
def t6_182jobs0 : List Job := [⟨plan6469,[],none,⟨15,3,0⟩⟩]

def t6_182jobs : List Job := t6_182jobs0




def t6_183root : Job := ⟨plan6470,[],none,⟨15,3,0⟩⟩
def t6_183jobs0 : List Job := [⟨plan6470,[],none,⟨15,3,0⟩⟩]

def t6_183jobs : List Job := t6_183jobs0




def t6_184root : Job := ⟨plan6287,[],none,⟨15,0,0⟩⟩
def t6_184jobs0 : List Job := [⟨plan6287,[],none,⟨15,0,0⟩⟩]

def t6_184jobs : List Job := t6_184jobs0




def t6_185root : Job := ⟨plan6334,[],none,⟨15,1,0⟩⟩
def t6_185jobs0 : List Job := [⟨plan6334,[],none,⟨15,1,0⟩⟩]

def t6_185jobs : List Job := t6_185jobs0




def t6_186root : Job := ⟨plan6335,[],none,⟨15,1,0⟩⟩
def t6_186jobs0 : List Job := [⟨plan6335,[],none,⟨15,1,0⟩⟩]

def t6_186jobs : List Job := t6_186jobs0




def t6_187root : Job := ⟨plan6336,[],none,⟨15,1,0⟩⟩
def t6_187jobs0 : List Job := [⟨plan6336,[],none,⟨15,1,0⟩⟩]

def t6_187jobs : List Job := t6_187jobs0




def t6_188root : Job := ⟨plan6471,[],none,⟨15,3,0⟩⟩
def t6_188jobs0 : List Job := [⟨plan6471,[],none,⟨15,3,0⟩⟩]

def t6_188jobs : List Job := t6_188jobs0




def t6_189root : Job := ⟨plan6472,[],none,⟨15,3,0⟩⟩
def t6_189jobs0 : List Job := [⟨plan6472,[],none,⟨15,3,0⟩⟩]

def t6_189jobs : List Job := t6_189jobs0




def t6_190root : Job := ⟨plan6473,[],none,⟨15,3,0⟩⟩
def t6_190jobs0 : List Job := [⟨plan6473,[],none,⟨15,3,0⟩⟩]

def t6_190jobs : List Job := t6_190jobs0




def t6_191root : Job := ⟨plan6474,[],none,⟨15,3,0⟩⟩
def t6_191jobs0 : List Job := [⟨plan6474,[],none,⟨15,3,0⟩⟩]

def t6_191jobs : List Job := t6_191jobs0




def t6_192root : Job := ⟨plan6475,[],none,⟨15,3,0⟩⟩
def t6_192jobs0 : List Job := [⟨plan6475,[],none,⟨15,3,0⟩⟩]

def t6_192jobs : List Job := t6_192jobs0




def t6_193root : Job := ⟨plan6476,[],none,⟨15,3,0⟩⟩
def t6_193jobs0 : List Job := [⟨plan6476,[],none,⟨15,3,0⟩⟩]

def t6_193jobs : List Job := t6_193jobs0




def t6_194root : Job := ⟨plan6756,[],none,⟨15,6,0⟩⟩
def t6_194jobs0 : List Job := [⟨plan6756,[],none,⟨15,6,0⟩⟩]

def t6_194jobs : List Job := t6_194jobs0




def t6_195root : Job := ⟨plan6477,[],none,⟨15,3,0⟩⟩
def t6_195jobs0 : List Job := [⟨plan6477,[],none,⟨15,3,0⟩⟩]

def t6_195jobs : List Job := t6_195jobs0




def t6_196root : Job := ⟨plan6757,[],none,⟨15,6,0⟩⟩
def t6_196jobs0 : List Job := [⟨plan6757,[],none,⟨15,6,0⟩⟩]

def t6_196jobs : List Job := t6_196jobs0




def t6_197root : Job := ⟨plan6758,[],none,⟨15,6,0⟩⟩
def t6_197jobs0 : List Job := [⟨plan6758,[],none,⟨15,6,0⟩⟩]

def t6_197jobs : List Job := t6_197jobs0




def t6_198root : Job := ⟨plan6759,[],none,⟨15,6,0⟩⟩
def t6_198jobs0 : List Job := [⟨plan6759,[],none,⟨15,6,0⟩⟩]

def t6_198jobs : List Job := t6_198jobs0




def t6_199root : Job := ⟨plan6760,[],none,⟨15,6,0⟩⟩
def t6_199jobs0 : List Job := [⟨plan6760,[],none,⟨15,6,0⟩⟩]

def t6_199jobs : List Job := t6_199jobs0




def t6_200root : Job := ⟨plan6761,[],none,⟨15,6,0⟩⟩
def t6_200jobs0 : List Job := [⟨plan6761,[],none,⟨15,6,0⟩⟩]

def t6_200jobs : List Job := t6_200jobs0




def t6_201root : Job := ⟨plan6762,[],none,⟨15,6,0⟩⟩
def t6_201jobs0 : List Job := [⟨plan6762,[],none,⟨15,6,0⟩⟩]

def t6_201jobs : List Job := t6_201jobs0




def t6_202root : Job := ⟨plan6763,[],none,⟨15,6,0⟩⟩
def t6_202jobs0 : List Job := [⟨plan6763,[],none,⟨15,6,0⟩⟩]

def t6_202jobs : List Job := t6_202jobs0




def t6_203root : Job := ⟨plan6764,[],none,⟨15,6,0⟩⟩
def t6_203jobs0 : List Job := [⟨plan6764,[],none,⟨15,6,0⟩⟩]

def t6_203jobs : List Job := t6_203jobs0




def t6_204root : Job := ⟨plan6765,[],none,⟨15,6,0⟩⟩
def t6_204jobs0 : List Job := [⟨plan6765,[],none,⟨15,6,0⟩⟩]

def t6_204jobs : List Job := t6_204jobs0




def t6_205root : Job := ⟨plan6766,[],none,⟨15,6,0⟩⟩
def t6_205jobs0 : List Job := [⟨plan6766,[],none,⟨15,6,0⟩⟩]

def t6_205jobs : List Job := t6_205jobs0




def t6_206root : Job := ⟨plan6767,[],none,⟨15,6,0⟩⟩
def t6_206jobs0 : List Job := [⟨plan6767,[],none,⟨15,6,0⟩⟩]

def t6_206jobs : List Job := t6_206jobs0




def t6_207root : Job := ⟨plan6478,[],none,⟨15,3,0⟩⟩
def t6_207jobs0 : List Job := [⟨plan6478,[],none,⟨15,3,0⟩⟩]

def t6_207jobs : List Job := t6_207jobs0




def t6_208root : Job := ⟨plan6768,[],none,⟨15,6,0⟩⟩
def t6_208jobs0 : List Job := [⟨plan6768,[],none,⟨15,6,0⟩⟩]

def t6_208jobs : List Job := t6_208jobs0




def t6_209root : Job := ⟨plan6769,[],none,⟨15,6,0⟩⟩
def t6_209jobs0 : List Job := [⟨plan6769,[],none,⟨15,6,0⟩⟩]

def t6_209jobs : List Job := t6_209jobs0




def t6_210root : Job := ⟨plan6770,[],none,⟨15,6,0⟩⟩
def t6_210jobs0 : List Job := [⟨plan6770,[],none,⟨15,6,0⟩⟩]

def t6_210jobs : List Job := t6_210jobs0




def t6_211root : Job := ⟨plan6771,[],none,⟨15,6,0⟩⟩
def t6_211jobs0 : List Job := [⟨plan6771,[],none,⟨15,6,0⟩⟩]

def t6_211jobs : List Job := t6_211jobs0




def t6_212root : Job := ⟨plan6772,[],none,⟨15,6,0⟩⟩
def t6_212jobs0 : List Job := [⟨plan6772,[],none,⟨15,6,0⟩⟩]

def t6_212jobs : List Job := t6_212jobs0




def t6_213root : Job := ⟨plan6773,[],none,⟨15,6,0⟩⟩
def t6_213jobs0 : List Job := [⟨plan6773,[],none,⟨15,6,0⟩⟩]

def t6_213jobs : List Job := t6_213jobs0




def t6_214root : Job := ⟨plan6337,[],none,⟨15,1,0⟩⟩
def t6_214jobs0 : List Job := [⟨plan6337,[],none,⟨15,1,0⟩⟩]

def t6_214jobs : List Job := t6_214jobs0




def t6_215root : Job := ⟨plan6288,[],none,⟨15,0,0⟩⟩
def t6_215jobs0 : List Job := [⟨plan6288,[],none,⟨15,0,0⟩⟩]

def t6_215jobs : List Job := t6_215jobs0




def t6_216root : Job := ⟨plan6338,[],none,⟨15,1,0⟩⟩
def t6_216jobs0 : List Job := [⟨plan6338,[],none,⟨15,1,0⟩⟩]

def t6_216jobs : List Job := t6_216jobs0




def t6_217root : Job := ⟨plan6339,[],none,⟨15,1,0⟩⟩
def t6_217jobs0 : List Job := [⟨plan6339,[],none,⟨15,1,0⟩⟩]

def t6_217jobs : List Job := t6_217jobs0




def t6_218root : Job := ⟨plan6340,[],none,⟨15,1,0⟩⟩
def t6_218jobs0 : List Job := [⟨plan6340,[],none,⟨15,1,0⟩⟩]

def t6_218jobs : List Job := t6_218jobs0




def t6_219root : Job := ⟨plan6479,[],none,⟨15,3,0⟩⟩
def t6_219jobs0 : List Job := [⟨plan6479,[],none,⟨15,3,0⟩⟩]

def t6_219jobs : List Job := t6_219jobs0




def t6_220root : Job := ⟨plan6480,[],none,⟨15,3,0⟩⟩
def t6_220jobs0 : List Job := [⟨plan6480,[],none,⟨15,3,0⟩⟩]

def t6_220jobs : List Job := t6_220jobs0




def t6_221root : Job := ⟨plan6481,[],none,⟨15,3,0⟩⟩
def t6_221jobs0 : List Job := [⟨plan6481,[],none,⟨15,3,0⟩⟩]

def t6_221jobs : List Job := t6_221jobs0




def t6_222root : Job := ⟨plan6482,[],none,⟨15,3,0⟩⟩
def t6_222jobs0 : List Job := [⟨plan6482,[],none,⟨15,3,0⟩⟩]

def t6_222jobs : List Job := t6_222jobs0




def t6_223root : Job := ⟨plan6483,[],none,⟨15,3,0⟩⟩
def t6_223jobs0 : List Job := [⟨plan6483,[],none,⟨15,3,0⟩⟩]

def t6_223jobs : List Job := t6_223jobs0




def t6_224root : Job := ⟨plan6484,[],none,⟨15,3,0⟩⟩
def t6_224jobs0 : List Job := [⟨plan6484,[],none,⟨15,3,0⟩⟩]

def t6_224jobs : List Job := t6_224jobs0




def t6_225root : Job := ⟨plan6485,[],none,⟨15,3,0⟩⟩
def t6_225jobs0 : List Job := [⟨plan6485,[],none,⟨15,3,0⟩⟩]

def t6_225jobs : List Job := t6_225jobs0




def t6_226root : Job := ⟨plan6486,[],none,⟨15,3,0⟩⟩
def t6_226jobs0 : List Job := [⟨plan6486,[],none,⟨15,3,0⟩⟩]

def t6_226jobs : List Job := t6_226jobs0




def t6_227root : Job := ⟨plan6277,[],none,⟨15,0,0⟩⟩
def t6_227jobs0 : List Job := [⟨plan6277,[],none,⟨15,0,0⟩⟩]

def t6_227jobs : List Job := t6_227jobs0




def t6_228root : Job := ⟨plan6289,[],none,⟨15,0,0⟩⟩
def t6_228jobs0 : List Job := [⟨plan6289,[],none,⟨15,0,0⟩⟩]

def t6_228jobs : List Job := t6_228jobs0




def t6_229root : Job := ⟨plan6290,[],none,⟨15,0,0⟩⟩
def t6_229jobs0 : List Job := [⟨plan6290,[],none,⟨15,0,0⟩⟩]

def t6_229jobs : List Job := t6_229jobs0




def t6_230root : Job := ⟨plan6291,[],none,⟨15,0,0⟩⟩
def t6_230jobs0 : List Job := [⟨plan6291,[],none,⟨15,0,0⟩⟩]

def t6_230jobs : List Job := t6_230jobs0




def t6_231root : Job := ⟨plan6341,[],none,⟨15,1,0⟩⟩
def t6_231jobs0 : List Job := [⟨plan6341,[],none,⟨15,1,0⟩⟩]

def t6_231jobs : List Job := t6_231jobs0




def t6_232root : Job := ⟨plan6342,[],none,⟨15,1,0⟩⟩
def t6_232jobs0 : List Job := [⟨plan5382,[⟨1,0,2⟩],(some ⟨1,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5382,[⟨1,1,1⟩],(some ⟨1,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_232jobs1 : List Job := [⟨plan5382,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_232jobs : List Job := t6_232jobs0++t6_232jobs1




def t6_233root : Job := ⟨plan6343,[],none,⟨15,1,0⟩⟩
def t6_233jobs0 : List Job := [⟨plan6343,[],none,⟨15,1,0⟩⟩]

def t6_233jobs : List Job := t6_233jobs0




def t6_234root : Job := ⟨plan6344,[],none,⟨15,1,0⟩⟩
def t6_234jobs0 : List Job := [⟨plan5384,[⟨1,0,2⟩],(some ⟨1,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5384,[⟨1,1,1⟩],(some ⟨1,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_234jobs1 : List Job := [⟨plan5384,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_234jobs : List Job := t6_234jobs0++t6_234jobs1




def t6_235root : Job := ⟨plan6345,[],none,⟨15,1,0⟩⟩
def t6_235jobs0 : List Job := [⟨plan5385,[⟨1,0,2⟩],(some ⟨1,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5385,[⟨1,1,1⟩],(some ⟨1,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_235jobs1 : List Job := [⟨plan5385,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_235jobs : List Job := t6_235jobs0++t6_235jobs1




def t6_236root : Job := ⟨plan6346,[],none,⟨15,1,0⟩⟩
def t6_236jobs0 : List Job := [⟨plan6346,[],none,⟨15,1,0⟩⟩]

def t6_236jobs : List Job := t6_236jobs0




def t6_237root : Job := ⟨plan6487,[],none,⟨15,3,0⟩⟩
def t6_237jobs0 : List Job := [⟨plan6487,[],none,⟨15,3,0⟩⟩]

def t6_237jobs : List Job := t6_237jobs0




def t6_238root : Job := ⟨plan6488,[],none,⟨15,3,0⟩⟩
def t6_238jobs0 : List Job := [⟨plan5454,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5454,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_238jobs1 : List Job := [⟨plan5454,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_238jobs : List Job := t6_238jobs0++t6_238jobs1




def t6_239root : Job := ⟨plan6489,[],none,⟨15,3,0⟩⟩
def t6_239jobs0 : List Job := [⟨plan6489,[],none,⟨15,3,0⟩⟩]

def t6_239jobs : List Job := t6_239jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


