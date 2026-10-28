-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans096
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans096
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:08:44.48447+00:00
-- url     : https://prove2.me/theorems/b6bd4c03-f00a-4b6e-8565-184e817eda09
-- title:
--   Endpoint22 Reach Plans096 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans096 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan9222`, `ThreeBoundEndpoint22Reachable.plan9223`, `ThreeBoundEndpoint22Reachable.plan9224`, `ThreeBoundEndpoint22Reachable.plan9225`, `ThreeBoundEndpoint22Reachable.plan9226`, `ThreeBoundEndpoint22Reachable.plan9227`, `ThreeBoundEndpoint22Reachable.plan9228`, `ThreeBoundEndpoint22Reachable.plan9229`, `ThreeBoundEndpoint22Reachable.plan9230`, `ThreeBoundEndpoint22Reachable.plan9231`, `ThreeBoundEndpoint22Reachable.plan9232`, `ThreeBoundEndpoint22Reachable.plan9233`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans096.lean, lines 1–93.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans095
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
def plan9217 : Plan := .step choices320 bits1828 plan9144

def plan9218 : Plan := .step choices320 bits1829 plan9145

def plan9219 : Plan := .step choices320 bits1828 plan9146

def plan9220 : Plan := .step choices322 bits1833 plan9163

def plan9221 : Plan := .step choices322 bits1834 plan9166

def plan9222 : Plan := .step choices322 bits1833 plan9168

def plan9223 : Plan := .step choices323 bits1833 plan9159

def plan9224 : Plan := .step choices323 bits1833 plan9161

def plan9225 : Plan := .step choices323 bits1834 plan9163

def plan9226 : Plan := .step choices323 bits1833 plan9164

def plan9227 : Plan := .step choices323 bits1835 plan9166

def plan9228 : Plan := .step choices323 bits1833 plan9167

def plan9229 : Plan := .step choices323 bits1834 plan9168

def plan9230 : Plan := .step choices323 bits1833 plan9169

def plan9231 : Plan := .step choices324 bits1833 plan9160

def plan9232 : Plan := .step choices324 bits1834 plan9161

def plan9233 : Plan := .step choices324 bits1833 plan9162

def plan9234 : Plan := .step choices324 bits1835 plan9163

def plan9235 : Plan := .step choices324 bits1834 plan9164

def plan9236 : Plan := .step choices324 bits1833 plan9165

def plan9237 : Plan := .step choices324 bits1836 plan9166

def plan9238 : Plan := .step choices324 bits1835 plan9168

def plan9239 : Plan := .step choices324 bits1834 plan9169

def plan9240 : Plan := .step choices324 bits1833 plan9170

def plan9241 : Plan := .step choices325 bits1837 plan9166

def plan9242 : Plan := .step choices326 bits1833 plan9163

def plan9243 : Plan := .step choices326 bits1834 plan9166

def plan9244 : Plan := .step choices326 bits1833 plan9168

def plan9245 : Plan := .step choices327 bits1833 plan9161

def plan9246 : Plan := .step choices327 bits1834 plan9163

def plan9247 : Plan := .step choices327 bits1833 plan9164

def plan9248 : Plan := .step choices327 bits1835 plan9166

def plan9249 : Plan := .step choices327 bits1833 plan9167

def plan9250 : Plan := .step choices327 bits1834 plan9168

def plan9251 : Plan := .step choices327 bits1833 plan9169

def plan9252 : Plan := .step choices328 bits1836 plan9166

def plan9253 : Plan := .step choices328 bits1835 plan9168

def plan9254 : Plan := .step choices328 bits1834 plan9169

def plan9255 : Plan := .step choices328 bits1833 plan9170

def plan9256 : Plan := .step choices329 bits1838 plan9171

def plan9257 : Plan := .step choices329 bits1839 plan9256

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


