-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans006
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:44:35.797953+00:00
-- url     : https://prove2.me/theorems/a1ad66e8-9fa3-4920-b9b0-49b566f50346
-- title:
--   Endpoint22 Reach Plans006 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans006 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan647`, `ThreeBoundEndpoint22Reachable.plan648`, `ThreeBoundEndpoint22Reachable.plan649`, `ThreeBoundEndpoint22Reachable.plan581`, `ThreeBoundEndpoint22Reachable.plan650`, `ThreeBoundEndpoint22Reachable.plan651`, `ThreeBoundEndpoint22Reachable.plan652`, `ThreeBoundEndpoint22Reachable.plan653`, `ThreeBoundEndpoint22Reachable.plan654`, `ThreeBoundEndpoint22Reachable.plan655`, `ThreeBoundEndpoint22Reachable.plan656`, `ThreeBoundEndpoint22Reachable.plan657`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans006.lean, lines 1–208.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans002
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
def plan577 : Plan := .step choices219 bits279 plan135

def plan578 : Plan := .step choices220 bits281 plan134

def plan579 : Plan := .step choices223 bits280 plan134

def plan580 : Plan := .step choices223 bits279 plan135

def plan581 : Plan := .step choices226 bits339 plan136

def plan582 : Plan := .step choices226 bits340 plan137

def plan583 : Plan := .step choices226 bits339 plan138

def plan584 : Plan := .step choices227 bits341 plan137

def plan585 : Plan := .step choices230 bits340 plan137

def plan586 : Plan := .step choices230 bits339 plan138

def plan587 : Plan := .step choices231 bits55 plan139

def plan588 : Plan := .step choices233 bits78 plan140

def plan589 : Plan := .step choices233 bits79 plan141

def plan590 : Plan := .step choices233 bits78 plan142

def plan591 : Plan := .step choices239 bits122 plan144

def plan592 : Plan := .step choices241 bits101 plan143

def plan593 : Plan := .step choices241 bits104 plan144

def plan594 : Plan := .step choices241 bits101 plan145

def plan595 : Plan := .step choices242 bits105 plan144

def plan596 : Plan := .step choices244 bits104 plan144

def plan597 : Plan := .step choices244 bits101 plan145

def plan598 : Plan := .step choices251 bits148 plan146

def plan599 : Plan := .step choices251 bits151 plan147

def plan600 : Plan := .step choices251 bits148 plan148

def plan601 : Plan := .step choices252 bits152 plan147

def plan602 : Plan := .step choices255 bits151 plan147

def plan603 : Plan := .step choices255 bits148 plan148

def plan604 : Plan := .step choices262 bits210 plan149

def plan605 : Plan := .step choices262 bits211 plan150

def plan606 : Plan := .step choices262 bits210 plan151

def plan607 : Plan := .step choices263 bits212 plan150

def plan608 : Plan := .step choices266 bits211 plan150

def plan609 : Plan := .step choices266 bits210 plan151

def plan610 : Plan := .step choices273 bits282 plan152

def plan611 : Plan := .step choices273 bits283 plan153

def plan612 : Plan := .step choices273 bits282 plan154

def plan613 : Plan := .step choices274 bits284 plan153

def plan614 : Plan := .step choices277 bits283 plan153

def plan615 : Plan := .step choices277 bits282 plan154

def plan616 : Plan := .step choices284 bits342 plan155

def plan617 : Plan := .step choices284 bits343 plan156

def plan618 : Plan := .step choices284 bits342 plan157

def plan619 : Plan := .step choices285 bits344 plan156

def plan620 : Plan := .step choices288 bits343 plan156

def plan621 : Plan := .step choices288 bits342 plan157

def plan622 : Plan := .step choices291 bits441 plan158

def plan623 : Plan := .step choices291 bits442 plan159

def plan624 : Plan := .step choices291 bits441 plan160

def plan625 : Plan := .step choices292 bits443 plan159

def plan626 : Plan := .step choices295 bits442 plan159

def plan627 : Plan := .step choices295 bits441 plan160

def plan628 : Plan := .step choices297 bits213 plan161

def plan629 : Plan := .step choices301 bits285 plan162

def plan630 : Plan := .step choices308 bits345 plan163

def plan631 : Plan := .step choices318 bits444 plan164

def plan632 : Plan := .step choices325 bits565 plan165

def plan633 : Plan := .step choices329 bits638 plan166

def plan634 : Plan := .step choices33 bits127 plan233

def plan635 : Plan := .step choices33 bits127 plan234

def plan636 : Plan := .step choices33 bits128 plan235

def plan637 : Plan := .step choices33 bits128 plan236

def plan638 : Plan := .step choices33 bits128 plan237

def plan639 : Plan := .step choices34 bits127 plan232

def plan640 : Plan := .step choices34 bits128 plan233

def plan641 : Plan := .step choices34 bits128 plan234

def plan642 : Plan := .step choices34 bits130 plan235

def plan643 : Plan := .step choices34 bits130 plan236

def plan644 : Plan := .step choices34 bits130 plan237

def plan645 : Plan := .step choices35 bits131 plan235

def plan646 : Plan := .step choices35 bits131 plan236

def plan647 : Plan := .step choices35 bits131 plan237

def plan648 : Plan := .step choices36 bits131 plan237

def plan649 : Plan := .step choices37 bits166 plan239

def plan650 : Plan := .step choices37 bits166 plan240

def plan651 : Plan := .step choices37 bits166 plan241

def plan652 : Plan := .step choices37 bits166 plan243

def plan653 : Plan := .step choices37 bits166 plan244

def plan654 : Plan := .step choices37 bits167 plan247

def plan655 : Plan := .step choices37 bits167 plan248

def plan656 : Plan := .step choices37 bits167 plan249

def plan657 : Plan := .step choices37 bits167 plan250

def plan658 : Plan := .step choices37 bits167 plan251

def plan659 : Plan := .step choices37 bits167 plan253

def plan660 : Plan := .step choices37 bits167 plan254

def plan661 : Plan := .step choices37 bits167 plan255

def plan662 : Plan := .step choices37 bits165 plan256

def plan663 : Plan := .step choices37 bits165 plan257

def plan664 : Plan := .step choices37 bits167 plan258

def plan665 : Plan := .step choices37 bits165 plan259

def plan666 : Plan := .step choices37 bits165 plan260

def plan667 : Plan := .step choices37 bits167 plan261

def plan668 : Plan := .step choices38 bits168 plan238

def plan669 : Plan := .step choices38 bits170 plan239

def plan670 : Plan := .step choices38 bits170 plan240

def plan671 : Plan := .step choices38 bits170 plan241

def plan672 : Plan := .step choices38 bits168 plan242

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


