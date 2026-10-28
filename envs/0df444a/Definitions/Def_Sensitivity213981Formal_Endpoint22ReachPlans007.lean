-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans007
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans007
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:44:50.470493+00:00
-- url     : https://prove2.me/theorems/7c53cc97-677b-4cbb-9320-4cac223a10f3
-- title:
--   Endpoint22 Reach Plans007 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans007 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan744`, `ThreeBoundEndpoint22Reachable.plan745`, `ThreeBoundEndpoint22Reachable.plan746`, `ThreeBoundEndpoint22Reachable.plan747`, `ThreeBoundEndpoint22Reachable.plan678`, `ThreeBoundEndpoint22Reachable.plan748`, `ThreeBoundEndpoint22Reachable.plan749`, `ThreeBoundEndpoint22Reachable.plan750`, `ThreeBoundEndpoint22Reachable.plan751`, `ThreeBoundEndpoint22Reachable.plan752`, `ThreeBoundEndpoint22Reachable.plan753`, `ThreeBoundEndpoint22Reachable.plan754`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans007.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans003
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
def plan673 : Plan := .step choices38 bits170 plan243

def plan674 : Plan := .step choices38 bits170 plan244

def plan675 : Plan := .step choices38 bits172 plan247

def plan676 : Plan := .step choices38 bits172 plan248

def plan677 : Plan := .step choices38 bits172 plan249

def plan678 : Plan := .step choices38 bits172 plan250

def plan679 : Plan := .step choices38 bits172 plan251

def plan680 : Plan := .step choices38 bits172 plan253

def plan681 : Plan := .step choices38 bits172 plan254

def plan682 : Plan := .step choices38 bits172 plan255

def plan683 : Plan := .step choices38 bits169 plan256

def plan684 : Plan := .step choices38 bits169 plan257

def plan685 : Plan := .step choices38 bits172 plan258

def plan686 : Plan := .step choices38 bits169 plan259

def plan687 : Plan := .step choices38 bits169 plan260

def plan688 : Plan := .step choices38 bits172 plan261

def plan689 : Plan := .step choices39 bits174 plan247

def plan690 : Plan := .step choices39 bits174 plan248

def plan691 : Plan := .step choices39 bits174 plan249

def plan692 : Plan := .step choices39 bits174 plan250

def plan693 : Plan := .step choices39 bits174 plan251

def plan694 : Plan := .step choices39 bits174 plan253

def plan695 : Plan := .step choices39 bits174 plan254

def plan696 : Plan := .step choices39 bits174 plan255

def plan697 : Plan := .step choices39 bits174 plan258

def plan698 : Plan := .step choices39 bits174 plan261

def plan699 : Plan := .step choices40 bits174 plan253

def plan700 : Plan := .step choices40 bits174 plan254

def plan701 : Plan := .step choices40 bits174 plan255

def plan702 : Plan := .step choices41 bits171 plan245

def plan703 : Plan := .step choices41 bits171 plan246

def plan704 : Plan := .step choices41 bits171 plan252

def plan705 : Plan := .step choices42 bits174 plan252

def plan706 : Plan := .step choices45 bits171 plan245

def plan707 : Plan := .step choices45 bits171 plan246

def plan708 : Plan := .step choices45 bits171 plan252

def plan709 : Plan := .step choices46 bits174 plan252

def plan710 : Plan := .step choices48 bits233 plan273

def plan711 : Plan := .step choices48 bits233 plan274

def plan712 : Plan := .step choices48 bits233 plan275

def plan713 : Plan := .step choices48 bits233 plan277

def plan714 : Plan := .step choices48 bits233 plan278

def plan715 : Plan := .step choices48 bits234 plan280

def plan716 : Plan := .step choices48 bits234 plan281

def plan717 : Plan := .step choices48 bits234 plan282

def plan718 : Plan := .step choices48 bits234 plan283

def plan719 : Plan := .step choices48 bits234 plan284

def plan720 : Plan := .step choices48 bits234 plan285

def plan721 : Plan := .step choices48 bits234 plan286

def plan722 : Plan := .step choices48 bits234 plan287

def plan723 : Plan := .step choices48 bits234 plan288

def plan724 : Plan := .step choices48 bits233 plan291

def plan725 : Plan := .step choices48 bits233 plan292

def plan726 : Plan := .step choices48 bits233 plan293

def plan727 : Plan := .step choices48 bits233 plan295

def plan728 : Plan := .step choices48 bits233 plan296

def plan729 : Plan := .step choices48 bits234 plan298

def plan730 : Plan := .step choices48 bits234 plan299

def plan731 : Plan := .step choices48 bits234 plan300

def plan732 : Plan := .step choices48 bits234 plan301

def plan733 : Plan := .step choices48 bits234 plan302

def plan734 : Plan := .step choices48 bits234 plan303

def plan735 : Plan := .step choices49 bits235 plan272

def plan736 : Plan := .step choices49 bits236 plan273

def plan737 : Plan := .step choices49 bits236 plan274

def plan738 : Plan := .step choices49 bits236 plan275

def plan739 : Plan := .step choices49 bits235 plan276

def plan740 : Plan := .step choices49 bits236 plan277

def plan741 : Plan := .step choices49 bits236 plan278

def plan742 : Plan := .step choices49 bits237 plan280

def plan743 : Plan := .step choices49 bits237 plan281

def plan744 : Plan := .step choices49 bits237 plan282

def plan745 : Plan := .step choices49 bits237 plan283

def plan746 : Plan := .step choices49 bits237 plan284

def plan747 : Plan := .step choices49 bits237 plan285

def plan748 : Plan := .step choices49 bits237 plan286

def plan749 : Plan := .step choices49 bits237 plan287

def plan750 : Plan := .step choices49 bits237 plan288

def plan751 : Plan := .step choices49 bits236 plan291

def plan752 : Plan := .step choices49 bits236 plan292

def plan753 : Plan := .step choices49 bits236 plan293

def plan754 : Plan := .step choices49 bits235 plan294

def plan755 : Plan := .step choices49 bits236 plan295

def plan756 : Plan := .step choices49 bits236 plan296

def plan757 : Plan := .step choices49 bits237 plan298

def plan758 : Plan := .step choices49 bits237 plan299

def plan759 : Plan := .step choices49 bits237 plan300

def plan760 : Plan := .step choices49 bits237 plan301

def plan761 : Plan := .step choices49 bits237 plan302

def plan762 : Plan := .step choices49 bits237 plan303

def plan763 : Plan := .step choices50 bits240 plan280

def plan764 : Plan := .step choices50 bits240 plan281

def plan765 : Plan := .step choices50 bits240 plan282

def plan766 : Plan := .step choices50 bits240 plan283

def plan767 : Plan := .step choices50 bits240 plan284

def plan768 : Plan := .step choices50 bits240 plan285

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


