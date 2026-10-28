-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans008
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans008
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:44:45.263363+00:00
-- url     : https://prove2.me/theorems/d892189f-aef3-4ad6-9230-b6a863cbcce9
-- title:
--   Endpoint22 Reach Plans008 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans008 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan840`, `ThreeBoundEndpoint22Reachable.plan841`, `ThreeBoundEndpoint22Reachable.plan842`, `ThreeBoundEndpoint22Reachable.plan843`, `ThreeBoundEndpoint22Reachable.plan844`, `ThreeBoundEndpoint22Reachable.plan845`, `ThreeBoundEndpoint22Reachable.plan774`, `ThreeBoundEndpoint22Reachable.plan846`, `ThreeBoundEndpoint22Reachable.plan847`, `ThreeBoundEndpoint22Reachable.plan848`, `ThreeBoundEndpoint22Reachable.plan849`, `ThreeBoundEndpoint22Reachable.plan850`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans008.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
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
def plan769 : Plan := .step choices50 bits240 plan286

def plan770 : Plan := .step choices50 bits240 plan287

def plan771 : Plan := .step choices50 bits240 plan288

def plan772 : Plan := .step choices50 bits240 plan298

def plan773 : Plan := .step choices50 bits240 plan299

def plan774 : Plan := .step choices50 bits240 plan300

def plan775 : Plan := .step choices50 bits240 plan301

def plan776 : Plan := .step choices50 bits240 plan302

def plan777 : Plan := .step choices50 bits240 plan303

def plan778 : Plan := .step choices51 bits240 plan285

def plan779 : Plan := .step choices51 bits240 plan286

def plan780 : Plan := .step choices51 bits240 plan287

def plan781 : Plan := .step choices51 bits240 plan288

def plan782 : Plan := .step choices51 bits240 plan302

def plan783 : Plan := .step choices51 bits240 plan303

def plan784 : Plan := .step choices52 bits239 plan262

def plan785 : Plan := .step choices52 bits239 plan263

def plan786 : Plan := .step choices52 bits239 plan264

def plan787 : Plan := .step choices52 bits239 plan265

def plan788 : Plan := .step choices52 bits239 plan266

def plan789 : Plan := .step choices52 bits239 plan267

def plan790 : Plan := .step choices52 bits239 plan268

def plan791 : Plan := .step choices52 bits239 plan269

def plan792 : Plan := .step choices52 bits238 plan270

def plan793 : Plan := .step choices52 bits238 plan271

def plan794 : Plan := .step choices52 bits239 plan279

def plan795 : Plan := .step choices52 bits238 plan289

def plan796 : Plan := .step choices52 bits238 plan290

def plan797 : Plan := .step choices52 bits239 plan297

def plan798 : Plan := .step choices53 bits240 plan267

def plan799 : Plan := .step choices53 bits240 plan268

def plan800 : Plan := .step choices53 bits240 plan269

def plan801 : Plan := .step choices53 bits240 plan279

def plan802 : Plan := .step choices53 bits240 plan297

def plan803 : Plan := .step choices56 bits239 plan262

def plan804 : Plan := .step choices56 bits239 plan263

def plan805 : Plan := .step choices56 bits239 plan264

def plan806 : Plan := .step choices56 bits239 plan265

def plan807 : Plan := .step choices56 bits239 plan266

def plan808 : Plan := .step choices56 bits239 plan267

def plan809 : Plan := .step choices56 bits239 plan268

def plan810 : Plan := .step choices56 bits239 plan269

def plan811 : Plan := .step choices56 bits239 plan279

def plan812 : Plan := .step choices56 bits238 plan289

def plan813 : Plan := .step choices56 bits238 plan290

def plan814 : Plan := .step choices56 bits239 plan297

def plan815 : Plan := .step choices57 bits240 plan267

def plan816 : Plan := .step choices57 bits240 plan268

def plan817 : Plan := .step choices57 bits240 plan269

def plan818 : Plan := .step choices57 bits240 plan297

def plan819 : Plan := .step choices59 bits309 plan304

def plan820 : Plan := .step choices59 bits310 plan305

def plan821 : Plan := .step choices59 bits310 plan306

def plan822 : Plan := .step choices59 bits310 plan307

def plan823 : Plan := .step choices59 bits309 plan308

def plan824 : Plan := .step choices59 bits310 plan309

def plan825 : Plan := .step choices59 bits310 plan310

def plan826 : Plan := .step choices59 bits311 plan311

def plan827 : Plan := .step choices59 bits311 plan312

def plan828 : Plan := .step choices59 bits311 plan313

def plan829 : Plan := .step choices59 bits311 plan314

def plan830 : Plan := .step choices59 bits311 plan315

def plan831 : Plan := .step choices59 bits311 plan316

def plan832 : Plan := .step choices59 bits311 plan317

def plan833 : Plan := .step choices59 bits311 plan318

def plan834 : Plan := .step choices59 bits311 plan319

def plan835 : Plan := .step choices59 bits310 plan320

def plan836 : Plan := .step choices59 bits310 plan321

def plan837 : Plan := .step choices59 bits310 plan322

def plan838 : Plan := .step choices59 bits309 plan323

def plan839 : Plan := .step choices59 bits310 plan324

def plan840 : Plan := .step choices59 bits310 plan325

def plan841 : Plan := .step choices59 bits311 plan326

def plan842 : Plan := .step choices59 bits311 plan327

def plan843 : Plan := .step choices59 bits311 plan328

def plan844 : Plan := .step choices59 bits311 plan329

def plan845 : Plan := .step choices59 bits311 plan330

def plan846 : Plan := .step choices59 bits311 plan331

def plan847 : Plan := .step choices60 bits312 plan311

def plan848 : Plan := .step choices60 bits312 plan312

def plan849 : Plan := .step choices60 bits312 plan313

def plan850 : Plan := .step choices60 bits312 plan314

def plan851 : Plan := .step choices60 bits312 plan315

def plan852 : Plan := .step choices60 bits312 plan316

def plan853 : Plan := .step choices60 bits312 plan317

def plan854 : Plan := .step choices60 bits312 plan318

def plan855 : Plan := .step choices60 bits312 plan319

def plan856 : Plan := .step choices60 bits312 plan326

def plan857 : Plan := .step choices60 bits312 plan327

def plan858 : Plan := .step choices60 bits312 plan328

def plan859 : Plan := .step choices60 bits312 plan329

def plan860 : Plan := .step choices60 bits312 plan330

def plan861 : Plan := .step choices60 bits312 plan331

def plan862 : Plan := .step choices61 bits312 plan316

def plan863 : Plan := .step choices61 bits312 plan317

def plan864 : Plan := .step choices61 bits312 plan318

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


