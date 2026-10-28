-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks005
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks005
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:08.126294+00:00
-- url     : https://prove2.me/theorems/d80549c5-78ee-468c-b0ee-4e31cc4ca867
-- title:
--   Endpoint22 Reach Checks005 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks005 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_6root`, `ThreeBoundEndpoint22Reachable.t5_6jobs0`, `ThreeBoundEndpoint22Reachable.t5_6jobs`, `ThreeBoundEndpoint22Reachable.t5_7root`, `ThreeBoundEndpoint22Reachable.t5_7jobs0`, `ThreeBoundEndpoint22Reachable.t4_701root`, `ThreeBoundEndpoint22Reachable.t5_7jobs`, `ThreeBoundEndpoint22Reachable.t4_701jobs0`, `ThreeBoundEndpoint22Reachable.t5_8root`, `ThreeBoundEndpoint22Reachable.t5_8jobs0`, `ThreeBoundEndpoint22Reachable.t5_8jobs`, `ThreeBoundEndpoint22Reachable.t5_9root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks005.lean, lines 1–2044.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans018
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans020
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans021
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans023
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans024
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans025
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
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

def t4_688root : Job := ⟨plan2276,[],none,⟨6,3,0⟩⟩
def t4_688jobs0 : List Job := [⟨plan2276,[],none,⟨6,3,0⟩⟩]

def t4_688jobs : List Job := t4_688jobs0




def t4_689root : Job := ⟨plan2277,[],none,⟨6,3,0⟩⟩
def t4_689jobs0 : List Job := [⟨plan2277,[],none,⟨6,3,0⟩⟩]

def t4_689jobs : List Job := t4_689jobs0




def t4_690root : Job := ⟨plan2278,[],none,⟨6,3,0⟩⟩
def t4_690jobs0 : List Job := [⟨plan2278,[],none,⟨6,3,0⟩⟩]

def t4_690jobs : List Job := t4_690jobs0




def t4_691root : Job := ⟨plan2279,[],none,⟨6,3,0⟩⟩
def t4_691jobs0 : List Job := [⟨plan2279,[],none,⟨6,3,0⟩⟩]

def t4_691jobs : List Job := t4_691jobs0




def t4_692root : Job := ⟨plan2280,[],none,⟨6,3,0⟩⟩
def t4_692jobs0 : List Job := [⟨plan2280,[],none,⟨6,3,0⟩⟩]

def t4_692jobs : List Job := t4_692jobs0




def t4_693root : Job := ⟨plan1802,[],none,⟨6,0,0⟩⟩
def t4_693jobs0 : List Job := [⟨plan1802,[],none,⟨6,0,0⟩⟩]

def t4_693jobs : List Job := t4_693jobs0




def t4_694root : Job := ⟨plan2008,[],none,⟨6,1,0⟩⟩
def t4_694jobs0 : List Job := [⟨plan2008,[],none,⟨6,1,0⟩⟩]

def t4_694jobs : List Job := t4_694jobs0




def t4_695root : Job := ⟨plan2009,[],none,⟨6,1,0⟩⟩
def t4_695jobs0 : List Job := [⟨plan2009,[],none,⟨6,1,0⟩⟩]

def t4_695jobs : List Job := t4_695jobs0




def t4_696root : Job := ⟨plan2010,[],none,⟨6,1,0⟩⟩
def t4_696jobs0 : List Job := [⟨plan2010,[],none,⟨6,1,0⟩⟩]

def t4_696jobs : List Job := t4_696jobs0




def t4_697root : Job := ⟨plan2281,[],none,⟨6,3,0⟩⟩
def t4_697jobs0 : List Job := [⟨plan2281,[],none,⟨6,3,0⟩⟩]

def t4_697jobs : List Job := t4_697jobs0




def t4_698root : Job := ⟨plan2282,[],none,⟨6,3,0⟩⟩
def t4_698jobs0 : List Job := [⟨plan2282,[],none,⟨6,3,0⟩⟩]

def t4_698jobs : List Job := t4_698jobs0




def t4_699root : Job := ⟨plan2283,[],none,⟨6,3,0⟩⟩
def t4_699jobs0 : List Job := [⟨plan2283,[],none,⟨6,3,0⟩⟩]

def t4_699jobs : List Job := t4_699jobs0




def t4_700root : Job := ⟨plan2284,[],none,⟨6,3,0⟩⟩
def t4_700jobs0 : List Job := [⟨plan2284,[],none,⟨6,3,0⟩⟩]

def t4_700jobs : List Job := t4_700jobs0




def t4_701root : Job := ⟨plan2285,[],none,⟨6,3,0⟩⟩
def t4_701jobs0 : List Job := [⟨plan2285,[],none,⟨6,3,0⟩⟩]

def t4_701jobs : List Job := t4_701jobs0




def t4_702root : Job := ⟨plan2286,[],none,⟨6,3,0⟩⟩
def t4_702jobs0 : List Job := [⟨plan2286,[],none,⟨6,3,0⟩⟩]

def t4_702jobs : List Job := t4_702jobs0




def t4_703root : Job := ⟨plan2011,[],none,⟨6,1,0⟩⟩
def t4_703jobs0 : List Job := [⟨plan2011,[],none,⟨6,1,0⟩⟩]

def t4_703jobs : List Job := t4_703jobs0




def t4_704root : Job := ⟨plan2287,[],none,⟨6,3,0⟩⟩
def t4_704jobs0 : List Job := [⟨plan2287,[],none,⟨6,3,0⟩⟩]

def t4_704jobs : List Job := t4_704jobs0




def t4_705root : Job := ⟨plan2288,[],none,⟨6,3,0⟩⟩
def t4_705jobs0 : List Job := [⟨plan2288,[],none,⟨6,3,0⟩⟩]

def t4_705jobs : List Job := t4_705jobs0




def t4_706root : Job := ⟨plan2289,[],none,⟨6,3,0⟩⟩
def t4_706jobs0 : List Job := [⟨plan2289,[],none,⟨6,3,0⟩⟩]

def t4_706jobs : List Job := t4_706jobs0




def t4_707root : Job := ⟨plan2290,[],none,⟨6,3,0⟩⟩
def t4_707jobs0 : List Job := [⟨plan2290,[],none,⟨6,3,0⟩⟩]

def t4_707jobs : List Job := t4_707jobs0




def t4_708root : Job := ⟨plan2437,[],none,⟨6,6,0⟩⟩
def t4_708jobs0 : List Job := [⟨plan2437,[],none,⟨6,6,0⟩⟩]

def t4_708jobs : List Job := t4_708jobs0




def t4_709root : Job := ⟨plan2438,[],none,⟨6,6,0⟩⟩
def t4_709jobs0 : List Job := [⟨plan2438,[],none,⟨6,6,0⟩⟩]

def t4_709jobs : List Job := t4_709jobs0




def t4_710root : Job := ⟨plan2439,[],none,⟨6,6,0⟩⟩
def t4_710jobs0 : List Job := [⟨plan2439,[],none,⟨6,6,0⟩⟩]

def t4_710jobs : List Job := t4_710jobs0




def t4_711root : Job := ⟨plan2440,[],none,⟨6,6,0⟩⟩
def t4_711jobs0 : List Job := [⟨plan2440,[],none,⟨6,6,0⟩⟩]

def t4_711jobs : List Job := t4_711jobs0




def t4_712root : Job := ⟨plan2441,[],none,⟨6,6,0⟩⟩
def t4_712jobs0 : List Job := [⟨plan2441,[],none,⟨6,6,0⟩⟩]

def t4_712jobs : List Job := t4_712jobs0




def t4_713root : Job := ⟨plan2442,[],none,⟨6,6,0⟩⟩
def t4_713jobs0 : List Job := [⟨plan2442,[],none,⟨6,6,0⟩⟩]

def t4_713jobs : List Job := t4_713jobs0




def t4_714root : Job := ⟨plan2443,[],none,⟨6,6,0⟩⟩
def t4_714jobs0 : List Job := [⟨plan2443,[],none,⟨6,6,0⟩⟩]

def t4_714jobs : List Job := t4_714jobs0




def t4_715root : Job := ⟨plan2444,[],none,⟨6,6,0⟩⟩
def t4_715jobs0 : List Job := [⟨plan2444,[],none,⟨6,6,0⟩⟩]

def t4_715jobs : List Job := t4_715jobs0




def t4_716root : Job := ⟨plan2445,[],none,⟨6,6,0⟩⟩
def t4_716jobs0 : List Job := [⟨plan2445,[],none,⟨6,6,0⟩⟩]

def t4_716jobs : List Job := t4_716jobs0




def t4_717root : Job := ⟨plan2291,[],none,⟨6,3,0⟩⟩
def t4_717jobs0 : List Job := [⟨plan2291,[],none,⟨6,3,0⟩⟩]

def t4_717jobs : List Job := t4_717jobs0




def t4_718root : Job := ⟨plan2446,[],none,⟨6,6,0⟩⟩
def t4_718jobs0 : List Job := [⟨plan2446,[],none,⟨6,6,0⟩⟩]

def t4_718jobs : List Job := t4_718jobs0




def t4_719root : Job := ⟨plan2447,[],none,⟨6,6,0⟩⟩
def t4_719jobs0 : List Job := [⟨plan2447,[],none,⟨6,6,0⟩⟩]

def t4_719jobs : List Job := t4_719jobs0




def t4_720root : Job := ⟨plan2448,[],none,⟨6,6,0⟩⟩
def t4_720jobs0 : List Job := [⟨plan2448,[],none,⟨6,6,0⟩⟩]

def t4_720jobs : List Job := t4_720jobs0




def t4_721root : Job := ⟨plan2449,[],none,⟨6,6,0⟩⟩
def t4_721jobs0 : List Job := [⟨plan2449,[],none,⟨6,6,0⟩⟩]

def t4_721jobs : List Job := t4_721jobs0




def t4_722root : Job := ⟨plan2450,[],none,⟨6,6,0⟩⟩
def t4_722jobs0 : List Job := [⟨plan2450,[],none,⟨6,6,0⟩⟩]

def t4_722jobs : List Job := t4_722jobs0




def t4_723root : Job := ⟨plan2451,[],none,⟨6,6,0⟩⟩
def t4_723jobs0 : List Job := [⟨plan2451,[],none,⟨6,6,0⟩⟩]

def t4_723jobs : List Job := t4_723jobs0




def t4_724root : Job := ⟨plan2452,[],none,⟨6,6,0⟩⟩
def t4_724jobs0 : List Job := [⟨plan2452,[],none,⟨6,6,0⟩⟩]

def t4_724jobs : List Job := t4_724jobs0




def t4_725root : Job := ⟨plan2453,[],none,⟨6,6,0⟩⟩
def t4_725jobs0 : List Job := [⟨plan2453,[],none,⟨6,6,0⟩⟩]

def t4_725jobs : List Job := t4_725jobs0




def t4_726root : Job := ⟨plan2454,[],none,⟨6,6,0⟩⟩
def t4_726jobs0 : List Job := [⟨plan2454,[],none,⟨6,6,0⟩⟩]

def t4_726jobs : List Job := t4_726jobs0




def t4_727root : Job := ⟨plan2455,[],none,⟨6,6,0⟩⟩
def t4_727jobs0 : List Job := [⟨plan2455,[],none,⟨6,6,0⟩⟩]

def t4_727jobs : List Job := t4_727jobs0




def t4_728root : Job := ⟨plan2456,[],none,⟨6,6,0⟩⟩
def t4_728jobs0 : List Job := [⟨plan2456,[],none,⟨6,6,0⟩⟩]

def t4_728jobs : List Job := t4_728jobs0




def t4_729root : Job := ⟨plan2457,[],none,⟨6,6,0⟩⟩
def t4_729jobs0 : List Job := [⟨plan2457,[],none,⟨6,6,0⟩⟩]

def t4_729jobs : List Job := t4_729jobs0




def t4_730root : Job := ⟨plan2458,[],none,⟨6,6,0⟩⟩
def t4_730jobs0 : List Job := [⟨plan2458,[],none,⟨6,6,0⟩⟩]

def t4_730jobs : List Job := t4_730jobs0




def t4_731root : Job := ⟨plan2012,[],none,⟨6,1,0⟩⟩
def t4_731jobs0 : List Job := [⟨plan2012,[],none,⟨6,1,0⟩⟩]

def t4_731jobs : List Job := t4_731jobs0




def t4_732root : Job := ⟨plan2013,[],none,⟨6,1,0⟩⟩
def t4_732jobs0 : List Job := [⟨plan2013,[],none,⟨6,1,0⟩⟩]

def t4_732jobs : List Job := t4_732jobs0




def t4_733root : Job := ⟨plan2292,[],none,⟨6,3,0⟩⟩
def t4_733jobs0 : List Job := [⟨plan2292,[],none,⟨6,3,0⟩⟩]

def t4_733jobs : List Job := t4_733jobs0




def t4_734root : Job := ⟨plan2293,[],none,⟨6,3,0⟩⟩
def t4_734jobs0 : List Job := [⟨plan2293,[],none,⟨6,3,0⟩⟩]

def t4_734jobs : List Job := t4_734jobs0




def t4_735root : Job := ⟨plan2294,[],none,⟨6,3,0⟩⟩
def t4_735jobs0 : List Job := [⟨plan2294,[],none,⟨6,3,0⟩⟩]

def t4_735jobs : List Job := t4_735jobs0




def t4_736root : Job := ⟨plan2295,[],none,⟨6,3,0⟩⟩
def t4_736jobs0 : List Job := [⟨plan2295,[],none,⟨6,3,0⟩⟩]

def t4_736jobs : List Job := t4_736jobs0




def t4_737root : Job := ⟨plan2296,[],none,⟨6,3,0⟩⟩
def t4_737jobs0 : List Job := [⟨plan2296,[],none,⟨6,3,0⟩⟩]

def t4_737jobs : List Job := t4_737jobs0




def t4_738root : Job := ⟨plan2014,[],none,⟨6,1,0⟩⟩
def t4_738jobs0 : List Job := [⟨plan2014,[],none,⟨6,1,0⟩⟩]

def t4_738jobs : List Job := t4_738jobs0




def t4_739root : Job := ⟨plan2297,[],none,⟨6,3,0⟩⟩
def t4_739jobs0 : List Job := [⟨plan2297,[],none,⟨6,3,0⟩⟩]

def t4_739jobs : List Job := t4_739jobs0




def t4_740root : Job := ⟨plan2298,[],none,⟨6,3,0⟩⟩
def t4_740jobs0 : List Job := [⟨plan2298,[],none,⟨6,3,0⟩⟩]

def t4_740jobs : List Job := t4_740jobs0




def t4_741root : Job := ⟨plan2299,[],none,⟨6,3,0⟩⟩
def t4_741jobs0 : List Job := [⟨plan2299,[],none,⟨6,3,0⟩⟩]

def t4_741jobs : List Job := t4_741jobs0




def t4_742root : Job := ⟨plan2300,[],none,⟨6,3,0⟩⟩
def t4_742jobs0 : List Job := [⟨plan2300,[],none,⟨6,3,0⟩⟩]

def t4_742jobs : List Job := t4_742jobs0




def t4_743root : Job := ⟨plan2459,[],none,⟨6,6,0⟩⟩
def t4_743jobs0 : List Job := [⟨plan2459,[],none,⟨6,6,0⟩⟩]

def t4_743jobs : List Job := t4_743jobs0




def t4_744root : Job := ⟨plan2460,[],none,⟨6,6,0⟩⟩
def t4_744jobs0 : List Job := [⟨plan2460,[],none,⟨6,6,0⟩⟩]

def t4_744jobs : List Job := t4_744jobs0




def t4_745root : Job := ⟨plan2461,[],none,⟨6,6,0⟩⟩
def t4_745jobs0 : List Job := [⟨plan2461,[],none,⟨6,6,0⟩⟩]

def t4_745jobs : List Job := t4_745jobs0




def t4_746root : Job := ⟨plan2462,[],none,⟨6,6,0⟩⟩
def t4_746jobs0 : List Job := [⟨plan2462,[],none,⟨6,6,0⟩⟩]

def t4_746jobs : List Job := t4_746jobs0




def t4_747root : Job := ⟨plan2463,[],none,⟨6,6,0⟩⟩
def t4_747jobs0 : List Job := [⟨plan2463,[],none,⟨6,6,0⟩⟩]

def t4_747jobs : List Job := t4_747jobs0




def t4_748root : Job := ⟨plan2464,[],none,⟨6,6,0⟩⟩
def t4_748jobs0 : List Job := [⟨plan2464,[],none,⟨6,6,0⟩⟩]

def t4_748jobs : List Job := t4_748jobs0




def t4_749root : Job := ⟨plan2465,[],none,⟨6,6,0⟩⟩
def t4_749jobs0 : List Job := [⟨plan2465,[],none,⟨6,6,0⟩⟩]

def t4_749jobs : List Job := t4_749jobs0




def t4_750root : Job := ⟨plan2466,[],none,⟨6,6,0⟩⟩
def t4_750jobs0 : List Job := [⟨plan2466,[],none,⟨6,6,0⟩⟩]

def t4_750jobs : List Job := t4_750jobs0




def t4_751root : Job := ⟨plan2467,[],none,⟨6,6,0⟩⟩
def t4_751jobs0 : List Job := [⟨plan2467,[],none,⟨6,6,0⟩⟩]

def t4_751jobs : List Job := t4_751jobs0




def t4_752root : Job := ⟨plan2301,[],none,⟨6,3,0⟩⟩
def t4_752jobs0 : List Job := [⟨plan2301,[],none,⟨6,3,0⟩⟩]

def t4_752jobs : List Job := t4_752jobs0




def t4_753root : Job := ⟨plan2468,[],none,⟨6,6,0⟩⟩
def t4_753jobs0 : List Job := [⟨plan2468,[],none,⟨6,6,0⟩⟩]

def t4_753jobs : List Job := t4_753jobs0




def t4_754root : Job := ⟨plan2469,[],none,⟨6,6,0⟩⟩
def t4_754jobs0 : List Job := [⟨plan2469,[],none,⟨6,6,0⟩⟩]

def t4_754jobs : List Job := t4_754jobs0




def t4_755root : Job := ⟨plan2470,[],none,⟨6,6,0⟩⟩
def t4_755jobs0 : List Job := [⟨plan2470,[],none,⟨6,6,0⟩⟩]

def t4_755jobs : List Job := t4_755jobs0




def t4_756root : Job := ⟨plan2302,[],none,⟨6,3,0⟩⟩
def t4_756jobs0 : List Job := [⟨plan2302,[],none,⟨6,3,0⟩⟩]

def t4_756jobs : List Job := t4_756jobs0




def t4_757root : Job := ⟨plan2471,[],none,⟨6,6,0⟩⟩
def t4_757jobs0 : List Job := [⟨plan2471,[],none,⟨6,6,0⟩⟩]

def t4_757jobs : List Job := t4_757jobs0




def t4_758root : Job := ⟨plan2472,[],none,⟨6,6,0⟩⟩
def t4_758jobs0 : List Job := [⟨plan2472,[],none,⟨6,6,0⟩⟩]

def t4_758jobs : List Job := t4_758jobs0




def t4_759root : Job := ⟨plan2473,[],none,⟨6,6,0⟩⟩
def t4_759jobs0 : List Job := [⟨plan2473,[],none,⟨6,6,0⟩⟩]

def t4_759jobs : List Job := t4_759jobs0




def t4_760root : Job := ⟨plan2474,[],none,⟨6,6,0⟩⟩
def t4_760jobs0 : List Job := [⟨plan2474,[],none,⟨6,6,0⟩⟩]

def t4_760jobs : List Job := t4_760jobs0




def t4_761root : Job := ⟨plan2475,[],none,⟨6,6,0⟩⟩
def t4_761jobs0 : List Job := [⟨plan2475,[],none,⟨6,6,0⟩⟩]

def t4_761jobs : List Job := t4_761jobs0




def t4_762root : Job := ⟨plan2476,[],none,⟨6,6,0⟩⟩
def t4_762jobs0 : List Job := [⟨plan2476,[],none,⟨6,6,0⟩⟩]

def t4_762jobs : List Job := t4_762jobs0




def t4_763root : Job := ⟨plan2015,[],none,⟨6,1,0⟩⟩
def t4_763jobs0 : List Job := [⟨plan2015,[],none,⟨6,1,0⟩⟩]

def t4_763jobs : List Job := t4_763jobs0




def t4_764root : Job := ⟨plan2303,[],none,⟨6,3,0⟩⟩
def t4_764jobs0 : List Job := [⟨plan2303,[],none,⟨6,3,0⟩⟩]

def t4_764jobs : List Job := t4_764jobs0




def t4_765root : Job := ⟨plan2304,[],none,⟨6,3,0⟩⟩
def t4_765jobs0 : List Job := [⟨plan2304,[],none,⟨6,3,0⟩⟩]

def t4_765jobs : List Job := t4_765jobs0




def t4_766root : Job := ⟨plan2305,[],none,⟨6,3,0⟩⟩
def t4_766jobs0 : List Job := [⟨plan2305,[],none,⟨6,3,0⟩⟩]

def t4_766jobs : List Job := t4_766jobs0




def t4_767root : Job := ⟨plan2477,[],none,⟨6,6,0⟩⟩
def t4_767jobs0 : List Job := [⟨plan2477,[],none,⟨6,6,0⟩⟩]

def t4_767jobs : List Job := t4_767jobs0




def t4_768root : Job := ⟨plan2478,[],none,⟨6,6,0⟩⟩
def t4_768jobs0 : List Job := [⟨plan2478,[],none,⟨6,6,0⟩⟩]

def t4_768jobs : List Job := t4_768jobs0




def t4_769root : Job := ⟨plan2479,[],none,⟨6,6,0⟩⟩
def t4_769jobs0 : List Job := [⟨plan2479,[],none,⟨6,6,0⟩⟩]

def t4_769jobs : List Job := t4_769jobs0




def t4_770root : Job := ⟨plan2480,[],none,⟨6,6,0⟩⟩
def t4_770jobs0 : List Job := [⟨plan2480,[],none,⟨6,6,0⟩⟩]

def t4_770jobs : List Job := t4_770jobs0




def t4_771root : Job := ⟨plan2306,[],none,⟨6,3,0⟩⟩
def t4_771jobs0 : List Job := [⟨plan2306,[],none,⟨6,3,0⟩⟩]

def t4_771jobs : List Job := t4_771jobs0




def t4_772root : Job := ⟨plan2481,[],none,⟨6,6,0⟩⟩
def t4_772jobs0 : List Job := [⟨plan2481,[],none,⟨6,6,0⟩⟩]

def t4_772jobs : List Job := t4_772jobs0




def t4_773root : Job := ⟨plan2482,[],none,⟨6,6,0⟩⟩
def t4_773jobs0 : List Job := [⟨plan2482,[],none,⟨6,6,0⟩⟩]

def t4_773jobs : List Job := t4_773jobs0




def t4_774root : Job := ⟨plan2483,[],none,⟨6,6,0⟩⟩
def t4_774jobs0 : List Job := [⟨plan2483,[],none,⟨6,6,0⟩⟩]

def t4_774jobs : List Job := t4_774jobs0




def t4_775root : Job := ⟨plan2484,[],none,⟨6,6,0⟩⟩
def t4_775jobs0 : List Job := [⟨plan2484,[],none,⟨6,6,0⟩⟩]

def t4_775jobs : List Job := t4_775jobs0




def t4_776root : Job := ⟨plan2485,[],none,⟨6,6,0⟩⟩
def t4_776jobs0 : List Job := [⟨plan2485,[],none,⟨6,6,0⟩⟩]

def t4_776jobs : List Job := t4_776jobs0




def t4_777root : Job := ⟨plan2486,[],none,⟨6,6,0⟩⟩
def t4_777jobs0 : List Job := [⟨plan2486,[],none,⟨6,6,0⟩⟩]

def t4_777jobs : List Job := t4_777jobs0




def t4_778root : Job := ⟨plan2487,[],none,⟨6,6,0⟩⟩
def t4_778jobs0 : List Job := [⟨plan2487,[],none,⟨6,6,0⟩⟩]

def t4_778jobs : List Job := t4_778jobs0




def t4_779root : Job := ⟨plan2488,[],none,⟨6,6,0⟩⟩
def t4_779jobs0 : List Job := [⟨plan2488,[],none,⟨6,6,0⟩⟩]

def t4_779jobs : List Job := t4_779jobs0




def t4_780root : Job := ⟨plan2489,[],none,⟨6,6,0⟩⟩
def t4_780jobs0 : List Job := [⟨plan2489,[],none,⟨6,6,0⟩⟩]

def t4_780jobs : List Job := t4_780jobs0




def t4_781root : Job := ⟨plan1803,[],none,⟨6,0,0⟩⟩
def t4_781jobs0 : List Job := [⟨plan1803,[],none,⟨6,0,0⟩⟩]

def t4_781jobs : List Job := t4_781jobs0




def t4_782root : Job := ⟨plan2016,[],none,⟨6,1,0⟩⟩
def t4_782jobs0 : List Job := [⟨plan2016,[],none,⟨6,1,0⟩⟩]

def t4_782jobs : List Job := t4_782jobs0




def t4_783root : Job := ⟨plan2017,[],none,⟨6,1,0⟩⟩
def t4_783jobs0 : List Job := [⟨plan2017,[],none,⟨6,1,0⟩⟩]

def t4_783jobs : List Job := t4_783jobs0




def t4_784root : Job := ⟨plan2018,[],none,⟨6,1,0⟩⟩
def t4_784jobs0 : List Job := [⟨plan2018,[],none,⟨6,1,0⟩⟩]

def t4_784jobs : List Job := t4_784jobs0




def t4_785root : Job := ⟨plan2307,[],none,⟨6,3,0⟩⟩
def t4_785jobs0 : List Job := [⟨plan2307,[],none,⟨6,3,0⟩⟩]

def t4_785jobs : List Job := t4_785jobs0




def t4_786root : Job := ⟨plan2308,[],none,⟨6,3,0⟩⟩
def t4_786jobs0 : List Job := [⟨plan2308,[],none,⟨6,3,0⟩⟩]

def t4_786jobs : List Job := t4_786jobs0




def t4_787root : Job := ⟨plan2309,[],none,⟨6,3,0⟩⟩
def t4_787jobs0 : List Job := [⟨plan2309,[],none,⟨6,3,0⟩⟩]

def t4_787jobs : List Job := t4_787jobs0




def t4_788root : Job := ⟨plan2310,[],none,⟨6,3,0⟩⟩
def t4_788jobs0 : List Job := [⟨plan2310,[],none,⟨6,3,0⟩⟩]

def t4_788jobs : List Job := t4_788jobs0




def t4_789root : Job := ⟨plan2311,[],none,⟨6,3,0⟩⟩
def t4_789jobs0 : List Job := [⟨plan2311,[],none,⟨6,3,0⟩⟩]

def t4_789jobs : List Job := t4_789jobs0




def t4_790root : Job := ⟨plan2312,[],none,⟨6,3,0⟩⟩
def t4_790jobs0 : List Job := [⟨plan2312,[],none,⟨6,3,0⟩⟩]

def t4_790jobs : List Job := t4_790jobs0




def t4_791root : Job := ⟨plan2490,[],none,⟨6,6,0⟩⟩
def t4_791jobs0 : List Job := [⟨plan2490,[],none,⟨6,6,0⟩⟩]

def t4_791jobs : List Job := t4_791jobs0




def t4_792root : Job := ⟨plan2491,[],none,⟨6,6,0⟩⟩
def t4_792jobs0 : List Job := [⟨plan2491,[],none,⟨6,6,0⟩⟩]

def t4_792jobs : List Job := t4_792jobs0




def t4_793root : Job := ⟨plan2492,[],none,⟨6,6,0⟩⟩
def t4_793jobs0 : List Job := [⟨plan2492,[],none,⟨6,6,0⟩⟩]

def t4_793jobs : List Job := t4_793jobs0




def t4_794root : Job := ⟨plan2493,[],none,⟨6,6,0⟩⟩
def t4_794jobs0 : List Job := [⟨plan2493,[],none,⟨6,6,0⟩⟩]

def t4_794jobs : List Job := t4_794jobs0




def t4_795root : Job := ⟨plan2494,[],none,⟨6,6,0⟩⟩
def t4_795jobs0 : List Job := [⟨plan2494,[],none,⟨6,6,0⟩⟩]

def t4_795jobs : List Job := t4_795jobs0




def t4_796root : Job := ⟨plan2495,[],none,⟨6,6,0⟩⟩
def t4_796jobs0 : List Job := [⟨plan2495,[],none,⟨6,6,0⟩⟩]

def t4_796jobs : List Job := t4_796jobs0




def t4_797root : Job := ⟨plan2496,[],none,⟨6,6,0⟩⟩
def t4_797jobs0 : List Job := [⟨plan2496,[],none,⟨6,6,0⟩⟩]

def t4_797jobs : List Job := t4_797jobs0




def t4_798root : Job := ⟨plan2019,[],none,⟨6,1,0⟩⟩
def t4_798jobs0 : List Job := [⟨plan2019,[],none,⟨6,1,0⟩⟩]

def t4_798jobs : List Job := t4_798jobs0




def t4_799root : Job := ⟨plan2313,[],none,⟨6,3,0⟩⟩
def t4_799jobs0 : List Job := [⟨plan2313,[],none,⟨6,3,0⟩⟩]

def t4_799jobs : List Job := t4_799jobs0




def t4_800root : Job := ⟨plan2314,[],none,⟨6,3,0⟩⟩
def t4_800jobs0 : List Job := [⟨plan2314,[],none,⟨6,3,0⟩⟩]

def t4_800jobs : List Job := t4_800jobs0




def t4_801root : Job := ⟨plan2315,[],none,⟨6,3,0⟩⟩
def t4_801jobs0 : List Job := [⟨plan2315,[],none,⟨6,3,0⟩⟩]

def t4_801jobs : List Job := t4_801jobs0




def t4_802root : Job := ⟨plan2497,[],none,⟨6,6,0⟩⟩
def t4_802jobs0 : List Job := [⟨plan2497,[],none,⟨6,6,0⟩⟩]

def t4_802jobs : List Job := t4_802jobs0




def t4_803root : Job := ⟨plan2498,[],none,⟨6,6,0⟩⟩
def t4_803jobs0 : List Job := [⟨plan2498,[],none,⟨6,6,0⟩⟩]

def t4_803jobs : List Job := t4_803jobs0




def t4_804root : Job := ⟨plan2499,[],none,⟨6,6,0⟩⟩
def t4_804jobs0 : List Job := [⟨plan2499,[],none,⟨6,6,0⟩⟩]

def t4_804jobs : List Job := t4_804jobs0




def t4_805root : Job := ⟨plan2500,[],none,⟨6,6,0⟩⟩
def t4_805jobs0 : List Job := [⟨plan2500,[],none,⟨6,6,0⟩⟩]

def t4_805jobs : List Job := t4_805jobs0




def t4_806root : Job := ⟨plan2316,[],none,⟨6,3,0⟩⟩
def t4_806jobs0 : List Job := [⟨plan2316,[],none,⟨6,3,0⟩⟩]

def t4_806jobs : List Job := t4_806jobs0




def t4_807root : Job := ⟨plan2501,[],none,⟨6,6,0⟩⟩
def t4_807jobs0 : List Job := [⟨plan2501,[],none,⟨6,6,0⟩⟩]

def t4_807jobs : List Job := t4_807jobs0




def t4_808root : Job := ⟨plan2502,[],none,⟨6,6,0⟩⟩
def t4_808jobs0 : List Job := [⟨plan2502,[],none,⟨6,6,0⟩⟩]

def t4_808jobs : List Job := t4_808jobs0




def t4_809root : Job := ⟨plan2503,[],none,⟨6,6,0⟩⟩
def t4_809jobs0 : List Job := [⟨plan2503,[],none,⟨6,6,0⟩⟩]

def t4_809jobs : List Job := t4_809jobs0




def t4_810root : Job := ⟨plan2504,[],none,⟨6,6,0⟩⟩
def t4_810jobs0 : List Job := [⟨plan2504,[],none,⟨6,6,0⟩⟩]

def t4_810jobs : List Job := t4_810jobs0




def t4_811root : Job := ⟨plan2505,[],none,⟨6,6,0⟩⟩
def t4_811jobs0 : List Job := [⟨plan2505,[],none,⟨6,6,0⟩⟩]

def t4_811jobs : List Job := t4_811jobs0




def t4_812root : Job := ⟨plan2506,[],none,⟨6,6,0⟩⟩
def t4_812jobs0 : List Job := [⟨plan2506,[],none,⟨6,6,0⟩⟩]

def t4_812jobs : List Job := t4_812jobs0




def t4_813root : Job := ⟨plan2507,[],none,⟨6,6,0⟩⟩
def t4_813jobs0 : List Job := [⟨plan2507,[],none,⟨6,6,0⟩⟩]

def t4_813jobs : List Job := t4_813jobs0




def t4_814root : Job := ⟨plan2508,[],none,⟨6,6,0⟩⟩
def t4_814jobs0 : List Job := [⟨plan2508,[],none,⟨6,6,0⟩⟩]

def t4_814jobs : List Job := t4_814jobs0




def t4_815root : Job := ⟨plan2509,[],none,⟨6,6,0⟩⟩
def t4_815jobs0 : List Job := [⟨plan2509,[],none,⟨6,6,0⟩⟩]

def t4_815jobs : List Job := t4_815jobs0




def t4_816root : Job := ⟨plan2510,[],none,⟨6,6,0⟩⟩
def t4_816jobs0 : List Job := [⟨plan2510,[],none,⟨6,6,0⟩⟩]

def t4_816jobs : List Job := t4_816jobs0




def t4_817root : Job := ⟨plan2511,[],none,⟨6,6,0⟩⟩
def t4_817jobs0 : List Job := [⟨plan2511,[],none,⟨6,6,0⟩⟩]

def t4_817jobs : List Job := t4_817jobs0




def t4_818root : Job := ⟨plan2512,[],none,⟨6,6,0⟩⟩
def t4_818jobs0 : List Job := [⟨plan2512,[],none,⟨6,6,0⟩⟩]

def t4_818jobs : List Job := t4_818jobs0




def t4_819root : Job := ⟨plan2513,[],none,⟨6,6,0⟩⟩
def t4_819jobs0 : List Job := [⟨plan2513,[],none,⟨6,6,0⟩⟩]

def t4_819jobs : List Job := t4_819jobs0




def t5_0root : Job := ⟨plan3674,[],none,⟨10,0,0⟩⟩
def t5_0jobs0 : List Job := [⟨plan3674,[],none,⟨10,0,0⟩⟩]

def t5_0jobs : List Job := t5_0jobs0




def t5_1root : Job := ⟨plan3759,[],none,⟨10,1,0⟩⟩
def t5_1jobs0 : List Job := [⟨plan3759,[],none,⟨10,1,0⟩⟩]

def t5_1jobs : List Job := t5_1jobs0




def t5_2root : Job := ⟨plan3760,[],none,⟨10,1,0⟩⟩
def t5_2jobs0 : List Job := [⟨plan3760,[],none,⟨10,1,0⟩⟩]

def t5_2jobs : List Job := t5_2jobs0




def t5_3root : Job := ⟨plan3761,[],none,⟨10,1,0⟩⟩
def t5_3jobs0 : List Job := [⟨plan3761,[],none,⟨10,1,0⟩⟩]

def t5_3jobs : List Job := t5_3jobs0




def t5_4root : Job := ⟨plan3658,[],none,⟨10,0,0⟩⟩
def t5_4jobs0 : List Job := [⟨plan3658,[],none,⟨10,0,0⟩⟩]

def t5_4jobs : List Job := t5_4jobs0




def t5_5root : Job := ⟨plan3675,[],none,⟨10,0,0⟩⟩
def t5_5jobs0 : List Job := [⟨plan3675,[],none,⟨10,0,0⟩⟩]

def t5_5jobs : List Job := t5_5jobs0




def t5_6root : Job := ⟨plan3676,[],none,⟨10,0,0⟩⟩
def t5_6jobs0 : List Job := [⟨plan3676,[],none,⟨10,0,0⟩⟩]

def t5_6jobs : List Job := t5_6jobs0




def t5_7root : Job := ⟨plan3677,[],none,⟨10,0,0⟩⟩
def t5_7jobs0 : List Job := [⟨plan3677,[],none,⟨10,0,0⟩⟩]

def t5_7jobs : List Job := t5_7jobs0




def t5_8root : Job := ⟨plan3762,[],none,⟨10,1,0⟩⟩
def t5_8jobs0 : List Job := [⟨plan3762,[],none,⟨10,1,0⟩⟩]

def t5_8jobs : List Job := t5_8jobs0




def t5_9root : Job := ⟨plan3763,[],none,⟨10,1,0⟩⟩
def t5_9jobs0 : List Job := [⟨plan3763,[],none,⟨10,1,0⟩⟩]

def t5_9jobs : List Job := t5_9jobs0




def t5_10root : Job := ⟨plan3764,[],none,⟨10,1,0⟩⟩
def t5_10jobs0 : List Job := [⟨plan3764,[],none,⟨10,1,0⟩⟩]

def t5_10jobs : List Job := t5_10jobs0




def t5_11root : Job := ⟨plan3765,[],none,⟨10,1,0⟩⟩
def t5_11jobs0 : List Job := [⟨plan3765,[],none,⟨10,1,0⟩⟩]

def t5_11jobs : List Job := t5_11jobs0




def t5_12root : Job := ⟨plan3766,[],none,⟨10,1,0⟩⟩
def t5_12jobs0 : List Job := [⟨plan3766,[],none,⟨10,1,0⟩⟩]

def t5_12jobs : List Job := t5_12jobs0




def t5_13root : Job := ⟨plan3767,[],none,⟨10,1,0⟩⟩
def t5_13jobs0 : List Job := [⟨plan3767,[],none,⟨10,1,0⟩⟩]

def t5_13jobs : List Job := t5_13jobs0




def t5_14root : Job := ⟨plan3768,[],none,⟨10,1,0⟩⟩
def t5_14jobs0 : List Job := [⟨plan3768,[],none,⟨10,1,0⟩⟩]

def t5_14jobs : List Job := t5_14jobs0




def t5_15root : Job := ⟨plan4000,[],none,⟨10,3,0⟩⟩
def t5_15jobs0 : List Job := [⟨plan4000,[],none,⟨10,3,0⟩⟩]

def t5_15jobs : List Job := t5_15jobs0




def t5_16root : Job := ⟨plan4001,[],none,⟨10,3,0⟩⟩
def t5_16jobs0 : List Job := [⟨plan4001,[],none,⟨10,3,0⟩⟩]

def t5_16jobs : List Job := t5_16jobs0




def t5_17root : Job := ⟨plan4002,[],none,⟨10,3,0⟩⟩
def t5_17jobs0 : List Job := [⟨plan4002,[],none,⟨10,3,0⟩⟩]

def t5_17jobs : List Job := t5_17jobs0




def t5_18root : Job := ⟨plan4003,[],none,⟨10,3,0⟩⟩
def t5_18jobs0 : List Job := [⟨plan4003,[],none,⟨10,3,0⟩⟩]

def t5_18jobs : List Job := t5_18jobs0




def t5_19root : Job := ⟨plan4004,[],none,⟨10,3,0⟩⟩
def t5_19jobs0 : List Job := [⟨plan4004,[],none,⟨10,3,0⟩⟩]

def t5_19jobs : List Job := t5_19jobs0




def t5_20root : Job := ⟨plan4005,[],none,⟨10,3,0⟩⟩
def t5_20jobs0 : List Job := [⟨plan4005,[],none,⟨10,3,0⟩⟩]

def t5_20jobs : List Job := t5_20jobs0




def t5_21root : Job := ⟨plan4006,[],none,⟨10,3,0⟩⟩
def t5_21jobs0 : List Job := [⟨plan4006,[],none,⟨10,3,0⟩⟩]

def t5_21jobs : List Job := t5_21jobs0




def t5_22root : Job := ⟨plan4007,[],none,⟨10,3,0⟩⟩
def t5_22jobs0 : List Job := [⟨plan4007,[],none,⟨10,3,0⟩⟩]

def t5_22jobs : List Job := t5_22jobs0




def t5_23root : Job := ⟨plan4008,[],none,⟨10,3,0⟩⟩
def t5_23jobs0 : List Job := [⟨plan4008,[],none,⟨10,3,0⟩⟩]

def t5_23jobs : List Job := t5_23jobs0




def t5_24root : Job := ⟨plan4009,[],none,⟨10,3,0⟩⟩
def t5_24jobs0 : List Job := [⟨plan4009,[],none,⟨10,3,0⟩⟩]

def t5_24jobs : List Job := t5_24jobs0




def t5_25root : Job := ⟨plan3769,[],none,⟨10,1,0⟩⟩
def t5_25jobs0 : List Job := [⟨plan3769,[],none,⟨10,1,0⟩⟩]

def t5_25jobs : List Job := t5_25jobs0




def t5_26root : Job := ⟨plan4010,[],none,⟨10,3,0⟩⟩
def t5_26jobs0 : List Job := [⟨plan4010,[],none,⟨10,3,0⟩⟩]

def t5_26jobs : List Job := t5_26jobs0




def t5_27root : Job := ⟨plan4011,[],none,⟨10,3,0⟩⟩
def t5_27jobs0 : List Job := [⟨plan4011,[],none,⟨10,3,0⟩⟩]

def t5_27jobs : List Job := t5_27jobs0




def t5_28root : Job := ⟨plan4012,[],none,⟨10,3,0⟩⟩
def t5_28jobs0 : List Job := [⟨plan4012,[],none,⟨10,3,0⟩⟩]

def t5_28jobs : List Job := t5_28jobs0




def t5_29root : Job := ⟨plan4013,[],none,⟨10,3,0⟩⟩
def t5_29jobs0 : List Job := [⟨plan4013,[],none,⟨10,3,0⟩⟩]

def t5_29jobs : List Job := t5_29jobs0




def t5_30root : Job := ⟨plan4014,[],none,⟨10,3,0⟩⟩
def t5_30jobs0 : List Job := [⟨plan4014,[],none,⟨10,3,0⟩⟩]

def t5_30jobs : List Job := t5_30jobs0




def t5_31root : Job := ⟨plan4015,[],none,⟨10,3,0⟩⟩
def t5_31jobs0 : List Job := [⟨plan4015,[],none,⟨10,3,0⟩⟩]

def t5_31jobs : List Job := t5_31jobs0




def t5_32root : Job := ⟨plan3678,[],none,⟨10,0,0⟩⟩
def t5_32jobs0 : List Job := [⟨plan3678,[],none,⟨10,0,0⟩⟩]

def t5_32jobs : List Job := t5_32jobs0




def t5_33root : Job := ⟨plan3659,[],none,⟨10,0,0⟩⟩
def t5_33jobs0 : List Job := [⟨plan3659,[],none,⟨10,0,0⟩⟩]

def t5_33jobs : List Job := t5_33jobs0




def t5_34root : Job := ⟨plan3679,[],none,⟨10,0,0⟩⟩
def t5_34jobs0 : List Job := [⟨plan3679,[],none,⟨10,0,0⟩⟩]

def t5_34jobs : List Job := t5_34jobs0




def t5_35root : Job := ⟨plan3680,[],none,⟨10,0,0⟩⟩
def t5_35jobs0 : List Job := [⟨plan3680,[],none,⟨10,0,0⟩⟩]

def t5_35jobs : List Job := t5_35jobs0




def t5_36root : Job := ⟨plan3681,[],none,⟨10,0,0⟩⟩
def t5_36jobs0 : List Job := [⟨plan3681,[],none,⟨10,0,0⟩⟩]

def t5_36jobs : List Job := t5_36jobs0




def t5_37root : Job := ⟨plan3770,[],none,⟨10,1,0⟩⟩
def t5_37jobs0 : List Job := [⟨plan3770,[],none,⟨10,1,0⟩⟩]

def t5_37jobs : List Job := t5_37jobs0




def t5_38root : Job := ⟨plan3771,[],none,⟨10,1,0⟩⟩
def t5_38jobs0 : List Job := [⟨plan3771,[],none,⟨10,1,0⟩⟩]

def t5_38jobs : List Job := t5_38jobs0




def t5_39root : Job := ⟨plan3772,[],none,⟨10,1,0⟩⟩
def t5_39jobs0 : List Job := [⟨plan3772,[],none,⟨10,1,0⟩⟩]

def t5_39jobs : List Job := t5_39jobs0




def t5_40root : Job := ⟨plan3773,[],none,⟨10,1,0⟩⟩
def t5_40jobs0 : List Job := [⟨plan3773,[],none,⟨10,1,0⟩⟩]

def t5_40jobs : List Job := t5_40jobs0




def t5_41root : Job := ⟨plan3774,[],none,⟨10,1,0⟩⟩
def t5_41jobs0 : List Job := [⟨plan3774,[],none,⟨10,1,0⟩⟩]

def t5_41jobs : List Job := t5_41jobs0




def t5_42root : Job := ⟨plan3775,[],none,⟨10,1,0⟩⟩
def t5_42jobs0 : List Job := [⟨plan3775,[],none,⟨10,1,0⟩⟩]

def t5_42jobs : List Job := t5_42jobs0




def t5_43root : Job := ⟨plan3776,[],none,⟨10,1,0⟩⟩
def t5_43jobs0 : List Job := [⟨plan3776,[],none,⟨10,1,0⟩⟩]

def t5_43jobs : List Job := t5_43jobs0




def t5_44root : Job := ⟨plan3777,[],none,⟨10,1,0⟩⟩
def t5_44jobs0 : List Job := [⟨plan3777,[],none,⟨10,1,0⟩⟩]

def t5_44jobs : List Job := t5_44jobs0




def t5_45root : Job := ⟨plan3660,[],none,⟨10,0,0⟩⟩
def t5_45jobs0 : List Job := [⟨plan3660,[],none,⟨10,0,0⟩⟩]

def t5_45jobs : List Job := t5_45jobs0




def t5_46root : Job := ⟨plan3682,[],none,⟨10,0,0⟩⟩
def t5_46jobs0 : List Job := [⟨plan3682,[],none,⟨10,0,0⟩⟩]

def t5_46jobs : List Job := t5_46jobs0




def t5_47root : Job := ⟨plan3683,[],none,⟨10,0,0⟩⟩
def t5_47jobs0 : List Job := [⟨plan3683,[],none,⟨10,0,0⟩⟩]

def t5_47jobs : List Job := t5_47jobs0




def t5_48root : Job := ⟨plan3684,[],none,⟨10,0,0⟩⟩
def t5_48jobs0 : List Job := [⟨plan3684,[],none,⟨10,0,0⟩⟩]

def t5_48jobs : List Job := t5_48jobs0




def t5_49root : Job := ⟨plan3778,[],none,⟨10,1,0⟩⟩
def t5_49jobs0 : List Job := [⟨plan3778,[],none,⟨10,1,0⟩⟩]

def t5_49jobs : List Job := t5_49jobs0




def t5_50root : Job := ⟨plan3779,[],none,⟨10,1,0⟩⟩
def t5_50jobs0 : List Job := [⟨plan3779,[],none,⟨10,1,0⟩⟩]

def t5_50jobs : List Job := t5_50jobs0




def t5_51root : Job := ⟨plan3780,[],none,⟨10,1,0⟩⟩
def t5_51jobs0 : List Job := [⟨plan3780,[],none,⟨10,1,0⟩⟩]

def t5_51jobs : List Job := t5_51jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


