-- Prove2me | Definitions.Def_Sensitivity213981Formal_Label5591Data
-- name    : Sensitivity213981Formal_Label5591Data
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:13:18.646199+00:00
-- url     : https://prove2.me/theorems/a2e77b2e-549e-41d1-bca7-423dc406d4b9
-- title:
--   Label5591 Data — sensitivity certificate definitions
-- statement:
--   The definitions for Label5591 Data in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity5591Labeling.Caps.ordinaryProduct`, `Sensitivity5591Labeling.Caps.ordinaryLoad`, `Sensitivity5591Labeling.Caps.markedA`, `Sensitivity5591Labeling.Caps.marked`, `Sensitivity5591Labeling.Caps.markedW`, `Sensitivity5591Labeling.Caps.markedHead`, `Sensitivity5591Labeling.Caps.markedPref`, `Sensitivity5591Labeling.Caps.markedLoad`, `Sensitivity5591Labeling.Caps.sourceLoad`, `Sensitivity5591Labeling.Caps.dominatorLoad`, `Sensitivity5591Labeling.Caps.perfectLoad`, `Sensitivity5591Labeling.Caps.ordinaryCeilings`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Label5591Data.lean, lines 1–49.

import Definitions.Def_Sensitivity213981Formal_LabelLoads
import Definitions.Def_Sensitivity213981Formal_MarkedArcLoad
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace Sensitivity213981Formal
section
/- Exact 5591 labeling parameters; all load ceilings are independently kernel checked. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
set_option exponentiation.threshold 1000000
namespace Sensitivity5591Labeling.Caps
open Sensitivity10007Labeling ZL ZL.RowCounting
open scoped Classical BigOperators
abbrev Parameters := CompactLabeling10007.MarkedParameters

def N:ℕ:=5591
def degree:ℕ:=2795
def common:ℕ:=1397
def lam:ℚ:=387/386
def scale:ℕ:=1000000000000000000
def ordinaryCutoffs:List ℕ:=[21,29,35,41,47,52,57,63,68]
def markedCutoffs:List ℕ:=[27,33,39,45,25,31,22,26,29,27,31,25]
def ordinaryA(q:Fin 9):ℕ:=ordinaryCutoffs.getD q.val 0
def ordinaryLo(q:Fin 9):ℕ:=(ordinaryA q-1)/2
def ordinaryRem(q:Fin 9):ℕ:=(ordinaryA q).choose 2-ordinaryA q*ordinaryLo q
def ordinaryLowValue(q:Fin 9):ℕ:=rowPatterns q.val (ordinaryLo q)
def ordinaryHighValue(q:Fin 9):ℕ:=rowPatterns q.val (ordinaryLo q+1)
def ordinaryProduct(q:Fin 9):ℕ:=ordinaryLowValue q^(ordinaryA q-ordinaryRem q)*ordinaryHighValue q^ordinaryRem q
def ordinaryLoad(q:Fin 9):ℚ:=
  (N.choose (ordinaryA q-2):ℚ)*((2:ℚ)^ordinaryA q*ordinaryProduct q/(2:ℚ)^((ordinaryA q).choose 2))*lam^((ordinaryA q).choose 2)/2

def markedA(i:Fin 12):ℕ:=markedCutoffs.getD i.val 0
def marked(i:Fin 12):Parameters:={CompactLabeling10007.marked i with a:=markedA i}
def markedW(p:Parameters):ℚ:=p.alpha*((N:ℚ)-p.m)+p.beta*((p.m:ℚ)*degree-p.m.choose 2)+p.gamma*(p.m.choose 2:ℚ)*common
def markedHead(p:Parameters):ℕ:=if p.zero then 1 else if p.m=2 then
  ThreeBoundRefinedMarked.headFactor p.q p.a else (rowPatterns (p.q+1) p.a)^p.m
def markedPref(p:Parameters):ℚ:=(2:ℚ)^p.a*markedHead p*p.u^(p.a.choose 2)/(2:ℚ)^(p.a.choose 2+p.m*p.a)
def markedLoad(i:Fin 12):ℚ:=let p:=marked i
  markedPref p*((p.a.choose 2+p.m*p.a:ℕ)*((N.choose p.m:ℚ)*(markedW p)^p.a/p.a.factorial)/N.choose 2)*lam^(p.a.choose 2+p.m*p.a)/2

def sourceLoad:ℚ:=((degree.choose 18+common*degree.choose 17:ℕ):ℚ)*((2:ℚ)^19/(2:ℚ)^190)*lam^190/2
def dominatorLoad:ℚ:=((common.choose 2*common.choose 15+degree*common.choose 16:ℕ):ℚ)*((2:ℚ)^17/(2:ℚ)^170)*lam^170/2
def perfectLoad:ℚ:=((150:ℕ)*((N.choose 3:ℚ)*(800:ℕ).choose 15)/N.choose 2)*((2:ℚ)^15/(2:ℚ)^150)*lam^150/2
def ordinaryCeilings:List ℕ:=[1393727001797799,778824846178,10998912427734,1818393001178,7859658787,1491332240814,79477139050551,339322829,923979273]
def markedCeilings:List ℕ:=[28718126423472,69735483881849,14274853375569,105509624118,28716248435987,184761509608921,6628827732007,2928103952981,78526917887933,11933603013169,377731609223778,6309350823865]
def ordinaryCeiling(q:Fin 9):ℚ:=(ordinaryCeilings.getD q.val 0:ℕ)/scale
def markedCeiling(i:Fin 12):ℚ:=(markedCeilings.getD i.val 0:ℕ)/scale
def sourceCeiling:ℚ:=43983509846343/scale
def dominatorCeiling:ℚ:=8835163200583/scale
def perfectCeiling:ℚ:=111500102151839/scale
end Sensitivity5591Labeling.Caps

end
end Sensitivity213981Formal


