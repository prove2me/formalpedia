-- Prove2me | Definitions.Def_Paley11987Support_012
-- name    : Paley11987Support_012
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T00:50:02.680806+00:00
-- url     : https://prove2.me/theorems/d8ed2887-f355-4097-953f-ed78e8e55a5f
-- title:
--   Exact arithmetic parameters for order 11987
-- statement:
--   Fixes the order $11987$, degree $5993$, common-neighbor parameter $2996$, activity and scale constants, ordinary cutoffs, marked parameter arrays, and the prescribed event-family ceilings.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module JointLabeling11987Arithmetic.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module JointLabeling11987Arithmetic, SHA256 c4ee99ab1d38c989595d3138ac5f2ebd9d90c91501fe3dc7a8636599ef958930

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
import Definitions.Def_Paley11987Support_000
import Definitions.Def_Paley11987Support_001
import Definitions.Def_Paley11987Support_002
import Definitions.Def_Paley11987Support_003
import Definitions.Def_Paley11987Support_004
import Definitions.Def_Paley11987Support_005
import Definitions.Def_Paley11987Support_006
import Definitions.Def_Paley11987Support_007
import Definitions.Def_Paley11987Support_008
import Definitions.Def_Paley11987Support_009
import Definitions.Def_Paley11987Support_010
import Definitions.Def_Paley11987Support_011

set_option autoImplicit false
set_option Elab.async false
section z16

section
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 32768
open scoped Classical BigOperators

namespace CompactLabeling11987
open ZL ZL.RowCounting

def N : ℕ := 11987
def degree : ℕ := 5993
def common : ℕ := 2996
def lam : ℚ := 190/189
def scale : ℕ := 1000000000000000000

def ordinaryCutoffs : List ℕ := [24,31,38,44,50,57,62,69,74]
def ordinaryA (q : Fin 9) : ℕ := ordinaryCutoffs.getD q.val 0
def ordinaryLo (q : Fin 9) : ℕ := (ordinaryA q-1)/2
def ordinaryRem (q : Fin 9) : ℕ := (ordinaryA q).choose 2 - ordinaryA q * ordinaryLo q
def ordinaryLowValue (q : Fin 9) : ℕ := rowPatterns q.val (ordinaryLo q)
def ordinaryHighValue (q : Fin 9) : ℕ := rowPatterns q.val (ordinaryLo q+1)
def ordinaryProduct (q : Fin 9) : ℕ :=
  ordinaryLowValue q ^ (ordinaryA q-ordinaryRem q) * ordinaryHighValue q ^ ordinaryRem q

def ordinaryLoad (q : Fin 9) : ℚ :=
  (N.choose (ordinaryA q-2) : ℚ) *
    ((2 : ℚ)^ordinaryA q * ordinaryProduct q / (2 : ℚ)^((ordinaryA q).choose 2)) *
    lam^((ordinaryA q).choose 2) / 2

def sourceLoad : ℚ :=
  ((degree.choose 20 + common * degree.choose 19 : ℕ) : ℚ) *
    ((2 : ℚ)^21 / (2 : ℚ)^(22).choose 2) * lam^((22).choose 2) / 2

def dominatorLoad : ℚ :=
  ((common.choose 2 * common.choose 16 + degree * common.choose 17 : ℕ) : ℚ) *
    ((2 : ℚ)^18 / (2 : ℚ)^189) * lam^189 / 2

structure MarkedParameters where
  q : ℕ
  a : ℕ
  m : ℕ
  zero : Bool
  u : ℚ
  cs : List ℚ
  alpha : ℚ
  beta : ℚ
  gamma : ℚ
  wm : ℚ
  ceiling : ℕ

def MarkedParameters.C (p : MarkedParameters) (t : ℕ) : ℚ := p.cs.getD t 0

def MarkedParameters.W (p : MarkedParameters) : ℚ :=
  p.alpha * ((N : ℚ)-p.m) + p.beta * ((p.m : ℚ)*degree-p.m.choose 2) +
    p.gamma * (p.m.choose 2 : ℚ) * common

def MarkedParameters.B (p : MarkedParameters) : ℕ := if p.zero then 0 else p.m*(p.q+1)

def MarkedParameters.load (p : MarkedParameters) : ℚ :=
  ((2 : ℚ)^p.a * headErrorFactor p.q p.a p.m p.B * p.u^(p.a.choose 2) /
    (2 : ℚ)^(p.a.choose 2+p.m*p.a)) *
    (((N.choose p.m : ℚ)*p.wm^2)*(p.W^(p.a-2)/(p.a-2).factorial) +
     ((N.choose (p.m-1) : ℚ)*p.wm)*(p.W^(p.a-1)/(p.a-1).factorial)) *
    lam^(p.a.choose 2+p.m*p.a) / 2

def marked0 : MarkedParameters := ⟨1,30,1,false,(1053/1000 : ℚ),[1,(15/2 : ℚ)],(15/2 : ℚ),(-11/2 : ℚ),0,(15/2 : ℚ),5568130982⟩
def marked1 : MarkedParameters := ⟨2,36,1,false,(138/125 : ℚ),[1,(821/200 : ℚ),(3646/125 : ℚ)],(3646/125 : ℚ),(-10479/500 : ℚ),0,(3646/125 : ℚ),98741212706⟩
def marked2 : MarkedParameters := ⟨3,42,1,false,(571/500 : ℚ),[1,(3159/1000 : ℚ),(16519/1000 : ℚ),(96643/1000 : ℚ)],(96643/1000 : ℚ),(-12721/200 : ℚ),0,(96643/1000 : ℚ),123581041847⟩
def marked3 : MarkedParameters := ⟨4,48,1,false,(293/250 : ℚ),[1,(1357/500 : ℚ),(11763/1000 : ℚ),(7108/125 : ℚ),(72237/250 : ℚ)],(72237/250 : ℚ),(-8761/50 : ℚ),0,(72237/250 : ℚ),5406513125⟩
def marked4 : MarkedParameters := ⟨1,28,2,false,(131/125 : ℚ),[1,(8223/1000 : ℚ)],(8223/1000 : ℚ),(-6223/1000 : ℚ),(4223/1000 : ℚ),(8223/1000 : ℚ),138388555976⟩
def marked5 : MarkedParameters := ⟨2,34,2,false,(219/200 : ℚ),[1,(4439/1000 : ℚ),(17249/500 : ℚ)],(17249/500 : ℚ),(-1281/50 : ℚ),(10371/500 : ℚ),(17249/500 : ℚ),3570949434003⟩
def marked6 : MarkedParameters := ⟨1,24,3,true,(26691/25000 : ℚ),[1,6],6,-4,2,6,244703967129004⟩
def marked7 : MarkedParameters := ⟨2,29,4,true,(1103/1000 : ℚ),[1,(4139/1000 : ℚ),(14851/500 : ℚ)],(14851/500 : ℚ),(-11851/750 : ℚ),(8851/1500 : ℚ),(14851/500 : ℚ),30697943987⟩
def marked8 : MarkedParameters := ⟨3,32,5,true,(571/500 : ℚ),[1,(3159/1000 : ℚ),(16519/1000 : ℚ),(96643/1000 : ℚ)],(96643/1000 : ℚ),(-81689/1500 : ℚ),(14947/600 : ℚ),(96643/1000 : ℚ),8391983867666⟩
def marked9 : MarkedParameters := ⟨3,30,6,true,(571/500 : ℚ),[1,(3159/1000 : ℚ),(16519/1000 : ℚ),(96643/1000 : ℚ)],(96643/1000 : ℚ),(-80643/2000 : ℚ),(64643/6000 : ℚ),(96643/1000 : ℚ),1540541451507⟩
def marked10 : MarkedParameters := ⟨4,35,6,true,(1179/1000 : ℚ),[1,(1317/500 : ℚ),(1369/125 : ℚ),(50993/1000 : ℚ),(248981/1000 : ℚ)],(248981/1000 : ℚ),(-222837/2000 : ℚ),(212693/6000 : ℚ),(248981/1000 : ℚ),5792967979⟩
def marked11 : MarkedParameters := ⟨3,28,7,true,(579/500 : ℚ),[1,(2903/1000 : ℚ),(1708/125 : ℚ),(3593/50 : ℚ)],(3593/50 : ℚ),(-21151/750 : ℚ),(2593/375 : ℚ),(3593/50 : ℚ),1342674802820⟩

def markedParameters : List MarkedParameters := [marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11]
def marked (i : Fin 12) : MarkedParameters := markedParameters.getD i.val marked0
def ordinaryCeilings : List ℕ := [139456027322,5843882139428,15136511037,20415616273,703515071,1,70,1,1]
def ordinaryCeiling (q : Fin 9) : ℚ := (ordinaryCeilings.getD q.val 0 : ℚ)/scale
def sourceCeiling : ℚ := 16129981948803/scale
def dominatorCeiling : ℚ := 4851688396110963/scale
def markedCeiling (i : Fin 12) : ℚ := ((marked i).ceiling : ℚ)/scale

































































































end CompactLabeling11987
end
end z16


