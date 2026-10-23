-- Prove2me | Definitions.Def_Paley11987Support_029
-- name    : Paley11987Support_029
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:30:56.671057+00:00
-- url     : https://prove2.me/theorems/1d56bb98-3d2c-4bc4-9459-847c6ca017cf
-- title:
--   Natural-valued profiles and raw transfer coefficients
-- statement:
--   Defines profile coefficient indices A, B, M, P and D; finite recipes and recipe entries; cutoff and cap arrays; finite case data; and the five raw transfer formulas.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module FiniteProfile11987Raw.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfile11987Raw, SHA256 6483484ef69a1e85dd9912bd2ce5533b29c475c14e17dc6a9442fdcf0b102576

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
import Definitions.Def_Paley11987Support_012
import Definitions.Def_Paley11987Support_013
import Definitions.Def_Paley11987Support_014
import Definitions.Def_Paley11987Support_015
import Definitions.Def_Paley11987Support_016
import Definitions.Def_Paley11987Support_017
import Definitions.Def_Paley11987Support_018
import Definitions.Def_Paley11987Support_019
import Definitions.Def_Paley11987Support_020
import Definitions.Def_Paley11987Support_021
import Definitions.Def_Paley11987Support_022
import Definitions.Def_Paley11987Support_023
import Definitions.Def_Paley11987Support_024
import Definitions.Def_Paley11987Support_025
import Definitions.Def_Paley11987Support_026
import Definitions.Def_Paley11987Support_027
import Definitions.Def_Paley11987Support_028

set_option autoImplicit false
set_option Elab.async false
section z44

namespace ZP



abbrev Profile := Nat → Nat

structure RecipeEntry where
  target : Nat
  guard : Nat
  tol : Nat
  deriving Inhabited, DecidableEq, Repr
abbrev Recipe := Array RecipeEntry

def aIndex (i j : Nat) : Nat := i * (41 - i) / 2 + (j-i)
def bIndex (i j : Nat) : Nat := 210 + aIndex i j
def mIndex (i j : Nat) : Nat := 420 + j*(j+1)/2+i
def pIndex (j l : Nat) : Nat := 610+j*(39-j)/2+(l-j-1)
def dIndex (i j l : Nat) : Nat :=
  800 + ((List.range j).map (fun k => (k+1)*(19-k))).sum + i*(19-j)+(l-j-1)

def entry (v : Profile) (i : Nat) : Nat := v i

def A (v : Profile) (i j : Nat) : Nat := entry v (aIndex i j)
def B (v : Profile) (i j : Nat) : Nat := entry v (bIndex i j)
def M (v : Profile) (i j : Nat) : Nat := entry v (mIndex i j)
def P (v : Profile) (j l : Nat) : Nat := entry v (pIndex j l)
def D (v : Profile) (i j l : Nat) : Nat := entry v (dIndex i j l)

def maximum (xs : List Nat) : Nat := xs.foldl max 0
def interval (a b : Nat) : List Nat := (List.range (b-a)).map (a+·)

def minus (v : Profile) (i j k : Nat) : Nat :=
  if i ≤ j ∧ j < k then maximum ((interval j k).map (M v i)) else 0

def plus (v : Profile) (i j k : Nat) : Nat :=
  if i < j ∧ j ≤ k then maximum ((interval i j).map (fun m => P v m k)) else 0

def union (v : Profile) (i j k l : Nat) : Nat :=
  if i ≤ j ∧ j < k ∧ k ≤ l then maximum ((interval j k).map (fun m => D v i m l)) else 0

def cutoffs : Array Nat := #[24,31,38,44,50,57,62,69,74]
def guardCaps : Array Nat := #[21,29,35,41,47,56,61,68,73]
def targetCaps : Array Nat := #[21,30,36,42,48,56,61,68,73]
def cutoff (q : Nat) : Nat := cutoffs[q]?.getD 0
def guardCap (q : Nat) : Nat := guardCaps[q]?.getD 0
def targetCap (q : Nat) : Nat := targetCaps[q]?.getD 0

def markedCap (q m : Nat) : Nat :=
  if q = 1 ∧ m = 3 then 23 else
  if q = 2 ∧ m = 4 then 28 else
  if q = 3 ∧ m = 5 then 31 else
  if q = 3 ∧ m = 6 then 29 else
  if q = 4 ∧ m = 6 then 34 else
  if q = 3 ∧ m = 7 then 27 else 1000000000

def crossCost (K t ext intr budget bb ss jj : Nat) : Nat :=
  let k := min K t
  let extra := min t (k+budget)-k
  max (k*bb+ext*ss+intr*jj)
      ((k+extra)*bb+(ext-extra)*ss+(intr+extra)*jj)

structure Case where
  m : Nat
  u : Nat
  tt : Nat
  ext : Nat
  intr : Nat
  low : Nat
  save : Nat
  cap : Nat
  deriving Inhabited, Repr

def caseFor (q m u : Nat) : Option Case :=
  let e := m*(m-1)/2
  let ext := m*(q+1)-e
  let intr := min e (2*m)
  let t := if m > 0 then min (cutoff q-m) (guardCap q) else cutoff q-1
  if (u+m)*(u+m-1)/2 > q*u+(q+1)*m then none else
    let tt := if u > 0 then min t (targetCap q) else t
    let tt := if q = 1 ∧ u ≥ 2 then min tt 29 else tt
    let tt := if q = 1 ∧ u ≥ 3 then min tt 26 else tt
    let tt := if q = 1 ∧ m ≥ 2 then min tt 27 else tt
    let tt := if q = 2 ∧ m ≥ 2 then min tt 33 else tt
    if u > tt then none else
      let low := ((u : Int)*((m : Int)-(q : Int))+(u*(u-1)/2 : Nat)).toNat
      some ⟨m,u,tt,ext,intr,low,low-u,markedCap q m⟩

def cases (q maxM : Nat) : List Case :=
  (List.range (maxM+1)).flatMap fun m =>
    (List.range (2*q+2)).filterMap (caseFor q m)

def rawA (v : Profile) (recipe : Recipe) (a b : Nat) : Nat :=
  let ⟨ta,ga,qa⟩ := recipe[a]?.getD default
  let ⟨tb,gb,q⟩ := recipe[b]?.getD default
  let aa := plus v gb ta tb
  let bb := A v gb tb
  let ss := B v gb ga
  let jj := B v gb tb
  if q = 0 then
    let z := max (23*bb) (aa+20*bb)
    if qa = q then maximum [z,
      17*bb+max (min (aa+ss) (union v gb ga ta tb)) (aa+jj),
      20*bb+ss,21*bb+jj,17*bb+ss+jj,18*bb+2*jj,17*bb+3*jj]
    else z
  else
    maximum ((cases q (if qa = q then 2*q+3 else 0)).map fun c =>
      if c.u > 0 ∧ gb = ta then 0 else
        c.u*aa+crossCost c.cap (c.tt-c.u) (c.ext-c.save)
          (c.intr+min c.u c.save) (c.ext-c.low) bb ss jj)

def rawB (v : Profile) (recipe : Recipe) (a b : Nat) : Nat :=
  let ⟨ta,ga,qa⟩ := recipe[a]?.getD default
  let ⟨tb,gb,q⟩ := recipe[b]?.getD default
  2*B v ta tb + (if qa = q then (5993-q)*A v gb ga else 0)

def rawM (v : Profile) (recipe : Recipe) (i j : Nat) : Nat :=
  let ⟨ti,gi,qi⟩ := recipe[i]?.getD default
  let ⟨tj,gj,qj⟩ := recipe[j]?.getD default
  let ⟨tk,gk,qk⟩ := recipe[j+1]?.getD default
  if qj = qk then
    let aa := A v gj gi
    max (if tj < tk then
      B v ti tj+(if qi = qj then (5993-qj)*aa else 0)+minus v ti tj tk else 0)
      (if gk < gj then
        2*B v ti tk+(if qi = qj then (5993-qj-1)*aa+plus v gk gj gi else 0) else 0)
  else rawB v recipe i j

def rawP (v : Profile) (recipe : Recipe) (j l : Nat) : Nat :=
  rawA v recipe (j+1) l

def rawD (v : Profile) (recipe : Recipe) (i j l : Nat) : Nat :=
  let ⟨ti,gi,qi⟩ := recipe[i]?.getD default
  let ⟨tj,gj,_⟩ := recipe[j]?.getD default
  let ⟨tk,gk,_⟩ := recipe[j+1]?.getD default
  let ⟨tl,gl,ql⟩ := recipe[l]?.getD default
  if qi = 0 ∧ ql = 0 then
    if tj = tk ∧ gj = gk then 0 else
      let bb := B v ti tl
      let aa := A v gl gi
      max (max (rawM v recipe i j)
        (if tj < tk then bb+5993*aa+union v ti tj tk tl else 0))
        (if gk < gj then 2*bb+5992*aa+union v gl gk gj gi else 0)
  else rawM v recipe i j+rawP v recipe j l

end ZP
end z44


