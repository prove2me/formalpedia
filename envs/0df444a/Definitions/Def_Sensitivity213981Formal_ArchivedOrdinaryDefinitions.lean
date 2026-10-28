-- Prove2me | Definitions.Def_Sensitivity213981Formal_ArchivedOrdinaryDefinitions
-- name    : Sensitivity213981Formal_ArchivedOrdinaryDefinitions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:08:58.731688+00:00
-- url     : https://prove2.me/theorems/714d0f2e-8a3c-40cd-96e3-ae63a7cb8207
-- title:
--   Archived Ordinary Definitions — sensitivity certificate definitions
-- statement:
--   The definitions for Archived Ordinary Definitions in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundOrdinaryArchive.ZL.ordinaryGood_complement`, `ThreeBoundOrdinaryArchive.ZL.markedGood_complement`, `ThreeBoundOrdinaryArchive.ZL.ordinaryBad_complement`, `ThreeBoundOrdinaryArchive.ZL.markedBad_complement`, `ThreeBoundOrdinaryArchive.ZL.mismatch_eq_of_agrees`, `ThreeBoundOrdinaryArchive.ZL.markedGood_congr`, `ThreeBoundOrdinaryArchive.ZL.markedBad_congr`, `ThreeBoundOrdinaryArchive.CompactLabeling11987.ordinaryCutoffs`, `ThreeBoundOrdinaryArchive.CompactLabeling11987.ordinaryA`, `ThreeBoundOrdinaryArchive.CompactLabeling11987.MarkedParameters`, `ThreeBoundOrdinaryArchive.CompactLabeling11987.marked0`, `ThreeBoundOrdinaryArchive.CompactLabeling11987.marked1`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryDefinitions.lean, lines 1–2333.

import Definitions.Def_Sensitivity213981Formal_Namespaces
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Data.Fintype.Powerset
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
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Def_Paley11987Support_000.lean -/
set_option autoImplicit false
set_option Elab.async false
section z0

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def outOn (R : V → V → Prop) (S : Finset V) (x : V) : Finset V :=
  S.filter (R x)



def internalEdges (R : V → V → Prop) (S : Finset V) : Finset (V × V) :=
  (S ×ˢ S).filter fun e => R e.1 e.2



























end
end ZL
end
end z0



/- Def_Paley11987Support_001.lean -/
set_option autoImplicit false
set_option Elab.async false
section z1

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL.RowCounting
noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω]



















end
end ZL.RowCounting
end
end z1



/- Def_Paley11987Support_002.lean -/
set_option autoImplicit false
set_option Elab.async false
section z2

section

namespace SensitivityLabelCache12607

set_option maxHeartbeats 8000000
open scoped BigOperators

namespace SensitivityLLL

variable {ι : Type*} [DecidableEq ι]







noncomputable section
open scoped Classical

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]















end
end SensitivityLLL

end SensitivityLabelCache12607
end
end z2



/- Def_Paley11987Support_003.lean -/
set_option autoImplicit false
set_option Elab.async false
section z3

section

set_option maxHeartbeats 4000000
open scoped Classical BigOperators

namespace CompactAtomicLLL

noncomputable section

open SensitivityLabelCache12607.SensitivityLLL

variable {V E : Type*} [Fintype V] [DecidableEq V]























end

end CompactAtomicLLL
end
end z3



/- Def_Paley11987Support_004.lean -/
set_option autoImplicit false
set_option Elab.async false
section z4

section

set_option maxHeartbeats 4000000
open scoped Classical BigOperators

namespace CompactAtomicLLL

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]









end

end CompactAtomicLLL
end
end z4



/- Def_Paley11987Support_005.lean -/
set_option autoImplicit false
set_option Elab.async false
section z7

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

open CompactAtomicLLL

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

structure SupportedFamily (V D : Type*) [DecidableEq V] where
  support : D → Finset V
  bad : D → (V → Fin 2) → Prop
  locality : ∀ d x y, (∀ v ∈ support d, x v = y v) → (bad d x ↔ bad d y)
  complement : ∀ d x, bad d (fun v => (x v).rev) ↔ bad d x

namespace SupportedFamily

variable (F : SupportedFamily V D)

def extend (d : D) (u : F.support d → Fin 2) : V → Fin 2 :=
  fun v => if hv : v ∈ F.support d then u ⟨v,hv⟩ else 0

def LocalBad (d : D) := {u : F.support d → Fin 2 // F.bad d (F.extend d u)}

def Index := Σ d : D, F.LocalBad d

instance localBadFintype (d : D) : Fintype (F.LocalBad d) := by
  unfold LocalBad
  infer_instance

instance indexFintype : Fintype F.Index := by
  unfold Index
  infer_instance































end SupportedFamily
end
end ZL
end
end z7



/- Def_Paley11987Support_006.lean -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def mismatch (R : V → V → Prop) (ell : V × V → Fin 2)
    (S : Finset V) (color : V → Fin 2) (x : V) : Finset V :=
  S.filter fun y => R x y ∧ ell (x,y) ≠ color y

def OrdinaryGood (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (q : ℕ) (color : V → Fin 2) : Prop :=
  ∀ x ∈ A, (mismatch R ell A color x).card ≤ q

def MarkedGood (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) (color : V → Fin 2) : Prop :=
  (∀ x ∈ A, (mismatch R ell A color x).card + (outOn R M x).card ≤ q) ∧
  (∀ y ∈ M, (outOn R M y).card + (mismatch R ell A color y).card ≤
    q + if y ∈ P then 0 else 1) ∧
  (∑ y ∈ M, (mismatch R ell A color y).card) ≤ B

def OrdinaryBad (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (q : ℕ) : Prop := ∃ color, OrdinaryGood R ell A q color

def MarkedBad (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) : Prop := ∃ color, MarkedGood R ell A M P q B color

def crossEdges (R : V → V → Prop) (M A : Finset V) : Finset (V × V) :=
  (M ×ˢ A).filter fun e => R e.1 e.2

def markedSupport (R : V → V → Prop) (A M : Finset V) : Finset (V × V) :=
  internalEdges R A ∪ crossEdges R M A

def Coherent (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M : Finset V) (color : V → Fin 2) : Prop :=
  ∀ e ∈ markedSupport R A M, ell e = color e.2

def TwoDominatorGood (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M : Finset V) (color : V → Fin 2) : Prop :=
  Disjoint A M ∧ M.card = 2 ∧
    (∀ x ∈ M, ∀ y ∈ A, R x y) ∧ Coherent R ell A M color











theorem mismatch_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (color : V → Fin 2) (x : V) :
    mismatch R (fun e => (ell e).rev) A (fun y => (color y).rev) x =
      mismatch R ell A color x := by
  ext y
  simp only [mismatch, Finset.mem_filter]
  constructor
  · rintro ⟨hy,hR,hn⟩
    exact ⟨hy,hR,fun h => hn (congrArg Fin.rev h)⟩
  · rintro ⟨hy,hR,hn⟩
    refine ⟨hy,hR,fun h => hn ?_⟩
    simpa only [Fin.rev_rev] using congrArg Fin.rev h

theorem ordinaryGood_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (q : ℕ) (color : V → Fin 2) :
    OrdinaryGood R (fun e => (ell e).rev) A q (fun y => (color y).rev) ↔
      OrdinaryGood R ell A q color := by
  simp only [OrdinaryGood, mismatch_complement]

theorem markedGood_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) (color : V → Fin 2) :
    MarkedGood R (fun e => (ell e).rev) A M P q B (fun y => (color y).rev) ↔
      MarkedGood R ell A M P q B color := by
  simp only [MarkedGood, mismatch_complement]

theorem ordinaryBad_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A : Finset V) (q : ℕ) :
    OrdinaryBad R (fun e => (ell e).rev) A q ↔ OrdinaryBad R ell A q := by
  constructor
  · rintro ⟨color,hcolor⟩
    refine ⟨fun y => (color y).rev, ?_⟩
    have h := (ordinaryGood_complement R (fun e => (ell e).rev) A q color).mpr hcolor
    simpa only [Fin.rev_rev] using h
  · rintro ⟨color,hcolor⟩
    exact ⟨fun y => (color y).rev,(ordinaryGood_complement R ell A q color).mpr hcolor⟩

theorem markedBad_complement (R : V → V → Prop) (ell : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) :
    MarkedBad R (fun e => (ell e).rev) A M P q B ↔ MarkedBad R ell A M P q B := by
  constructor
  · rintro ⟨color,hcolor⟩
    refine ⟨fun y => (color y).rev, ?_⟩
    have h := (markedGood_complement R (fun e => (ell e).rev) A M P q B color).mpr hcolor
    simpa only [Fin.rev_rev] using h
  · rintro ⟨color,hcolor⟩
    exact ⟨fun y => (color y).rev,(markedGood_complement R ell A M P q B color).mpr hcolor⟩





theorem mismatch_eq_of_agrees (R : V → V → Prop) (ell ell' : V × V → Fin 2)
    (A : Finset V) (color : V → Fin 2) (x : V)
    (h : ∀ y ∈ A, R x y → ell (x,y) = ell' (x,y)) :
    mismatch R ell A color x = mismatch R ell' A color x := by
  ext y
  by_cases hy : y ∈ A
  · by_cases hxy : R x y
    · simp only [mismatch, Finset.mem_filter, hy, hxy, h y hy hxy]
    · simp only [mismatch, Finset.mem_filter, hxy, and_false, false_and]
  · simp only [mismatch, Finset.mem_filter, hy, false_and]

theorem markedGood_congr (R : V → V → Prop) (ell ell' : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ) (color : V → Fin 2)
    (heq : ∀ e ∈ markedSupport R A M, ell e = ell' e) :
    MarkedGood R ell A M P q B color ↔ MarkedGood R ell' A M P q B color := by
  have hA (x : V) (hx : x ∈ A) :
      mismatch R ell A color x = mismatch R ell' A color x := by
    apply mismatch_eq_of_agrees
    intro y hy hxy
    exact heq (x,y) (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩))
  have hM (x : V) (hx : x ∈ M) :
      mismatch R ell A color x = mismatch R ell' A color x := by
    apply mismatch_eq_of_agrees
    intro y hy hxy
    exact heq (x,y) (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩))
  have hsum : (∑ y ∈ M, (mismatch R ell A color y).card) =
      ∑ y ∈ M, (mismatch R ell' A color y).card :=
    Finset.sum_congr rfl fun y hy => congrArg Finset.card (hM y hy)
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
    · rw [← hA x hx]
      exact h.1 x hx
    · rw [← hM y hy]
      exact h.2.1 y hy
    · rw [← hsum]
      exact h.2.2
  · intro h
    refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
    · rw [hA x hx]
      exact h.1 x hx
    · rw [hM y hy]
      exact h.2.1 y hy
    · rw [hsum]
      exact h.2.2

theorem markedBad_congr (R : V → V → Prop) (ell ell' : V × V → Fin 2)
    (A M P : Finset V) (q B : ℕ)
    (heq : ∀ e ∈ markedSupport R A M, ell e = ell' e) :
    MarkedBad R ell A M P q B ↔ MarkedBad R ell' A M P q B := by
  exact exists_congr fun color => markedGood_congr R ell ell' A M P q B color heq



end
end ZL
end
end z8



/- Def_Paley11987Support_007.lean -/
set_option autoImplicit false
set_option Elab.async false
section z9

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

namespace SupportedFamily
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
variable (F : SupportedFamily V D)










end SupportedFamily

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

open RowCounting

















end
end ZL
end
end z9



/- Def_Paley11987Support_008.lean -/
set_option autoImplicit false
set_option Elab.async false
section z10

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [DecidableEq V]













end
end ZL
end
end z10



/- Def_Paley11987Support_009.lean -/
set_option autoImplicit false
set_option Elab.async false
section z11

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

















end
end ZL
end
end z11



/- Def_Paley11987Support_010.lean -/
set_option autoImplicit false
set_option Elab.async false
section z13

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]















end
end ZL
end
end z13



/- Def_Paley11987Support_011.lean -/
set_option autoImplicit false
set_option Elab.async false
section z15

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

















end
end ZL
end
end z15



/- Def_Paley11987Support_012.lean -/
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







def ordinaryCutoffs : List ℕ := [24,31,38,44,50,57,62,69,74]
def ordinaryA (q : Fin 9) : ℕ := ordinaryCutoffs.getD q.val 0












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






































































































end CompactLabeling11987
end
end z16



/- Def_Paley11987Support_013.lean -/
set_option autoImplicit false
set_option Elab.async false
section z17

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def OrdinaryIndex (V : Type*) [Fintype V] [DecidableEq V] (a : ℕ) :=
  ((Finset.univ : Finset V).powersetCard a)

def MarkedIndex (V : Type*) [Fintype V] [DecidableEq V] (a m : ℕ) :=
  Σ M : ((Finset.univ : Finset V).powersetCard m), M.valᶜ.powersetCard a

def SourceIndex (R : V → V → Prop) (a : ℕ) :=
  Σ s : V, (outOn R Finset.univ s).powersetCard a

def dominatedBy (R : V → V → Prop) (M : Finset V) : Finset V :=
  Finset.univ.filter (fun y => ∀ x ∈ M, R x y)

def DominatorIndex (R : V → V → Prop) (a : ℕ) :=
  Σ M : ((Finset.univ : Finset V).powersetCard 2), (dominatedBy R M.val).powersetCard a

instance ordinaryIndexFintype (a : ℕ) : Fintype (OrdinaryIndex V a) := by
  unfold OrdinaryIndex
  infer_instance
instance markedIndexFintype (a m : ℕ) : Fintype (MarkedIndex V a m) := by
  unfold MarkedIndex
  infer_instance
instance sourceIndexFintype (R : V → V → Prop) (a : ℕ) : Fintype (SourceIndex R a) := by
  unfold SourceIndex
  infer_instance
instance dominatorIndexFintype (R : V → V → Prop) (a : ℕ) : Fintype (DominatorIndex R a) := by
  unfold DominatorIndex
  infer_instance

theorem ordinaryBad_congr (R : V → V → Prop) (A : Finset V) (q : ℕ)
    (ell ell' : V × V → Fin 2)
    (heq : ∀ e ∈ internalEdges R A, ell e = ell' e) :
    OrdinaryBad R ell A q ↔ OrdinaryBad R ell' A q := by
  apply exists_congr
  intro color
  have hm (x : V) (hx : x ∈ A) :
      mismatch R ell A color x = mismatch R ell' A color x := by
    apply mismatch_eq_of_agrees
    intro y hy hxy
    exact heq (x,y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩)
  constructor <;> intro h x hx
  · rw [← hm x hx]
    exact h x hx
  · rw [hm x hx]
    exact h x hx







def ordinaryFamily (R : V → V → Prop) (q a : ℕ) :
    SupportedFamily (V × V) (OrdinaryIndex V a) where
  support I := internalEdges R I.val
  bad I ell := OrdinaryBad R ell I.val q
  locality I ell ell' heq := ordinaryBad_congr R I.val q ell ell' heq
  complement I ell := ordinaryBad_complement R ell I.val q

def markedFamily (R : V → V → Prop) (q a m B : ℕ) :
    SupportedFamily (V × V) (MarkedIndex V a m) where
  support I := markedSupport R I.2.val I.1.val
  bad I ell := MarkedBad R ell I.2.val I.1.val ∅ q B
  locality I ell ell' heq := markedBad_congr R ell ell' I.2.val I.1.val ∅ q B heq
  complement I ell := markedBad_complement R ell I.2.val I.1.val ∅ q B



















end
end ZL
end
end z17



/- Def_Paley11987Support_014.lean -/
set_option autoImplicit false
set_option Elab.async false
section z20

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]







end
end ZL
end
end z20



/- Def_Paley11987Support_015.lean -/
set_option autoImplicit false
set_option Elab.async false
section z23

set_option maxHeartbeats 200000
open scoped Classical BigOperators
noncomputable section

namespace ZL
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]







end ZL
end
end z23



/- Def_Paley11987Support_016.lean -/
set_option autoImplicit false
set_option Elab.async false
section z24

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace ZL
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]















end ZL
end
end z24



/- Def_Paley11987Support_017.lean -/
set_option autoImplicit false
set_option Elab.async false
section z27

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL.SupportedFamily
noncomputable section
variable {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T]
variable {D : T → Type*} [∀ t, Fintype (D t)]







end
end ZL.SupportedFamily
end
end z27



/- Def_Paley11987Support_018.lean -/
set_option autoImplicit false
set_option Elab.async false
section z28

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped Classical BigOperators
noncomputable section

namespace CompactLabeling11987
open ZL ZL.RowCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev FamilyKind := Fin 9 ⊕ (Fin 12 ⊕ Bool)

def Description (R : V → V → Prop) : FamilyKind → Type _
  | .inl q => OrdinaryIndex V (ordinaryA q)
  | .inr (.inl i) => MarkedIndex V (marked i).a (marked i).m
  | .inr (.inr false) => SourceIndex R 21
  | .inr (.inr true) => DominatorIndex R 18

instance descriptionFintype (R : V → V → Prop) (t : FamilyKind) : Fintype (Description R t) := by
  rcases t with q | i | b
  · exact ordinaryIndexFintype (ordinaryA q)
  · exact markedIndexFintype (marked i).a (marked i).m
  · cases b
    · exact sourceIndexFintype R 21
    · exact dominatorIndexFintype R 18





























end CompactLabeling11987
end
end z28



/- Def_Paley11987Support_019.lean -/
set_option autoImplicit false
set_option Elab.async false
section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320

structure NestedFamily {h : ℕ} {I : Type}
    (F : Fin h → (I → Bool) → Bool) : Prop where
  accepts_of_le : ∀ {q q' : Fin h} {x}, q ≤ q' → F q' x = true → F q x = true









structure Tournament (k : ℕ) extends Digraph (Fin k) where
  loopless : ∀ i, ¬ Adj i i
  edge_compl : ∀ {i j}, i ≠ j → (Adj i j ↔ ¬ Adj j i)

namespace Tournament
variable {k : ℕ} (T : Tournament k)









end Tournament

def recursiveChild {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) : I → Bool :=
  fun a => x ((j, c), a)





def childLift {J I : Type} (j : J) (A : Finset I) : Finset (J × I) :=
  A.map ⟨fun a => (j, a), fun _ _ h => congrArg (fun p : J × I => p.2) h⟩











end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205

def missingTargets {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin r) :=
  Finset.univ.filter fun c => F A (recursiveChild x i c) = false

def failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun j => T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true

def tolerantRow {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Bool :=
  decide ((∀ c, F A (recursiveChild x i c) = true) ∧
    (failedGuards T label F G x i).card ≤ q)

def tolerantFamily {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) : Bool :=
  decide (∃ i, tolerantRow T label F A G q x i = true)

def tolerantTargets {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => (missingTargets F A x i).card = 1 ∧
    (failedGuards T label F G x i).card ≤ q

def tolerantGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => missingTargets F A x i = ∅ ∧
    (failedGuards T label F G x i).card = q+1













section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)





end Nesting

def missingWitness {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k) : Fin r :=
  if h : (missingTargets F A x i).Nonempty then h.choose else ⟨0, hr⟩









section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29



/- Def_Paley11987Support_020.lean -/
set_option autoImplicit false
set_option Elab.async false
section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]

def flipsTo (f : (I → Bool) → Bool) (b : Bool) (x : I → Bool) : Finset I :=
  Finset.univ.filter fun a => f (_root_.OAI.Paper320.flip x {a}) = b



def ABound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j : Fin h) (v : ℕ) : Prop :=
  ∀ x, F i x = false → (flipsTo (F j) true x).card ≤ v

def BBound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j : Fin h) (v : ℕ) : Prop :=
  ∀ x, F j x = true → (flipsTo (F i) false x).card ≤ v



def PBound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j k : Fin h) (v : ℕ) : Prop :=
  ∀ x, F i x = true → F j x = false → (flipsTo (F k) true x).card ≤ v















end ZT
end
end z30



/- Def_Paley11987Support_021.lean -/
set_option autoImplicit false
set_option Elab.async false
section z31

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k r : ℕ} {I : Type} [Fintype I]

def childFlipsTo (F : Fin n → (I → Bool) → Bool) (a : Fin n) (b : Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (v,c) (flipsTo (F a) b (recursiveChild x v c))





















end ZT
end
end z31



/- Def_Paley11987Support_022.lean -/
set_option autoImplicit false
set_option Elab.async false
section z32
set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

def internalEdges (I : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (I ×ˢ I).filter fun p => T.Adj p.1 p.2





end OAI.Paper320.Tournament
namespace SensitivityQ

def DefectBound {k r : ℕ} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (q s : ℕ) : Prop :=
  ∀ (S : Finset (Fin k)) (m : Fin k → Fin r),
    (∀ i ∈ S, (S.filter fun j => T.Adj i j ∧ label i j ≠ m j).card ≤ q) →
    S.card < s









def positiveTargets {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    Finset (Fin k) :=
  (tolerantTargets T label F A G q x).filter fun i =>
    F G (recursiveChild x i (missingWitness F A x hr i)) = true







end SensitivityQ
namespace SensitivitySourceZero
variable {n k r : ℕ} {I : Type}

def HasSource (T : Tournament k) (S : Finset (Fin k)) : Prop :=
  ∃ s ∈ S, ∀ j ∈ S, j ≠ s → T.Adj s j

def SourceBound (T : Tournament k) (label : Fin k → Fin k → Fin r) (v : ℕ) : Prop :=
  ∀ (S : Finset (Fin k)) (colors : Fin k → Fin r), HasSource T S →
    (∀ i ∈ S, (S.filter fun j => T.Adj i j ∧ label i j ≠ colors j).card ≤ 0) →
    S.card < v

















end SensitivitySourceZero
end
end z32



/- Def_Paley11987Support_023.lean -/
set_option autoImplicit false
set_option Elab.async false
section z33

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

def targetRepairs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) : Finset ((Fin k × Fin 2) × I) :=
  (tolerantTargets T label F t g q x).biUnion fun v =>
    childFlipsTo F t true x v (missingWitness F t x (by decide) v)

def guardRepairs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) : Finset ((Fin k × Fin 2) × I) :=
  (tolerantGuards T label F t g q x).biUnion fun v =>
    (failedGuards T label F g x v).biUnion fun w =>
      childFlipsTo F g false x w (label v w)











end ZT
end
end z33



/- Def_Paley11987Support_024.lean -/
set_option autoImplicit false
set_option Elab.async false
section z34

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

def guardArcs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) : Finset (Fin k × Fin k) :=
  ((tolerantGuards T label F t g q x) ×ˢ Finset.univ).filter fun e =>
    e.2 ∈ failedGuards T label F g x e.1

def externalGuardArcs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) : Finset (Fin k × Fin k) :=
  (guardArcs T label F t g q x).filter fun e => e.2 ∉ tolerantGuards T label F t g q x

def internalGuardArcs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) : Finset (Fin k × Fin k) :=
  (guardArcs T label F t g q x).filter fun e => e.2 ∈ tolerantGuards T label F t g q x

def arcCoordinate (label : Fin k → Fin k → Fin 2) (e : Fin k × Fin k) : Fin k × Fin 2 :=
  (e.2,label e.1 e.2)













end ZT
end
end z34



/- Def_Paley11987Support_025.lean -/
set_option autoImplicit false
set_option Elab.async false
section z37

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

def externalGuardCoordinates (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) : Finset (Fin k × Fin 2) :=
  (externalGuardArcs T label F t g q x).image (arcCoordinate label)

def crossedTargetHeads (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) : Finset (Fin k) :=
  ((externalGuardCoordinates T label F t g q x).filter fun z =>
    z.1 ∈ tolerantTargets T label F t g q x ∧
      z.1 ∉ positiveTargets T label F t g q x (by decide)).image Prod.fst











end ZT
end
end z37



/- Def_Paley11987Support_026.lean -/
set_option autoImplicit false
set_option Elab.async false
section z38

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace CompactTournament
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def neighbors (R : V → V → Prop) (x : V) : Finset V := univ.filter (R x)











end CompactTournament
end
end z38



/- Def_Paley11987Support_027.lean -/
set_option autoImplicit false
set_option Elab.async false
section z41

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

def remainingOrdinaryTargets (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) : Finset (Fin k) :=
  (tolerantTargets T label F t g q x \ positiveTargets T label F t g q x (by decide)) \
    crossedTargetHeads T label F t g q x















end ZT
end
end z41



/- Def_Paley11987Support_028.lean -/
set_option autoImplicit false
set_option Elab.async false
section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

def MarkedCardBound (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (q m p B w : ℕ) : Prop :=
  ∀ (A M P : Finset (Fin k)) (color : Fin k → Fin 2),
    Disjoint A M → P ⊆ M → M.card=m → P.card=p →
      MarkedGood T.Adj (fun e => label e.1 e.2) A M P q B color → A.card < w

def DoubleCardBound (T : Tournament k) (label : Fin k → Fin k → Fin 2) (w : ℕ) : Prop :=
  ∀ (A M : Finset (Fin k)) (color : Fin k → Fin 2),
    TwoDominatorGood T.Adj (fun e => label e.1 e.2) A M color → A.card < w















end ZT
end
end z43



/- Def_Paley11987Support_029.lean -/
set_option autoImplicit false
set_option Elab.async false
section z44

namespace ZP





structure RecipeEntry where
  target : Nat
  guard : Nat
  tol : Nat
  deriving Inhabited, DecidableEq, Repr

























def cutoffs : Array Nat := #[23,30,37,43,49,54,60,65,71]
def guardCaps : Array Nat := #[20,28,34,40,46,53,59,64,70]

def cutoff (q : Nat) : Nat := cutoffs[q]?.getD 0
def guardCap (q : Nat) : Nat := guardCaps[q]?.getD 0






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















end ZP
end z44



/- Def_Paley11987Support_030.lean -/
set_option autoImplicit false
set_option Elab.async false
section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

structure LabelCaps (T : Tournament k) (label : Fin k → Fin k → Fin 2) : Prop where
  ordinary : ∀ q, q ≤ 8 → DefectBound T label q (cutoff q)
  source : SensitivitySourceZero.SourceBound T label 21
  double : DoubleCardBound T label 18
  one : ∀ q, 1 ≤ q → q ≤ 4 → MarkedCardBound T label q 1 0 (q+1) (guardCap q+1)
  two_one : MarkedCardBound T label 1 2 0 4 27
  two_two : MarkedCardBound T label 2 2 0 6 34
  zero_one_three : MarkedCardBound T label 1 3 0 0 24
  zero_two_four : MarkedCardBound T label 2 4 0 0 28
  zero_three_five : MarkedCardBound T label 3 5 0 0 31
  zero_three_six : MarkedCardBound T label 3 6 0 0 29
  zero_four_six : MarkedCardBound T label 4 6 0 0 34
  zero_three_seven : MarkedCardBound T label 3 7 0 0 27







end ZT
end
end z45



/- Def_Paley11987Support_038.lean -/
set_option autoImplicit false
set_option Elab.async false
section z59

set_option maxHeartbeats 5000000
namespace ZT

def deletionCost (K t ext intr budget B S J : ℕ) : ℕ :=
  let k := min K t
  let extra := min t (k+budget)-k
  max (k*B+ext*S+intr*J)
    ((k+extra)*B+(ext-extra)*S+(intr+extra)*J)







end ZT
end z59



/- Def_Paley11987Support_039.lean -/
set_option autoImplicit false
set_option Elab.async false
section z60

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

def candidateCost (q t u m δ a b s j : ℕ) : ℕ :=
  let E := m*(q+1)-m.choose 2
  let L := (u*m+u.choose 2)-q*u
  let save := L-u
  let intr := min (m.choose 2) (2*m)
  u*a+(t-u)*b+(E-save-δ)*s+(intr+min u save+δ)*j









end ZT
end
end z60



/- Def_Paley11987Support_040.lean -/
set_option autoImplicit false
set_option Elab.async false
section z61

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]













end ZT
end
end z61



/- Def_Paley11987Support_041.lean -/
set_option autoImplicit false
set_option Elab.async false
section z62

set_option maxHeartbeats 5000000
namespace ZT









end ZT
end z62



end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal


