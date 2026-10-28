-- Prove2me | Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryDefinitions
-- name    : BS2_b3ba934b_ArchivedOrdinaryDefinitions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:36:04.379826+00:00
-- url     : https://prove2.me/theorems/64ca9abb-e226-4b99-bbfc-81b0ef91e0bd
-- title:
--   Sensitivity separation: ArchivedOrdinaryDefinitions (complete source module)
-- statement:
--   Complete Lean source module `ArchivedOrdinaryDefinitions` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ArchivedOrdinaryDefinitions.lean; original SHA-256 8489186dc387c7a717d9057444b46c64de8b27fb4a9c3034b600784c8ed21c32; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/
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

def inOn (R : V → V → Prop) (S : Finset V) (x : V) : Finset V :=
  S.filter fun y => R y x

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

def smallSubsets (R : Finset Ω) (q : ℕ) : Finset (Finset Ω) :=
  R.powerset.filter (fun s => s.card ≤ q)

def rowPatterns (q d : ℕ) : ℕ :=
  ∑ j : Fin (q + 1), d.choose j.val



def rowUnion (R : ι → Finset Ω) : Finset Ω :=
  Finset.univ.biUnion R

def rowGood (R : ι → Finset Ω) (q : ι → ℕ) (c : Ω → Fin 2) :
    Finset (Ω → Fin 2) :=
  Finset.univ.filter (fun a =>
    ∀ i, ((R i).filter (fun e => a e ≠ c e)).card ≤ q i)









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

def avoid (bad : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  Finset.univ.filter fun ω => ∀ i ∈ S, ω ∉ bad i













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

structure Atom (V : Type*) where
  support : Finset V
  value : V → Fin 2

def Holds (a : Atom V) (x : V → Fin 2) : Prop :=
  ∀ v ∈ a.support, x v = a.value v

def event (a : Atom V) : Finset (V → Fin 2) :=
  Finset.univ.filter (Holds a)



def Conflict (a b : Atom V) : Prop :=
  ∃ v ∈ a.support, v ∈ b.support ∧ a.value v ≠ b.value v

def overwrite (a : Atom V) (x : V → Fin 2) (u : a.support → Fin 2) : V → Fin 2 :=
  fun v => if hv : v ∈ a.support then u ⟨v, hv⟩ else x v







def neighbors [Fintype E] (atoms : E → Atom V) (i : E) : Finset E :=
  Finset.univ.filter fun j => Conflict (atoms i) (atoms j)



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

def conflictSlice (a : Atom V) (atoms : E → Atom V) (v : V) : Finset E :=
  Finset.univ.filter fun j => v ∈ (atoms j).support ∧ a.value v ≠ (atoms j).value v







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

def atom (i : F.Index) : Atom V := ⟨F.support i.1, F.extend i.1 i.2.val⟩



theorem bad_restrict (d : D) (ell : V → Fin 2) :
    F.bad d (F.extend d (fun v => ell v.val)) ↔ F.bad d ell := by
  apply F.locality
  intro v hv
  simp only [extend, dif_pos hv]

def complementLocal (d : D) (u : F.LocalBad d) : F.LocalBad d :=
  ⟨fun v => (u.val v).rev, by
    have hc := (F.complement d (F.extend d u.val)).mpr u.property
    apply (F.locality d _ _ ?_).mp hc
    intro v hv
    simp only [extend, dif_pos hv]⟩

def complementIndex (i : F.Index) : F.Index := ⟨i.1,F.complementLocal i.1 i.2⟩

theorem complementIndex_involutive : Function.Involutive F.complementIndex := by
  rintro ⟨d,u⟩
  apply congrArg (Sigma.mk d)
  apply Subtype.ext
  funext v
  exact Fin.rev_rev (u.val v)

def complementEquiv : F.Index ≃ F.Index :=
  ⟨F.complementIndex,F.complementIndex,F.complementIndex_involutive,F.complementIndex_involutive⟩







def atomWeight (M : D → ℕ) (lam : ℚ) (i : F.Index) : ℚ :=
  (1 / (2 : ℚ) ^ (F.support i.1).card) * lam ^ M i.1

def localProbability (d : D) : ℚ :=
  (Fintype.card (F.LocalBad d) : ℚ) / (2 : ℚ) ^ (F.support d).card







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

def glue (d : D) (u : F.support d → Fin 2) (v : ((F.support d)ᶜ : Finset V) → Fin 2) : V → Fin 2 :=
  fun x => if hx : x ∈ F.support d then u ⟨x,hx⟩ else v ⟨x,Finset.mem_compl.mpr hx⟩

def globalBadEquiv (d : D) :
    {ell : V → Fin 2 // F.bad d ell} ≃ F.LocalBad d × (((F.support d)ᶜ : Finset V) → Fin 2) where
  toFun ell := ⟨⟨fun v => ell.val v.val,(F.bad_restrict d ell.val).mpr ell.property⟩,
    fun v => ell.val v.val⟩
  invFun p := ⟨F.glue d p.1.val p.2, by
    apply (F.locality d (F.extend d p.1.val) _ ?_).mp p.1.property
    intro v hv
    simp only [glue,extend,dif_pos hv]⟩
  left_inv ell := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ F.support d <;> simp [glue,hv]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext v
      simp only [glue,dif_pos v.property]
    · funext v
      simp only [glue,dif_neg (Finset.mem_compl.mp v.property)]






end SupportedFamily

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

open RowCounting

def outgoingRow (A : Finset V) (i : V) : Finset (V × V) :=
  (outOn R A i).image (fun j => (i,j))





def ordinaryRows (A : Finset V) (i : A) : Finset (V × V) := outgoingRow R A i.val



def headColor (A : Finset V) (c : A → Fin 2) (e : V × V) : Fin 2 :=
  if h : e.2 ∈ A then c ⟨e.2,h⟩ else 0

def ordinaryAssignments (A : Finset V) (q : ℕ) : Finset ((V × V) → Fin 2) :=
  Finset.univ.filter (fun ell => OrdinaryBad R ell A q)



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

def weightedSubsets (S : Finset V) (w : V → ℚ) (a : ℕ) : ℚ :=
  ∑ A ∈ S.powersetCard a, ∏ x ∈ A, w x











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

def markedRows (A M : Finset V) : A ⊕ M → Finset (V × V) :=
  Sum.elim (fun i => outgoingRow R A i.val) (fun i => outgoingRow R A i.val)



def markedRowBudget (A M P : Finset V) (q B : ℕ) : A ⊕ M → ℕ :=
  Sum.elim (fun x => q - (outOn R M x.val).card)
    (fun _y => if B=0 then 0 else q+1)



def markedAssignments (A M P : Finset V) (q B : ℕ) : Finset ((V × V) → Fin 2) :=
  Finset.univ.filter (fun ell => MarkedBad R ell A M P q B)







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











def headErrorFactor (q a m B : ℕ) : ℕ :=
  if B=0 then 1 else (rowPatterns (q+1) a)^m



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

def orientationWeight (q : ℕ) (C : ℕ → ℚ) (f : ℕ) : ℚ :=
  if f ≤ q then (2 : ℚ)^f * C (q-f) else 0















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

def CoherentBad (R : V → V → Prop) (A M : Finset V) (ell : V × V → Fin 2) : Prop :=
  ∃ color, Coherent R ell A M color

theorem coherentBad_congr (R : V → V → Prop) (A M : Finset V)
    (ell ell' : V × V → Fin 2)
    (heq : ∀ e ∈ markedSupport R A M, ell e = ell' e) :
    CoherentBad R A M ell ↔ CoherentBad R A M ell' := by
  apply exists_congr
  intro color
  constructor <;> intro h e he
  · rw [← heq e he]
    exact h e he
  · rw [heq e he]
    exact h e he

theorem coherentBad_complement (R : V → V → Prop) (A M : Finset V)
    (ell : V × V → Fin 2) :
    CoherentBad R A M (fun e => (ell e).rev) ↔ CoherentBad R A M ell := by
  constructor
  · rintro ⟨color,hcolor⟩
    refine ⟨fun y => (color y).rev,?_⟩
    intro e he
    simpa only [Fin.rev_rev] using congrArg Fin.rev (hcolor e he)
  · rintro ⟨color,hcolor⟩
    refine ⟨fun y => (color y).rev,?_⟩
    intro e he
    exact congrArg Fin.rev (hcolor e he)

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

def sourceFamily (R : V → V → Prop) (a : ℕ) :
    SupportedFamily (V × V) (SourceIndex R a) where
  support I := markedSupport R I.2.val {I.1}
  bad I ell := CoherentBad R I.2.val {I.1} ell
  locality I ell ell' heq := coherentBad_congr R I.2.val {I.1} ell ell' heq
  complement I ell := coherentBad_complement R I.2.val {I.1} ell

def dominatorFamily (R : V → V → Prop) (a : ℕ) :
    SupportedFamily (V × V) (DominatorIndex R a) where
  support I := markedSupport R I.2.val I.1.val
  bad I ell := CoherentBad R I.2.val I.1.val ell
  locality I ell ell' heq := coherentBad_congr R I.2.val I.1.val ell ell' heq
  complement I ell := coherentBad_complement R I.2.val I.1.val ell















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



def markedWeightedLoad (R : V → V → Prop) (a m : ℕ)
    (w : Finset V → V → ℚ) (x y : V) : ℚ :=
  ∑ M ∈ (Finset.univ : Finset V).powersetCard m,
    ∑ A ∈ (Mᶜ.powersetCard a).filter (fun A => (x,y) ∈ markedSupport R A M),
      ∏ z ∈ A, w M z



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

def commonOutSet (R : V → V → Prop) (M : Finset V) : Finset V :=
  univ.filter fun x => ∀ y ∈ M, R y x





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



def sourceEncode (R : V → V → Prop) (a : ℕ) (I : SourceIndex R a) : V × Finset V :=
  (I.1,I.2.val)





def dominatorEncode (R : V → V → Prop) (a : ℕ) (I : DominatorIndex R a) :
    Finset V × Finset V := (I.2.val,I.1.val)





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

def iUnion (F : ∀ t, ZL.SupportedFamily V (D t)) :
    ZL.SupportedFamily V (Σ t, D t) where
  support i := (F i.1).support i.2
  bad i ell := (F i.1).bad i.2 ell
  locality i ell ell' h := (F i.1).locality i.2 ell ell' h
  complement i ell := (F i.1).complement i.2 ell





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
attribute [local irreducible] N degree common lam
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

def family (R : V → V → Prop) : (t : FamilyKind) → SupportedFamily (V × V) (Description R t)
  | .inl q => ordinaryFamily R q.val (ordinaryA q)
  | .inr (.inl i) => markedFamily R (marked i).q (marked i).a (marked i).m (marked i).B
  | .inr (.inr false) => sourceFamily R 21
  | .inr (.inr true) => dominatorFamily R 18

def exponent : FamilyKind → ℕ
  | .inl q => (ordinaryA q).choose 2
  | .inr (.inl i) => (marked i).a.choose 2+(marked i).m*(marked i).a
  | .inr (.inr false) => 231
  | .inr (.inr true) => 189

def lowerExponent : FamilyKind → ℕ
  | .inl q => (ordinaryA q).choose 2
  | .inr (.inl i) => (marked i).a.choose 2
  | .inr (.inr false) => 231
  | .inr (.inr true) => 189

def ceiling : FamilyKind → ℚ
  | .inl q => ordinaryCeiling q
  | .inr (.inl i) => markedCeiling i
  | .inr (.inr false) => sourceCeiling
  | .inr (.inr true) => dominatorCeiling

structure JointExclusions (R : V → V → Prop) (ell : V × V → Fin 2) : Prop where
  ordinary : ∀ (q : Fin 9) (I : OrdinaryIndex V (ordinaryA q)),
    ¬ (ordinaryFamily R q.val (ordinaryA q)).bad I ell
  marked : ∀ (i : Fin 12) (I : MarkedIndex V (marked i).a (marked i).m),
    ¬ (markedFamily R (marked i).q (marked i).a (marked i).m (marked i).B).bad I ell
  source : ∀ I : SourceIndex R 21, ¬ (sourceFamily R 21).bad I ell
  dominator : ∀ I : DominatorIndex R 18, ¬ (dominatorFamily R 18).bad I ell



















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



def jointSensitivityAt {I : Type} [Fintype I]
    (f g : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i =>
    f (_root_.OAI.Paper320.flip x {i}) ≠ f x ∧ g (_root_.OAI.Paper320.flip x {i}) ≠ g x).card

theorem flip_prod_same {I J : Type} (x : J × I → Bool) (j : J) (i : I) :
    (fun a => _root_.OAI.Paper320.flip x {(j, i)} (j, a)) = _root_.OAI.Paper320.flip (fun a => x (j, a)) {i} := by
  funext a
  simp [_root_.OAI.Paper320.flip]

theorem flip_prod_other {I J : Type} (x : J × I → Bool) {j k : J} (i : I) (hk : k ≠ j) :
    (fun a => _root_.OAI.Paper320.flip x {(j, i)} (k, a)) = fun a => x (k, a) := by
  funext a
  simp [_root_.OAI.Paper320.flip, hk]

structure Tournament (k : ℕ) extends Digraph (Fin k) where
  loopless : ∀ i, ¬ Adj i i
  edge_compl : ∀ {i j}, i ≠ j → (Adj i j ↔ ¬ Adj j i)

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h







end Tournament

def recursiveChild {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) : I → Bool :=
  fun a => x ((j, c), a)

theorem recursiveChild_flip_same {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) (a : I) :
    recursiveChild (_root_.OAI.Paper320.flip x {((j, c), a)}) j c = _root_.OAI.Paper320.flip (recursiveChild x j c) {a} :=
  flip_prod_same x (j, c) a

theorem recursiveChild_flip_other {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j j' : Fin k) (c c' : Fin r) (a : I)
    (h : (j', c') ≠ (j, c)) :
    recursiveChild (_root_.OAI.Paper320.flip x {((j, c), a)}) j' c' = recursiveChild x j' c' :=
  flip_prod_other x a h

def childLift {J I : Type} (j : J) (A : Finset I) : Finset (J × I) :=
  A.map ⟨fun a => (j, a), fun _ _ h => congrArg (fun p : J × I => p.2) h⟩





def childJointChanges {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (j, c) (Finset.univ.filter fun a =>
    F q (_root_.OAI.Paper320.flip (recursiveChild x j c) {a}) ≠ F q (recursiveChild x j c) ∧
    F q' (_root_.OAI.Paper320.flip (recursiveChild x j c) {a}) ≠ F q' (recursiveChild x j c))





end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320

def PairBound {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (b : Bool) (V : Fin n → Fin n → ℕ) : Prop :=
  ∀ (q q' : Fin n), q ≤ q' → ∀ x, F q x = b → F q' x = b →
    jointSensitivityAt (F q) (F q') x ≤ V q q'





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







theorem tolerantRow_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    tolerantRow T label F A G q x i = true ↔
      (∀ c, F A (recursiveChild x i c) = true) ∧
      (failedGuards T label F G x i).card ≤ q := by
  simp only [tolerantRow, decide_eq_true_eq]

theorem tolerantFamily_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantFamily T label F A G q x = true ↔
      ∃ i, tolerantRow T label F A G q x i = true := by
  simp only [tolerantFamily, decide_eq_true_eq]

theorem tolerantFamily_false {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantFamily T label F A G q x = false ↔
      ∀ i, tolerantRow T label F A G q x i = false := by
  simp [tolerantFamily]

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

def MBound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j k : Fin h) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false → (flipsTo (F i) false x).card ≤ v

def PBound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j k : Fin h) (v : ℕ) : Prop :=
  ∀ x, F i x = true → F j x = false → (flipsTo (F k) true x).card ≤ v

def DBound {h : ℕ} (F : Fin h → (I → Bool) → Bool) (i j k l : Fin h) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false →
    ((flipsTo (F i) false x) ∪ (flipsTo (F l) true x)).card ≤ v













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





def criticalGuards (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (I → Bool) → Bool) (g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) : Finset (Fin k) :=
  if (failedGuards T label F g x v).card = q then
    (Finset.univ.filter (T.Adj v)) \ failedGuards T label F g x v
  else ∅















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

def cutoffs : Array Nat := #[23,30,37,43,49,54,60,65,71]
def guardCaps : Array Nat := #[20,28,34,40,46,53,59,64,70]
def targetCaps : Array Nat := #[20,29,35,41,47,53,59,64,70]
def cutoff (q : Nat) : Nat := cutoffs[q]?.getD 0
def guardCap (q : Nat) : Nat := guardCaps[q]?.getD 0
def targetCap (q : Nat) : Nat := targetCaps[q]?.getD 0

def markedCap (q m : Nat) : Nat :=
  if q = 1 ∧ m = 3 then 23 else
  if q = 2 ∧ m = 4 then 27 else
  if q = 3 ∧ m = 5 then 30 else
  if q = 3 ∧ m = 6 then 28 else
  if q = 4 ∧ m = 6 then 33 else
  if q = 3 ∧ m = 7 then 26 else 1000000000

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
    let tt := if q = 1 ∧ u ≥ 2 then min tt 28 else tt
    let tt := if q = 1 ∧ u ≥ 3 then min tt 26 else tt
    let tt := if q = 1 ∧ m ≥ 2 then min tt 26 else tt
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
    let z := max (22*bb) (aa+19*bb)
    if qa = q then maximum [z,
      17*bb+max (min (aa+ss) (union v gb ga ta tb)) (aa+jj),
      19*bb+ss,20*bb+jj,17*bb+ss+jj,18*bb+2*jj,17*bb+3*jj]
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

def candidateTotalCap (q m u : ℕ) : ℕ :=
  let t := if m > 0 then min (cutoff q-m) (guardCap q) else cutoff q-1
  let tt := if u > 0 then min t (targetCap q) else t
  let tt := if q=1 ∧ u≥2 then min tt 28 else tt
  let tt := if q=1 ∧ u≥3 then min tt 26 else tt
  let tt := if q=1 ∧ m≥2 then min tt 26 else tt
  if q=2 ∧ m≥2 then min tt 33 else tt





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

def positiveCaseCost (q m u a b s j : ℕ) : ℕ :=
  let E := m*(q+1)-m.choose 2
  let L := (u*m+u.choose 2)-q*u
  let save := L-u
  let intr := min (m.choose 2) (2*m)
  u*a+deletionCost (markedCap q m) (candidateTotalCap q m u-u)
    (E-save) (intr+min u save) (E-L) b s j



def booleanCase (q m u : ℕ) : Case :=
  let L := (u*m+u.choose 2)-q*u
  ⟨m,u,candidateTotalCap q m u,m*(q+1)-m.choose 2,
    min (m.choose 2) (2*m),L,L-u,markedCap q m⟩







end ZT
end
end z61



/- Def_Paley11987Support_041.lean -/
set_option autoImplicit false
set_option Elab.async false
section z62

set_option maxHeartbeats 5000000
namespace ZT

def zeroCost (a b s j d : ℕ) : ℕ :=
  max (22*b) (max (a+19*b)
    (max (17*b+max (min (a+s) d) (a+j))
      (max (19*b+s) (max (20*b+j)
        (max (17*b+s+j) (max (18*b+2*j) (17*b+3*j)))))))







end ZT
end z62



end ThreeBoundOrdinaryArchive


