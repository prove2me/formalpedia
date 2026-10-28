-- Prove2me | Definitions.Def_Sensitivity213303_LabelDefinitions
-- name    : Sensitivity213303_LabelDefinitions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:52:51.496311+00:00
-- url     : https://prove2.me/theorems/93ff34b8-297c-4b11-b3e3-cd1fc991cead
-- title:
--   Finite bad-event families for a jointly avoiding tournament labeling
-- statement:
--   An atomic event fixes a finite set of binary edge labels. Supported event families encode ordinary low-mismatch sets, marked sets with additional guard budgets, coherent sets with a source, and coherent sets with two dominators. JointExclusions requires one labeling to avoid every event in all these families. The numerical specialization uses a tournament on 10007 vertices with degree 5003 and pairwise common-out count 2501, local-lemma activity factor 181/180, and ordinary thresholds [23,30,37,43,49,54,60,65,71]. The definitions include event supports, complementary colorings, local probabilities, incidence weights and the finite sums needed to bound the total dependency load.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module LabelDefinitions; source SHA256 e8e4efc1c8e8c93430184568dfcbc1cb9c539b0cd29ba4453f1134647d2a7ae5.

/- Reassembled from supplied accepted Prove2me source proofs. See provenance.json. -/
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
namespace Sensitivity10007Labeling.CompactAtomicLLL
end Sensitivity10007Labeling.CompactAtomicLLL
namespace Sensitivity10007Labeling.SensitivityLabelCache12607.SensitivityLLL
end Sensitivity10007Labeling.SensitivityLabelCache12607.SensitivityLLL
namespace Sensitivity10007Labeling.ZL
end Sensitivity10007Labeling.ZL
namespace Sensitivity10007Labeling.ZL.RowCounting
end Sensitivity10007Labeling.ZL.RowCounting


namespace Sensitivity10007Labeling


/- Source: Def_Paley11987Support_000.lean -/
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



/- Source: Def_Paley11987Support_001.lean -/
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



/- Source: Def_Paley11987Support_002.lean -/
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



/- Source: Def_Paley11987Support_003.lean -/
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



/- Source: Def_Paley11987Support_004.lean -/
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



/- Source: Def_Paley11987Support_005.lean -/
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



/- Source: Def_Paley11987Support_006.lean -/
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



/- Source: Def_Paley11987Support_007.lean -/
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



/- Source: Def_Paley11987Support_008.lean -/
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



/- Source: Def_Paley11987Support_009.lean -/
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



/- Source: Def_Paley11987Support_010.lean -/
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



/- Source: Def_Paley11987Support_011.lean -/
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



/- Source: Def_Paley11987Support_012.lean -/
set_option autoImplicit false
set_option Elab.async false
section z16

section
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 32768
open scoped Classical BigOperators

namespace CompactLabeling10007
open ZL ZL.RowCounting

def N : ℕ := 10007
def degree : ℕ := 5003
def common : ℕ := 2501
def lam : ℚ := 181/180
def scale : ℕ := 1000000000000000000

def ordinaryCutoffs : List ℕ := [23,30,37,43,49,54,60,65,71]
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
  ((degree.choose 19 + common * degree.choose 18 : ℕ) : ℚ) *
    ((2 : ℚ)^20 / (2 : ℚ)^(21).choose 2) * lam^((21).choose 2) / 2

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

def marked0 : MarkedParameters := ⟨1,29,1,false,(1053/1000 : ℚ),[1,(15/2 : ℚ)],(15/2 : ℚ),(-11/2 : ℚ),0,(15/2 : ℚ),1878255968582⟩
def marked1 : MarkedParameters := ⟨2,35,1,false,(138/125 : ℚ),[1,(821/200 : ℚ),(3646/125 : ℚ)],(3646/125 : ℚ),(-10479/500 : ℚ),0,(3646/125 : ℚ),31253820420987⟩
def marked2 : MarkedParameters := ⟨3,41,1,false,(571/500 : ℚ),[1,(3159/1000 : ℚ),(16519/1000 : ℚ),(96643/1000 : ℚ)],(96643/1000 : ℚ),(-12721/200 : ℚ),0,(96643/1000 : ℚ),40265530883916⟩
def marked3 : MarkedParameters := ⟨4,47,1,false,(293/250 : ℚ),[1,(1357/500 : ℚ),(11763/1000 : ℚ),(7108/125 : ℚ),(72237/250 : ℚ)],(72237/250 : ℚ),(-8761/50 : ℚ),0,(72237/250 : ℚ),1937932176054⟩
def marked4 : MarkedParameters := ⟨1,27,2,false,(131/125 : ℚ),[1,(8223/1000 : ℚ)],(8223/1000 : ℚ),(-6223/1000 : ℚ),(4223/1000 : ℚ),(8223/1000 : ℚ),47028860983740⟩
def marked5 : MarkedParameters := ⟨2,34,2,false,(219/200 : ℚ),[1,(4439/1000 : ℚ),(17249/500 : ℚ)],(17249/500 : ℚ),(-1281/50 : ℚ),(10371/500 : ℚ),(17249/500 : ℚ),9084184004⟩
def marked6 : MarkedParameters := ⟨1,24,3,true,(26691/25000 : ℚ),[1,6],6,-4,2,6,2935944737099⟩
def marked7 : MarkedParameters := ⟨2,28,4,true,(1103/1000 : ℚ),[1,(4139/1000 : ℚ),(14851/500 : ℚ)],(14851/500 : ℚ),(-11851/750 : ℚ),(8851/1500 : ℚ),(14851/500 : ℚ),5862705403127⟩
def marked8 : MarkedParameters := ⟨3,31,5,true,(571/500 : ℚ),[1,(3159/1000 : ℚ),(16519/1000 : ℚ),(96643/1000 : ℚ)],(96643/1000 : ℚ),(-81689/1500 : ℚ),(14947/600 : ℚ),(96643/1000 : ℚ),1087176035863125⟩
def marked9 : MarkedParameters := ⟨3,29,6,true,(571/500 : ℚ),[1,(3159/1000 : ℚ),(16519/1000 : ℚ),(96643/1000 : ℚ)],(96643/1000 : ℚ),(-80643/2000 : ℚ),(64643/6000 : ℚ),(96643/1000 : ℚ),205034567379428⟩
def marked10 : MarkedParameters := ⟨4,34,6,true,(1179/1000 : ℚ),[1,(1317/500 : ℚ),(1369/125 : ℚ),(50993/1000 : ℚ),(248981/1000 : ℚ)],(248981/1000 : ℚ),(-222837/2000 : ℚ),(212693/6000 : ℚ),(248981/1000 : ℚ),708501892467⟩
def marked11 : MarkedParameters := ⟨3,27,7,true,(579/500 : ℚ),[1,(2903/1000 : ℚ),(1708/125 : ℚ),(3593/50 : ℚ)],(3593/50 : ℚ),(-21151/750 : ℚ),(2593/375 : ℚ),(3593/50 : ℚ),150902517168379⟩

def markedParameters : List MarkedParameters := [marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11]
def marked (i : Fin 12) : MarkedParameters := markedParameters.getD i.val marked0
def ordinaryCeilings : List ℕ := [22894154115438,1095416327599945,4351604359981,5841637795285,211442999561,589669702078718,138387601628,20753302926674,63060408]
def ordinaryCeiling (q : Fin 9) : ℚ := (ordinaryCeilings.getD q.val 0 : ℚ)/scale
def sourceCeiling : ℚ := 1646248323999137/scale
def dominatorCeiling : ℚ := 195983874428420/scale
def markedCeiling (i : Fin 12) : ℚ := ((marked i).ceiling : ℚ)/scale

































































































end CompactLabeling10007
end
end z16



/- Source: Def_Paley11987Support_013.lean -/
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



/- Source: Def_Paley11987Support_014.lean -/
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



/- Source: Def_Paley11987Support_015.lean -/
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



/- Source: Def_Paley11987Support_016.lean -/
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



/- Source: Def_Paley11987Support_017.lean -/
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



/- Source: Def_Paley11987Support_018.lean -/
set_option autoImplicit false
set_option Elab.async false
section z28

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped Classical BigOperators
noncomputable section

namespace CompactLabeling10007
open ZL ZL.RowCounting
attribute [local irreducible] N degree common lam
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev FamilyKind := Fin 9 ⊕ (Fin 12 ⊕ Bool)

def Description (R : V → V → Prop) : FamilyKind → Type _
  | .inl q => OrdinaryIndex V (ordinaryA q)
  | .inr (.inl i) => MarkedIndex V (marked i).a (marked i).m
  | .inr (.inr false) => SourceIndex R 20
  | .inr (.inr true) => DominatorIndex R 18

instance descriptionFintype (R : V → V → Prop) (t : FamilyKind) : Fintype (Description R t) := by
  rcases t with q | i | b
  · exact ordinaryIndexFintype (ordinaryA q)
  · exact markedIndexFintype (marked i).a (marked i).m
  · cases b
    · exact sourceIndexFintype R 20
    · exact dominatorIndexFintype R 18

def family (R : V → V → Prop) : (t : FamilyKind) → SupportedFamily (V × V) (Description R t)
  | .inl q => ordinaryFamily R q.val (ordinaryA q)
  | .inr (.inl i) => markedFamily R (marked i).q (marked i).a (marked i).m (marked i).B
  | .inr (.inr false) => sourceFamily R 20
  | .inr (.inr true) => dominatorFamily R 18

def exponent : FamilyKind → ℕ
  | .inl q => (ordinaryA q).choose 2
  | .inr (.inl i) => (marked i).a.choose 2+(marked i).m*(marked i).a
  | .inr (.inr false) => 210
  | .inr (.inr true) => 189

def lowerExponent : FamilyKind → ℕ
  | .inl q => (ordinaryA q).choose 2
  | .inr (.inl i) => (marked i).a.choose 2
  | .inr (.inr false) => 210
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
  source : ∀ I : SourceIndex R 20, ¬ (sourceFamily R 20).bad I ell
  dominator : ∀ I : DominatorIndex R 18, ¬ (dominatorFamily R 18).bad I ell



















end CompactLabeling10007
end
end z28



end Sensitivity10007Labeling


