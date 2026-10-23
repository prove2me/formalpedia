-- Prove2me | Definitions.Def_Paley11987Support_043
-- name    : Paley11987Support_043
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T03:05:19.248501+00:00
-- url     : https://prove2.me/theorems/2f0668d9-65a4-4322-8878-d07116215e24
-- title:
--   Seed families and sensitivity witnesses
-- statement:
--   Defines typed recipes, recursive seed steps, row inputs and lifts, and the block and sensitive-witness structures used to certify lower bounds throughout the construction.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module FiniteProfileSeedFoundation.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfileSeedFoundation, SHA256 2e27fd933c67f1a75c91f2d392d4adcbfd4cab363e35f8142eaaa11b65c94b88

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
import Definitions.Def_Paley11987Support_029
import Definitions.Def_Paley11987Support_030
import Definitions.Def_Paley11987Support_031
import Definitions.Def_Paley11987Support_032
import Definitions.Def_Paley11987Support_033
import Definitions.Def_Paley11987Support_034
import Definitions.Def_Paley11987Support_035
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_037
import Definitions.Def_Paley11987Support_038
import Definitions.Def_Paley11987Support_039
import Definitions.Def_Paley11987Support_040
import Definitions.Def_Paley11987Support_041
import Definitions.Def_Paley11987Support_042

set_option autoImplicit false
set_option Elab.async false
section z74

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical
open OAI.Paper320 Sensitivity2075

namespace CompactFiniteProfileSeeds

structure TypedRecipe (h : ℕ) where
  target : Fin h → Fin h
  guard : Fin h → Fin h
  tolerance : Fin h → ℕ

 def step {h k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (r : TypedRecipe h)
    (F : Fin h → (I → Bool) → Bool) :
    Fin h → (((Fin k × Fin 2) × I) → Bool) → Bool :=
  fun q => tolerantFamily T label F (r.target q) (r.guard q) (r.tolerance q)

 theorem row_false_of_target_false {h k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin h → (I → Bool) → Bool)
    (A G : Fin h) (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (i : Fin k) (c : Fin 2) (hc : F A (recursiveChild x i c) = false) :
    tolerantRow T label F A G q x i = false := by
  apply Bool.eq_false_iff.mpr
  intro hr
  have ht := ((tolerantRow_true T label F A G q x i).mp hr).1 c
  simp [hc] at ht

 theorem step_zero {h k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (r : TypedRecipe h)
    (F : Fin h → (I → Bool) → Bool)
    (hz : ∀ q, F q (fun _ => false) = false) (q : Fin h) :
    step T label r F q (fun _ => false) = false := by
  apply (tolerantFamily_false T label F (r.target q) (r.guard q) (r.tolerance q) _).mpr
  intro i
  apply row_false_of_target_false T label F (r.target q) (r.guard q) (r.tolerance q) _ i 0
  exact hz (r.target q)

 def rowInput {k : ℕ} {I : Type} (i : Fin k) (x : I → Bool) :
    ((Fin k × Fin 2) × I) → Bool := fun p => if p.1.1 = i then x p.2 else false

 @[simp] theorem rowInput_child_same {k : ℕ} {I : Type}
    (i : Fin k) (x : I → Bool) (c : Fin 2) :
    recursiveChild (rowInput i x) i c = x := by
  funext a
  simp [recursiveChild, rowInput]
 theorem rowInput_child_other {k : ℕ} {I : Type}
    (i j : Fin k) (x : I → Bool) (c : Fin 2) (hji : j ≠ i) :
    recursiveChild (rowInput i x) j c = fun _ => false := by
  funext a
  simp [recursiveChild, rowInput, hji]

 theorem step_rowInput_on {h k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (r : TypedRecipe h)
    (F : Fin h → (I → Bool) → Bool)
    (hz : ∀ q, F q (fun _ => false) = false)
    (x : I → Bool) (hon : ∀ q, F q x = true) (i : Fin k) (q : Fin h) :
    step T label r F q (rowInput i x) = true := by
  apply (tolerantFamily_true T label F (r.target q) (r.guard q) (r.tolerance q) _).mpr
  refine ⟨i,(tolerantRow_true T label F (r.target q) (r.guard q) (r.tolerance q) _ i).mpr ⟨?_,?_⟩⟩
  · intro c
    simpa using hon (r.target q)
  · have he : failedGuards T label F (r.guard q) (rowInput i x) i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨_,hij,htrue⟩ := Finset.mem_filter.mp hj
      rw [rowInput_child_other i j x (label i j) (T.ne_of_adj hij).symm, hz] at htrue
      contradiction
    rw [he]
    simp

 def rowLift {k : ℕ} {I : Type} (i : Fin k) (B : Finset I) :
    Finset ((Fin k × Fin 2) × I) :=
  (Finset.univ.product B).map
    ⟨fun p : Fin 2 × I => ((i,p.1),p.2), by
      intro p q hpq
      exact Prod.ext (congrArg (fun z => z.1.2) hpq)
        (congrArg (fun z : (Fin k × Fin 2) × I => z.2) hpq)⟩

 @[simp] theorem mem_rowLift {k : ℕ} {I : Type} (i : Fin k) (B : Finset I)
    (p : (Fin k × Fin 2) × I) : p ∈ rowLift i B ↔ p.1.1 = i ∧ p.2 ∈ B := by
  rcases p with ⟨⟨j,c⟩,a⟩
  unfold rowLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨⟨c',b⟩,hb,hp⟩
    change ((i,c'),b) = ((j,c),a) at hp
    cases hp
    exact ⟨rfl,(Finset.mem_product.mp hb).2⟩
  · rintro ⟨rfl,ha⟩
    exact ⟨(c,a),Finset.mem_product.mpr ⟨Finset.mem_univ _,ha⟩,rfl⟩

 @[simp] theorem rowLift_card {k : ℕ} {I : Type} (i : Fin k) (B : Finset I) :
    (rowLift i B).card = 2*B.card := by simp [rowLift]

 theorem flip_zero_rowLift {k : ℕ} {I : Type} (i : Fin k) (B : Finset I) :
    flip (fun _ => false) (rowLift i B) = rowInput i (flip (fun _ => false) B) := by
  funext p
  simp only [OAI.Paper320.flip, mem_rowLift, Bool.not_false, rowInput]
  split_ifs <;> simp_all

 structure Blocks {h : ℕ} {I : Type} (F : Fin h → (I → Bool) → Bool) (n : ℕ) where
  zero : ∀ q, F q (fun _ => false) = false
  sets : Fin n → Finset I
  nonempty : ∀ i, (sets i).Nonempty
  disjoint : Pairwise fun i j => Disjoint (sets i) (sets j)
  on : ∀ q i, F q (flip (fun _ => false) (sets i)) = true

 def Blocks.stage {h k : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (r : TypedRecipe h)
    (F : Fin h → (I → Bool) → Bool) {n : ℕ} (w : Blocks F n) :
    Blocks (step T label r F) (k*n) where
  zero q := step_zero T label r F w.zero q
  sets i := rowLift (finProdFinEquiv.symm i).1 (w.sets (finProdFinEquiv.symm i).2)
  nonempty i := by
    obtain ⟨a,ha⟩ := w.nonempty (finProdFinEquiv.symm i).2
    exact ⟨(((finProdFinEquiv.symm i).1,0),a),(mem_rowLift _ _ _).mpr ⟨rfl,ha⟩⟩
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hi := (mem_rowLift _ _ _).mp hp
    have hj := (mem_rowLift _ _ _).mp hq
    have he : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 := hi.1.symm.trans hj.1
    have hne : (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 := by
      intro hh
      exact hij (finProdFinEquiv.symm.injective (Prod.ext he hh))
    exact Finset.disjoint_left.mp (w.disjoint hne) hi.2 hj.2
  on q i := by
    rw [flip_zero_rowLift]
    exact step_rowInput_on T label r F w.zero _ (fun j => w.on j _) _ q

 

 structure SensitiveWitness {h : ℕ} {I : Type}
    (F : Fin h → (I → Bool) → Bool) (n : ℕ) where
  input : I → Bool
  bits : Finset I
  card : bits.card = n
  on : ∀ q, F q input = true
  off : ∀ q a, a ∈ bits → F q (flip input {a}) = false

 def SensitiveWitness.stage {h k : ℕ} {I : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (r : TypedRecipe h) (F : Fin h → (I → Bool) → Bool)
    (hz : ∀ q, F q (fun _ => false) = false) {n : ℕ}
    (w : SensitiveWitness F n) (i : Fin k) :
    SensitiveWitness (step T label r F) (2*n) where
  input := rowInput i w.input
  bits := rowLift i w.bits
  card := by simp [w.card]
  on q := step_rowInput_on T label r F hz w.input w.on i q
  off q p hp := by
    rcases p with ⟨⟨j,c⟩,a⟩
    obtain ⟨hji,ha⟩ := (mem_rowLift _ _ _).mp hp
    change j = i at hji
    subst j
    apply (tolerantFamily_false T label F (r.target q) (r.guard q) (r.tolerance q) _).mpr
    intro j
    by_cases hji : j = i
    · subst j
      apply row_false_of_target_false T label F (r.target q) (r.guard q) (r.tolerance q) _ i c
      rw [recursiveChild_flip_same,rowInput_child_same]
      exact w.off (r.target q) a ha
    · apply row_false_of_target_false T label F (r.target q) (r.guard q) (r.tolerance q) _ j 0
      rw [recursiveChild_flip_other _ i j c 0 a (by
        intro he
        exact hji (congrArg Prod.fst he)),rowInput_child_other i j w.input 0 hji]
      exact hz (r.target q)

 

end CompactFiniteProfileSeeds
end
end z74


