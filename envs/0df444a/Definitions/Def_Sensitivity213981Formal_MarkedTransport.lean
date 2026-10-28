-- Prove2me | Definitions.Def_Sensitivity213981Formal_MarkedTransport
-- name    : Sensitivity213981Formal_MarkedTransport
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:05:22.217269+00:00
-- url     : https://prove2.me/theorems/82495310-1165-4273-b28b-b3d79acadb01
-- title:
--   Marked Transport — sensitivity certificate definitions
-- statement:
--   The definitions for Marked Transport in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundArcAverage.markedPairMap`, `ThreeBoundArcAverage.markedIndexMap`, `ThreeBoundArcAverage.markedIndexMap_markers`, `ThreeBoundArcAverage.markedIndexMap_targets`, `ThreeBoundArcAverage.outOn_map`, `ThreeBoundArcAverage.markedSupport_map`, `ThreeBoundArcAverage.markedIndex_support`, `ThreeBoundArcAverage.MarkedPair`, `ThreeBoundArcAverage.markedIndex_weight`, `ThreeBoundArcAverage.instFintypeMarkedPair`, `ThreeBoundArcAverage.markedPairEquiv`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MarkedTransport.lean, lines 1–91.

import Definitions.Def_Sensitivity213981Formal_ArcAverage
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
/- Finite transport of the marked-event support and orientation weight. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundArcAverage
open Sensitivity10007Labeling ZL ZL.RowCounting
open scoped Classical BigOperators
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def MarkedPair (V : Type*) [DecidableEq V] (a m : ℕ) :=
  {s : Finset V × Finset V // s.1.card=m ∧ s.2.card=a ∧ Disjoint s.1 s.2}

instance _root_.Sensitivity213981Formal.ThreeBoundArcAverage.instFintypeMarkedPair (a m : ℕ) : Fintype (MarkedPair V a m) := by
  unfold MarkedPair
  infer_instance

def markedPairEquiv (a m : ℕ) : MarkedPair V a m≃MarkedIndex V a m where
  toFun s :=
    ⟨⟨s.val.1,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,s.property.1⟩⟩,
      ⟨s.val.2,Finset.mem_powersetCard.mpr
        ⟨Finset.subset_compl_iff_disjoint_left.mpr s.property.2.2,s.property.2.1⟩⟩⟩
  invFun I := ⟨(I.1.val,I.2.val),markedIndex_cardM a m I,markedIndex_cardA a m I,
    (markedIndex_disjoint a m I).symm⟩
  left_inv s := by cases s; rfl
  right_inv I := by rcases I with ⟨⟨M,hM⟩,⟨A,hA⟩⟩; rfl

def markedPairMap (a m : ℕ) (e : V≃V) : MarkedPair V a m≃MarkedPair V a m where
  toFun s := ⟨(s.val.1.map e.toEmbedding,s.val.2.map e.toEmbedding),by
    simpa only [Finset.card_map,Finset.disjoint_map] using s.property⟩
  invFun s := ⟨(s.val.1.map e.symm.toEmbedding,s.val.2.map e.symm.toEmbedding),by
    simpa only [Finset.card_map,Finset.disjoint_map] using s.property⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext <;> simp only [← Equiv.finsetCongr_apply,← Equiv.finsetCongr_symm,
      Equiv.symm_apply_apply]
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext <;> simp only [← Equiv.finsetCongr_apply,← Equiv.finsetCongr_symm,
      Equiv.apply_symm_apply]

def markedIndexMap (a m : ℕ) (e : V≃V) : MarkedIndex V a m≃MarkedIndex V a m :=
  (markedPairEquiv a m).symm.trans ((markedPairMap a m e).trans (markedPairEquiv a m))

@[simp] theorem markedIndexMap_markers (a m : ℕ) (e : V≃V) (I : MarkedIndex V a m) :
    (markedIndexMap a m e I).1.val=I.1.val.map e.toEmbedding := rfl

@[simp] theorem markedIndexMap_targets (a m : ℕ) (e : V≃V) (I : MarkedIndex V a m) :
    (markedIndexMap a m e I).2.val=I.2.val.map e.toEmbedding := rfl

theorem outOn_map (R : V → V → Prop) (e : V≃V)
    (hR : ∀ x y, R (e x) (e y) ↔ R x y) (M : Finset V) (z : V) :
    outOn R (M.map e.toEmbedding) (e z)=(outOn R M z).map e.toEmbedding := by
  ext y
  obtain ⟨y,rfl⟩ := e.surjective y
  simp only [outOn,Finset.mem_filter,Finset.mem_map_equiv,Equiv.symm_apply_apply,hR]

theorem markedSupport_map (R : V → V → Prop) (e : V≃V)
    (hR : ∀ x y, R (e x) (e y) ↔ R x y) (A M : Finset V) :
    markedSupport R (A.map e.toEmbedding) (M.map e.toEmbedding)=
      (markedSupport R A M).map (e.prodCongr e).toEmbedding := by
  ext xy
  rcases xy with ⟨x,y⟩
  obtain ⟨x,rfl⟩ := e.surjective x
  obtain ⟨y,rfl⟩ := e.surjective y
  simp only [markedSupport,internalEdges,crossEdges,Finset.mem_union,Finset.mem_filter,
    Finset.mem_product,Finset.mem_map_equiv,Equiv.symm_apply_apply,hR]
  simp only [Equiv.prodCongr_symm,Equiv.prodCongr_apply,Prod.map_apply,Equiv.symm_apply_apply]

theorem markedIndex_support (R : V → V → Prop) (a m : ℕ) (e : V≃V)
    (hR : ∀ x y, R (e x) (e y) ↔ R x y) (I : MarkedIndex V a m) :
    markedSupport R (markedIndexMap a m e I).2.val (markedIndexMap a m e I).1.val=
      (markedSupport R I.2.val I.1.val).map (e.prodCongr e).toEmbedding :=
  markedSupport_map R e hR I.2.val I.1.val

theorem markedIndex_weight (R : V → V → Prop) (a m q : ℕ) (C : ℕ → ℚ) (e : V≃V)
    (hR : ∀ x y, R (e x) (e y) ↔ R x y) (I : MarkedIndex V a m) :
    (∏ z∈(markedIndexMap a m e I).2.val,
      orientationWeight q C (outOn R (markedIndexMap a m e I).1.val z).card)=
      ∏ z∈I.2.val, orientationWeight q C (outOn R I.1.val z).card := by
  rw [markedIndexMap_targets,markedIndexMap_markers,Finset.prod_map]
  simp only [Equiv.toEmbedding_apply,outOn_map R e hR,Finset.card_map]

end
end ThreeBoundArcAverage




end
end Sensitivity213981Formal


