-- Prove2me | Definitions.Def_Sensitivity213981Formal_LabelCard
-- name    : Sensitivity213981Formal_LabelCard
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:35:29.279539+00:00
-- url     : https://prove2.me/theorems/6662b6d2-a82d-41be-9a71-5991d7151c90
-- title:
--   Label Card — sensitivity certificate definitions
-- statement:
--   The definitions for Label Card in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; LabelCard.lean, lines 1–95.

import Definitions.Def_Sensitivity213981Formal_LabelDefinitions
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
/- Reassembled from supplied accepted Prove2me source proofs. See provenance.json. -/


namespace Sensitivity10007Labeling


/- Source: Sol_Paley11987Verified_CompactLabeling_card_internalEdges.lean -/
set_option autoImplicit false
set_option Elab.async false
section z0

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]







theorem _root_.Sensitivity213981Formal.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (S : Finset V) : (internalEdges R S).card = S.card.choose 2 := by
  have hne {x y : V} (h : R x y) : x ≠ y := by
    rintro rfl
    exact hloop x h
  have hrev {x y : V} (h : R x y) : ¬ R y x := (htour x y (hne h)).mp h
  let U := internalEdges R S
  let W := (S ×ˢ S).filter fun p => R p.2 p.1
  have hd : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact hrev (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion W hd = S.offDiag := by
    ext ⟨x,y⟩
    simp only [Finset.mem_disjUnion, U, W, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hx,hy⟩,h⟩ | ⟨⟨hx,hy⟩,h⟩)
      · exact ⟨hx,hy,hne h⟩
      · exact ⟨hx,hy,(hne h).symm⟩
    · rintro ⟨hx,hy,hxy⟩
      by_cases h : R x y
      · exact Or.inl ⟨⟨hx,hy⟩,h⟩
      · exact Or.inr ⟨⟨hx,hy⟩,(htour y x hxy.symm).mpr h⟩
  have hs : U.card = W.card := Finset.card_equiv (Equiv.prodComm V V) (by
    intro p
    simp only [U,W,internalEdges,Finset.mem_filter,Finset.mem_product,
      Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

























end
end ZL
end
end z0

end Sensitivity10007Labeling

end
end Sensitivity213981Formal


