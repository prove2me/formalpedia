-- Prove2me | Definitions.Def_BS2_b3ba934b_LabelCard
-- name    : BS2_b3ba934b_LabelCard
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:36:13.831566+00:00
-- url     : https://prove2.me/theorems/28db4834-5ce4-4ca9-a2da-c5ecaac7dee7
-- title:
--   Sensitivity separation: LabelCard (complete source module)
-- statement:
--   Complete Lean source module `LabelCard` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/LabelCard.lean; original SHA-256 27e11699fa999e45ffee314d1c9d6f1efecded01c6c4f82d86bbb2c54dfecaf7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Reassembled from supplied accepted Prove2me source proofs. See provenance.json. -/
import Definitions.Def_BS2_b3ba934b_LabelDefinitions

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







theorem _root_.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges (R : V → V → Prop)
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


