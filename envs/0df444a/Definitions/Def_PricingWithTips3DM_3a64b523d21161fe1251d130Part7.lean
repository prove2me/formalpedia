-- Prove2me | Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part7
-- name    : PricingWithTips3DM_3a64b523d21161fe1251d130Part7
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T08:14:32.888973+00:00
-- url     : https://prove2.me/theorems/e937e030-8a88-484b-82ed-0dc46adc31a6
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShape3DM.Part7
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3a64b523d21161fe1251d130Part6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShape3DM

open Hardness Hardness.Cert Hardness.Sat3dm

theorem matching_normalized_iff (input : List CLRS.Chapter34.CNFSym) :
    MATCHING_3D (abstractInstance input) ↔
      MATCHING_3D (normalizedInstance input) := by
  let e := (wEquiv input).prodCongr
    ((slotEquiv input).prodCongr (slotEquiv input))
  let f := fun t : Sat3dm.Trip (variableList input).length
      (paddedCNF input).length =>
    ((wMap input) t.1, ((slotMap input) t.2.1, (slotMap input) t.2.2))
  have hef : ∀ t, e t = f t := by
    rintro ⟨w, x, y⟩
    apply Prod.ext
    · apply Fin.ext
      exact SatToMatching3DCode.extEquivFin_val _ _ w
    · apply Prod.ext <;> apply Fin.ext
      · exact SatToMatching3DCode.slotEquivFin_val _ _ x
      · exact SatToMatching3DCode.slotEquivFin_val _ _ y
  apply matching3D_iff_of_equiv (wEquiv input) (slotEquiv input) (slotEquiv input)
  intro t
  change t ∈ triples input ↔ e t ∈ (triples input).image f
  rw [hef t]
  constructor
  · exact Finset.mem_image_of_mem f
  · intro ht
    obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp ht
    have hut : u = t := e.injective ((hef u).trans (heu.trans (hef t).symm))
    subst u
    exact hu
end PricingWithTips.FixedShape3DM


