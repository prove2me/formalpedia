-- Prove2me | Definitions.Def_PricingWithTips3DM_e7e44ed57595d80dbeb263ea
-- name    : PricingWithTips3DM_e7e44ed57595d80dbeb263ea
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:36:51.678054+00:00
-- url     : https://prove2.me/theorems/fa8c186f-317d-4575-8f45-cc77509279ad
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_External3DM_Bridge
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_e5bee0ce4f35f592b340b7b1
import Definitions.Def_PricingWithTips_Finset3DM
import Theorems.Thm_PricingWithTips_finset3DM_iff_allocation3DM
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.External3DM

open Hardness

def extToFin (n m : ℕ) :
    Sat3dm.Ext n m ≃ Fin ((n + 1) * (m * 2)) :=
  ((Equiv.refl (Fin (n + 1))).prodCongr
      ((Equiv.refl (Fin m)).prodCongr finTwoEquiv.symm)).trans
    (((Equiv.refl (Fin (n + 1))).prodCongr finProdFinEquiv).trans
      finProdFinEquiv)

def slotToFin (n m : ℕ) :
    Sat3dm.Slot n m ≃ Fin ((n + 1) * m + (m + m * n)) :=
  (((finProdFinEquiv (m := n + 1) (n := m)).sumCongr
      ((Equiv.refl (Fin m)).sumCongr
        (finProdFinEquiv (m := m) (n := n)))).trans
    ((Equiv.refl (Fin ((n + 1) * m))).sumCongr finSumFinEquiv)).trans
      finSumFinEquiv

theorem satToMatching3D_card_W_eq_X (x : SatInstance) :
    Fintype.card (satToMatching3DInstance x).W =
      Fintype.card (satToMatching3DInstance x).X := by
  change Fintype.card (Sat3dm.Ext (cnfVars x.φ).length x.φ.length) =
    Fintype.card (Sat3dm.Slot (cnfVars x.φ).length x.φ.length)
  rw [Fintype.card_congr (extToFin _ _),
    Fintype.card_congr (slotToFin _ _)]
  simp only [Fintype.card_fin]
  ring

theorem satToMatching3D_card_W_eq_Y (x : SatInstance) :
    Fintype.card (satToMatching3DInstance x).W =
      Fintype.card (satToMatching3DInstance x).Y := by
  change Fintype.card (Sat3dm.Ext (cnfVars x.φ).length x.φ.length) =
    Fintype.card (Sat3dm.Slot (cnfVars x.φ).length x.φ.length)
  rw [Fintype.card_congr (extToFin _ _),
    Fintype.card_congr (slotToFin _ _)]
  simp only [Fintype.card_fin]
  ring

def satDimension (x : SatInstance) : ℕ :=
  ((cnfVars x.φ).length + 1) * (x.φ.length * 2)

def satWEquiv (x : SatInstance) :
    (satToMatching3DInstance x).W ≃ Fin (satDimension x) :=
  extToFin _ _

theorem sat_slot_count_eq_dimension (x : SatInstance) :
    ((cnfVars x.φ).length + 1) * x.φ.length +
        (x.φ.length + x.φ.length * (cnfVars x.φ).length) =
      satDimension x := by
  simp only [satDimension]
  ring

def satXEquiv (x : SatInstance) :
    (satToMatching3DInstance x).X ≃ Fin (satDimension x) :=
  (slotToFin _ _).trans (finCongr (sat_slot_count_eq_dimension x))

def satYEquiv (x : SatInstance) :
    (satToMatching3DInstance x).Y ≃ Fin (satDimension x) :=
  (slotToFin _ _).trans (finCongr (sat_slot_count_eq_dimension x))

def satNormalizedTriples (x : SatInstance) :
    Finset (ThreeDMTriple (satDimension x)) :=
  (satToMatching3DInstance x).triples.image
    ((satWEquiv x).prodCongr ((satXEquiv x).prodCongr (satYEquiv x)))

def satNormalized3DM (x : SatInstance) : ThreeDMInstance :=
  ⟨satDimension x,
    fun b s d => decide ((b, s, d) ∈ satNormalizedTriples x)⟩

def satNormalizedMatchingInstance (x : SatInstance) :
    Matching3DInstance where
  W := Fin (satDimension x)
  X := Fin (satDimension x)
  Y := Fin (satDimension x)
  triples := satNormalizedTriples x

theorem matching3D_normalized_iff (x : SatInstance) :
    MATCHING_3D (satToMatching3DInstance x) ↔
      MATCHING_3D (satNormalizedMatchingInstance x) := by
  let e := (satWEquiv x).prodCongr ((satXEquiv x).prodCongr (satYEquiv x))
  apply matching3D_iff_of_equiv (satWEquiv x) (satXEquiv x) (satYEquiv x)
  intro t
  change t ∈ (satToMatching3DInstance x).triples ↔
    e t ∈ (satToMatching3DInstance x).triples.image e
  constructor
  · exact Finset.mem_image_of_mem e
  · intro ht
    obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp ht
    have hut : u = t := e.injective heu
    simpa [hut] using hu

theorem matching3D_finset_iff (x : SatInstance) :
    MATCHING_3D (satNormalizedMatchingInstance x) ↔
      HasPerfectFinset3DM
        (satDimension x)
        (satNormalizedTriples x) := by
  rfl

theorem sat_iff_normalized3DM (x : SatInstance) :
    SAT x ↔ ThreeDMYes (satNormalized3DM x) := by
  calc
    SAT x ↔ MATCHING_3D (satToMatching3DInstance x) :=
      satToMatching3D.correct x
    _ ↔ MATCHING_3D (satNormalizedMatchingInstance x) :=
      matching3D_normalized_iff x
    _ ↔ HasPerfectFinset3DM
        (satDimension x)
        (satNormalizedTriples x) := matching3D_finset_iff x
    _ ↔ HasPerfect3DMatching
        (satDimension x)
        (fun b s d => decide ((b, s, d) ∈ satNormalizedTriples x)) :=
      finset3DM_iff_allocation3DM _ _
    _ ↔ ThreeDMYes (satNormalized3DM x) := by rfl

end PricingWithTips.External3DM


