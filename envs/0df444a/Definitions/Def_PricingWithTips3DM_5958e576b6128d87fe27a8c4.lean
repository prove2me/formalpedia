-- Prove2me | Definitions.Def_PricingWithTips3DM_5958e576b6128d87fe27a8c4
-- name    : PricingWithTips3DM_5958e576b6128d87fe27a8c4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:48:35.085756+00:00
-- url     : https://prove2.me/theorems/ad3f7f2e-d309-4a76-8522-921e35c8be0a
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_Certified3DM_Bridge
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_3b6a88d9be5918e3cb96dca9
import Definitions.Def_PricingWithTips_Finset3DM
import Theorems.Thm_PricingWithTips_finset3DM_iff_allocation3DM
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.Certified3DM

open Hardness Hardness.Cert

/-- Turn the concrete output of the certified SAT gadget into the incidence
table representation used by the pricing mission.  The SAT gadget produces
three coordinate lists of equal length; the first list fixes the common
dimension. -/
def concreteThreeDM (q : Matching3DTy.denote) : ThreeDMInstance :=
  ⟨q.1.length, fun b s d => decide ((b.1, s.1, d.1) ∈ q.2.2.2)⟩

/-- The actual executable SAT-to-mission-3DM map.  Unlike the earlier
semantic normalization, this is definitionally the evaluator of the
polynomial certificate-language program followed by a linear view change. -/
def certifiedSatToThreeDM (x : SatTy.denote) : ThreeDMInstance :=
  concreteThreeDM (satToMatching3DCode.eval x)

theorem sat_output_lengths (x : SatTy.denote) :
    (satToMatching3DCode.eval x).2.1.length =
        (satToMatching3DCode.eval x).1.length ∧
      (satToMatching3DCode.eval x).2.2.1.length =
        (satToMatching3DCode.eval x).1.length := by
  have hE := SatToMatching3DCode.length_extElems x
  have hS := SatToMatching3DCode.length_slotElems x
  have harith :
      ((vsOf x).length + 1) * x.length +
          (x.length + x.length * (vsOf x).length) =
        ((vsOf x).length + 1) * (x.length * 2) := by
    ring
  have h : (satToMatching3DCode.eval x).2.1.length =
      (satToMatching3DCode.eval x).1.length := by
    change (SatToMatching3DCode.slotElems.eval x).length =
      (SatToMatching3DCode.extElems.eval x).length
    rw [hS, hE, harith]
  exact ⟨h, h⟩

theorem matching3D_concrete_iff_threeDM
    (q : Matching3DTy.denote)
    (hx : q.2.1.length = q.1.length)
    (hy : q.2.2.1.length = q.1.length) :
    Concrete.MATCHING_3D q ↔ ThreeDMYes (concreteThreeDM q) := by
  rcases q with ⟨ws, xs, ys, ts⟩
  let q : Matching3DTy.denote := (ws, xs, ys, ts)
  let ex : Fin xs.length ≃ Fin ws.length := finCongr hx
  let ey : Fin ys.length ≃ Fin ws.length := finCongr hy
  let I : Matching3DInstance :=
    { W := Fin ws.length
      X := Fin xs.length
      Y := Fin ys.length
      triples := Finset.univ.filter fun t =>
        ((t.1 : ℕ), (t.2.1 : ℕ), (t.2.2 : ℕ)) ∈ ts }
  let T : Finset (ThreeDMTriple q.1.length) :=
    Finset.univ.filter fun t =>
      ((t.1 : ℕ), (t.2.1 : ℕ), (t.2.2 : ℕ)) ∈ q.2.2.2
  let J : Matching3DInstance :=
    { W := Fin q.1.length
      X := Fin q.1.length
      Y := Fin q.1.length
      triples := T }
  have hrename : MATCHING_3D I ↔
      MATCHING_3D J := by
    apply matching3D_iff_of_equiv (I := I) (J := J)
      (Equiv.refl _) ex ey
    rintro ⟨w, x, y⟩
    change Fin ws.length at w
    change Fin xs.length at x
    change Fin ys.length at y
    simp only [q, I, J, T, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor <;> intro h
    · rw [show (ex x).val = x.val by rfl,
        show (ey y).val = y.val by rfl]
      exact h
    ·
      rw [← show (ex x).val = x.val by rfl,
        ← show (ey y).val = y.val by rfl]
      exact h
  rw [show Concrete.MATCHING_3D q = MATCHING_3D I by rfl,
    hrename]
  rw [show ThreeDMYes (concreteThreeDM q) =
      HasPerfect3DMatching q.1.length
        (fun b s d => decide ((b.1, s.1, d.1) ∈ q.2.2.2)) from rfl]
  change MATCHING_3D J ↔ _
  change HasPerfectFinset3DM q.1.length T ↔ _
  simpa [T, Finset.mem_filter] using
    (PricingWithTips.finset3DM_iff_allocation3DM q.1.length T)

theorem concrete_sat_iff_certifiedThreeDM (x : SatTy.denote) :
    Concrete.SAT x ↔ ThreeDMYes (certifiedSatToThreeDM x) := by
  have hlen := sat_output_lengths x
  exact (satToMatching3DCertified.correct x).trans
    (matching3D_concrete_iff_threeDM _ hlen.1 hlen.2)

end PricingWithTips.Certified3DM


