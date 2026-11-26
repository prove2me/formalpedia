-- Prove2me | solution 1 for Auto.aux_crossIndices_b_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:59.728804+00:00
-- url     : https://prove2.me/submissions/51ec5c14-d23b-4a4e-b503-d060f4fd480b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {b : Fin (J + 1) → ℤ}
    (hb : Monotone b) :
    Function.Injective (fun j : aux_crossIndices b ↦ b j.1.castSucc) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hcross := Finset.mem_filter.mp i.2 |>.2
    have hsuc_le : i.1.succ ≤ j.1.castSucc :=
      Fin.succ_le_castSucc_iff.mpr hijlt
    have hlt : b i.1.castSucc < b j.1.castSucc := hcross.trans_le (hb hsuc_le)
    exact hlt.ne hij
  · have hcross := Finset.mem_filter.mp j.2 |>.2
    have hsuc_le : j.1.succ ≤ i.1.castSucc :=
      Fin.succ_le_castSucc_iff.mpr hjilt
    have hlt : b j.1.castSucc < b i.1.castSucc := hcross.trans_le (hb hsuc_le)
    exact hlt.ne hij.symm
end Auto
