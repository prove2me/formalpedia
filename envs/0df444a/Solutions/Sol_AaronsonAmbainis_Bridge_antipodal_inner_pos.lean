-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.antipodal_inner_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:36:43.700751+00:00
-- url     : https://prove2.me/submissions/33261ddf-01a4-49de-a09f-6b17db553854

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Theorems.Thm_AaronsonAmbainis_Bridge_diffSet_antipode
import Theorems.Thm_AaronsonAmbainis_mem_zone
import Theorems.Thm_AaronsonAmbainis_overlap_pos


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {g : Cube ι → Bool} {u : Cube ι} (hu : u ∈ zone g) {w : ι → ℝ}
    (hw : ∀ j, 0 < w j) {lam : Cube ι → ι → ℝ}
    (h1 : IsRow g u (lam u)) (h2 : IsRow g (antipode u) (lam (antipode u))) :
    0 < ∑ j, w j * lam u j * lam (antipode u) j := by
  have hu' : g u = true ∧ g (antipode u) = false := AaronsonAmbainis.mem_zone.mp hu
  have hne : g u ≠ g (antipode u) := by
    rw [hu'.1, hu'.2]
    exact fun h => Bool.noConfusion h
  have h := AaronsonAmbainis.overlap_pos hne h1 h2 hw
  rw [diffSet_antipode] at h
  exact h
end AaronsonAmbainis.Bridge
