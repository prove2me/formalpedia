-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBound_concl_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:48.126484+00:00
-- url     : https://prove2.me/submissions/2eaa61c5-7cf3-442f-a670-76a7fe21fe20

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Theorems.Thm_AaronsonAmbainis_Bridge_diffSet_comp_equiv

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (e : ι ≃ κ) (f : Cube ι → ℝ) (B : ℝ)
    (h : ∃ c : Cube κ → κ → ℝ,
      (∀ x y, |f (fun i => x (e i)) - f (fun i => y (e i))| ≤ ∑ k ∈ diffSet x y, c x k) ∧
      (∀ x, ∑ k, c x k ≤ B)) :
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧ (∀ x, ∑ i, c x i ≤ B) := by
  obtain ⟨c, hc1, hc2⟩ := h
  refine ⟨fun x i => c (fun k => x (e.symm k)) (e i), fun x y => ?_, fun x => ?_⟩
  · have h1 := hc1 (fun k => x (e.symm k)) (fun k => y (e.symm k))
    simp only [Equiv.symm_apply_apply] at h1
    rw [diffSet_comp_equiv, Finset.sum_map] at h1
    exact h1
  · have h2 := hc2 (fun k => x (e.symm k))
    rw [← Equiv.sum_comp e] at h2
    exact h2
end AaronsonAmbainis.Bridge
