-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegLE_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:42.99169+00:00
-- url     : https://prove2.me/submissions/83ee06c3-c112-4c31-be20-9a359018f39c

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Theorems.Thm_AaronsonAmbainis_Bridge_mon_affine

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {φ ψ : Bool → ℝ} {α β : ℝ} (hψ : ∀ b, ψ b = β * φ b + α)
    {f : Cube ι → ℝ} {d : ℕ} (h : HasDegLE ψ f d) : HasDegLE φ f d := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun T => ∑ S : Finset ι, if T ⊆ S then c S * (β ^ T.card * α ^ (S \ T).card) else 0,
    fun T hT => ?_, fun x => ?_⟩
  · refine Finset.sum_eq_zero (fun S _ => ?_)
    split_ifs with hTS
    · rw [hc S (lt_of_lt_of_le hT (Finset.card_le_card hTS)), zero_mul]
    · rfl
  · rw [hf x]
    simp only [mon_affine hψ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun T _ => Finset.sum_congr rfl (fun S _ => ?_))
    split_ifs <;> ring
end AaronsonAmbainis.Bridge
