-- Prove2me | solution 1 for AaronsonAmbainis.Pack.card_blocks_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:03.686353+00:00
-- url     : https://prove2.me/submissions/391b0ce7-0cc4-4350-8844-da58ec9f1a25

import Definitions.Def_AaronsonAmbainis_Pack_Gate
import Definitions.Def_AaronsonAmbainis_Pack_Blocks
import Definitions.Def_AaronsonAmbainis_Pack_Scaled
import Theorems.Thm_AaronsonAmbainis_Pack_card_blocks


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
open Finset
namespace AaronsonAmbainis.Pack
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (κ : Finset ι → ℝ)
    (hκ : ∀ S, 0 ≤ κ S)
    (hpack : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) (N : ℕ) (i : ι) :
    (univ.filter fun b : (Σ S : Finset ι, Fin ⌊(N : ℝ) * κ S⌋₊) => i ∈ b.1).card ≤ N := by
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [card_blocks (fun S : Finset ι => ⌊(N : ℝ) * κ S⌋₊) i]
  have hreal : ((∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), ⌊(N : ℝ) * κ S⌋₊ : ℕ) : ℝ)
      ≤ (N : ℝ) := by
    rw [Nat.cast_sum]
    calc ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), ((⌊(N : ℝ) * κ S⌋₊ : ℕ) : ℝ)
        ≤ ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), (N : ℝ) * κ S :=
          Finset.sum_le_sum fun S _ => Nat.floor_le (mul_nonneg hN (hκ S))
      _ = (N : ℝ) * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := by
          rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left (hpack i) hN
      _ = (N : ℝ) := mul_one _
  exact Nat.cast_le.mp hreal
end AaronsonAmbainis.Pack
