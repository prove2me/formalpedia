-- Prove2me | solution 1 for AaronsonAmbainis.Pack.scaled_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:05.711547+00:00
-- url     : https://prove2.me/submissions/9814c3c0-9612-4f83-adaa-b64452b44216

import Definitions.Def_AaronsonAmbainis_Pack_Gate
import Definitions.Def_AaronsonAmbainis_Pack_Blocks
import Definitions.Def_AaronsonAmbainis_Pack_Scaled
import Theorems.Thm_AaronsonAmbainis_Pack_card_blocks_le
import Theorems.Thm_AaronsonAmbainis_Pack_gate_cos
import Theorems.Thm_AaronsonAmbainis_Pack_gate_pos
import Theorems.Thm_AaronsonAmbainis_Pack_gate_sq
import Theorems.Thm_AaronsonAmbainis_Pack_sum_blocks


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack
open Finset
namespace AaronsonAmbainis.Pack
theorem _root_.solution (hB : BlockInequality) (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hd : HasDegreeLE f d) (x : Cube ι)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hpack : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1)
    (M : ℕ) (hM : 0 < M) :
    (M : ℝ) ^ 2 * ∑ S, κ S * |f x - f (flipSet x S)|
      ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + ∑ S, |f x - f (flipSet x S)| := by
  -- the block inequality for the family `Σ S, Fin ⌊M² κ S⌋₊` and `m = ⌈π M / 2⌉₊`
  have hblock := hB ι d f hf hd x (Σ S : Finset ι, Fin ⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊)
    (fun b => b.1) (M ^ 2) ⌈Real.pi * (M : ℝ) / 2⌉₊ (gate_pos M hM)
    (card_blocks_le κ hκ hpack (M ^ 2)) (gate_cos M hM)
  rw [sum_blocks (fun S : Finset ι => ⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊)
    (fun S : Finset ι => |f x - f (flipSet x S)|)] at hblock
  have hcast : ((M ^ 2 : ℕ) : ℝ) = (M : ℝ) ^ 2 := by push_cast; ring
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  -- the right side of the block inequality
  have hright : 4 * (d : ℝ) ^ 2 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2
      ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 := by
    calc 4 * (d : ℝ) ^ 2 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2
        = (d : ℝ) ^ 2 * (4 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2) := by ring
      _ ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (gate_sq M) hd2
  -- termwise: `M² κ S < ⌊M² κ S⌋₊ + 1`
  have hterm : ∀ S : Finset ι, (M : ℝ) ^ 2 * (κ S * |f x - f (flipSet x S)|)
      ≤ ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
        + |f x - f (flipSet x S)| := by
    intro S
    have hlt : ((M ^ 2 : ℕ) : ℝ) * κ S < ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have habs : (0 : ℝ) ≤ |f x - f (flipSet x S)| := abs_nonneg _
    calc (M : ℝ) ^ 2 * (κ S * |f x - f (flipSet x S)|)
        = (((M ^ 2 : ℕ) : ℝ) * κ S) * |f x - f (flipSet x S)| := by rw [hcast]; ring
      _ ≤ (((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) + 1) * |f x - f (flipSet x S)| :=
          mul_le_mul_of_nonneg_right hlt.le habs
      _ = ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
            + |f x - f (flipSet x S)| := by ring
  calc (M : ℝ) ^ 2 * ∑ S, κ S * |f x - f (flipSet x S)|
      = ∑ S, (M : ℝ) ^ 2 * (κ S * |f x - f (flipSet x S)|) := by rw [Finset.mul_sum]
    _ ≤ ∑ S, (((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
          + |f x - f (flipSet x S)|) := Finset.sum_le_sum fun S _ => hterm S
    _ = ∑ S, ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
          + ∑ S, |f x - f (flipSet x S)| := Finset.sum_add_distrib
    _ ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + ∑ S, |f x - f (flipSet x S)| :=
        add_le_add (hblock.trans hright) le_rfl
end AaronsonAmbainis.Pack
