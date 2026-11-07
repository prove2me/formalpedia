-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.two_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:28:34.004251+00:00
-- url     : https://prove2.me/submissions/3bb2dd74-3389-492d-a754-92e8472ba547

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  rw [Nat.add_sub_cancel, pow_succ]
  ring
end AaronsonAmbainis.Bridge
