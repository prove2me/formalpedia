-- Prove2me | solution 1 for AME125.toZ_combineFirst_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:04:06.43188+00:00
-- url     : https://prove2.me/submissions/c3c394b8-a5f4-4a77-91f6-6047ba6b9b3e

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState

set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix
namespace AME125
theorem _root_.solution {n m : ℕ} (hm : m ≤ n) (a : Config m 5) (z : Config (n - m) 5)
    (i : Fin n) : toZ (combineFirst m hm a z) i =
      if hi : i.1 < m then toZ a ⟨i.1, hi⟩
      else toZ z ⟨i.1 - m, Nat.sub_lt_sub_right (Nat.le_of_not_lt hi) i.2⟩ :=
  rfl
end AME125
