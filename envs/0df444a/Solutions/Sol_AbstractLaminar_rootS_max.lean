-- Prove2me | solution 1 for AbstractLaminar.rootS_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:53.757178+00:00
-- url     : https://prove2.me/submissions/73205ab2-30bf-43c4-bae2-20dee50e00b2

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
namespace AbstractLaminar
theorem _root_.solution {a b : ℕ} {f : ι} (hf : f ∈ Sstrict fam a b) :
    ∀ g ∈ containersS fam a b f,
      fam.hi g - fam.lo g ≤ fam.hi (rootS fam a b f) - fam.lo (rootS fam a b f) := by
  unfold rootS; rw [dif_pos hf]
  exact (Finset.exists_max_image (containersS fam a b f) (fun g => fam.hi g - fam.lo g)
    (containersS_nonempty fam hf)).choose_spec.2
end AbstractLaminar
