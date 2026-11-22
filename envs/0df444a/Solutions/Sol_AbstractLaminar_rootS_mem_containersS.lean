-- Prove2me | solution 1 for AbstractLaminar.rootS_mem_containersS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:42.015981+00:00
-- url     : https://prove2.me/submissions/9a446d09-ce8d-4e42-a7de-a1afe86d2469

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
    rootS fam a b f ∈ containersS fam a b f := by
  unfold rootS; rw [dif_pos hf]
  exact (Finset.exists_max_image (containersS fam a b f) (fun g => fam.hi g - fam.lo g)
    (containersS_nonempty fam hf)).choose_spec.1
end AbstractLaminar
