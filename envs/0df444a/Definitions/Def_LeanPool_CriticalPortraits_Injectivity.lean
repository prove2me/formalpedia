-- Prove2me | Definitions.Def_LeanPool_CriticalPortraits_Injectivity
-- name    : LeanPool_CriticalPortraits_Injectivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:26:13.501333+00:00
-- url     : https://prove2.me/theorems/a47ed83e-686a-440f-b38a-8aeccc41c864
-- title:
--   Injectivity
-- statement:
--   Definitions and structural lemmas for Injectivity, from Keston Aquino-Michaels; LeanPool contributors's pinned Counting critical portraits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
open scoped BigOperators
namespace AbstractLaminar
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
end AbstractLaminar
namespace CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
noncomputable def maxVal {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : ZMod N :=
  (Finset.exists_max_image S (fun x => x.val) h).choose
noncomputable def spanLo {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : ℕ := (minVal S h).val
noncomputable def spanHi {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) : ℕ := (maxVal S h).val
def edgeStep [NeZero (d * m)] (P : Finset (Finset (ZMod (d * m)))) (u v : ZMod (d * m)) : Prop :=
  ∃ (hu : u ∈ T P) (hv : v ∈ T P), predIn P u hu = v ∨ predIn P v hv = u
end CriticalPortraits


