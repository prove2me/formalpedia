-- Prove2me | solution 1 for AbstractLaminar.rootS_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:26.8443+00:00
-- url     : https://prove2.me/submissions/4b00560e-5495-4895-a24f-c190c9cc3dbf

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
public import Theorems.Thm_AbstractLaminar_rootS_mem_E
public import Theorems.Thm_AbstractLaminar_rootS_mem_Sstrict
public import Theorems.Thm_AbstractLaminar_rootS_contains
public import Theorems.Thm_AbstractLaminar_rootS_maximal

set_option autoImplicit true
@[expose] public section
public section
open AbstractLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]
variable (fam : Family ι)
variable {a b : ℕ}
namespace AbstractLaminar
theorem _root_.solution {f : ι} (hf : f ∈ Sstrict fam a b) :
    rootS fam a b (rootS fam a b f) = rootS fam a b f := by
  set r := rootS fam a b f with hr
  have hrS : r ∈ Sstrict fam a b := rootS_mem_Sstrict fam hf
  obtain ⟨hc1, hc2⟩ := rootS_contains fam hrS
  have hmax := rootS_maximal fam hf (rootS_mem_Sstrict fam hrS) hc1 hc2
  exact (fam.inj _ (rootS_mem_E fam hrS) _ (rootS_mem_E fam hf) hmax.1 hmax.2)
end AbstractLaminar
