-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:05.722497+00:00
-- url     : https://prove2.me/theorems/4e51c170-0edb-4a61-8c8b-b54eb34788a1
-- title:
--   Unr Ext B
-- statement:
--   Definitions and structural lemmas for Unr Ext B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/UnrExtB.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_resK_mono
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_resK_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace UnramifiedExtensions
variable {p}
end UnramifiedExtensions
namespace UnramifiedExtensions
variable {p} {K}
noncomputable def comb {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) {ι : Type} [Fintype ι]
    (ω : ι → Obar p) (hL : ∀ j, (ω j : PadicAlgCl p) ∈ L) : (ι → K) →ₗ[ℚ_[p]] L where
  toFun a := ⟨∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p),
    L.sum_mem fun j _ => L.mul_mem (hKL (a j).2) (hL j)⟩
  map_add' a b := by
    apply Subtype.ext
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply Subtype.ext
    simp [Algebra.smul_def, mul_assoc, Finset.mul_sum]
noncomputable def resMod {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) :
    Submodule (resK p K) (kbar p) where
  carrier := (resK p L : Set (kbar p))
  add_mem' := fun ha hb => (resK p L).add_mem ha hb
  zero_mem' := (resK p L).zero_mem
  smul_mem' := fun c x hx => by
    rw [Subfield.smul_def, smul_eq_mul]
    exact (resK p L).mul_mem (resK_mono hKL c.2) hx
end UnramifiedExtensions
end ReciprocityTheory.DiscreteGroups.LocalClassField


