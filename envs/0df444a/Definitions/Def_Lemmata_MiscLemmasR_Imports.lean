-- Prove2me | Definitions.Def_Lemmata_MiscLemmasR_Imports
-- name    : Lemmata_MiscLemmasR_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:38.306952+00:00
-- url     : https://prove2.me/theorems/5e7d1e46-a826-4ad9-ac15-c9815d9bc50f
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MiscLemmasR/Imports.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Bl.ThirdBlockLemmaC
noncomputable def goal1 :
  {K : Type} →   [inst : Field K] →     [NumberField K] →       RingHom K K → Submodule (NumberField.RingOfIntegers K) K → Submodule (NumberField.RingOfIntegers K) K := @fun K _ _ σ M =>
  { carrier := σ ⁻¹' (M : Set K)
    add_mem' := fun {x y} hx hy => by
      simp only [Set.mem_preimage, map_add, SetLike.mem_coe] at *
      exact M.add_mem hx hy
    zero_mem' := by
      simp only [Set.mem_preimage, map_zero, SetLike.mem_coe]
      exact M.zero_mem
    smul_mem' := fun r x hx => by
      simp only [Set.mem_preimage, SetLike.mem_coe] at *
      have hr : IsIntegral ℤ (σ (r : K)) := (NumberField.RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom
      have h : σ (r • x) = (⟨σ (r : K), hr⟩ : NumberField.RingOfIntegers K) • σ x := by
        rw [Algebra.smul_def, map_mul, Algebra.smul_def]
        rfl
      rw [h]
      exact M.smul_mem _ hx }
end Bl.ThirdBlockLemmaC


