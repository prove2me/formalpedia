-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_CompProdReindex
-- name    : MarkovProcessModule_MarkovProcess_Kernel_CompProdReindex
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:30:30.69641+00:00
-- url     : https://prove2.me/theorems/bd324979-1827-4d4e-bda7-a74deb237eaa
-- title:
--   MarkovProcess.Kernel.CompProdReindex
-- statement:
--   # Mapping product kernels by coordinate maps
--
--   This file provides generic identities for mapping the coordinates of a kernel composition
--   product.  They are measure-kernel infrastructure and make no assertion about a stochastic
--   process.
--
--   Complete pinned Lean module MarkovProcess.Kernel.CompProdReindex by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/CompProdReindex.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Mapping product kernels by coordinate maps

This file provides generic identities for mapping the coordinates of a kernel composition
product.  They are measure-kernel infrastructure and make no assertion about a stochastic
process.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel

/-- Mapping the left output of a composition product by a measurable equivalence transports
the second kernel along the inverse equivalence. -/
theorem map_compProd_left_equiv
    {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel (X × A) B) [IsSFiniteKernel η]
    (e : A ≃ᵐ C) :
    (κ ⊗ₖ η).map (Prod.map e id) =
      κ.map e ⊗ₖ η.comap
        (fun z : X × C ↦ (z.1, e.symm z.2))
        (measurable_fst.prodMk (e.symm.measurable.comp measurable_snd)) := by
  ext x s hs
  rw [Kernel.map_apply' _ (e.measurable.prodMap measurable_id) x hs,
    Kernel.compProd_apply (hs.preimage (e.measurable.prodMap measurable_id)),
    Kernel.compProd_apply hs]
  rw [Kernel.map_apply κ e.measurable x]
  rw [MeasureTheory.lintegral_map]
  · congr with a
    rw [Kernel.comap_apply]
    change η (x, a) (Prod.mk (e a) ⁻¹' s) = _
    rw [e.symm_apply_apply]
  · exact Kernel.measurable_kernel_prodMk_left' hs x
  · exact e.measurable

/-- Mapping the right output of a composition product whose second kernel is `prodMkLeft`
is the same as mapping that second kernel before forming the composition product. -/
theorem map_compProd_prodMkLeft_right
    {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel A B) [IsSFiniteKernel η]
    (f : B → C) (hf : Measurable f) :
    (κ ⊗ₖ Kernel.prodMkLeft X η).map (fun z ↦ (z.1, f z.2)) =
      κ ⊗ₖ Kernel.prodMkLeft X (η.map f) := by
  have hpair : Measurable (fun z : A × B ↦ (z.1, f z.2)) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  ext x s hs
  rw [Kernel.map_apply' _ hpair x hs,
    Kernel.compProd_apply (hs.preimage hpair), Kernel.compProd_apply hs]
  congr with a
  rw [Kernel.prodMkLeft_apply', Kernel.prodMkLeft_apply',
    Kernel.map_apply' _ hf _ (measurable_prodMk_left hs)]
  rfl

/-- A measurable reindexing of the first output commutes with mapping the second output when
the latter kernel depends on the first output only through compatible measurable statistics. -/
theorem map_compProd_prodMkLeft_comap
    {X A B C D T : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace T]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel T B) [IsSFiniteKernel η]
    (terminal : A → T)
    (terminal' : C → T) (hterminal' : Measurable terminal')
    (f : A → C) (hf : Measurable f) (g : B → D) (hg : Measurable g)
    (hcompat : terminal' ∘ f = terminal) :
    (κ ⊗ₖ Kernel.prodMkLeft X
      (η.comap terminal (hcompat ▸ hterminal'.comp hf))).map (Prod.map f g) =
      κ.map f ⊗ₖ
        Kernel.prodMkLeft X ((η.map g).comap terminal' hterminal') := by
  have hpair : Measurable (Prod.map f g) := hf.prodMap hg
  ext x s hs
  rw [Kernel.map_apply' _ hpair x hs,
    Kernel.compProd_apply (hs.preimage hpair), Kernel.compProd_apply hs]
  rw [Kernel.map_apply κ hf x]
  rw [MeasureTheory.lintegral_map]
  · congr with a
    rw [Kernel.prodMkLeft_apply', Kernel.prodMkLeft_apply',
      Kernel.comap_apply, Kernel.comap_apply,
      Kernel.map_apply' _ hg _ (measurable_prodMk_left hs)]
    rw [← congrFun hcompat a]
    rfl
  · exact Kernel.measurable_kernel_prodMk_left' hs x
  · exact hf

end ProbabilityTheory.Kernel


