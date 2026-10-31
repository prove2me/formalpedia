-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_CompProdReindex_54ebfbc7
-- name    : MarkovProcess_V3H_Kernel_CompProdReindex_54ebfbc7
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:14:22.230323+00:00
-- url     : https://prove2.me/theorems/8620ae0a-5ccb-4b08-a818-df480391183a
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_CompProdReindex_54ebfbc7
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.Probability.Kernel.Composition.CompProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Mapping product kernels by coordinate maps

This file provides generic identities for mapping the coordinates of a kernel composition
product.  They are measure-kernel infrastructure and make no assertion about a stochastic
process.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel





/-- A measurable reindexing of the first output commutes with mapping the second output when
the latter kernel depends on the first output only through compatible measurable statistics. -/
theorem p2m_embedded_d9099d19e86a12a8
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


