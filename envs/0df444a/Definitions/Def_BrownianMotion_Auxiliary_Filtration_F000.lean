-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_Filtration_F000
-- name    : BrownianMotion_Auxiliary_Filtration_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:03:20.189124+00:00
-- url     : https://prove2.me/theorems/57ae7ced-dc50-4727-b88e-81f6c78f784d
-- title:
--   Source declarations: BrownianMotion.Auxiliary.Filtration
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Auxiliary.Filtration, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2025 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu
-/

@[expose] public section

namespace MeasureTheory

section Comp

variable {ι ι' Ω : Type*} [Preorder ι] [Preorder ι'] {mΩ : MeasurableSpace Ω}

/-- Given a filtration on `ι` and a monotone mapping `ι' → ι`, construct a filtration on `ι'`.
This is most commonly used to restrict a filtration to a subset of the index set. -/
@[simps]
def Filtration.indexComap (𝓕 : Filtration ι mΩ) {f : ι' → ι} (hf : Monotone f) :
    Filtration ι' mΩ where
  seq k := 𝓕 (f k)
  mono' := 𝓕.mono'.comp hf
  le' i := 𝓕.le (f i)
variable {𝓕 : Filtration ι mΩ} {f : ι' → ι} (hf : Monotone f)

instance {μ : Measure Ω} [SigmaFiniteFiltration μ 𝓕] :
    SigmaFiniteFiltration μ (𝓕.indexComap hf) where
  SigmaFinite i := SigmaFiniteFiltration.SigmaFinite (f i)
variable {E : Type*} [TopologicalSpace E] {X : ι → Ω → E}

theorem StronglyAdapted.indexComap (hX : StronglyAdapted 𝓕 X) (hf : Monotone f) :
    StronglyAdapted (𝓕.indexComap hf) (X ∘ f) := fun i ↦ hX (f i)
end Comp

end MeasureTheory


