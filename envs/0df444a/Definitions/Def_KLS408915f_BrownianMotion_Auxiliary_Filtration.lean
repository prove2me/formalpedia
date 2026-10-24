-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Filtration
-- name    : KLS408915f_BrownianMotion_Auxiliary_Filtration
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:37:10.279652+00:00
-- url     : https://prove2.me/theorems/f355e857-2ba7-4f7a-9071-3384ea2d6dc1
-- title:
--   Filtration reindexing by a monotone map
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `Filtration.indexComap` reindexes a filtration $\mathcal F$ along a monotone map $f$ by setting the new filtration at $k$ to $\mathcal F(f(k))$, and it transports sigma-finiteness of a filtration. `StronglyAdapted.indexComap` states that a strongly adapted process remains strongly adapted after the same reindexing and composition with $f$.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/Filtration.lean#L18-L36 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.Filtration`, definition bundle `KLS408915f_BrownianMotion_Auxiliary_Filtration`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2025 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/Filtration.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
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
lemma StronglyAdapted.indexComap (hX : StronglyAdapted 𝓕 X) (hf : Monotone f) :
    StronglyAdapted (𝓕.indexComap hf) (X ∘ f) := fun i ↦ hX (f i)
end Comp
end MeasureTheory


