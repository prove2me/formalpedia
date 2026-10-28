-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Filtration
-- name    : KLSModular_BrownianMotion_Auxiliary_Filtration
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:42:04.598097+00:00
-- url     : https://prove2.me/theorems/269122dd-2ba2-4668-a651-ab6bcb354e78
-- title:
--   Filtration reindexing by a monotone map
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `Filtration.indexComap` reindexes a filtration $\mathcal F$ along a monotone map $f$ by setting the new filtration at $k$ to $\mathcal F(f(k))$, and it transports sigma-finiteness of a filtration. `StronglyAdapted.indexComap` states that a strongly adapted process remains strongly adapted after the same reindexing and composition with $f$.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.Probability.Process.Adapted
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   @[simps]
--   def Filtration.indexComap (𝓕 : Filtration ι mΩ) {f : ι' → ι} (hf : Monotone f) :
--       Filtration ι' mΩ where
--     seq k := 𝓕 (f k)
--     mono' := 𝓕.mono'.comp hf
--     le' i := 𝓕.le (f i)
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/Filtration.lean) · `BrownianMotion.Auxiliary.Filtration` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/Filtration.lean#L18-L36 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.Filtration`, definition bundle `KLSModular_BrownianMotion_Auxiliary_Filtration`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

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


