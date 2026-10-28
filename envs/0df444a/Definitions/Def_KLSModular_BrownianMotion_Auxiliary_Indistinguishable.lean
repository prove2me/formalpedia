-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Auxiliary_Indistinguishable
-- name    : KLSModular_BrownianMotion_Auxiliary_Indistinguishable
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:47:14.415709+00:00
-- url     : https://prove2.me/theorems/3a794f16-2add-4e7d-a6e0-8ee3c433f2af
-- title:
--   Indistinguishable stochastic processes
-- statement:
--   Vendored from the BrownianMotion library (https://github.com/RemyDegenne/brownian-motion, commit `a7ad7af662044313bc80a7c0756360fb3745f931`). `ProbabilityTheory.Indistinguishable P X Y` means that for $P$-almost every outcome, $X_t(\omega)=Y_t(\omega)$ for every index $t$. The notation `X ≡ᵐ[P] Y` is provided, together with transitivity.
--
--   **Original module imports**
--
--   ```lean
--   public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   @[expose]
--   def Indistinguishable (P : Measure Ω) (X Y : ι → Ω → E) : Prop :=
--     ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Auxiliary/Indistinguishable.lean) · `BrownianMotion.Auxiliary.Indistinguishable` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Auxiliary/Indistinguishable.lean#L18-L43 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Auxiliary.Indistinguishable`, definition bundle `KLSModular_BrownianMotion_Auxiliary_Indistinguishable`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Auxiliary/Indistinguishable.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
namespace ProbabilityTheory
variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y Z : ι → Ω → E}
/-- Two processes are indistinguishable if almost surely they agree everywhere. -/
def Indistinguishable (P : Measure Ω) (X Y : ι → Ω → E) : Prop :=
  ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω
/-- Two processes are indistinguishable if almost surely they agree everywhere. -/
notation3:50 X " ≡ᵐ[" P:50 "] " Y:50 => Indistinguishable P X Y
namespace Indistinguishable
@[trans]
protected lemma trans (h1 : X ≡ᵐ[P] Y) (h2 : Y ≡ᵐ[P] Z) : X ≡ᵐ[P] Z := by
  filter_upwards [h1, h2] with ω h t
  grind
instance : IsTrans (ι → Ω → E) (· ≡ᵐ[P] ·) := ⟨fun _ _ _ ↦ .trans⟩
end Indistinguishable
end ProbabilityTheory


