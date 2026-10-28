-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_Comparison
-- name    : KLSModular_FunctionalInequalities_Poincare_Comparison
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:32:02.904982+00:00
-- url     : https://prove2.me/theorems/bd789e95-5acd-4c2b-acf1-7131ddc00a30
-- title:
--   Rayleigh maps between Poincaré test families
-- statement:
--   A `Poincare.TestFamily.RayleighMap` from a test family `F` to a test family `G` consists of a function sending each `F`-test to a `G`-test such that variance does not decrease and energy does not increase. Consequently, the image test has a Rayleigh quotient at least as large as the original one; all comparisons are stated directly in `ENNReal`, with no nonzero-energy hypothesis.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Poincare.SmoothTest.Optimal
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure RayleighMap (F : TestFamily.{u}) (G : TestFamily.{v}) where
--     /-- The image test. -/
--     toFun : F.Test → G.Test
--     /-- Variance does not decrease under the map. -/
--     variance_le : ∀ f, F.variance f ≤ G.variance (toFun f)
--     /-- Energy does not increase under the map. -/
--     energy_le : ∀ f, G.energy (toFun f) ≤ F.energy f
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Poincare/SmoothTest/Optimal`](https://prove2.me/theorems/1bd7b12a-ba10-47ca-83e9-4d99a34876b9).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/Comparison.lean) · `FunctionalInequalities.Poincare.Comparison` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/Comparison.lean#L19-L33 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.Comparison`, definition bundle `KLSModular_FunctionalInequalities_Poincare_Comparison`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Optimal

noncomputable section
namespace FunctionalInequalities
namespace Poincare
namespace TestFamily
universe u v
/-- A map from `F`-tests to `G`-tests that can only increase their Rayleigh quotients. -/
structure RayleighMap (F : TestFamily.{u}) (G : TestFamily.{v}) where
  /-- The image test. -/
  toFun : F.Test → G.Test
  /-- Variance does not decrease under the map. -/
  variance_le : ∀ f, F.variance f ≤ G.variance (toFun f)
  /-- Energy does not increase under the map. -/
  energy_le : ∀ f, G.energy (toFun f) ≤ F.energy f
namespace RayleighMap
variable {F : TestFamily.{u}} {G : TestFamily.{v}}
instance : CoeFun (RayleighMap F G) fun _ ↦ F.Test → G.Test :=
  ⟨RayleighMap.toFun⟩
end RayleighMap
end TestFamily
end Poincare
end FunctionalInequalities


