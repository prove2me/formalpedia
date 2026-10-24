-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Comparison
-- name    : KLS408915f_FunctionalInequalities_Poincare_Comparison
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:48:25.180975+00:00
-- url     : https://prove2.me/theorems/b4fc888c-c2a9-44cd-bc1d-4e3476e44868
-- title:
--   Rayleigh maps between Poincaré test families
-- statement:
--   A `Poincare.TestFamily.RayleighMap` from a test family `F` to a test family `G` consists of a function sending each `F`-test to a `G`-test such that variance does not decrease and energy does not increase. Consequently, the image test has a Rayleigh quotient at least as large as the original one; all comparisons are stated directly in `ENNReal`, with no nonzero-energy hypothesis.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/Comparison.lean#L19-L33 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.Comparison`, definition bundle `KLS408915f_FunctionalInequalities_Poincare_Comparison`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Mathlib.Data.ENNReal.Inv

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


