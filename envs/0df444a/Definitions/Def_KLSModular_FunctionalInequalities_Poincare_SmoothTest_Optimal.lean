-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Optimal
-- name    : KLSModular_FunctionalInequalities_Poincare_SmoothTest_Optimal
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:23:31.267311+00:00
-- url     : https://prove2.me/theorems/1bd7b12a-ba10-47ca-83e9-4d99a34876b9
-- title:
--   Optimal Rayleigh constant for a test family
-- statement:
--   `Poincare.TestFamily` records a test type together with finite nonnegative `NNReal` variance and energy values, without choosing a measure or gradient. `rayleigh` is the extended quotient $\operatorname{variance}(f)/\operatorname{energy}(f)$ in `ENNReal`, and `constant` is the supremum over all tests, so it may be $\top$. `Holds F C` means that the finite constant C bounds every variance by C times the corresponding energy.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Data.ENNReal.Inv
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure TestFamily where
--     /-- The chosen test domain; it need not contain every ambient function. -/
--     Test : Type u
--     /-- Finite nonnegative variance assigned to each test. -/
--     variance : Test → NNReal
--     /-- Finite nonnegative energy assigned to each test; zero is allowed. -/
--     energy : Test → NNReal
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/Optimal.lean) · `FunctionalInequalities.Poincare.SmoothTest.Optimal` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Optimal.lean#L20-L41 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Optimal`, definition bundle `KLSModular_FunctionalInequalities_Poincare_SmoothTest_Optimal`; the repository is private at upload time).

import Mathlib.Data.ENNReal.Inv

noncomputable section
namespace FunctionalInequalities
namespace Poincare
universe u
/-- A family of tests whose variance and energy are both finite and nonnegative. -/
structure TestFamily where
  /-- The chosen test domain; it need not contain every ambient function. -/
  Test : Type u
  /-- Finite nonnegative variance assigned to each test. -/
  variance : Test → NNReal
  /-- Finite nonnegative energy assigned to each test; zero is allowed. -/
  energy : Test → NNReal
namespace TestFamily
/-- The extended Rayleigh quotient of a test. -/
def rayleigh (F : TestFamily) (f : F.Test) : ENNReal :=
  (F.variance f : ENNReal) / (F.energy f : ENNReal)
/-- The optimal constant, including infinity when the Rayleigh quotients are unbounded. -/
def constant (F : TestFamily) : ENNReal :=
  ⨆ f, rayleigh F f
/-- A finite constant is valid when it bounds variance by that constant times energy. -/
def Holds (F : TestFamily) (C : NNReal) : Prop :=
  ∀ f, F.variance f ≤ C * F.energy f
end TestFamily
end Poincare
end FunctionalInequalities


