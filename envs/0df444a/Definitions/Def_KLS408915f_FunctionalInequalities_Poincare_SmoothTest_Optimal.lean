-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
-- name    : KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:36:24.468748+00:00
-- url     : https://prove2.me/theorems/c36ea46a-4ca5-4b5a-89fa-6ed3354eaa24
-- title:
--   Optimal Rayleigh constant for a test family
-- statement:
--   `Poincare.TestFamily` records a test type together with finite nonnegative `NNReal` variance and energy values, without choosing a measure or gradient. `rayleigh` is the extended quotient $\operatorname{variance}(f)/\operatorname{energy}(f)$ in `ENNReal`, and `constant` is the supremum over all tests, so it may be $\top$. `Holds F C` means that the finite constant C bounds every variance by C times the corresponding energy.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Optimal.lean#L20-L41 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Optimal`, definition bundle `KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal`; the repository is private at upload time).

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


