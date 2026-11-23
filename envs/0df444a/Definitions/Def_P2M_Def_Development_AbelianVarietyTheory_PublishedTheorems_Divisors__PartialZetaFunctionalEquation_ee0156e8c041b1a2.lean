-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:14.544584+00:00
-- url     : https://prove2.me/theorems/ba6233ac-16c3-44ac-8b0e-df77070a3ff9
-- title:
--   Partial Zeta Functional Equation
-- statement:
--   Definitions and structural lemmas for Partial Zeta Functional Equation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PartialZetaFunctionalEquation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
namespace GlobalTheory.Published
def PartialZetaFunctionalEquation : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (C C' : ClassGroup (𝓞 F)) (D : (Ideal (𝓞 F))⁰),
    (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F) → C * C' = ClassGroup.mk0 D →
    ∃ Z Z' : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z ∧ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C' Z' ∧
      ∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) →
        (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s =
          (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)
end GlobalTheory.Published


