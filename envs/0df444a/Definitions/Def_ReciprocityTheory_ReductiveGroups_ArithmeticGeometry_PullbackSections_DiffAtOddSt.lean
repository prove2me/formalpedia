-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:53.128959+00:00
-- url     : https://prove2.me/theorems/e8c17bda-ce50-47f0-b638-093701077263
-- title:
--   Diff At Odd St
-- statement:
--   Definitions and structural lemmas for Diff At Odd St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/DiffAtOddSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
def DiffExpSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (ℓ a m : ℕ), ℓ.Prime → ¬ ℓ ∣ m →
    (discr E).natAbs = ℓ ^ a * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (ℓ : 𝓞 E) ∈ P →
      (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E =
        a * (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P
def DiffAt2St : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (e m : ℕ), Module.finrank ℚ E = 2 ^ (e + 2) → Odd m →
    (discr E).natAbs = 2 ^ (2 ^ (e + 2) * (e + 1) - 4) * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (2 : 𝓞 E) ∈ P →
      ((normalizedFactors (differentIdeal ℤ (𝓞 E))).count P : ℝ) /
          ((normalizedFactors (Ideal.span {(2 : 𝓞 E)})).count P : ℝ) = (e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ e
def DiffAtOddSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (e ℓ m : ℕ), ℓ.Prime → Module.finrank ℚ E = 2 ^ (e + 2) →
    ¬ ℓ ∣ m → (discr E).natAbs = ℓ ^ (2 ^ (e + 1)) * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (ℓ : 𝓞 E) ∈ P →
      ((normalizedFactors (differentIdeal ℤ (𝓞 E))).count P : ℝ) /
          ((normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P : ℝ) = 1 / 2
end ReciprocityTheory.ChartRestriction.G.PullbackSections


