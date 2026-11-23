-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:37.814017+00:00
-- url     : https://prove2.me/theorems/a7251dbd-4ef4-40de-9de1-b7d1d04a1076
-- title:
--   Glob St
-- statement:
--   Definitions and structural lemmas for Glob St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/GlobSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField
noncomputable def logN {K₁ : Type*} [Field K₁] [NumberField K₁]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ)
def GlobalQuotStatement : Prop :=
  ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (ρ : ℕ) (m : Matrix (Fin ρ) (Fin ρ) K₁),
    m.det ≠ 0 →
    ∀ (s : Fin ρ → IsDedekindDomain.HeightOneSpectrum (𝓞 K₁) → ℝ)
      (β : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁) → ℝ)
      (a b : Fin ρ → InfinitePlace K₁ → ℝ) (B : Fin ρ → ℝ) (Bfin : ℝ),
      (∀ i, (Function.support (s i)).Finite) → (Function.support β).Finite →
      (∀ (σ : InfinitePlace K₁) (i j : Fin ρ), m i j ≠ 0 →
        Real.log (σ (m i j)) + a i σ ≤ b j σ) →
      (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
          (Module.finrank ℚ K₁ : ℝ) ≤ B i) →
      (∑ᶠ w, β w * logN w) / (Module.finrank ℚ K₁ : ℝ) ≤ Bfin →
      (∑ᶠ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w) /
          (Module.finrank ℚ K₁ : ℝ) ≤
        ∑ j, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) +
          (ρ : ℝ) / 2 * Real.log ρ + ∑ i, B i + ρ * Bfin
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


