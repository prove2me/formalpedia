-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDual
-- name    : Formalism_QuotientMetricDivisors_DivIntoDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:52.083929+00:00
-- url     : https://prove2.me/theorems/69f9801d-abb4-43d8-a431-c1e2c3cd8521
-- title:
--   Div Into Dual
-- statement:
--   Definitions and structural lemmas for Div Into Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/DivIntoDual.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
namespace Formalism.DivisionValues
def DivIntoDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ) (R : Submodule (𝓞 K) (Fin D → K))
    (B : (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (ι : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K),
    (∀ w, ζ w ≠ 0) → (∀ w, vw w (ζ w) = 0) →
    (∀ w (F : Fin (n w) → K), P w F = ζ w * B ((ι w).mulVec ((π w).mulVec F))) →
    (∀ w, ∀ F ∈ M w, P w F = 0 ∨ 0 ≤ vw w (P w F)) →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι w) (matLat (π w) (M w)))) →
    ∀ x ∈ R, B x ∈ Set.range (algebraMap (𝓞 K) K)
end Formalism.DivisionValues


