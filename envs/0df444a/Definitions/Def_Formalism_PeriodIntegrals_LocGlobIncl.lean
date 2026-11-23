-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
-- name    : Formalism_PeriodIntegrals_LocGlobIncl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:40.453815+00:00
-- url     : https://prove2.me/theorems/c5047f41-8f7b-4ac5-86a7-ceb6c8b149ed
-- title:
--   Loc Glob Incl
-- statement:
--   Definitions and structural lemmas for Loc Glob Incl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LocGlobIncl.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ScaledCoordinatesValuationLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace PI
def LocGlobIncl : Prop :=
  ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (M B : Submodule (𝓞 K) W) (T : Finset (HeightOneSpectrum (𝓞 K))) (a : HeightOneSpectrum (𝓞 K) → ℤ),
    (∀ w ∈ T, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal
      (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a w)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) B)) →
    (∀ w : HeightOneSpectrum (𝓞 K), w ∉ T →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) →
    M ≤ Formalism.HermitianLatticesTheory.idealSmul (Formalism.AtG.denIdeal T a : Submodule (𝓞 K) K) B
end PI


