-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_IsCMUnram
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_IsCMUnram
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:25.123632+00:00
-- url     : https://prove2.me/theorems/fc41a37a-d519-554d-97bf-f61b7619bcdb
-- title:
--   Is CMUnram
-- statement:
--   Definitions and structural lemmas for Is CMUnram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/IsCMUnram.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_Upq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace HcS.HermitianLatticesTheory
def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P
end HcS.HermitianLatticesTheory
namespace HcS.HermitianLatticesTheory
open NumberField
end HcS.HermitianLatticesTheory


