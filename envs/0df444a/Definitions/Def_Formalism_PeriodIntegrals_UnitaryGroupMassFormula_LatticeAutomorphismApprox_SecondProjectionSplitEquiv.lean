-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:32.636135+00:00
-- url     : https://prove2.me/theorems/2459f7f1-6a1a-444d-bff0-d842f64708e0
-- title:
--   Second Projection Split Equiv
-- statement:
--   Definitions and structural lemmas for Second Projection Split Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondProjectionSplitEquiv.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB
open Matrix PI.UnitaryGroupMassFormula.AdIndexEq
def piHom {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K) : R →+* K × K :=
  RingHom.prod p1 (p1.comp σ)
def piEquiv {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K)
    (hb : Function.Bijective (piHom σ p1)) : R ≃+* K × K :=
  RingEquiv.ofBijective (piHom σ p1) hb
end PI.UnitaryGroupMassFormula.ScXuExists.BrB


