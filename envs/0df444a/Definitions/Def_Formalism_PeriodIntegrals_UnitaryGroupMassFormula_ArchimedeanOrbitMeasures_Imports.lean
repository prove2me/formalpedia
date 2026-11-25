-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_Imports
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_Imports
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T07:58:01.342516+00:00
-- url     : https://prove2.me/theorems/edaf0bdb-f264-51db-9ce7-1d8de5f0f666
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/Imports.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix LinearMap Module
noncomputable section
namespace HcS.E
def hdual {S K V : Type*} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule S V) : Submodule S V :=
  ⨅ y ∈ L, (1 : Submodule S K).comap ((B y).restrictScalars S)
end HcS.E


