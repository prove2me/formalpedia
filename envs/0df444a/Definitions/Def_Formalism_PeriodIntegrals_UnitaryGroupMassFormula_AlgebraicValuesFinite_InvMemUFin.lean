-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_InvMemUFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:56.113493+00:00
-- url     : https://prove2.me/theorems/7fe3e7e7-1a07-47aa-ae6d-666c95a08f2a
-- title:
--   Inv Mem UFin
-- statement:
--   Definitions and structural lemmas for Inv Mem UFin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/InvMemUFin.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology
namespace PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
def toInt (x : Ideles L) (hx : x ∈ UFin L) (v : HeightOneSpectrum (𝓞 L)) :
    (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
  ⟨(x : AdeleRing (𝓞 L) L).2 v, (mem_adicCompletionIntegers _ _ _).2 (hx.2 v).le⟩
end PI.AlgValsFin.W


