-- Prove2me | Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
-- name    : Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:08.487237+00:00
-- url     : https://prove2.me/theorems/dd534196-f1ab-4639-90ac-a31b1821f591
-- title:
--   Gand So
-- statement:
--   Definitions and structural lemmas for Gand So, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean

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
namespace Formalism.MainNotions.J
open MvPowerSeries
section AlgebraTools
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]
def diagS (a : PowerSeries R) (i : ι) : MvPowerSeries ι R := PowerSeries.subst (X i : MvPowerSeries ι R) a
end AlgebraTools
section Exp
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
def Ex (f : MvPowerSeries ι K) : MvPowerSeries ι K := PowerSeries.subst f (PowerSeries.exp K)
end Exp
section Int
variable {ι κ : Type} {K : Type} [Field K]
end Int
end Formalism.MainNotions.J


