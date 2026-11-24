-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:25.879801+00:00
-- url     : https://prove2.me/theorems/6eaf0fb5-d2d7-4bca-aab6-e97cfba65295
-- title:
--   Fg Hon B
-- statement:
--   Definitions and structural lemmas for Fg Hon B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
section Ev
variable {R : Type} [CommRing R]
def ev0 (F : MvPowerSeries (Fin 2) R) : PowerSeries R :=
  MvPowerSeries.subst ![(X : PowerSeries R), 0] F
end Ev
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}
end ReciprocityTheory.ChartRestriction.L1


