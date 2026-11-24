-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonH
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonH
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:18.571297+00:00
-- url     : https://prove2.me/theorems/5c168409-c676-48b6-ba1c-77fdb691aa3b
-- title:
--   Fg Hon H
-- statement:
--   Definitions and structural lemmas for Fg Hon H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonH.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
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
section Regroup
variable {K : Type} [Field K]
end Regroup
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
def twC (l : ℕ) (τ : K →+* K) (lam : PowerSeries K) (n m : ℕ) : K :=
  if (l ^ 2) ^ m ∣ n then (τ ^ m) (coeff (n / (l ^ 2) ^ m) lam) else 0
end ReciprocityTheory.ChartRestriction.L1


