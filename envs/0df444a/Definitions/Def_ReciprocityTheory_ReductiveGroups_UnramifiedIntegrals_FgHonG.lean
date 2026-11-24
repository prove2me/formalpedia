-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:34.50215+00:00
-- url     : https://prove2.me/theorems/77f9262a-6b48-4999-924c-bc743e7cd902
-- title:
--   Fg Hon G
-- statement:
--   Definitions and structural lemmas for Fg Hon G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonG.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
def triSol {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) : ℕ → K
  | m => (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m
def triIter {K : Type} [Field K] (a : ℕ → ℕ → K) (π : K) : ℕ → ℕ → K
  | 0 => triSol a (fun m => if m = 0 then a 0 0 else 0)
  | k + 1 => triSol a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1))
end ReciprocityTheory.ChartRestriction.L1


