-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProj
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProj
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:56:59.822652+00:00
-- url     : https://prove2.me/theorems/650327bf-4a0d-4961-80bd-26f563883f1a
-- title:
--   Red Proj
-- statement:
--   Definitions and structural lemmas for Red Proj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedProj.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
namespace ReciprocityTheory.ChartRestriction.L1
section Proj
variable {E : Type} [Field E]
def serMap (ψ : E →+ E) (S : PowerSeries E) : PowerSeries E :=
  PowerSeries.mk fun n => ψ (PowerSeries.coeff n S)
def polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) : E[X] :=
  ∑ i ∈ Finset.range (m + 1), monomial i (ψ (Q.coeff i))
variable (k : Subfield E)
variable {k}
end Proj
end ReciprocityTheory.ChartRestriction.L1


