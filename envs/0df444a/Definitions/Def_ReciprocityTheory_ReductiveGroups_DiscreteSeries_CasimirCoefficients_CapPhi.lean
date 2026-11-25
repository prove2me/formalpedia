-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:18.304979+00:00
-- url     : https://prove2.me/theorems/6730ae7b-6693-4a35-812b-3062027adf39
-- title:
--   Cap Phi
-- statement:
--   Definitions and structural lemmas for Cap Phi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiffAt_phiM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace CapPhi
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
def negE : Fin n → Fin n → Module.End ℂ (smoothS n) := fun a b => eOp (-(Matrix.single a b (1 : ℂ)))
def phiS (μ : Fin n → ℤ) : smoothS n :=
  ⟨(OmegaSet n).indicator (PhiM μ),
    (show ContDiffOn ℂ ∞ (PhiM μ) (OmegaSet n) from fun _ hz => (contDiffAt_phiM μ hz).contDiffWithinAt).congr
      fun _ hz => Set.indicator_of_mem hz _⟩
end CapPhi
end ReciprocityTheory.ChartRestriction.DS.S7


