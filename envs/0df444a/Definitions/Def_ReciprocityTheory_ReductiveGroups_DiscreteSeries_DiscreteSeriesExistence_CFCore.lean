-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCore
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:21:25.615597+00:00
-- url     : https://prove2.me/theorems/5742c873-2214-4ff7-8e32-67f3fedbc2dc
-- title:
--   CFCore
-- statement:
--   Definitions and structural lemmas for CFCore, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFCore.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section ProdSub
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
def prodSub (V₁ : Submodule ℂ M₁) (V₂ : Submodule ℂ M₂) : Submodule ℂ (WithLp 2 (M₁ × M₂)) :=
  (V₁.prod V₂).comap (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap
end ProdSub
end ReciprocityTheory.ChartRestriction.DS


