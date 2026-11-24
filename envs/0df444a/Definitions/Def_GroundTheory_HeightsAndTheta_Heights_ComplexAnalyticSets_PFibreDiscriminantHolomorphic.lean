-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:57.762705+00:00
-- url     : https://prove2.me/theorems/a2f995c6-268a-41d4-9db4-c0ee60c0f85e
-- title:
--   PFibre Discriminant Holomorphic
-- statement:
--   Definitions and structural lemmas for PFibre Discriminant Holomorphic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreDiscriminantHolomorphic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric Set
noncomputable section
namespace FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]
def pairProd {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) (z : Fin N → σ → ℂ) : ℂ :=
  ∏ q ∈ (Finset.univ : Finset (Fin N)).offDiag, (l (z q.1) - l (z q.2))
end FibreDiscriminantHolomorphic
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


