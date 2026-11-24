-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:40.598438+00:00
-- url     : https://prove2.me/theorems/dfb6440e-b650-4ebf-b92f-7ef098f5e74f
-- title:
--   PTwin Div Diff Expansion
-- statement:
--   Definitions and structural lemmas for PTwin Div Diff Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
namespace dividedDifferenceExpansion
noncomputable def stair {r : ℕ} (μ : Fin r →₀ ℕ) (k : ℕ) : MvPolynomial (Fin r ⊕ Fin r) ℤ :=
  ∏ j : Fin r, X (if (j : ℕ) < k then Sum.inr j else Sum.inl j) ^ μ j
end dividedDifferenceExpansion
end GroundTheory.Heights₂.Heights.NumbersDVR


