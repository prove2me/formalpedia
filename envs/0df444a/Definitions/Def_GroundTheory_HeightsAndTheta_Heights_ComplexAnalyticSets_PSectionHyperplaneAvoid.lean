-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSectionHyperplaneAvoid
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSectionHyperplaneAvoid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:25.903678+00:00
-- url     : https://prove2.me/theorems/f7c817fb-d01d-4fe7-b1d6-2f1c301a7f2d
-- title:
--   PSection Hyperplane Avoid
-- statement:
--   Definitions and structural lemmas for PSection Hyperplane Avoid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSectionHyperplaneAvoid.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace SectionHyperplaneAvoid
def linFormMap (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
  Fintype.linearCombination ℂ (fun j => (X j : MvPolynomial (Fin n) ℂ))
def formSpace {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) : Submodule ℂ (Fin n → ℂ) :=
  (I.restrictScalars ℂ).comap (linFormMap n)
end SectionHyperplaneAvoid
end
end GroundTheory.Heights₂.Heights


