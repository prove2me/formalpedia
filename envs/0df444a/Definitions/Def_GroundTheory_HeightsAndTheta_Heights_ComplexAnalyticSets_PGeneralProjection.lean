-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:31.686818+00:00
-- url     : https://prove2.me/theorems/ec2e6f51-efdf-48d7-9f5b-71fbd82b5c8a
-- title:
--   PGeneral Projection
-- statement:
--   Definitions and structural lemmas for PGeneral Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGeneralProjection.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGeneralProjection
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
open Matrix MvPolynomial
noncomputable section
def genericMatrix (d n : ℕ) : Matrix (Fin d) (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) :=
  Matrix.of fun i k => X (i, k)
def detPoly {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) : MvPolynomial (Fin d × Fin n) ℂ :=
  Matrix.det (Matrix.of fun i j => ∑ k, genericMatrix d n i k * C (M k j))
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


