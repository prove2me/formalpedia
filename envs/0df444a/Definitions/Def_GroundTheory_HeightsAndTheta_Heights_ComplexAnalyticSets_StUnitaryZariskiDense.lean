-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:34.129325+00:00
-- url     : https://prove2.me/theorems/2654ea59-b93e-42db-af43-43fafd76a7e9
-- title:
--   St Unitary Zariski Dense
-- statement:
--   Definitions and structural lemmas for St Unitary Zariski Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StUnitaryZariskiDense.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
def UnitaryZariskiDense.Statement : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ), p ≠ 0 →
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun ij : Fin n × Fin n => U ij.1 ij.2) p ≠ 0
end
end GroundTheory.Heights₂.Heights.ComplexSets


