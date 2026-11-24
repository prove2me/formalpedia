-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsGeneric
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:56.74459+00:00
-- url     : https://prove2.me/theorems/f1dd9a04-6fd2-4597-a762-eab9be63149e
-- title:
--   PFinite Projections Generic
-- statement:
--   Definitions and structural lemmas for PFinite Projections Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteProjectionsGeneric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric
open MvPolynomial Matrix
noncomputable section
def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ := fun ij => A ij.1 ij.2
def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  bind₁ (fun ij : Fin d × Fin n => ∑ l, C (F (s ij.1) l) * X (l, ij.2)) p
end
end GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsGeneric


