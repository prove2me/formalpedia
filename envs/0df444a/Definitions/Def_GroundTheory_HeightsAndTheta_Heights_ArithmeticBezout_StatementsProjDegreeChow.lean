-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjDegreeChow
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjDegreeChow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:43.444073+00:00
-- url     : https://prove2.me/theorems/d36a8a0b-1abe-4ef2-b846-f489c943fd37
-- title:
--   Statements Proj Degree Chow
-- statement:
--   Definitions and structural lemmas for Statements Proj Degree Chow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsProjDegreeChow.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
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
def ProjDegreeChow.Statement : Prop :=
  ∀ (n e δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      ComplexSets.IsFiniteProjection W A → ComplexSets.projDegree W A = δ
end
end GroundTheory.Heights₂.Heights


