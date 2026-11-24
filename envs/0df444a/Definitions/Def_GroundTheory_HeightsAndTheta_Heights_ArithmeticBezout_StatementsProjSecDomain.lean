-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDomain
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:17.901186+00:00
-- url     : https://prove2.me/theorems/9f3b4361-67b2-408f-bbd4-574d78fe7a06
-- title:
--   Statements Proj Sec Domain
-- statement:
--   Definitions and structural lemmas for Statements Proj Sec Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsProjSecDomain.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDegree
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
def ProjSecDomain.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    W.IsPrime → ComplexSets.IsFiniteProjection W A →
      IsDomain (Vertical.SecAlg
          (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A)) ∧
        Module.Finite (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
          (Vertical.SecAlg
            (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
            (projPar A))
end
end GroundTheory.Heights₂.Heights


