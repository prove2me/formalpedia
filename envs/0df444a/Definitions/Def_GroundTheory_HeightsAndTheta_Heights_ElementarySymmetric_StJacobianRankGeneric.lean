-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StJacobianRankGeneric
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StJacobianRankGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:33.109027+00:00
-- url     : https://prove2.me/theorems/101a18d1-56ad-4aa9-b905-471f2b056b28
-- title:
--   St Jacobian Rank Generic
-- statement:
--   Definitions and structural lemmas for St Jacobian Rank Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StJacobianRankGeneric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
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
noncomputable section
open MvPolynomial
def genericGradient {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    Fin n → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J) :=
  fun l => algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
    (Ideal.Quotient.mk J (pderiv l f))
def JacobianRankGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime],
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      Module.finrank (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
        (Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (genericGradient J '' (J : Set _))) ≤ n - d
end
end GroundTheory.Heights₂.Heights


