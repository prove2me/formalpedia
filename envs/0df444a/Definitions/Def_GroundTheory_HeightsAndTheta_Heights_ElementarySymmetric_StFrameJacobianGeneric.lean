-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:19.507817+00:00
-- url     : https://prove2.me/theorems/bf9fd641-4278-4f15-ae53-3899cfe48396
-- title:
--   St Frame Jacobian Generic
-- statement:
--   Definitions and structural lemmas for St Frame Jacobian Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StFrameJacobianGeneric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
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
def frameDeriv {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (j : Fin n)
    (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ l, C (b j l) * pderiv l f
def frameJacobianDet {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  Matrix.det (Matrix.of fun k j : {j // j ∉ I} => frameDeriv b j (f k))
def FrameJacobianGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ),
        I₀.card = d ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ frameJacobianDet b I₀ f ∉ J ∧
          ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)
end
end GroundTheory.Heights₂.Heights


