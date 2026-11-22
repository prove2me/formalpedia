-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:10.595601+00:00
-- url     : https://prove2.me/theorems/25c8208c-a089-4673-96d1-3f6bb8b2c7db
-- title:
--   Gaussian Hessian Integral
-- statement:
--   Definitions and structural lemmas for Gaussian Hessian Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
section Factorisation
open scoped InnerProductSpace ComplexConjugate
open Module
namespace Formalism.FourierDecayAlt.P.G9
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
noncomputable def takMap {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d) →ₗ⋆[ℂ] EuclideanSpace ℂ (Fin d) where
  toFun x := WithLp.toLp 2 (H.mulVec (star (WithLp.ofLp x)))
  map_add' x y := by
    simp [Matrix.mulVec_add]
  map_smul' c x := by
    simp [Matrix.mulVec_smul]
end Formalism.FourierDecayAlt.P.G9
end Factorisation
section OneVariable
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.G9
end Formalism.FourierDecayAlt.P.G9
end OneVariable
section SeveralVariables
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
namespace Formalism.FourierDecayAlt.P.G9
end Formalism.FourierDecayAlt.P.G9
end SeveralVariables


