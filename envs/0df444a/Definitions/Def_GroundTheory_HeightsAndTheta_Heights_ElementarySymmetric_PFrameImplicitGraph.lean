-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:32.907912+00:00
-- url     : https://prove2.me/theorems/7dbcd904-37b1-46c4-9ec1-801a84c2e24d
-- title:
--   PFrame Implicit Graph
-- statement:
--   Definitions and structural lemmas for PFrame Implicit Graph, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameImplicitGraph.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
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
namespace FrameImplicitGraph
variable {n : ℕ}
def polyDeriv (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
  ∑ l, eval (fun i => x i) (pderiv l p) • EuclideanSpace.proj l
def projCLM (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) :=
  ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i)
def phi (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    (I → ℂ) × ({j // j ∉ I} → ℂ) :=
  (frameProj b I x, fun k => eval (fun i => x i) (f k))
def phiDeriv (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (I → ℂ) × ({j // j ∉ I} → ℂ) :=
  (projCLM b I).prod (ContinuousLinearMap.pi fun k => polyDeriv (f k) x)
end FrameImplicitGraph
end
end GroundTheory.Heights₂.Heights


