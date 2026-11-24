-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialChartInjective
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialChartInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:44.351493+00:00
-- url     : https://prove2.me/theorems/a0c32f4c-c86d-45a1-b89e-748c833656ef
-- title:
--   St Polynomial Chart Injective
-- statement:
--   Definitions and structural lemmas for St Polynomial Chart Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPolynomialChartInjective.lean

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
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Topology
noncomputable section
def PolynomialChartInjective.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (k : ℕ) (t : MvPolynomial σ ℂ) (f : Fin k → MvPolynomial σ ℂ) (w : σ → ℂ),
    k + 1 = Fintype.card σ →
    LinearIndependent ℂ (Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) :
      Fin (k + 1) → σ → ℂ) →
      ∃ U ∈ 𝓝 w, Set.InjOn (fun z : σ → ℂ ↦ eval z t) {z | z ∈ U ∧ ∀ j, eval z (f j) = 0}
end
end GroundTheory.Heights₂.Heights


