-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:29.044303+00:00
-- url     : https://prove2.me/theorems/aac9347a-eafa-4062-be11-92430058a45a
-- title:
--   PGood Chart Zero Set
-- statement:
--   Definitions and structural lemmas for PGood Chart Zero Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneousAlt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Finset
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
namespace GoodChartZeroSet
section Lemmas
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical in

def linForm {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : MvPolynomial (Fin m) ℂ :=
  ∑ a, C (Ψ (fun i' => if σ a = i' then (1 : ℂ) else 0) 0) * X a
end Lemmas
end GoodChartZeroSet
end GroundTheory.Heights₂.Heights


