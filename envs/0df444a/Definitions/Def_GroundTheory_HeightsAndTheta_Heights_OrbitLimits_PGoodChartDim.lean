-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartDim
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartDim
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:14:09.705212+00:00
-- url     : https://prove2.me/theorems/4b0e4574-3ea6-5e19-890d-36d9d282a849
-- title:
--   PGood Chart Dim
-- statement:
--   Definitions and structural lemmas for PGood Chart Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeVanishingHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomogPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
namespace GoodChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def segreCone (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, x = fun a => segre z (σ a)}
open Classical in

def psiCoeffs {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Fin m → ℂ :=
  fun a => Ψ (fun i' => if σ a = i' then (1 : ℂ) else 0) 0
end GoodChartDim
open GoodChartDim
end GroundTheory.Heights₂.Heights


