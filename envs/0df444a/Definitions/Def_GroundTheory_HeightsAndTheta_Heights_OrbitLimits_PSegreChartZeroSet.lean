-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:27.318325+00:00
-- url     : https://prove2.me/theorems/1a1da5e3-3a38-4a4b-bece-e01465760ab1
-- title:
--   PSegre Chart Zero Set
-- statement:
--   Definitions and structural lemmas for PSegre Chart Zero Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartZeroSet.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartZeroSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
namespace SegreChartZeroSet
section Lemmas
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def liftPoly {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (f : MRing ι) :
    MvPolynomial (Fin m) ℂ :=
  eval₂ (algebraMap ℤ (MvPolynomial (Fin m) ℂ)) (fun p => X (σ.symm (Function.update i p.1 p.2))) f
end Lemmas
end SegreChartZeroSet
end GroundTheory.Heights₂.Heights


