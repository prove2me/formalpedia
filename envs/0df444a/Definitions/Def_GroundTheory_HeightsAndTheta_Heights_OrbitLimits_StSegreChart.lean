-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChart
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:50.019811+00:00
-- url     : https://prove2.me/theorems/9c39cd70-80ff-43fe-a38e-99fa9993c400
-- title:
--   St Segre Chart
-- statement:
--   Definitions and structural lemmas for St Segre Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StSegreChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_oneLine

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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre PBlk oneLine
  isSmoothHerm_oneLine)
def SegreChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (u v : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsDegZeroSmooth u → IsDegZeroSmooth v →
    0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → u z = 0) →
      ∃ (m : ℕ) (Js : Finset (Ideal (MvPolynomial (Fin m) ℂ))) (U V : (Fin m → ℂ) → ℝ)
        (Φ : Fin n → (Fin m → ℂ) → ℝ),
        (∀ J ∈ Js, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (n + 1 : ℕ) ∧
          SmoothNear (ComplexSets.zeroSet J) U ∧ SmoothNear (ComplexSets.zeroSet J) V ∧
          ∀ j, SmoothNear (ComplexSets.zeroSet J) (Φ j)) ∧
        HasCompactSupport U ∧
        ptsIntegral P (Fin.cons v (pot L)) u = ∑ J ∈ Js, varInt J (n + 1) U (Matrix.vecCons V Φ) ∧
        ptsIntegral P (Fin.cons u (pot L)) v = ∑ J ∈ Js, varInt J (n + 1) V (Matrix.vecCons U Φ)
end GroundTheory.Heights₂.Heights


