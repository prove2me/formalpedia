-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:42.044029+00:00
-- url     : https://prove2.me/theorems/e2559958-9705-4311-887e-3cc3727895e5
-- title:
--   Statements Dual Geom Deg Charts
-- statement:
--   Definitions and structural lemmas for Statements Dual Geom Deg Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsDualGeomDegCharts.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder
noncomputable section
def DualGeomDegCharts.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∃ A : (K →+* ℂ) → Matrix (Fin i) (Fin (i - 1 + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
        ∑ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ)
example : Σ' (b : Module.Basis Unit ℤ (dualLattice HermLattice.scaledExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)) ∧ 1 ≤ 1 :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl⟩
example : Function.Bijective (1 : Matrix (Fin 1) (Fin (1 - 1 + 1)) ℂ).mulVec := by
  have h : (1 : Matrix (Fin 1) (Fin 1) ℂ).mulVec = id := funext Matrix.one_mulVec
  exact h ▸ Function.bijective_id
end
end GroundTheory.Heights₂.Heights


