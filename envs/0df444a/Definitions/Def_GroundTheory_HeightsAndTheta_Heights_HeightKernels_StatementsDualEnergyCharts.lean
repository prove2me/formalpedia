-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualEnergyCharts
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualEnergyCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:34.302204+00:00
-- url     : https://prove2.me/theorems/96053f5b-bc89-45db-ab98-c23927386efa
-- title:
--   Statements Dual Energy Charts
-- statement:
--   Definitions and structural lemmas for Statements Dual Energy Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsDualEnergyCharts.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergy
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
def DualEnergyCharts.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∃ A : (K →+* ℂ) → Matrix (Fin i) (Fin (i - 1 + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      ∀ k : ℕ,
        ptsIntegral (dualIdeal b)
            (pot fun j : Fin (i - 1) =>
              if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
            (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
          ∑ σ : K →+* ℂ, chartMixedEnergy ((A σ)ᴴ * F.metric σ * A σ) ((A σ)ᴴ * A σ) k
example : Σ' (b : Module.Basis Unit ℤ (dualLattice HermLattice.scaledExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)) ∧ 1 ≤ 1 ∧
      HermLattice.scaledExample.metric ≠ HermLattice.scaledExample.withStdMetric.metric :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl, fun h => by
    have h1 := congrFun (congrFun (congrFun h (Rat.castHom ℂ)) 0) 0
    simp [HermLattice.scaledExample, HermLattice.withStdMetric] at h1⟩
example : Function.Bijective (1 : Matrix (Fin 1) (Fin (1 - 1 + 1)) ℂ).mulVec := by
  have h : (1 : Matrix (Fin 1) (Fin 1) ℂ).mulVec = id := funext Matrix.one_mulVec
  exact h ▸ Function.bijective_id
end
end GroundTheory.Heights₂.Heights


