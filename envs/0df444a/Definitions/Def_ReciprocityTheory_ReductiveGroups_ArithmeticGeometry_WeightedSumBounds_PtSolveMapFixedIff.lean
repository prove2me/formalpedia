-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:55.015595+00:00
-- url     : https://prove2.me/theorems/f9d5a04f-121f-4e23-aa8c-a412566d9a08
-- title:
--   Pt Solve Map Fixed Iff
-- statement:
--   Definitions and structural lemmas for Pt Solve Map Fixed Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtSolveMapFixedIff.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}
def PTGood (v : AddValuation C (WithTop ℝ)) {ι τ : Type*} (x : ι → MvPowerSeries τ C) : Prop :=
  ∀ i, constantCoeff (x i) = 0 ∧ x i ∈ ptIntSer v τ
section Solve
variable {d : ℕ} {σ τ : Type*} [Finite σ]
  (A : (Fin d → MvPowerSeries τ C) → σ → MvPowerSeries τ C)
  (K : Fin d → MvPowerSeries σ C) (M N : Matrix (Fin d) (Fin d) C)
  (f : Fin d → MvPowerSeries τ C)
def ptSolveMap (x : Fin d → MvPowerSeries τ C) : Fin d → MvPowerSeries τ C :=
  fun c => ∑ b, N b c • (f b - subst (A x) (K b))
variable {A K}
end Solve
end
end ReciprocityTheory.ChartRestriction.G.Sh


