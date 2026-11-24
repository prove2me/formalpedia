-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:16.286837+00:00
-- url     : https://prove2.me/theorems/a6ee0a05-f623-4d6d-8acc-94ceb9d9a75d
-- title:
--   Statements Point Vert RSteps
-- statement:
--   Definitions and structural lemmas for Statements Point Vert RSteps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsPointVertRSteps.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField
noncomputable section
section Objects
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
def curveRing (y : (Σ k, ι k) → Ω) : Subring Ω :=
  ⨅ (c : ∀ k, ι k) (_ : ∀ k, y ⟨k, c k⟩ ≠ 0), (chartRingZ y c).toSubring
def curveMul (y : (Σ k, ι k) → Ω) (x : Ω) : AddSubgroup Ω :=
  (curveRing y).toAddSubgroup.map (AddMonoidHom.mulLeft x)
end Objects
def CurveCharts.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      Module.Finite ℤ (curveRing y) ∧
      Module.finrank ℤ (curveRing y) = Module.finrank ℚ (blockFnField y) ∧
      ∀ m : Ideal (curveRing y), m.IsMaximal → ∃ t : T, y ⟨(), t⟩ ≠ 0 ∧
        ∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a
def VertRIndex.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) s =
        Real.log (genIndex (chartLat y (fun _ => 1) 1) (curveMul y (aeval y s)))
def SectionIndexNorm.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      (Module.finrank (blockFnField y) K' : ℝ) *
          Real.log (genIndex (chartLat y (fun _ => 1) 1) (curveMul y (aeval y s))) =
        Real.log |(Algebra.norm ℚ (aeval y s) : ℝ)| +
          Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
            (1 : Submodule (𝓞 K') K').toAddSubgroup)
end
end GroundTheory.Heights₂.Heights


