-- Prove2me | Definitions.Def_Malliavin_WienerChaos
-- name    : Malliavin_WienerChaos
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:08:32.309958+00:00
-- url     : https://prove2.me/theorems/89958f7f-6c60-5830-849e-893d243a5797
-- title:
--   Wiener Chaos
-- statement:
--   Definitions and structural lemmas for Wiener Chaos, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean

import Definitions.Def_Malliavin_MultipleIntegral
import Theorems.Thm_Malliavin_inner_multipleIntegralCLM_ne

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
namespace Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
def multipleIntegralRange (hB : IsPreBrownianReal B P) (n : ℕ) :
    Submodule ℝ (RandomL2 P) :=
  LinearMap.range (multipleIntegralCLM hB n).toLinearMap
def homogeneousChaos (hB : IsPreBrownianReal B P) (n : ℕ) :
    ClosedSubmodule ℝ (RandomL2 P) :=
  (multipleIntegralRange hB n).closure
instance instCompleteSpaceHomogeneousChaos (hB : IsPreBrownianReal B P) (n : ℕ) :
    CompleteSpace ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) :=
  (homogeneousChaos hB n).isClosed'.completeSpace_coe
theorem multipleIntegralRange_isOrtho (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) : multipleIntegralRange hB m ⟂ multipleIntegralRange hB n := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  exact inner_multipleIntegralCLM_ne hB hmn f g
theorem homogeneousChaos_isOrtho (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) :
    (homogeneousChaos hB m : Submodule ℝ (RandomL2 P)) ⟂
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) := by
  change (multipleIntegralRange hB m).topologicalClosure ≤
    (multipleIntegralRange hB n).topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  exact Submodule.topologicalClosure_minimal (multipleIntegralRange hB m)
    (multipleIntegralRange_isOrtho hB hmn).le
    (multipleIntegralRange hB n).isClosed_orthogonal
theorem homogeneousChaos_orthogonalFamily (hB : IsPreBrownianReal B P) :
    OrthogonalFamily ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro m n hmn
  exact homogeneousChaos_isOrtho hB hmn
def constantRandomVariables (P : Measure Ω) [IsFiniteMeasure P] :
    Submodule ℝ (RandomL2 P) :=
  (MeasureTheory.Lp.constL 2 P ℝ : ℝ →L[ℝ] RandomL2 P).range.topologicalClosure
abbrev countableProcessMeasurableSpace (B : ℝ≥0 → Ω → ℝ) : MeasurableSpace Ω :=
  ⨆ n : ℕ, MeasurableSpace.comap (B (TopologicalSpace.denseSeq ℝ≥0 n)) (borel ℝ)
def brownianEvalL2 (hB : IsPreBrownianReal B P) (t : ℝ≥0) : RandomL2 P :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.toLp (B t)
def wienerSubspace (hB : IsPreBrownianReal B P) : Submodule ℝ (RandomL2 P) :=
  (⨆ n : ℕ, (homogeneousChaos hB n : Submodule ℝ (RandomL2 P))).topologicalClosure
def IsWienerTotal (hB : IsPreBrownianReal B P) : Prop :=
  wienerSubspace hB = ⊤
theorem wienerChaos_isHilbertSum_of_total (hB : IsPreBrownianReal B P)
    (htotal : IsWienerTotal hB) :
    IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ) := by
  refine IsHilbertSum.mkInternal
    (F := fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
    (homogeneousChaos_orthogonalFamily hB) ?_
  change ⊤ ≤ wienerSubspace hB
  rw [htotal]
def chaosProjection (hB : IsPreBrownianReal B P) (n : ℕ) :
    RandomL2 P →L[ℝ] RandomL2 P :=
  (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection
def wienerChaosEquiv (hB : IsPreBrownianReal B P) (htotal : IsWienerTotal hB) :
    RandomL2 P ≃ₗᵢ[ℝ]
      lp (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P))) 2 :=
  (wienerChaos_isHilbertSum_of_total hB htotal).linearIsometryEquiv
end Malliavin
end


