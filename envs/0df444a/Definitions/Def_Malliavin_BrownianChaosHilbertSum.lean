-- Prove2me | Definitions.Def_Malliavin_BrownianChaosHilbertSum
-- name    : Malliavin_BrownianChaosHilbertSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:00:04.46101+00:00
-- url     : https://prove2.me/theorems/f22f6b1a-4fc2-47ec-b02c-f6370b3cb96b
-- title:
--   Brownian Chaos Hilbert Sum
-- statement:
--   Definitions and structural lemmas for Brownian Chaos Hilbert Sum, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean

import Definitions.Def_Malliavin_BrownianChaosTotality
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical Brownian simplex integral at one positive order, bundled as a linear
isometry. -/
noncomputable def brownianSimplexIntegralLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    IteratedIntegralConstruction.SimplexKernel (n + 1) →ₗᵢ[ℝ] RandomL2 P where
  toLinearMap := (simplexIntegral hB (n + 1)).toLinearMap
  norm_map' f := by
    have hinner := inner_simplexIntegral hB hsm (orderedBoxDense_succ n) f f
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hinner
omit [CompleteSpace W] [BorelSpace W] in
/-- Positive-order canonical Brownian simplex integrals form an orthogonal family. -/
theorem brownianSimplexIntegralLI_orthogonalFamily
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    OrthogonalFamily ℝ
      (fun n : ℕ => IteratedIntegralConstruction.SimplexKernel (n + 1))
      (brownianSimplexIntegralLI hB hsm) := by
  intro m n hmn f g
  exact inner_simplexIntegral_of_ne hB hsm
    (fun h => hmn (Nat.succ.inj h))
    (orderedBoxDense_succ m) (orderedBoxDense_succ n) f g
omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical isometric embedding of the external sum of all positive simplex orders. -/
noncomputable def brownianPositiveTowerLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    IteratedIntegralConstruction.PositiveKernelSum →ₗᵢ[ℝ] RandomL2 P :=
  (brownianSimplexIntegralLI_orthogonalFamily hB hsm).linearIsometry
end Malliavin.BrownianIteratedConstruction


