-- Prove2me | Definitions.Def_OAIE3v2B281
-- name    : OAIE3v2B281
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:29:57.113798+00:00
-- url     : https://prove2.me/theorems/11f6483a-7bed-4b26-a86d-f1b74571af5f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 294 of 311
-- statement:
--   Definitions bundle 294 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B308`, `OAIE3v2B275` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateNestedTerminalUniformLayersBudget.lean`, `Dynamics/AllocatedCandidateStageScalarBudget.lean`, `Linear/AllocatedExternalCandidateCommonKeepPositiveKernelPreparation.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B308
import Definitions.Def_OAIE3v2B275

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateStageScalarBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration

attribute [local irreducible] allocatedFrozenCurrentGradeResetConstant
  allocatedCandidateStageResetLog allocatedCandidateStageLocalInput allocatedCandidateStageSliceLog

theorem allocatedCandidateStage_localSize_bound (s m d Hθ : ℕ) {v : ℝ}
    (_hv : 2 ≤ v) (hd : (d : ℝ) ≤ v) (hθ : (Hθ : ℝ) ≤ Real.exp v) :
    (d : ℝ) * Hθ * Real.exp (allocatedCandidateStageResetLog s m v) ≤
      Real.exp (allocatedCandidateStageLocalInput s m v) := by
  have hdExp : (d : ℝ) ≤ Real.exp v := by
    linarith only [hd, Real.add_one_le_exp v]
  calc
    _ ≤ Real.exp v * Real.exp v * Real.exp (allocatedCandidateStageResetLog s m v) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hdExp hθ (Nat.cast_nonneg Hθ) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (v + v + allocatedCandidateStageResetLog s m v) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold allocatedCandidateStageLocalInput
      nlinarith only [sq_nonneg v]

theorem allocatedCandidateStage_slice_bounds (s m : ℕ) {v : ℝ} (hv : 2 ≤ v) :
    0 ≤ allocatedCandidateStageSliceLog s m v ∧
    allocatedCandidateStageResetLog s m v ≤ allocatedCandidateStageSliceLog s m v ∧
    v + s + 1 ≤ allocatedCandidateStageSliceLog s m v ∧
    2 * (v + 2) ^ 9 < allocatedCandidateStageSliceLog s m v := by
  have hL := allocatedCandidateStage_local_bounds s m hv
  have hL0 : 0 ≤ allocatedCandidateStageLocalInput s m v := le_trans (by norm_num) hL.1
  have hbase : 1 ≤ allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ) := by
    linarith only [hL.1, Nat.cast_nonneg (α := ℝ) (s + 401)]
  have hLPow : allocatedCandidateStageLocalInput s m v ≤
      (allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ)) ^ (s + 401) := by
    calc
      _ ≤ allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg (s + 401))
      _ = (allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ)) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hbase (by omega : 1 ≤ s + 401)
  unfold allocatedCandidateStageSliceLog
  exact stageSlice_addition_bounds s hv (hL0.trans hLPow) (hL.2.2.trans hLPow)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateNestedTerminalUniformLayersBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem uniformLayersAffinePolynomial_eval (x : ℝ) :
    uniformLayersAffinePolynomial.eval₂ (Nat.castRingHom ℝ) x =
      certifiedAffineCenterBudget x := by
  simp only [uniformLayersAffinePolynomial, certifiedAffineCenterBudget,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one]

attribute [local irreducible] certifiedAffineCenterBudget
  preparedFiniteForwardParameter preparedFiniteForwardWork preparedFiniteForwardCap
  preparedFiniteForwardBranch preparedFiniteForwardCumulative

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedExternalCandidateCommonKeepPositiveKernelPreparation
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}

namespace PositiveKernelPreparation

variable {p : ℝ} {e : ℕ} (prep : P.PositiveKernelPreparation p e)

theorem conclusion_of_selected
    {q : ℝ} (hq : 0 ≤ q)
    (out : prep.selected.problem.Conclusion q (Real.exp (-q)) (Real.exp (-q)))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp q)
    (hσone : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤
      Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) :
    Nonempty (P.Conclusion (3 * q + 2) (Real.exp (-(3 * q + 2)))
      (Real.exp (-(3 * q + 2)))) := by
  let top := D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap
  let K := frequencyCodeKernel top prep.early.eta prep.selected.code
  have hK : K ≤ D.filtration.layer s :=
    (finiteFrequencyKernel_le top _ _).trans inf_le_left
  have hkernel : K ≤ LinearMap.ker φ.toLinearMap :=
    (finiteFrequencyKernel_le top _ _).trans inf_le_right
  have hobservable : (fun x => (prep.selected.tests x).observable) =
      (fun x => ((prep.tests x).kernelProjection K hK).observable) := by
    funext x
    exact congrArg (fun T => T.observable) (prep.selected.identity x)
  have hscore : ∀ z : prep.selected.retained,
      Real.exp (-positiveKernelPreparationParameter p) ≤
        (P.candidate ⟨z.val, prep.selected.subset z.property⟩).score
          (fun x => ((prep.tests x).kernelProjection K hK).observable) weight := by
    intro z
    rw [← P.precenterCandidate_score_mem_eq prep.positive_mass z.val
      (prep.selected.subset z.property)]
    simpa only [prep.selected.identity] using prep.selected.scores z.val z.property
  have transport (newObservable : (X → ℤ) → D.Space → ℂ)
      (heq : (fun x => (prep.selected.tests x).observable) = newObservable)
      (hnewScore : ∀ z : prep.selected.retained,
        Real.exp (-positiveKernelPreparationParameter p) ≤
          (P.candidate ⟨z.val, prep.selected.subset z.property⟩).score newObservable weight) :
      Nonempty ((P.restrictObservable newObservable prep.selected.retained
        prep.selected.subset prep.selected.mass hnewScore).Conclusion q
          (Real.exp (-q)) (Real.exp (-q))) := by
    subst newObservable
    exact ⟨out⟩
  obtain ⟨projectedOut⟩ := transport _ hobservable hscore
  exact P.conclusion_of_kernel_projection_normalized prep.tests prep.tests_unit
    prep.tests_observable K hK hkernel prep.selected.retained prep.selected.subset
    prep.selected.mass hscore hq projectedOut hweight hσone Cgeo hCgeo hchart hsmall hpoly

end PositiveKernelPreparation
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end


