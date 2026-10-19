-- Prove2me | Definitions.Def_OAIE3v2B280
-- name    : OAIE3v2B280
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:33:49.806863+00:00
-- url     : https://prove2.me/theorems/a59570f3-781b-46a8-bac1-3a01aa4950ef
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 293 of 311
-- statement:
--   Definitions bundle 293 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B308`, `OAIE3v2B275` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateStageScalarBudget.lean`, `Dynamics/PreparedFiniteNestedFrontNativeBudget.lean`, `Polynomial/AllocatedNestedDegreeInduction.lean`.
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

theorem allocatedCandidateStage_localDen_bound (s m d Hθ : ℕ) {v : ℝ}
    (hv : 2 ≤ v) (hd : (d : ℝ) ≤ v) (hθ : (Hθ : ℝ) ≤ Real.exp v) :
    (Hθ : ℝ) ^ d * Real.exp (allocatedCandidateStageResetLog s m v) ≤
      Real.exp (allocatedCandidateStageLocalInput s m v) := by
  have hv0 : 0 ≤ v := by linarith only [hv]
  have hpow : (Hθ : ℝ) ^ d ≤ Real.exp ((d : ℝ) * v) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg Hθ) hθ d
  calc
    _ ≤ Real.exp ((d : ℝ) * v) * Real.exp (allocatedCandidateStageResetLog s m v) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = Real.exp ((d : ℝ) * v + allocatedCandidateStageResetLog s m v) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hdv := mul_le_mul_of_nonneg_right hd hv0
      unfold allocatedCandidateStageLocalInput
      nlinarith only [hdv, hv]

theorem allocatedCandidateStage_localCost_le_slice (s m r : ℕ) {v : ℝ}
    (hv : 2 ≤ v) (hrs : r ≤ s) :
    (allocatedCandidateStageLocalInput s m v + (r + 401 : ℕ)) ^ (r + 401) ≤
      allocatedCandidateStageSliceLog s m v := by
  have hL := (allocatedCandidateStage_local_bounds s m hv).1
  have hL0 : 0 ≤ allocatedCandidateStageLocalInput s m v := le_trans (by norm_num) hL
  have hshift : allocatedCandidateStageLocalInput s m v + (r + 401 : ℕ) ≤
      allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ) :=
    add_le_add le_rfl (Nat.cast_le.mpr (Nat.add_le_add_right hrs 401))
  have hbase : 1 ≤ allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ) := by
    linarith only [hL, Nat.cast_nonneg (α := ℝ) (s + 401)]
  have hpower :
      (allocatedCandidateStageLocalInput s m v + (r + 401 : ℕ)) ^ (r + 401) ≤
      (allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ)) ^ (s + 401) := by
    exact (pow_le_pow_left₀ (by positivity) hshift (r + 401)).trans
      (pow_le_pow_right₀ hbase (Nat.add_le_add_right hrs 401))
  have hrest : 0 ≤ 2 * (v + 2) ^ 9 + v + s + 4 := by positivity
  unfold allocatedCandidateStageSliceLog
  -- opaque atoms: `ring1` inside `linarith` would otherwise expand (v + 2) ^ 9 and the
  -- symbolic powers (x ^ (r + 401) becomes x ^ r * x ^ 401, then a 401st power)
  generalize (v + 2) ^ 9 = A at hrest ⊢
  generalize (allocatedCandidateStageLocalInput s m v + (s + 401 : ℕ)) ^ (s + 401) = B at hpower ⊢
  generalize (allocatedCandidateStageLocalInput s m v + (r + 401 : ℕ)) ^ (r + 401) = C at hpower ⊢
  linarith only [hpower, hrest]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.degreeSourceProfileSiteNonempty
structure FrontSourceProfile (degree : ℕ) (p : ℝ) (e : ℕ) where
  u : ℝ
  pModel : ℝ
  sliceBudget : ℝ
  testBudget : ℝ
  nativeBudget : ℝ
  projectionPrecision : ℝ
  marginalCap : ℝ
  narrow : ξ ≤ 1
  u_nonneg : 0 ≤ u
  model_nonneg : 0 ≤ pModel
  input_model : 2 * p + 3 ≤ pModel
  native_nonneg : 0 ≤ nativeBudget
  slice_nonneg : 0 ≤ sliceBudget
  test_nontrivial : 2 ≤ testBudget
  slice_log : sliceBudget * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel
  marginal_one : 1 ≤ marginalCap
  marginal_bound : marginalCap ≤ Real.exp pModel
  projection_precision : u + 2 * pModel + max (max nativeBudget 3)
    (2 * u + 4 * pModel + 20) + 32 ≤ projectionPrecision
  detection : A.NativeDetection degree sliceBudget testBudget nativeBudget
    (Real.exp (-(2 * u + 4 * pModel + 8)))
  physical_excess :
    (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox narrow (fun x => (A.trimMargin_proper x).le)))
      marginalCap ≤ 6 * positiveProjectionAccuracy projectionPrecision
  input_slice : p ≤ sliceBudget
  projection_test :
    AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤ testBudget
  markov_precision :
    AllocatedExternalCandidateProblem.positiveKernelMarkovPrecisionParameter (2 * p) e ≤ u

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedFrontNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

noncomputable def familyCap : ℝ :=
  p + AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) +
    source.u + source.pModel + source.nativeBudget + (m : ℝ) +
    Fintype.card (LayerSamplerVariables G I n B) + 3

noncomputable def familyParameter : ℝ := candidateFrontFamilyParameter source.familyCap

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

noncomputable def frontModelBudget : ℝ :=
  max (max source.nativeBudget 3) (2 * source.u + 4 * source.pModel + 20)

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

noncomputable def factorBudget : ℝ :=
  2 * source.familyParameter +
    verticalDecompositionBudget (3 * source.familyParameter + 1) + 2

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

end OAI
end


