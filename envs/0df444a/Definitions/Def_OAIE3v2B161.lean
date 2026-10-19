-- Prove2me | Definitions.Def_OAIE3v2B161
-- name    : OAIE3v2B161
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:13:42.048222+00:00
-- url     : https://prove2.me/theorems/765d724d-f34c-4f1c-a0cf-ffed6bc9bcdf
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 163 of 311
-- statement:
--   Definitions bundle 163 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152` of this split.
--
--   Modules: `Dynamics/RestrictedSymbolGradeIteration.lean`, `Estimates/AllocatedReferenceJetWindow.lean`, `Estimates/AllocatedRowsAmbientProjectedFamilyMultiple.lean`, `Estimates/AveragedModeledPatchTransfer.lean`, `Estimates/BiasedSynchronizedSquareFamily.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/CommonDependentWordLayers.lean`, `Estimates/CommonMarkedMultidegree.lean`, `Estimates/CommonRefilteredMappedOrbitFactors.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/HomogeneousQuotientSymbolLiftBounds.lean`, `Estimates/HomogeneousRealSymbolPullback.lean`, `Estimates/MarkedShiftGeneratorBounds.lean`, `Estimates/NativeFrozenMarkedLocalMark.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/NativePhysicalHaarExpansion.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/RealSymbolGradeQuotientSplitting.lean`, `Fourier/StandardJetFourier.lean`, `Geometry/GlobalChartNativeFactorization.lean`, `Geometry/NativeCoordinateSplitFreezing.lean`, `Geometry/PhysicalFactorCoordinates.lean`, `Geometry/RestrictedChartPrefixControl.lean`, `Linear/AllocatedOriginalSourceProjection.lean`, `Linear/ControlledMarkedKernelNormalization.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/NativeRankQuotientOrbit.lean`, `Linear/NativeRankRelationExistence.lean`, `Linear/RankIntervalFactorization.lean`, `Nilpotent/NativeRankZeroNiltest.lean`, `Polynomial/GradedPolynomialSymbolInverse.lean`, `Polynomial/MarkedPolynomialGenerators.lean`, `Polynomial/MeasureDegreeZeroTwistTransfer.lean`, `Polynomial/NativeDegreeRankFamily.lean`, `Polynomial/PolynomialOrbitLogSum.lean`, `Polynomial/PolynomialPatchMarkedChartRestoration.lean`, `Probability/AllocatedAmbientProjectedDensityMultiple.lean`, `Probability/AllocatedZeroLayerLaw.lean`, `Probability/CommonSectionAmbientDensityMultiple.lean`, `Probability/PositiveDensityNormalization.lean`, `Probability/PreparedModularGeneralCenteredLaw.lean`, `Sampling/AllocatedExternalCandidateSamplerFamily.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))

noncomputable def fastPointwiseSquare (w : σ → ℕ)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  F.squareFiltration.quotientTop.symbolPointwiseSubalgebra
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w W

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GradedPolynomialSymbolInverse
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolOfGradedPolynomial_coordinate
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis e ω hF w).baseChange ℝ).repr
      (F.realSymbolOfGradedPolynomial e ω hF w P) z =
      ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr (coefficients P z.val.1) z.val.2 := by
  rw [realSymbolOfGradedPolynomial, LinearEquiv.apply_symm_apply]
  rfl

theorem realGradedSymbolPolynomial_ofGradedPolynomial
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : P ∈ gradedPolynomialSubmodule ((F.associatedGradedBasis e ω hF).baseChange ℝ) ω w) :
    F.realGradedSymbolPolynomial e ω hF w (F.realSymbolOfGradedPolynomial e ω hF w P) = P := by
  apply coefficients.injective
  ext α
  apply ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight w α = ω i
  · exact (F.realGradedSymbolPolynomial_coordinate e ω hF w _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfGradedPolynomial_coordinate e ω hF w P ⟨(α, i), h⟩)
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne e ω hF w _ α i h]
    have hi := congrArg (fun v => ((F.associatedGradedBasis e ω hF).baseChange ℝ).repr v i) (hP α)
    simp only [LinearMap.restrictScalars_apply] at hi
    rw [basisGradeProjection_repr, if_neg (Ne.symm h)] at hi
    exact hi

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L Q : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def homogeneousQuotientGradedPolynomial (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  map (((basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k).comp S).restrictScalars ℚ) p

noncomputable def homogeneousQuotientSymbolLift (w : σ → ℕ) (k : ℕ)
    (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded)) (p : VectorPolynomial σ ℚ Q) :
    F.RealPolynomialSymbol w :=
  F.realSymbolOfGradedPolynomial b ω hF w
    (F.homogeneousQuotientGradedPolynomial b ω hF k S p)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def scalarSymbolPolynomial (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (g : F.RealPolynomialSymbolGroup w) : MvPolynomial σ ℝ :=
  coordinate (realifyFunctional θ).toAddMonoidHom
    (F.realGradedSymbolPolynomial b ω hF w g.coord)

@[simp] theorem coeff_scalarSymbolPolynomial (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (g : F.RealPolynomialSymbolGroup w) (α : σ →₀ ℕ) :
    (F.scalarSymbolPolynomial b ω hF w θ g).coeff α =
      realifyFunctional θ
        (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) := by
  simp only [scalarSymbolPolynomial, coeff_coordinate, LinearMap.toAddMonoidHom_coe]

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realSymbolGradeQuotientPolynomial
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ) (x : F.RealPolynomialSymbol w) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)) :=
  VectorPolynomial.map ((U.mkQ.baseChange ℝ).restrictScalars ℚ)
    (F.realGradedSymbolPolynomial b ω hF w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
        (fun z => ω z.val.2) k x))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RestrictedSymbolGradeIteration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)
  (U : Submodule ℚ F.AssociatedGraded)
  (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

noncomputable def restrictedMajorCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.RealPolynomialSymbolGroup w :=
  ⟨F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
    (weightedHomogeneousPart w k p)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreeRankFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

namespace NativeDegreeRankFamily

variable {s r : ℕ} {A : Type*} {p q : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def eval (i : Fin W.outputDim) (a : A) (n : ℤ) : ℂ :=
  W.vertical.observable i (QuotientGroup.mk
    (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) (fun _ => n) (W.orbit a)))

end NativeDegreeRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure AdaptedModelData (D : RationalFilteredNilmanifold L s d) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  layers : ∀ j, D.filtration.layer j = Submodule.span ℚ (basis '' {i | j ≤ weight i})
  grid : ℕ
  grid_pos : 0 < grid
  inner : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates basis D.lattice
  outer : bchSubgroupCoordinates basis D.lattice ⊆ denominatorGrid grid

namespace AdaptedModelData

variable {D : RationalFilteredNilmanifold L s d}

noncomputable def model (F : D.AdaptedModelData) : RationalFilteredNilmanifold L s (finrank ℚ L) :=
  D.filtration.ofAdaptedBasis F.basis F.weight F.layers D.lattice F.grid F.grid_pos F.inner F.outer

end AdaptedModelData

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

noncomputable def physicalCubeCoveredSample {I : Type*} {m q : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (v : I → (Unit ⊕ Fin q) → ℤ) :
    ∀ j, SubspaceArrayTorus (Finset (Fin q)) (U j) := fun j =>
  QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
    ((D : ℝ)⁻¹ • fun s => eval (fun i => (physicalCubeVertexValue v s i : ℝ))
      (restrictCoefficients (U j) (p j) (hm j)))

theorem affineCoveredSiteSample_physical {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : I → ℤ) (z : Option K × I → ℤ) :
    affineCoveredSiteSample U root difference D
        (fun j => translate (fun i => (base i : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
        (fun k i => (z (k, i) : ℝ)) =
      physicalCubeCoveredSample U D p hm (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  funext j
  rw [affineCoveredSiteSample_eq_values]
  dsimp only [physicalCubeCoveredSample]
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)))
  apply congrArg (fun v : Finset (Fin q) → U j => (D : ℝ)⁻¹ • v)
  funext s
  apply Subtype.ext
  rw [eval_restrictCoefficients, eval_restrictCoefficients, eval_translate]
  apply congrArg (fun x : I → ℝ => eval x (p j))
  funext i
  have h := congrFun (integerSiteValue_affine_physical root difference base z s) i
  simpa only [Pi.add_apply, add_comm] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem coefficientTorusFourierSum_sample {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (z : Option K → I → ℝ) :
    coefficientTorusFourierSum U frequency c (affineSampleCoefficientTorus U p hm z) =
      affineCubeFourierSum frequency p c z := by
  unfold coefficientTorusFourierSum affineCubeFourierSum
  apply Finset.sum_congr rfl
  intro a _
  rw [coefficientTorusCharacter_sample U (frequency a) p hp hm z]

theorem coefficientCoverSample_sites {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (z : Option K → I → ℝ) :
    coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k))
        (affineCoefficientCoverSample U p hm D z) =
      affineCoveredSiteSample U root difference D p hm z := by
  funext j
  rw [affineCoefficientCoverSample, coefficientSiteTorusMap_mk]
  change QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
    (matrixModuleAction (fun s d =>
      (boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k)) s d : ℝ))
      ((D : ℝ)⁻¹ • fun d => coefficients
        (substitute (affineParameterSubstitution z) (restrictCoefficients (U j) (p j) (hm j))) d.val)) = _
  rw [map_smul, ← siteEvaluation_bounded_coefficients _ _
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree z) _
      (degreeLE_restrictCoefficients (U j) (p j) (hm j) (hp j)))]
  rfl

noncomputable def physicalCubeEuclideanSample {I : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (v : I → (Unit ⊕ Fin q) → ℤ) :
    EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) :=
  euclideanJetEquiv U (siteBooleanJetTorusMap U
    (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    (physicalCubeCoveredSample U D p hm v))

theorem coefficientCoverSample_physicalJet {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : I → ℤ) (z : Option K × I → ℤ) :
    euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
        (affineCoefficientCoverSample U (fun j => translate (fun i => (base i : ℝ)) (p j))
          (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
          D (fun k i => (z (k, i) : ℝ))) =
      physicalCubeEuclideanSample U D p hm (physicalCubeRootDifferences root (Matrix.of difference) base z) := by
  have hs := coefficientCoverSample_sites U root difference D
    (fun j => translate (fun i => (base i : ℝ)) (p j))
    (fun j => degreeLE_translate (1 : I → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
    (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
    (fun k i => (z (k, i) : ℝ))
  rw [affineCoveredSiteSample_physical] at hs
  exact congrArg (fun t : SiteTorus (Finset (Fin q)) U => euclideanJetEquiv U
    (siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) t)) hs

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

noncomputable def physicalCubeRowSample {X : Type*} {m dim : ℕ}
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (rows : ∀ j, O j → Finset (Fin dim))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    EuclideanJetLayers U O :=
  euclideanJetEquiv U (siteBooleanJetTorusMap U rows (physicalCubeCoveredSample U d p hm v))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

theorem affineCoveredSiteSample_zero_base_physical {X K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (d : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K × X → ℤ) :
    affineCoveredSiteSample U root difference d p hm (fun k x => (z (k,x) : ℝ)) =
      physicalCubeCoveredSample U d p hm (physicalCubeRootDifferences root (Matrix.of difference) 0 z) := by
  funext j
  rw [affineCoveredSiteSample_eq_values]
  dsimp only [physicalCubeCoveredSample]
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)))
  apply congrArg (fun v : Finset (Fin q) → U j => (d : ℝ)⁻¹ • v)
  funext s
  apply congrArg (fun x => eval x (restrictCoefficients (U j) (p j) (hm j)))
  funext x
  have h := congrFun (integerSiteValue_affine_physical root difference (0 : X → ℤ) z s) x
  simpa only [Pi.zero_apply, Int.cast_zero, Pi.add_apply, zero_add] using h

theorem coefficientCoverSample_standardPhysicalJet {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option (Fin q) × X → ℤ) :
    standardPhysicalJetMap U
      (affineCoefficientCoverSample U p hm d (fun k x => (z (k,x) : ℝ))) =
      physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z) := by
  let D : Fin q → Fin q → ℤ := fun i j => if i = j then 1 else 0
  have hD : Matrix.of D = (1 : Matrix (Fin q) (Fin q) ℤ) := by
    ext i j
    simp [D, Matrix.one_apply]
  have h := coefficientCoverSample_sites U (fun _ : Fin q => 0)
    D d p hp hm (fun k x => (z (k,x) : ℝ))
  have hs := affineCoveredSiteSample_zero_base_physical U (fun _ : Fin q => 0)
    D d p hm z
  rw [hs, hD, physicalCubeRootDifferences_standard] at h
  have hjet : euclideanCoefficientJetMap U (fun _ : Fin q => 0) (Matrix.of D)
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
      (affineCoefficientCoverSample U p hm d (fun k x => (z (k,x) : ℝ))) =
      physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z) :=
    congrArg (fun t : SiteTorus (Finset (Fin q)) U => euclideanJetEquiv U
    (siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))) t)) h
  rw [hD] at hjet
  exact hjet

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

variable {X : Type*} {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

noncomputable def physicalSingleSiteValue (w : X → ℝ) : EuclideanJetLayers U (fun _ => Unit) :=
  fun j _ => (euclideanSubspaceTorusEquiv (U j)).symm
    (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
      (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j))))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PositiveDensityNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

theorem selectedJointReference_densityMass (D : B → (K × I → ℤ) → ℝ) :
    (selectedJointReference A hA modulus T W hW hZ).mean (fun z => D z.1.val z.2.val) =
      selectedJointDensityMass A modulus T W D := by
  rw [selectedJointReference, FiniteProbabilityWeights.mean_prod]
  simp_rw [selectedResidueFiniteLaw_densityMass]
  exact FiniteProbabilityWeights.uniformFinset_mean A hA
    (fun a => selectedResidueDensityMass modulus T W (D a))

noncomputable def selectedJointFiniteLaw (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D) :
    FiniteProbabilityWeights (A × rectangularWeightIndices 0 W 1) :=
  (selectedJointReference A hA modulus T W hW hZ).reweightPositive
    (fun z => D z.1.val z.2.val) (fun z => hD0 z.1.val z.2.val)
    (by rw [selectedJointReference_densityMass]; exact hD)

theorem selectedJointFiniteLaw_complexMean (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D)
    (f : B → (K × I → ℤ) → ℂ) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).complexMean
      (fun z => f z.1.val z.2.val) =
      (selectedJointReference A hA modulus T W hW hZ).normalizedDensityTest
        (fun z => D z.1.val z.2.val) (fun z => f z.1.val z.2.val) := by
  rw [selectedJointFiniteLaw, FiniteProbabilityWeights.reweightPositive_complexMean_eq_normalizedDensityTest]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem physicalCubeCoveredSample_translate {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (cover : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (base : X → ℤ)
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubeCoveredSample U cover
        (fun j => translate (fun x => (base x : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j)) v =
      physicalCubeCoveredSample U cover p hm (translatePhysicalCube base v) := by
  funext j
  dsimp only [physicalCubeCoveredSample]
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)))
  apply congrArg (fun w : Finset (Fin q) → U j => (cover : ℝ)⁻¹ • w)
  funext s
  apply Subtype.ext
  rw [eval_restrictCoefficients, eval_restrictCoefficients, eval_translate]
  apply congrArg (fun x : X → ℝ => eval x (p j))
  funext x
  rw [physicalCubeVertexValue_translate]
  simp only [Int.cast_add, add_comm]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.StandardJetFourier
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical Matrix

theorem boundedSiteMatrix_standard {q h : ℕ} (s : Finset (Fin q))
    (e : BoundedCoefficientExponent (Fin q) h) :
    boundedSiteMatrix h standardPhysicalSite s e = if e.val.support ⊆ s then 1 else 0 := by
  change (∏ i ∈ e.val.support, standardPhysicalSite s i ^ e.val i) = _
  simp only [standardPhysicalSite_apply]
  by_cases hs : e.val.support ⊆ s
  · rw [if_pos hs]
    exact Finset.prod_eq_one (fun i hi => by rw [if_pos (hs hi), one_pow])
  · rw [if_neg hs]
    obtain ⟨i, hi, his⟩ := Finset.not_subset.mp hs
    exact Finset.prod_eq_zero hi (by rw [if_neg his, zero_pow (Finsupp.mem_support_iff.mp hi)])

theorem boundedCoefficientJetMatrix_standard {q h : ℕ} {O : Type*}
    (rows : O → Finset (Fin q)) (o : O) (e : BoundedCoefficientExponent (Fin q) h) :
    boundedCoefficientJetMatrix (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) h rows o e =
      if rows o = e.val.support then 1 else 0 := by
  rw [← booleanJetExtractionMatrix_mul_boundedSite]
  change (booleanJetExtractionMatrix rows *ᵥ (fun s => boundedSiteMatrix h standardPhysicalSite s e)) o = _
  rw [booleanJetExtractionMatrix_mulVec]
  simp only [boundedSiteMatrix_standard]
  exact booleanCoefficient_monomial e.val.support (rows o)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalFactorCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial
variable {X : Type*} {m : ℕ} {J : Fin m → Type*}

noncomputable def physicalGridFactorInput (period : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    (Σ j, J j) → UnitAddCircle :=
  fun a => ((eval t (p a.1) a.2 / period : ℝ) : UnitAddCircle)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

variable {L M σ κ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d n t : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s n)
    (hEF : E.filtration = D.filtration.gradedRefiltration W)

noncomputable def includedRefilteredOrbit (w : σ → ℕ)
    (g : E.filtration.realification.PolynomialOrbit w) :
    D.filtration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (map ((realificationLieHom (D.filtration.gradedRefiltrationSubalgebra W).incl).toLinearMap.restrictScalars ℚ) g.log)
    (E.filtration.realification.adapted_map D.filtration.realification _
      (E.filtration.realificationLieHom_mem_layer D.filtration
        (D.filtration.gradedRefiltrationSubalgebra W).incl (by
          intro j x hx
          apply D.filtration.gradedRefiltrationLayer_le W j
          exact (D.filtration.mem_gradedRefiltration_layer W j x).mp (hEF ▸ hx))) w g.adapted)

@[simp] theorem includedRefilteredOrbit_log (w : σ → ℕ)
    (g : E.filtration.realification.PolynomialOrbit w) :
    (D.includedRefilteredOrbit W E hEF w g).log =
      map ((realificationLieHom (D.filtration.gradedRefiltrationSubalgebra W).incl).toLinearMap.restrictScalars ℚ) g.log := rfl

noncomputable def externalCandidateOrbit (w : σ → ℕ)
    (left right : D.filtration.realification.PolynomialOrbit w)
    (middle : E.filtration.realification.PolynomialOrbit w) :
    D.filtration.realification.PolynomialOrbit w :=
  left * D.includedRefilteredOrbit W E hEF w middle * right

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledMarkedKernelNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ)

@[simp] theorem realPolynomialSymbolHom_constant (g : F.realification.Group) :
    F.realPolynomialSymbolHom b ω hF w
      (F.realification.adaptedConstantGroupHom w g) = 1 := by
  apply NilpotentLieBCHGroup.ext
  change F.realPolynomialSymbolMap b ω hF w _ = 0
  rw [F.realPolynomialSymbolMap_eq_zero_iff]
  exact F.realification.polynomialSymbolMap_constant w g.coord

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RestrictedChartPrefixControl
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realPolynomialChartSubstitution

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)
  (U : Submodule ℚ F.AssociatedGraded)
  (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

noncomputable def restrictedMajorChartCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
  ⟨F.homogeneousQuotientGradedPolynomial b ω hF k (S.baseChange ℝ)
    (weightedHomogeneousPart w k p)⟩

@[simp] theorem restrictedMajorChartCorrection_coord (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorChartCorrection b ω hF w U S k p).coord =
      F.homogeneousQuotientGradedPolynomial b ω hF k (S.baseChange ℝ)
        (weightedHomogeneousPart w k p) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousRealSymbolPullback
namespace OAI

section

namespace Erdos3
open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem realChartSubstitute_mem_gradedPolynomialSubmodule
    {σ τ ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
    [IsScalarTower ℚ ℝ V] (b : Basis ι ℝ V) (ω : ι → ℕ)
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : VectorPolynomial σ ℚ V) (hp : p ∈ gradedPolynomialSubmodule b ω w) :
    realChartSubstitute β p ∈ gradedPolynomialSubmodule b ω v := by
  classical
  intro α
  change basisGradeProjection b ω (Finsupp.weight v α)
    (coefficients (realChartSubstitute β p) α) = _
  rw [coefficients_realChartSubstitute, map_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [map_smul]
  by_cases h : Finsupp.weight v α = Finsupp.weight w γ
  · rw [h]
    exact congrArg (fun z =>
      (MvPolynomial.aeval β (MvPolynomial.monomial γ (1 : ℝ))).coeff α • z) (hp γ)
  · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero α h,
      zero_smul, zero_smul]

namespace NilpotentLieFiltration
variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)

noncomputable def realSymbolHomogeneousPullback (x : F.RealPolynomialSymbol w) :
    F.RealPolynomialSymbol v :=
  F.realSymbolOfGradedPolynomial b ω hF v
    (realChartSubstitute β (F.realGradedSymbolPolynomial b ω hF w x))

attribute [local irreducible] realSymbolHomogeneousPullback realSymbolOfGradedPolynomial
  realChartSubstitute realGradedSymbolPolynomial gradedPolynomialSubmodule

theorem realGradedSymbolPolynomial_homogeneousPullback
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) (x : F.RealPolynomialSymbol w) :
    F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v β x) =
    realChartSubstitute β (F.realGradedSymbolPolynomial b ω hF w x) := by
  have hp := F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule b ω hF w x
  have hsub := realChartSubstitute_mem_gradedPolynomialSubmodule
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w v β hβ
    (F.realGradedSymbolPolynomial b ω hF w x) hp
  rw [realSymbolHomogeneousPullback]
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF v
    (realChartSubstitute β (F.realGradedSymbolPolynomial b ω hF w x)) hsub

noncomputable def realSymbolHomogeneousPullbackLie
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol v where
  toFun := F.realSymbolHomogeneousPullback b ω hF w v β
  map_add' x y := by
    apply F.realGradedSymbolPolynomial_injective b ω hF v
    simp only [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
      map_add]
  map_smul' r x := by
    apply F.realGradedSymbolPolynomial_injective b ω hF v
    simp only [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
      map_smul, RingHom.id_apply]
  map_lie' {x y} := by
    apply F.realGradedSymbolPolynomial_injective b ω hF v
    simp only [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ,
      LieHom.map_lie, realChartSubstitute_lie]

noncomputable def realSymbolHomogeneousPullbackHom
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i)) :
    F.RealPolynomialSymbolGroup w →* F.RealPolynomialSymbolGroup v :=
  NilpotentLieBCHGroup.map (F.realSymbolHomogeneousPullbackLie b ω hF w v β hβ)

@[simp] theorem realSymbolHomogeneousPullbackHom_coord
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (x : F.RealPolynomialSymbolGroup w) :
    (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ x).coord =
      F.realSymbolHomogeneousPullback b ω hF w v β x.coord := rfl

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial
open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

theorem adapted_realChartSubstitute_weightedSupport
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    {p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)} (hp : F.realification.Adapted w p) :
    F.realification.Adapted v (realChartSubstitute β p) := by
  classical
  apply (F.realification.adapted_iff_coefficients v _).mpr
  intro α
  rw [coefficients_realChartSubstitute]
  apply Submodule.sum_mem
  intro γ _
  by_cases hc : (aeval β (monomial γ (1 : ℝ))).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · change _ ∈ (F.realLayer (Finsupp.weight v α)).toSubmodule
    apply (F.realLayer _).toSubmodule.smul_mem
    exact F.realLayer_antitone
      (aeval_monomial_weightedSupport β w v hβ γ (mem_support_iff.mpr hc))
      ((F.realification.adapted_iff_coefficients w p).mp hp γ)

attribute [local irreducible] realChartSubstitute

noncomputable def weightedAdaptedRealChartLie
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    F.realification.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra v where
  toLinearMap := ((realChartSubstitute β).comp
    (F.realification.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.realification.adaptedSubmodule v) (fun p =>
        (F.realification.mem_adaptedSubmodule v _).mpr
          (F.adapted_realChartSubstitute_weightedSupport w v β hβ
            ((F.realification.mem_adaptedSubmodule w _).mp p.property)))
  map_lie' := by
    intro p q
    apply Subtype.ext
    exact realChartSubstitute_lie β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
      (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))

@[simp] theorem weightedAdaptedRealChartLie_coe
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (p : F.realification.adaptedLieSubalgebra w) :
    (F.weightedAdaptedRealChartLie w v β hβ p : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

noncomputable def weightedAdaptedRealChartHom
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) :
    (F.realification.adaptedPolynomialFiltration w).Group →*
      (F.realification.adaptedPolynomialFiltration v).Group :=
  NilpotentLieBCHGroup.map (F.weightedAdaptedRealChartLie w v β hβ)

@[simp] theorem weightedAdaptedRealChartHom_coord
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    ((F.weightedAdaptedRealChartHom w v β hβ g).coord :
        VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute β (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchMarkedChartRestoration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitRealChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) : F.realification.PolynomialOrbit v :=
  polynomialOrbitOfLog (realChartSubstitute β g.log)
    (F.adapted_realChartSubstitute_weightedSupport w v β hβ g.adapted)

attribute [local irreducible] realChartSubstitute

@[simp] theorem polynomialOrbitRealChart_log
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) :
    (F.polynomialOrbitRealChart w v β hβ g).log = realChartSubstitute β g.log := by
  unfold polynomialOrbitRealChart
  exact polynomialOrbitOfLog_log _ _

attribute [local irreducible] polynomialOrbitRealChart

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialPatch

variable {σ τ ξ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

noncomputable def ofWeightedChartShearOrbit (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    PolynomialPatch τ s d :=
  A.ofShearOrbit ((polynomialShearFiltration A.weight s A.weight_le).polynomialOrbitRealChart
    w (fun _ : τ => 1) β hβ g)

@[simp] theorem ofWeightedChartShearOrbit_weight (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    (A.ofWeightedChartShearOrbit w β hβ g).weight = A.weight := rfl

@[simp] theorem ofWeightedChartShearOrbit_kernel (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    (A.ofWeightedChartShearOrbit w β hβ g).kernel = A.kernel := rfl

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AveragedModeledPatchTransfer
namespace OAI

section

namespace Erdos3.PatchKernel

open scoped NNReal

variable {d : ℕ}

noncomputable def weightBounded (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C) (hf : LipschitzWith L f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) : PatchKernel d :=
  Φ.weight (fun x => f x / C) (L / C)
    (by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_nonneg C.coe_nonneg]
      have h := div_le_div_of_nonneg_right (hf.dist_le_mul x y) C.coe_nonneg
      simpa only [Real.dist_eq, NNReal.coe_div, mul_div_right_comm] using h)
    (fun x => ⟨div_nonneg (hbound x).1 C.coe_nonneg,
      (div_le_one (show (0 : ℝ) < C by exact lt_of_lt_of_le zero_lt_one hC)).mpr (hbound x).2⟩)

@[simp] theorem weightBounded_lip (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C) (hf : LipschitzWith L f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) :
    (Φ.weightBounded f L C hC hf hbound).lip = Φ.lip + L / C := rfl

end Erdos3.PatchKernel

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal

variable {σ : Type*} {s d E m : ℕ} {p : Fin m → ℕ}

noncomputable abbrev withRecoveredWeight (A : PolynomialPatch σ s d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) : PolynomialPatch σ s d :=
  { A with kernel := recoveredCellKernel A.kernel Ψ M a c K hM }

noncomputable def recoveredPatch (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i) : PolynomialPatch σ s (d + E) :=
  (A.withRecoveredWeight Ψ M a c K hM).insertAffineLifts B
    (fun i => (c i : ℝ)) (fun i j => (M i j : ℝ))
    (fun i j h => hweight i j (by exact_mod_cast h))

@[simp] theorem recoveredPatch_lip (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i) :
    (A.recoveredPatch B Ψ M a c K hM hweight).kernel.lip = A.kernel.lip + Ψ.lip * K + B.kernel.lip := rfl

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical NNReal

namespace NormalizedPolynomialTwist
variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def eval (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) : ℂ :=
  W.mask (fun i => (u i : ZMod W.modulus)) *
    W.smooth (fun i => (u i : ℝ) / N i, physicalGridFactorInput W.cover p (fun i => (u i : ℝ)))

@[simp] theorem eval_mono (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    {periodCap' coverCap' : ℝ} {L' : ℝ≥0}
    (hp : periodCap ≤ periodCap') (hc : coverCap ≤ coverCap') (hL : L ≤ L')
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.mono hp hc hL).eval N p u = W.eval N p u := rfl

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal Classical

variable {X : Type*} {m : ℕ} {J : Fin m → Type*}

theorem physicalGridFactorInput_subtractConstant (period : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ) (t : X → ℝ) :
    physicalGridFactorInput period (fun j => subtractConstant (c j) (p j)) t =
      physicalGridFactorInput period p t -
        (fun a : Σ j, J j => ((c a.1 a.2 / period : ℝ) : UnitAddCircle)) := by
  funext a
  simp only [physicalGridFactorInput, eval_subtractConstant, Pi.sub_apply, sub_div,
    AddCircle.coe_sub]

namespace NormalizedPolynomialTwist

variable [Fintype X] [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def shiftConstant
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) :
    NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L :=
  { W with
    smooth := fun z => W.smooth (z.1, z.2 -
      (fun a : Σ j, J j => ((c a.1 a.2 / W.cover : ℝ) : UnitAddCircle)))
    smooth_bound := fun z => W.smooth_bound _
    smooth_lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Prod.dist_eq, dist_sub_right] using W.smooth_lipschitz.dist_le_mul
        (x.1, x.2 - (fun a : Σ j, J j => ((c a.1 a.2 / W.cover : ℝ) : UnitAddCircle)))
        (y.1, y.2 - (fun a : Σ j, J j => ((c a.1 a.2 / W.cover : ℝ) : UnitAddCircle))) }

@[simp] theorem shiftConstant_modulus
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) : (W.shiftConstant c).modulus = W.modulus := rfl

@[simp] theorem shiftConstant_cover
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) : (W.shiftConstant c).cover = W.cover := rfl

@[simp] theorem shiftConstant_mask
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) : (W.shiftConstant c).mask = W.mask := rfl

@[simp] theorem eval_shiftConstant
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ∀ j, J j → ℝ) (N : X → ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.shiftConstant c).eval N p u =
      W.eval N (fun j => subtractConstant (c j) (p j)) u := by
  simp only [eval, shiftConstant, physicalGridFactorInput_subtractConstant]
  rfl

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

namespace VectorPolynomial.NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def scaleMask
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (c : ℂ) (hc : ‖c‖ ≤ 1) : NormalizedPolynomialTwist X Y periodCap coverCap L :=
  { W with
    mask := fun z => c * W.mask z
    mask_bound := fun z => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (W.mask_bound z) }

@[simp] theorem scaleMask_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (W.scaleMask c hc).eval N poly u = c * W.eval N poly u := by
  simp only [eval, scaleMask, mul_assoc]
  rfl

end VectorPolynomial.NormalizedPolynomialTwist

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateSplitFreezing
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeCoordinateSplit {σ : Type} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (i : σ) (s d : ℕ) (p epsilon : ℝ) (f : (σ → ℤ) → ℂ) where
  count : ℕ
  count_pos : 0 < count
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Bool → Type
  [lie : ∀ b, LieRing (L b)]
  [algebra : ∀ b, LieAlgebra ℚ (L b)]
  dim : Bool → ℕ
  [topology : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] L b)]
  [topologicalAdd : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] L b)]
  [continuousSMul : ∀ b, ContinuousSMul ℝ (ℝ ⊗[ℚ] L b)]
  [hausdorff : ∀ b, T2Space (ℝ ⊗[ℚ] L b)]
  model : ∀ b, RationalFilteredNilmanifold (L b) (∑ _ : σ, s) (dim b)
  multi : ∀ b, (model b).MultidegreeStructure (coordinateSplitBound s i b)
  complexity : ∀ b, (multi b).ComplexityLE p
  dimension_bound : ∀ b, dim b ≤ 2 ^ (Fintype.card σ * s) * d
  orbit : ∀ b, (multi b).filtration.realification.PolynomialOrbit
  test : ∀ b, Fin count → (model b).Niltest (fun _ : σ => 1)
  test_norm : ∀ b j, (test b j).normBound ≤ 1
  test_complexity : ∀ b j, (test b j).ComplexityLE p
  test_orbit : ∀ b j, (test b j).orbit = (multi b).orbitToOrdinary (orbit b)
  approximation : ∀ x, ‖f x - ∑ j, (test false j).eval x * (test true j).eval x‖ ≤ epsilon

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  {D : RationalFilteredNilmanifold L s d}

structure AdaptedData (R : D.DegreeRankStructure r) extends D.AdaptedModelData where
  central : IsCentralLieBasis basis
  rank_layers : ∀ i j, ∃ c ≤ finrank ℚ L, R.filtration.layer i j = basisTail basis c

namespace AdaptedData

variable {R : D.DegreeRankStructure r} (F : R.AdaptedData)

noncomputable def model : RationalFilteredNilmanifold L s (finrank ℚ L) := F.toAdaptedModelData.model

noncomputable def rank : F.model.DegreeRankStructure r where
  filtration := R.filtration
  associated := R.associated
  basis i j := basisOfTail F.basis _ (Classical.choose (F.rank_layers i.val j.val))
    (Classical.choose_spec (F.rank_layers i.val j.val)).2

end AdaptedData

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankRelationExistence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

structure NativeWeightedRankIntervals {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (H : Finset (ZMod N)) (p : ℝ) where
  budget_two : 2 ≤ p
  count : ℕ
  count_pos : 0 < count
  index : Fin count → ZMod N × ZMod N × ZMod N
  index_injective : Function.Injective index
  density : Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ count
  first_mem : ∀ i, (index i).2.1 ∈ H
  second_mem : ∀ i, (index i).2.1 - (index i).1 ∈ H
  third_mem : ∀ i, (index i).2.2 ∈ H
  fourth_mem : ∀ i, (index i).2.2 - (index i).1 ∈ H
  integer_relation : ∀ i,
    -((index i).2.1.val : ℤ) + ((index i).2.1 - (index i).1).val +
      (index i).2.2.val - ((index i).2.2 - (index i).1).val = 0
  branch : Fin count → Bool
  start : Fin count → ℕ
  length : Fin count → ℕ
  length_pos : ∀ i, 0 < length i
  endpoint_le : ∀ i, start i + length i ≤ N
  length_short : ∀ i, 2 * ((length i : ℤ) - 1) < N
  length_ratio : ∀ i, Real.exp (-p) ≤ (length i : ℝ) / N
  weight : ℤ → ℂ
  weight_norm : ∀ n, ‖weight n‖ ≤ 1
  lower : Fin count → ℤ → ℂ
  expansion : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) p (fun x => lower i (x ()))
  correlation : ∀ i, Real.exp (-p) ≤ ‖𝔼 n ∈ Finset.Ico (start i : ℤ) (start i + length i),
    fourPointProduct (W.eval out (index i).2.1) (W.eval out ((index i).2.1 - (index i).1))
      (W.eval out (index i).2.2) (W.eval out ((index i).2.2 - (index i).1))
      (cyclicBranchOffset (index i).1 (branch i)) n * weight n * lower i n‖

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

structure NativeRankInterval {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (H : Finset (ZMod N)) (t : ZMod N × ZMod N × ZMod N)
    (branch : Bool) (p q : ℝ) where
  first_mem : t.2.1 ∈ H
  second_mem : t.2.1 - t.1 ∈ H
  third_mem : t.2.2 ∈ H
  fourth_mem : t.2.2 - t.1 ∈ H
  integer_relation :
    -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0
  start : ℕ
  length : ℕ
  length_pos : 0 < length
  endpoint_le : start + length ≤ N
  length_short : 2 * ((length : ℤ) - 1) < N
  length_ratio : Real.exp (-p) ≤ (length : ℝ) / N
  lower : ℤ → ℂ
  expansion : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) q (fun x => lower (x ()))
  correlation : Real.exp (-p) ≤ ‖𝔼 n ∈ Finset.Ico (start : ℤ) (start + length),
    fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
      (W.eval out t.2.2) (W.eval out (t.2.2 - t.1))
      (cyclicBranchOffset t.1 branch) n * lower n‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedSynchronizedSquareFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

def ReducedSquareRelativeCongruent {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (P Q : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) : Prop :=
  (F.reducedSquareRealRelativePart w P).coord - (F.reducedSquareRealRelativePart w Q).coord ∈
    (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def SynchronizedNativeSquareData (T : σ → ℝ)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (S : Finset (σ → ℤ)) (h₀ : σ → ℤ)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (p q : ℝ) (l m : ℕ) : Prop :=
  let U := D.filtration.fastPointwiseSquare b ω hF (fun _ : σ => 1) W
  ∃ (ε γ : (σ → ℤ) → D.RealGroup)
    (r : (σ → ℤ) → D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (E P R : (σ → ℤ) → D.filtration.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (A B D₀ : D.filtration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1)),
    A * B * D₀ = D.filtration.adaptedReducedRealSymbolHom (fun _ => 1) g ∧
    D.filtration.quotientTop.SymbolSlowBound (D.filtration.quotientTopBasis b ω hF)
      (fun i => ω i.val) (D.filtration.quotientTopBasis_layers b ω hF)
      (fun _ => 1) T (Real.exp p) A ∧
    D.filtration.quotientTop.SymbolRationalGrid (D.filtration.quotientTopBasis b ω hF)
      (fun i => ω i.val) (D.filtration.quotientTopBasis_layers b ω hF) (fun _ => 1) l D₀ ∧
    D.filtration.quotientTop.SymbolFastIn (fun _ => 1)
      (U.map (D.filtration.reducedSquareSndSymbolMap (fun _ => 1))) B ∧
    (∀ h ∈ S, γ h ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr (ε h).coord i| ≤ Real.exp p) ∧
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) (r h)).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-(ε h).coord) (-(γ h).coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) (r h) = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) (ε h).coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) (γ h).coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h)) ∧
      E h * P h * R h = D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h) ∧
      D.filtration.squareFiltration.quotientTop.SymbolFastIn (fun _ => 1) U (P h) ∧
      D.filtration.reducedSquareRealSymbolHom (fun _ => 1) (E h) = A ∧
      D.filtration.reducedSquareRealSymbolHom (fun _ => 1) (R h) = D₀ ∧
      D.filtration.reducedSquareRealSymbolHom (fun _ => 1) (P h) = B ∧
      D.filtration.squareFiltration.quotientTop.SymbolSlowBound
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T (Real.exp q) (E h) ∧
      D.filtration.squareFiltration.quotientTop.SymbolRationalGrid
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) m (R h)) ∧
    ∀ h ∈ S, D.filtration.ReducedSquareRelativeCongruent (fun _ => 1) U (P h) (P h₀)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def BiasedSynchronizedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (_hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (l m : ℕ)
          (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
          (u : Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i}) →
            D.filtration.squareFiltration.quotientTop.AssociatedGraded),
          h₀ ∈ S ∧ Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ S.card ∧
          0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
          Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
          BasisGradedSubmodule
            (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
              (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
              (D.filtration.reducedSquareBasis_layers e ω hF))
            (fun i => squareBasisWeight ω i.val) W.toSubmodule ∧
          (∀ i j, rationalLogHeight
            ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
              (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
              (D.filtration.reducedSquareBasis_layers e ω hF)).repr (u i) j) ≤ (p + C) ^ C) ∧
          (∀ x ∈ D.filtration.fullFastGradedRelative e ω hF W,
            basisGradeProjection (D.filtration.associatedGradedBasis e ω hF) ω (s + 1) x = x →
              D.filtration.gradedFrequency e ω hF η x = 0) ∧
          (∀ h ∈ S, (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            ∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
          D.SynchronizedNativeSquareData e ω hF (fun i => (lengths i : ℝ)) g S h₀ W
            ((p + C) ^ C) ((p + C) ^ C) l m

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeRankZeroNiltest
namespace OAI

section

namespace Erdos3.NativeDegreeRankFamily

open scoped NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def component (i : Fin W.outputDim) (a : A) :
    W.model.Niltest (fun _ : Unit => 1) where
  orbit := W.orbit a
  observable := W.vertical.observable i
  normBound := 1
  lipBound := W.vertical.lipBound
  norm_le := W.vertical.norm i
  lipschitz := W.vertical.lipschitz i

end Erdos3.NativeDegreeRankFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (R : ∀ i, (D i).DegreeRankStructure r)

noncomputable def productRankLayerBasis (j k : Fin (s + 1)) :
    Basis (Σ i, Fin (finrank ℚ ((R i).filtration.layer j.val k.val))) ℚ
      ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val) :=
  (Pi.basis (fun i => (R i).basis j k)).map
    (DegreeRankLieFiltration.piLayerEquiv (fun i => (R i).filtration) j.val k.val)

noncomputable def productRankLayerFinBasis (j k : Fin (s + 1)) :
    Basis (Fin (finrank ℚ
      ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val))) ℚ
      ((DegreeRankLieFiltration.pi (fun i => (R i).filtration)).layer j.val k.val) :=
  (productRankLayerBasis D R j k).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis (productRankLayerBasis D R j k)).symm)

noncomputable def piRank : (pi D).DegreeRankStructure r where
  filtration := DegreeRankLieFiltration.pi (fun i => (R i).filtration)
  associated := by
    rw [DegreeRankLieFiltration.pi_associatedDegree]
    exact congrArg NilpotentLieFiltration.pi (funext (fun i => (R i).associated))
  basis := productRankLayerFinBasis D R

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NativeDegreeRankFamily

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r : ℕ} {A : Type*} {p : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def fourPointFactors (out : Fin W.outputDim) (a : Fin 4 → A) (δ : ℤ) :
    Fin 4 → W.model.Niltest (fun _ : Unit => 1) :=
  ![(W.component out (a 0)).conjugate,
    (W.component out (a 1)).translate (fun _ => by decide) (fun _ => δ),
    W.component out (a 2),
    ((W.component out (a 3)).translate (fun _ => by decide) (fun _ => δ)).conjugate]

noncomputable def fourPointFrequencies : Fin 4 → (W.L →ₗ[ℚ] ℚ) :=
  ![-W.vertical.frequency, W.vertical.frequency, W.vertical.frequency, -W.vertical.frequency]

end Erdos3.NativeDegreeRankFamily

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

namespace NativeRankInterval

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

noncomputable def productModels (i : Fin I.expansion.count) : ∀ k : Option (Fin 4),
    RationalFilteredNilmanifold (optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) s
      (optionDimension (I.expansion.dim i) (fun _ : Fin 4 => W.dim) k) :=
  optionFactors ((I.expansion.model i).raiseStep (Nat.sub_le s 1)) (fun _ : Fin 4 => W.model)

noncomputable def productRanks (i : Fin I.expansion.count)
    (R₀ : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r) :
    ∀ k, (I.productModels i k).DegreeRankStructure r
  | none => R₀
  | some _ => W.rank

noncomputable def productTests (i : Fin I.expansion.count) :
    ∀ k, (I.productModels i k).Niltest (fun _ : Unit => 1)
  | none => (I.expansion.test i).raiseStep (Nat.sub_le s 1)
  | some k => W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch) k

noncomputable def productFrequencies (i : Fin I.expansion.count) :
    ∀ k, optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => W.fourPointFrequencies k

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

noncomputable def productOrbit :
    (pi (I.productModels i)).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
  NilpotentLieFiltration.piRealOrbit (fun k => (I.productModels i k).filtration)
    (fun k => (I.productTests i k).orbit)

noncomputable def productSymbol {κ : Type*}
    (e : Basis κ ℚ (∀ k : Option (Fin 4),
      optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)) (ω : κ → ℕ)
    (hF : ∀ j, (pi (I.productModels i)).filtration.layer j =
      Submodule.span ℚ (e '' {a | j ≤ ω a})) :
    (pi (I.productModels i)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1) :=
  (pi (I.productModels i)).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
    ⟨⟨(I.productOrbit i).log, (I.productOrbit i).property⟩⟩

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

def rankProjection :
    (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k) →ₗ⁅ℚ⁆
      (Fin 4 → W.L) :=
  liePiMap (fun k : Fin 4 => liePiEval (R := ℚ)
    (M := optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L))
    (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)))

theorem rankProjection_mem_layer (d : ℕ)
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    (hx : x ∈ (pi (I.productModels i)).filtration.layer d) (k : Fin 4) :
    I.rankProjection i x k ∈ W.rank.filtration.layer d 1 := by
  have h := (NilpotentLieFiltration.mem_pi_layer (fun j => (I.productModels i j).filtration) d x).mp hx
    (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))
  change I.rankProjection i x k ∈ W.model.filtration.layer d at h
  rw [← W.rank.associated] at h
  change I.rankProjection i x k ∈ W.rank.filtration.layer d 0 at h
  rwa [W.rank.filtration.rank_zero_eq_one] at h

theorem rankProjection_mem_refiltered
    (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded) (d : ℕ)
    (x : ∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k)
    (hx : x ∈ (pi (I.productModels i)).filtration.gradedRefiltrationLayer U d) (k : Fin 4) :
    I.rankProjection i x k ∈ W.rank.filtration.layer d 1 :=
  I.rankProjection_mem_layer i d x
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer_le U d hx) k

end Erdos3.NativeRankInterval

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)
  (U : LieSubalgebra ℚ (pi (I.productModels i)).filtration.AssociatedGraded)

noncomputable def refilteredHorizontalImage (d : ℕ) :
    Submodule ℚ (Fin 4 → W.rank.filtration.HigherHorizontal d) :=
  W.rank.filtration.layerHorizontalImage
    ((pi (I.productModels i)).filtration.gradedRefiltrationLayer U)
    (I.rankProjection i) (I.rankProjection_mem_refiltered i U) d

def SunflowerKernel : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℕ) (a : FreeMagma (Fin n)),
    lieTreeWeight d a = s → a.length = r →
    ∀ v : ∀ j, W.rank.filtration.HigherHorizontal (d j),
      (∀ j, v j ∈ fourFirstProjection (I.refilteredHorizontalImage i U (d j))) →
      ∀ j k, j ≠ k → j ∈ lieTreeSupport a → k ∈ lieTreeSupport a →
      v j ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d j)) →
      v k ∈ fourDependentProjection (I.refilteredHorizontalImage i U (d k)) →
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue d a v) = 0

def BracketKernel : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℕ) (a : FreeMagma (Fin n)),
    lieTreeWeight d a = s → a.length = r →
    ∀ z : Fin n → ℝ ⊗[ℚ]
      (∀ k : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) k),
    (∀ j, z j ∈ (pi (I.productModels i)).filtration.realGradedRefiltrationLayer U (d j)) →
    realifyFunctional (piFrequency (I.productFrequencies i)) (lieTreeEval z a) = 0

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

structure SunflowerWitness (I : NativeRankInterval W out H t branch p q) (P : ℝ) where
  index : Fin I.expansion.count
  lowerRank : ((I.expansion.model index).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r
  lower_complexity : lowerRank.ComplexityLE P
  lower_top : lowerRank.realSubgroup s r = ⊥
  adapted : (piRank (I.productModels index) (I.productRanks index lowerRank)).AdaptedData
  adapted_complexity : adapted.rank.ComplexityLE P
  forward : ∀ j k, rationalLogHeight ((pi (I.productModels index)).basis.repr (adapted.basis j) k) ≤ P
  backward : ∀ k j, rationalLogHeight (adapted.basis.repr ((pi (I.productModels index)).basis k) j) ≤ P
  denominator : ℕ
  subalgebra : LieSubalgebra ℚ (pi (I.productModels index)).filtration.AssociatedGraded
  spanning : Fin (finrank ℚ (∀ k : Option (Fin 4),
    optionLieSpace (I.expansion.L index) (fun _ : Fin 4 => W.L) k)) →
    (pi (I.productModels index)).filtration.AssociatedGraded
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp P
  span : Submodule.span ℚ (Set.range spanning) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule
    ((pi (I.productModels index)).filtration.associatedGradedBasis adapted.basis adapted.weight adapted.layers)
    adapted.weight subalgebra.toSubmodule
  height : ∀ j k, rationalLogHeight
    (((pi (I.productModels index)).filtration.associatedGradedBasis adapted.basis adapted.weight adapted.layers).repr
      (spanning j) k) ≤ P
  bracket : I.BracketKernel index subalgebra
  sunflower : I.SunflowerKernel index subalgebra
  factorization : (pi (I.productModels index)).filtration.SymbolFactorizationIn
    adapted.basis adapted.weight adapted.layers (fun _ : Unit => (I.length : ℝ))
    (I.productSymbol index adapted.basis adapted.weight adapted.layers) P denominator subalgebra

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

noncomputable def projectedOrbitCoefficient (α : Unit →₀ ℕ) :
    (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ :=
  ⟨(I.rankProjection D.index).toLinearMap.baseChange ℝ (coefficients (I.productOrbit D.index).log α),
    W.rank.filtration.real_projectedCoefficient_mem (pi (I.productModels D.index)).filtration
      (I.rankProjection D.index) (I.rankProjection_mem_layer D.index)
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) α
      ⟨(I.productOrbit D.index).log, (I.productOrbit D.index).property⟩⟩

@[simp] theorem projectedOrbitCoefficient_coe (α : Unit →₀ ℕ) :
    (D.projectedOrbitCoefficient α : ℝ ⊗[ℚ] (Fin 4 → W.L)) =
      (I.rankProjection D.index).toLinearMap.baseChange ℝ
        (coefficients (I.productOrbit D.index).log α) := rfl

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι J Ω L : Type*} [Fintype σ] [Fintype ι] [Fintype J] [Fintype Ω]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

def HasCommonRefilteredOrbitFactors
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
    (side : σ → ℝ) (q : ℝ) (m : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) : Prop :=
  ∃ e middle r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
    e * middle * r = g ∧
    (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b w hF (fun _ => 1)
      (F.realPolynomialSymbolHom b w hF (fun _ => 1) middle).coord) ∈
        realificationLieSubalgebra W) ∧
    F.PolynomialSlowBound b (fun _ => 1) side (Real.exp q) e ∧
    F.PolynomialRationalGrid b (fun _ => 1) m r ∧
    coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
    coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
      coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3.FreeDegreeRankLieAlgebra

open VectorPolynomial

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (hr : r ≤ s) {σ : Type*} (g : X → σ →₀ ℕ)

noncomputable def gradingHom :
    FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆
      VectorPolynomial σ ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  lift ((filtration X s r w hw hr).polynomialFiltration (σ := σ)) w hw
    (fun x => monomial (g x) (of X s r w hw x)) (fun x => by
      apply (filtration X s r w hw hr).monomial_mem_polynomialFiltration
      rw [(filtration X s r w hw hr).rank_zero_eq_one]
      exact of_mem_layer X s r w hw hr x)

@[simp] theorem gradingHom_of (x : X) :
    gradingHom X s r w hw hr g (of X s r w hw x) = monomial (g x) (of X s r w hw x) := by
  simp only [gradingHom, lift_of]

end Erdos3.FreeDegreeRankLieAlgebra

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def markedPolynomialLayer (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (d k l : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈
    markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (markedLieSpan v w marked _ _ _).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (markedLieSpan v w marked _ _ _).smul_mem c (hp α)

theorem markedPolynomialLayer_antitone (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    markedPolynomialLayer (σ := σ) v w marked e m n ≤ markedPolynomialLayer v w marked d k l := by
  intro p hp α
  exact markedLieSpan_antitone v w marked hde (Nat.add_le_add_right hkm _) hln (hp α)

theorem monomial_mem_markedPolynomialLayer (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (d k l : ℕ) (α : σ →₀ ℕ) {x : L}
    (hx : x ∈ markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l) :
    monomial (R := ℚ) α x ∈ markedPolynomialLayer v w marked d k l := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp only [coefficients_monomial, Finsupp.single_eq_of_ne (Ne.symm h), Submodule.zero_mem]

theorem markedPolynomialLayer_lie_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ markedPolynomialLayer v w marked d k l)
    (hq : q ∈ markedPolynomialLayer v w marked e m n) :
    ⁅p, q⁆ ∈ markedPolynomialLayer v w marked (d + e) (k + m) (l + n) := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, sum_lie_sum]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  apply monomial_mem_markedPolynomialLayer
  simpa only [map_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    markedLieSpan_lie_mem v w marked (hp α) (hq β)

theorem markedPolynomialLayer_directionalDerivative [Fintype σ]
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (h : σ → ℚ)
    {d k l : ℕ} {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    directionalDerivative h p ∈ markedPolynomialLayer v w marked d (k + 1) l := by
  intro α
  change coefficients (directionalDerivative h p) α ∈
    markedLieSpan v w marked d (k + 1 + Finsupp.weight (fun _ : σ => 1) α) l
  rw [coefficients_directionalDerivative]
  apply (markedLieSpan v w marked d (k + 1 + Finsupp.weight (fun _ : σ => 1) α) l).sum_mem
  intro i _
  have he : k + Finsupp.weight (fun _ : σ => 1) (α + Finsupp.single i 1) =
      k + 1 + Finsupp.weight (fun _ : σ => 1) α := by
    rw [map_add, Finsupp.weight_single, one_smul]
    omega
  have hi := hp (α + Finsupp.single i 1)
  rw [he] at hi
  exact (markedLieSpan v w marked _ _ _).smul_mem _
    ((markedLieSpan v w marked _ _ _).smul_mem _ hi)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedPolynomialLayer_degree_zero_eq_one (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (k l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked 0 k l = markedPolynomialLayer v w marked 1 k l := by
  ext p
  change (∀ α, coefficients p α ∈ markedLieSpan v w marked 0
    (k + Finsupp.weight (fun _ : σ => 1) α) l) ↔ _
  simp only [markedLieSpan_degree_zero_eq_one v w marked hw]
  rfl

theorem markedPolynomialLayer_degree_terminal {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (k l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked (s + 1) k l = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply coefficients.injective
  ext α
  have h := markedLieSpan_le_layer F v w marked hv (s + 1) _ l (hp α)
  rw [F.layer_eq_bot_of_past_top (Or.inl (Nat.lt_succ_self s)), Submodule.mem_bot] at h
  simpa only [map_zero, Finsupp.zero_apply] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftSubalgebra (t : ℕ) :
    LieSubalgebra ℚ (F.associatedDegree.PolynomialShiftAlgebra t) where
  carrier := {x | x.left.val ∈ markedPolynomialLayer v w marked 0 0 0}
  zero_mem' := (markedPolynomialLayer v w marked 0 0 0).zero_mem
  add_mem' hx hy := (markedPolynomialLayer v w marked 0 0 0).add_mem hx hy
  smul_mem' c _ hx := (markedPolynomialLayer v w marked 0 0 0).smul_mem c hx
  lie_mem' := by
    intro x y hx hy
    change ⁅x.left.val, y.left.val⁆ + directionalDerivative x.right y.left.val -
      directionalDerivative y.right x.left.val ∈ markedPolynomialLayer v w marked 0 0 0
    have hder (h : Fin t → ℚ) (p : VectorPolynomial (Fin t) ℚ L)
        (hp : p ∈ markedPolynomialLayer v w marked 0 0 0) :
        directionalDerivative h p ∈ markedPolynomialLayer v w marked 0 0 0 :=
      markedPolynomialLayer_antitone v w marked le_rfl (Nat.zero_le 1) le_rfl
        (markedPolynomialLayer_directionalDerivative v w marked h (d := 0) (k := 0) (l := 0) hp)
    exact (markedPolynomialLayer v w marked 0 0 0).sub_mem
      ((markedPolynomialLayer v w marked 0 0 0).add_mem
        (markedPolynomialLayer_lie_mem v w marked
          (d := 0) (e := 0) (k := 0) (m := 0) (l := 0) (n := 0) hx hy)
        (hder x.right y.left.val hy)) (hder y.right x.left.val hx)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftPolynomialSubmodule (t d k l : ℕ) :
    Submodule ℚ (markedShiftSubalgebra F v w marked t) where
  carrier := {x | x.val.right = 0 ∧ x.val.left.val ∈ markedPolynomialLayer v w marked d k l}
  zero_mem' := ⟨rfl, (markedPolynomialLayer v w marked d k l).zero_mem⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · change x.val.right + y.val.right = (0 : RationalTorus.Algebra t)
      rw [hx.1, hy.1, add_zero]
    · exact (markedPolynomialLayer v w marked d k l).add_mem hx.2 hy.2
  smul_mem' c x hx := by
    constructor
    · change c • x.val.right = 0
      rw [hx.1, smul_zero]
    · exact (markedPolynomialLayer v w marked d k l).smul_mem c hx.2

noncomputable def markedShiftSecondIdeal (t : ℕ) :
    LieIdeal ℚ (markedShiftSubalgebra F v w marked t) :=
  { markedShiftPolynomialSubmodule F v w marked t 0 2 0 with
    lie_mem := by
      intro x y hy
      constructor
      · rfl
      · change ⁅x.val.left.val, y.val.left.val⁆ + directionalDerivative x.val.right y.val.left.val -
          directionalDerivative y.val.right x.val.left.val ∈ markedPolynomialLayer v w marked 0 2 0
        rw [hy.1]
        have hz : directionalDerivative (0 : Fin t → ℚ) x.val.left.val = 0 := by
          simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
            LinearMap.zero_apply]
        change ⁅x.val.left.val, y.val.left.val⁆ + directionalDerivative x.val.right y.val.left.val -
          directionalDerivative (0 : Fin t → ℚ) x.val.left.val ∈ markedPolynomialLayer v w marked 0 2 0
        rw [hz, sub_zero]
        apply (markedPolynomialLayer v w marked 0 2 0).add_mem
        · exact markedPolynomialLayer_lie_mem v w marked
            (d := 0) (e := 0) (k := 0) (m := 2) (l := 0) (n := 0) x.property hy.2
        · exact markedPolynomialLayer_antitone v w marked le_rfl (by omega : 2 ≤ 2 + 1) le_rfl
            (markedPolynomialLayer_directionalDerivative v w marked x.val.right
              (d := 0) (k := 2) (l := 0) hy.2) }

abbrev MarkedShiftQuotient (t : ℕ) :=
  markedShiftSubalgebra F v w marked t ⧸ markedShiftSecondIdeal F v w marked t

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftBiLayer (t h n : ℕ) :
    Submodule ℚ (markedShiftSubalgebra F v w marked t) where
  carrier := {x | x.val.left.val ∈ markedPolynomialLayer v w marked n h 0 ∧
    (n ≠ 0 ∨ 1 < h → x.val.right = 0)}
  zero_mem' := ⟨(markedPolynomialLayer v w marked n h 0).zero_mem, fun _ => rfl⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨(markedPolynomialLayer v w marked n h 0).add_mem hx.1 hy.1, ?_⟩
    intro hc
    change x.val.right + y.val.right = 0
    rw [hx.2 hc, hy.2 hc, add_zero]
  smul_mem' c x hx := by
    refine ⟨(markedPolynomialLayer v w marked n h 0).smul_mem c hx.1, ?_⟩
    intro hc
    change c • x.val.right = 0
    rw [hx.2 hc, smul_zero]

theorem markedShiftBiLayer_antitone (t : ℕ) {h k n m : ℕ} (hh : h ≤ k) (hn : n ≤ m) :
    markedShiftBiLayer F v w marked t k m ≤ markedShiftBiLayer F v w marked t h n := by
  intro x hx
  refine ⟨markedPolynomialLayer_antitone v w marked hn hh le_rfl hx.1, ?_⟩
  intro hc
  exact hx.2 (by omega)

theorem markedShiftBiLayer_zero (t : ℕ) : markedShiftBiLayer F v w marked t 0 0 = ⊤ := by
  apply top_unique
  intro x _
  refine ⟨x.property, ?_⟩
  intro hc
  omega

theorem markedPolynomialLayer_shiftDerivative {t h n k m : ℕ} (u : Fin t → ℚ)
    (hu : n ≠ 0 ∨ 1 < h → u = 0) {p : VectorPolynomial (Fin t) ℚ L}
    (hp : p ∈ markedPolynomialLayer v w marked m k 0) :
    directionalDerivative u p ∈ markedPolynomialLayer v w marked (n + m) (h + k) 0 := by
  by_cases ha : n = 0 ∧ h ≤ 1
  · obtain ⟨rfl, hh⟩ := ha
    have hd := markedPolynomialLayer_directionalDerivative v w marked u hp
    simpa only [Nat.zero_add] using
      markedPolynomialLayer_antitone v w marked le_rfl (by omega : h + k ≤ k + 1) le_rfl hd
  · have hz := hu (by omega)
    rw [hz]
    simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      LinearMap.zero_apply, Submodule.zero_mem]

theorem markedShiftBiLayer_lie_mem (t : ℕ) {h k n m : ℕ}
    {x y : markedShiftSubalgebra F v w marked t}
    (hx : x ∈ markedShiftBiLayer F v w marked t h n)
    (hy : y ∈ markedShiftBiLayer F v w marked t k m) :
    ⁅x, y⁆ ∈ markedShiftBiLayer F v w marked t (h + k) (n + m) := by
  constructor
  · change ⁅x.val.left.val, y.val.left.val⁆ + directionalDerivative x.val.right y.val.left.val -
      directionalDerivative y.val.right x.val.left.val ∈ markedPolynomialLayer v w marked (n + m) (h + k) 0
    apply (markedPolynomialLayer v w marked (n + m) (h + k) 0).sub_mem
    · exact (markedPolynomialLayer v w marked (n + m) (h + k) 0).add_mem
        (markedPolynomialLayer_lie_mem v w marked (l := 0) (n := 0) hx.1 hy.1)
        (markedPolynomialLayer_shiftDerivative v w marked x.val.right hx.2 hy.1)
    · simpa only [Nat.add_comm] using
        markedPolynomialLayer_shiftDerivative v w marked y.val.right hy.2 hx.1
  · intro _
    rfl

theorem markedShiftBiLayer_eq_polynomialSubmodule (t h n : ℕ) (hc : n ≠ 0 ∨ 1 < h) :
    markedShiftBiLayer F v w marked t h n = markedShiftPolynomialSubmodule F v w marked t n h 0 := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2 hc, hx.1⟩
  · intro hx
    exact ⟨hx.2, fun _ => hx.1⟩

theorem markedShiftBiLayer_second (t : ℕ) :
    markedShiftBiLayer F v w marked t 2 0 = (markedShiftSecondIdeal F v w marked t).toSubmodule :=
  markedShiftBiLayer_eq_polynomialSubmodule F v w marked t 2 0 (Or.inr (by decide))

theorem markedShiftBiLayer_positive (hw : ∀ i, 0 < w i) (t : ℕ) :
    markedShiftBiLayer F v w marked t 0 1 ⊔ markedShiftBiLayer F v w marked t 1 0 = ⊤ := by
  apply top_unique
  intro x _
  let p : markedShiftSubalgebra F v w marked t := ⟨⟨x.val.left, 0⟩, x.property⟩
  let q : markedShiftSubalgebra F v w marked t :=
    ⟨⟨0, x.val.right⟩, (markedPolynomialLayer v w marked 0 0 0).zero_mem⟩
  have hp : p ∈ markedShiftBiLayer F v w marked t 0 1 := by
    exact ⟨(markedPolynomialLayer_degree_zero_eq_one v w marked hw 0 0).le x.property,
      fun _ => rfl⟩
  have hq : q ∈ markedShiftBiLayer F v w marked t 1 0 := by
    refine ⟨(markedPolynomialLayer v w marked 0 1 0).zero_mem, ?_⟩
    intro hc
    omega
  have he : p + q = x := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · change x.val.left + 0 = x.val.left
      exact add_zero _
    · change 0 + x.val.right = x.val.right
      exact zero_add _
  have hx := Submodule.add_mem _ (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hq)
  rwa [he] at hx

theorem markedShiftBiLayer_degree_terminal
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (t h : ℕ) :
    markedShiftBiLayer F v w marked t h (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  have hp : x.val.left.val = 0 := by
    simpa only [markedPolynomialLayer_degree_terminal F v w marked hv, Submodule.mem_bot] using hx.1
  have hq : x.val.right = 0 := hx.2 (Or.inl (by omega))
  change x = 0
  apply Subtype.ext
  apply LieAlgebra.SemiDirectSum.ext
  · apply Subtype.ext
    change x.val.left.val = 0
    exact hp
  · change x.val.right = 0
    exact hq

end Erdos3

end

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftQuotientLayer (t : ℕ) (a : Fin 2 → ℕ) :
    Submodule ℚ (MarkedShiftQuotient F v w marked t) :=
  (markedShiftBiLayer F v w marked t (a 0) (a 1)).map
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap

theorem markedShiftQuotientLayer_antitone (t : ℕ) :
    Antitone (markedShiftQuotientLayer F v w marked t) := by
  intro a b hab
  exact Submodule.map_mono (markedShiftBiLayer_antitone F v w marked t (hab 0) (hab 1))

theorem markedShiftQuotientLayer_zero (t : ℕ) : markedShiftQuotientLayer F v w marked t 0 = ⊤ := by
  change (markedShiftBiLayer F v w marked t 0 0).map _ = ⊤
  rw [markedShiftBiLayer_zero, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective _)

theorem markedShiftQuotientLayer_lie_mem (t : ℕ) {a b : Fin 2 → ℕ}
    {x y : MarkedShiftQuotient F v w marked t}
    (hx : x ∈ markedShiftQuotientLayer F v w marked t a)
    (hy : y ∈ markedShiftQuotientLayer F v w marked t b) :
    ⁅x, y⁆ ∈ markedShiftQuotientLayer F v w marked t (a + b) := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨⁅p, q⁆, markedShiftBiLayer_lie_mem F v w marked t hp hq,
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).map_lie p q⟩

theorem markedShiftQuotientLayer_eq_bot_of_le (t : ℕ) (a : Fin 2 → ℕ)
    (ha : markedShiftBiLayer F v w marked t (a 0) (a 1) ≤
      (markedShiftSecondIdeal F v w marked t).toSubmodule) :
    markedShiftQuotientLayer F v w marked t a = ⊥ := by
  apply bot_unique
  rintro x ⟨y, hy, rfl⟩
  exact (lieQuotientMap_eq_zero _ y).mpr (ha hy)

theorem markedShiftQuotientLayer_terminal
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ) (a : Fin 2 → ℕ)
    (ha : ¬a ≤ mixedCorrelationDegree s) : markedShiftQuotientLayer F v w marked t a = ⊥ := by
  have hnot : ¬(a 0 ≤ 1 ∧ a 1 ≤ s) := by
    intro h
    apply ha
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  have hcases : 1 < a 0 ∨ s < a 1 := by omega
  rcases hcases with hh | hn
  · apply markedShiftQuotientLayer_eq_bot_of_le F v w marked t a
    exact (markedShiftBiLayer_antitone F v w marked t (by omega : 2 ≤ a 0) (Nat.zero_le _)).trans
      (markedShiftBiLayer_second F v w marked t).le
  · have hzero : markedShiftBiLayer F v w marked t (a 0) (a 1) = ⊥ := by
      apply bot_unique
      exact (markedShiftBiLayer_antitone F v w marked t le_rfl (by omega : s + 1 ≤ a 1)).trans
        (markedShiftBiLayer_degree_terminal F v w marked hv t (a 0)).le
    unfold markedShiftQuotientLayer
    rw [hzero, Submodule.map_bot]

theorem markedShiftQuotientLayer_positive (hw : ∀ i, 0 < w i) (t : ℕ) :
    markedShiftQuotientLayer F v w marked t (correlationInput 0 1) ⊔
      markedShiftQuotientLayer F v w marked t (correlationInput 1 0) = ⊤ := by
  change (markedShiftBiLayer F v w marked t 0 1).map _ ⊔
    (markedShiftBiLayer F v w marked t 1 0).map _ = ⊤
  rw [← Submodule.map_sup, markedShiftBiLayer_positive F v w marked hw t, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective _)

theorem markedShiftQuotientLayer_total_one (hw : ∀ i, 0 < w i) (t : ℕ) :
    multidegreeTotalLayer (markedShiftQuotientLayer F v w marked t) 1 = ⊤ := by
  apply top_unique
  rw [← markedShiftQuotientLayer_positive F v w marked hw t]
  apply sup_le
  · apply layer_le_multidegreeTotalLayer _ (correlationInput 0 1) 1
    decide
  · apply layer_le_multidegreeTotalLayer _ (correlationInput 1 0) 1
    decide

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedCorrelationDegree_sum (s : ℕ) : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
  rw [Fin.sum_univ_two]
  change 1 + s = s + 1
  omega

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def markedShiftMultidegree (t : ℕ) :
    MultidegreeLieFiltration (Fin 2) (MarkedShiftQuotient F v w marked t) (s + 1)
      (mixedCorrelationDegree s) :=
  MultidegreeLieFiltration.ofLayers (markedShiftQuotientLayer F v w marked t)
    (markedShiftQuotientLayer_antitone F v w marked t) (markedShiftQuotientLayer_zero F v w marked t)
    (markedShiftQuotientLayer_lie_mem F v w marked t) (markedShiftQuotientLayer_total_one F v w marked hw t)
    (mixedCorrelationDegree s) (markedShiftQuotientLayer_terminal F v w marked hv t) (s + 1)
    (by rw [mixedCorrelationDegree_sum])

@[simp] theorem markedShiftMultidegree_layer (t : ℕ) (a : Fin 2 → ℕ) :
    (markedShiftMultidegree F v w marked hw hv t).layer a = markedShiftQuotientLayer F v w marked t a := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialOrbitLogSum
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {F : NilpotentLieFiltration L s} {w : σ → ℕ}

noncomputable def PolynomialOrbit.logSum (g h : F.PolynomialOrbit w) : F.PolynomialOrbit w :=
  ⟨⟨g.log + h.log⟩, (F.adaptedLieSubalgebra w).add_mem g.property h.property⟩

@[simp] theorem PolynomialOrbit.logSum_log (g h : F.PolynomialOrbit w) :
    (g.logSum h).log = g.log + h.log := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

noncomputable def allocatedCenteredJointDensity
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) : ℝ :=
  allocatedCoefficientDensity B U b hb o hR hσ S
    (coefficientConstantCenter U center +
      affineSampleCoefficientTorus U poly hmem
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

structure AllocatedExternalCandidateSampler : Prop where
  size_pos : ∀ x, 0 < N x
  trim_pos : 0 < τ
  narrow_pos : 0 < ξ
  stride_pos : ∀ x, 0 < stride x
  bases_nonempty : (trimmedIntegerBox N (spatialTrimMargin τ N)).Nonempty
  smooth_mass_pos : 0 < ∑' z, selectedResidueSmoothWeight stride cells
    (allocatedExternalCandidateWidths B U b S N τ ξ) z
  center_mass_pos : 0 < selectedJointDensityMass (trimmedIntegerBox N (spatialTrimMargin τ N))
    stride cells (allocatedExternalCandidateWidths B U b S N τ ξ)
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

abbrev Path (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Type _ :=
  trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 (allocatedExternalCandidateWidths B U b S N τ ξ) 1

abbrev Site (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Type _ :=
  integerBox (allocatedExternalCandidateSides B U b S)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
def physical (z : A.Path) (site : A.Site) : X → ℤ :=
  jointIntegerPhysicalSite site.val (z.1.val, z.2.val)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
@[simp] theorem physical_eq (z : A.Path) (site : A.Site) :
    A.physical z site = jointIntegerPhysicalSite site.val (z.1.val, z.2.val) := rfl

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedZeroLayerLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

omit [Fintype X] in

@[simp] theorem allocatedCenteredJointDensity_zero_layers
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z = 1 := by
  simp only [allocatedCenteredJointDensity, allocatedCoefficientDensity,
    canonicalCoefficientDensity, Finset.univ_eq_empty, Finset.prod_empty]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} {I J : Fin 0 → Type*} {n : Fin 0 → ℕ}
    (B : LayerSamplerAxis I n → Type*)

def zeroLayerVariablesEquiv : LayerSamplerVariables G I n B ≃ G where
  toFun := fun k => match k with
    | .inl g => g
    | .inr a => Fin.elim0 a.1.1
  invFun := Sum.inl
  left_inv := by
    intro k
    cases k with
    | inl g => rfl
    | inr a => exact Fin.elim0 a.1.1
  right_inv := fun _ => rfl

@[simp] theorem zeroLayerVariablesEquiv_inl (g : G) :
    zeroLayerVariablesEquiv B (Sum.inl g) = g := rfl

@[simp] theorem zeroLayerVariablesEquiv_symm (g : G) :
    (zeroLayerVariablesEquiv B).symm g = Sum.inl g := rfl

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

@[simp] theorem allocatedExternalCandidateSides_zero_layers
    (k : LayerSamplerVariables G I n B) :
    allocatedExternalCandidateSides B U b S k = S.value := by
  cases k with
  | inl g => rfl
  | inr a => exact Fin.elim0 a.1.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I J : Fin m → Type*} {n : Fin m → ℕ}
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type*)

def emptyLayerVariablesEquiv : LayerSamplerVariables G I n B ≃ G where
  toFun := fun k => match k with
    | .inl g => g
    | .inr a => Sum.elim isEmptyElim isEmptyElim a.1.2
  invFun := Sum.inl
  left_inv := by
    intro k
    cases k with
    | inl g => rfl
    | inr a => exact Sum.elim isEmptyElim isEmptyElim a.1.2
  right_inv := fun _ => rfl

@[simp] theorem emptyLayerVariablesEquiv_inl (g : G) :
    emptyLayerVariablesEquiv B (Sum.inl g) = g := rfl

@[simp] theorem emptyLayerVariablesEquiv_symm (g : G) :
    (emptyLayerVariablesEquiv B).symm g = Sum.inl g := rfl

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

@[simp] theorem allocatedExternalCandidateSides_empty_layers
    (k : LayerSamplerVariables G I n B) :
    allocatedExternalCandidateSides B U b S k = S.value := by
  cases k with
  | inl g => rfl
  | inr a => exact Sum.elim isEmptyElim isEmptyElim a.1.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedOriginalSourceProjection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

def physicalDensityProjection.{uK, uJ, uX, uF} {K : Type uK} [Fintype K] {m q : ℕ}
    {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (dirs : Fin q → K → ℤ) (d : ℕ)
    (density : CoefficientTorus (K := K) U → ℝ)
    (f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ) : Prop :=
  ∀ {X : Type uX} {F : Type uF} [Fintype F]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : F → ℂ) {η : ℝ},
    (∀ z, ‖coefficientTorusFourierSum U frequency coeff z - (density z : ℂ)‖ ≤ η) →
    ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
    ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : Option K → X → ℝ),
      ‖affineCubeFourierProjection U root dirs frequency p coeff v -
        (f (euclideanCoefficientJetMap U root (Matrix.of dirs)
          (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
          (affineCoefficientCoverSample U p hm d v)) : ℂ)‖ ≤ η

universe uK uJ uX uF

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CommonSectionAmbientDensityMultiple
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_fixed_kernel_ambient_density_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L C : ℝ≥0}
    (_hf : LipschitzWith L f) (_hcap : ∀ z, f z ∈ Set.Icc (0 : ℝ) C)
    (_hmass : (∫ x, f (coefficientAmbientTorus U x) ∂μ) = 1),
    let site := fun s k => affineSite root difference s (some k)
    let E := coefficientSiteTorusMap U site
    let π := Set.rangeFactorization E
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    ∃ (g : Set.range E → ℝ)
      (F : (JetAmbientIndex (fun _ : Fin m => Finset (Fin q)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) C) ∧
      Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x)))).map π =
        realDensityMeasure (μ.map π) g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith (L * (Fintype.card (Finset (Fin q)) *
        Real.toNNReal (Real.exp ((P + A) ^ A)))) F ∧
      (∀ x, g (π x) = F (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x))) ∧
      ∀ {X Index : Type*} [Fintype Index]
        (frequency : Index → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : Index → ℂ) {η : ℝ},
        (∀ x, ‖coefficientTorusFourierSum U frequency coeff x - (f (coefficientAmbientTorus U x) : ℂ)‖ ≤ η) →
        ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
        (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
        ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K → X → ℝ),
          ‖affineCubeFourierProjection U root difference frequency p coeff z -
            (g (π (affineCoefficientCoverSample U p hm d z)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hsection⟩ := exists_fixed_kernel_bounded_section_multiple m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hsection⟩ := hsection root₀ difference₀ a ha hperiod hP hK hsite period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ f L C hf hcap hmass site E π cover
  obtain ⟨T, hTb, hT⟩ := hsection root difference e hroot hdifference
  have hb (z) : ‖f z‖ ≤ C := by rw [Real.norm_of_nonneg (hcap z).1]; exact (hcap z).2
  obtain ⟨g, hgc, hgb, hgi, hgm, hg, hglaw⟩ :=
    exists_covered_coefficient_density U site d hd T (fun j x => hT j x) μ
      (fun x => f (coefficientAmbientTorus U x))
      (hf.continuous.comp (coefficientAmbientTorus_continuous U))
      (fun x => hcap _) hmass
  refine ⟨g, coefficientSectionAmbientDensity U site d T μ f,
    hgc, hgb, hgi, hgm, hglaw,
    coefficientSectionAmbientDensity_bounds U site d T μ f hcap, ?_, ?_, ?_⟩
  · apply coefficientSectionAmbientDensity_lipschitz U site d T μ f hf hb
    intro j i
    have hentry (s) : ‖T j i s‖ ≤ Real.exp ((P + A) ^ A) := by
      have h := (Finset.single_le_sum (fun k _ => abs_nonneg (T j k s : ℝ))
        (Finset.mem_univ i)).trans (hTb j s)
      simpa only [← Int.norm_cast_real, Real.norm_eq_abs] using h
    calc
      _ ≤ ∑ _s : Finset (Fin q), Real.exp ((P + A) ^ A) :=
        Finset.sum_le_sum (fun s _ => hentry s)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        NNReal.coe_mul, NNReal.coe_natCast, Real.toNNReal_of_nonneg (Real.exp_pos _).le]
                  rfl
  · intro x
    exact (hg x).trans (coefficientSectionAmbientDensity_eq U site d T μ f x).symm
  · intro X Index _ frequency coeff η happrox p hp hm z
    let R := coefficientSiteResidual U site (fun _ => d) T
    let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => d) T
    have hfactor (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
        (coefficientArrayFunctional U frequency).comp R = 0 ↔
          affineCubeModeFactors U root difference frequency := by
      change (coefficientArrayFunctional U frequency).comp
        (coefficientSiteResidual U site (fun _ => d) T) = 0 ↔ _
      rw [coefficientSiteResidual_zero_iff U site (fun _ => d) T (fun _ => hd) (fun j x => hT j x),
        affineCubeModeFactors_iff_bounded]
    have he := coefficientTorusFourierProjection_approx_residualAverage U R hR root difference hfactor
      frequency coeff μ (fun x => f (coefficientAmbientTorus U x)) happrox
      (affineSampleCoefficientTorus U p hm z)
      (coefficientResidual_section_integrable U R hR μ _
        (hf.continuous.comp (coefficientAmbientTorus_continuous U)) (fun x => hb _) _)
    have hvalue := hg (affineCoefficientCoverSample U p hm d z)
    rw [affineCoefficientCoverSample_projection U p hm d hd z] at hvalue
    rw [hvalue]
    simpa only [coefficientTorusCharacter_sample U _ p hp hm z, affineCubeFourierProjection] using he

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedAmbientProjectedDensityMultiple
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_fixed_kernel_euclidean_ambient_density_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L C : ℝ≥0}
    (_hf : LipschitzWith L f) (_hcap : ∀ z, f z ∈ Set.Icc (0 : ℝ) C)
    (_hmass : (∫ x, f (coefficientAmbientTorus U x) ∂μ) = 1),
    let rows := fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    ∃ (g : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
      (F : (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) C) ∧
      Integrable g ξ ∧ (∫ y, g y ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x)))).map
        (euclideanCoefficientJetMap U root (Matrix.of difference) rows) = realDensityMeasure ξ g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith ((L * (Fintype.card (Finset (Fin q)) *
        Real.toNNReal (Real.exp ((P + A) ^ A)))) *
        ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)) F ∧
      (∀ y, g y = F (coveredJetAmbientTorus U 1 y)) ∧
      physicalDensityProjection U root difference d
        (fun x => f (coefficientAmbientTorus U x)) g := by
  obtain ⟨A, hA, hsource⟩ := exists_fixed_kernel_ambient_density_multiple m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hsource⟩ := hsource root₀ difference₀ a ha hperiod hP hK hsite period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ ν _ _ f L C hf hcap hmass rows cover ξ
  have hfull := hperiod.trans (integerPeriod_range_le_of_columns
    (Matrix.of difference₀) (Matrix.of difference) e hdifference)
  obtain ⟨g, F, hgc, hgb, _, hgm, hglaw, hFb, hFl, heq, hprojection⟩ :=
    hsource root difference e hroot hdifference U μ f hf hcap hmass
  obtain ⟨hfc, hfb, hfi, hfm, hvalue, hflaw⟩ :=
    siteImage_density_euclideanJet U root (Matrix.of difference) a ha hfull μ ν
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x))))
      g hgc hgb hgm hglaw
  refine ⟨_, fun z => F (lowJetAmbientSites z), hfc, hfb, hfi, hfm, hflaw,
    fun z => hFb _, hFl.comp lowJetAmbientSites_lipschitz, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := euclideanCoefficientJetMap_surjective U root (Matrix.of difference) a ha hfull
      rows (fun _ => Subtype.val_injective) (fun _ o => o.property) y
    exact (hvalue (Set.rangeFactorization
      (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference))) x)).trans
      ((heq x).trans (congrArg F (lowJetAmbientSites_coefficient U root (Matrix.of difference) x).symm))
  · intro X Index _ frequency coeff η happrox p hp hm z
    have he := hvalue (Set.rangeFactorization
      (coefficientSiteTorusMap U (integerAffineCube root (Matrix.of difference)))
      (affineCoefficientCoverSample U p hm d z))
    exact (congrArg (fun r : ℝ =>
      ‖affineCubeFourierProjection U root difference frequency p coeff z - (r : ℂ)‖) he).trans_le
      (hprojection frequency coeff happrox p hp hm z)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin q))

noncomputable def coefficientAmbientRowsJet
    (z : CoefficientAmbientIndex (Fin q) J → UnitAddCircle) : JetAmbientIndex O J → UnitAddCircle :=
  fun t => ∑ e : BoundedCoefficientExponent (Fin q) (t.1.val + 1),
    (if rows t.1 t.2.1 = e.val.support then (1 : ℤ) else 0) • z ⟨⟨t.1, e⟩, t.2.2⟩

omit [∀ j, Fintype (O j)] in
theorem coefficientAmbientRowsJet_eq (U : ∀ j, Submodule ℝ (J j → ℝ))
    (z : CoefficientTorus (K := Fin q) U) :
    coefficientAmbientRowsJet rows (coefficientAmbientTorus U z) =
      coveredJetAmbientTorus U 1 (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows z) := by
  funext t
  rcases t with ⟨j, t, i⟩
  simp only [coefficientAmbientRowsJet,
    coveredJetAmbientTorus_coefficient, Nat.cast_one, one_mul, boundedCoefficientJetMatrix_standard]

theorem coefficientAmbientRowsJet_lipschitz :
    LipschitzWith (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0))
      (coefficientAmbientRowsJet (q := q) (J := J) rows) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, t, i⟩
  have hterm (e : BoundedCoefficientExponent (Fin q) (j.val + 1)) :
      dist ((if rows j t = e.val.support then (1 : ℤ) else 0) • z ⟨⟨j,e⟩,i⟩)
        ((if rows j t = e.val.support then (1 : ℤ) else 0) • w ⟨⟨j,e⟩,i⟩) ≤ dist z w := by
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨⟨j,e⟩,i⟩
    · simp only [zero_zsmul, dist_self]
      exact dist_nonneg
  have hc : (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0) ≤
      ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0) :=
    Finset.single_le_sum (f := fun j : Fin m => (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0)) (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _e : BoundedCoefficientExponent (Fin q) (j.val + 1), dist z w :=
      (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun e _ => hterm e))
    _ = (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ) * dist z w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {X : Type*} {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

include hp in
theorem coefficientCoverSample_physicalRows {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin q)) (v : X → (Unit ⊕ Fin q) → ℤ) :
    euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows
      (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))) =
      physicalCubeRowSample U d rows p hm v := by
  let D : Fin q → Fin q → ℤ := fun i j => if i = j then 1 else 0
  have hD : Matrix.of D = (1 : Matrix (Fin q) (Fin q) ℤ) := by
    ext i j
    simp [D, Matrix.one_apply]
  have h := coefficientCoverSample_sites U (fun _ : Fin q => 0) D d p hp hm
    (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))
  rw [affineCoveredSiteSample_zero_base_physical, hD,
    physicalCubeRootDifferences_standard, standardPhysicalCubeOutput_frame] at h
  have hjet := congrArg (fun t : SiteTorus (Finset (Fin q)) U =>
    euclideanJetEquiv U (siteBooleanJetTorusMap U rows t)) h
  change euclideanCoefficientJetMap U (fun _ : Fin q => 0) (Matrix.of D) rows
    (affineCoefficientCoverSample U p hm d (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))) =
      physicalCubeRowSample U d rows p hm v at hjet
  simpa only [hD] using hjet

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRowsAmbientProjectedFamilyMultiple
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
variable (g : Y → EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)

noncomputable def physicalRowsProjectedMean (law : FiniteProbabilityWeights Y) (g : Y → EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ) (y : EuclideanJetLayers U Row) : ℂ :=
  law.complexMean (fun a => (g a (physicalRowsToStandard U y) : ℂ))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical BigOperators NNReal

attribute [local irreducible] boundedBooleanJetRows

variable {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
local notation "Row" => (fun j : Fin m =>
  {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
local notation "Std" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))

attribute [local instance] OAI.Erdos3.BooleanCubeKernel.physicalRowsAmbientFintype
theorem finiteProbability_ambient_mean
    {Y X A B : Type*} [Fintype Y] [PseudoEMetricSpace A] [PseudoEMetricSpace B]
    (law : FiniteProbabilityWeights Y) (g : Y → X → ℝ) (F : Y → B → ℝ)
    (r : A → B) (q : X → A) {L C : ℝ≥0}
    (hr : LipschitzWith 1 r) (hF : ∀ a, LipschitzWith L (F a))
    (hFb : ∀ a z, F a z ∈ Set.Icc (0 : ℝ) C)
    (hFv : ∀ a x, g a x = F a (r (q x))) :
    ∃ G : A → ℂ, LipschitzWith L G ∧ (∀ z, ‖G z‖ ≤ C) ∧
      ∀ x, law.complexMean (fun a => (g a x : ℂ)) = G (q x) := by
  let R := fun z : A => law.mean (fun a => F a (r z))
  have hR : LipschitzWith L R := by
    apply law.mean_lipschitz_uniform_emetric
    intro a
    simpa only [mul_one, Function.comp_def] using (hF a).comp hr
  have hRb (z : A) : R z ∈ Set.Icc (0 : ℝ) C :=
    ⟨law.mean_nonneg (fun a => (hFb a _).1),
      (law.mean_mono (fun a => (hFb a _).2)).trans_eq (law.mean_const _)⟩
  refine ⟨fun z => (R z : ℂ), ?_, ?_, ?_⟩
  · simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp hR
  · intro z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hRb z).1]
    exact (hRb z).2
  · intro x
    simp only [hFv, law.complexMean_ofReal]
    rfl

theorem exists_physicalRowsProjectedMean_ambient
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U Std → ℝ)
    (F : Y → (JetAmbientIndex Std J → UnitAddCircle) → ℝ)
    {L C : ℝ≥0} (hF : ∀ a, LipschitzWith L (F a))
    (hFb : ∀ a z, F a z ∈ Set.Icc (0 : ℝ) C)
    (hFv : ∀ a y, g a y = F a (coveredJetAmbientTorus U 1 y)) :
    ∃ G : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
      LipschitzWith L G ∧ (∀ z, ‖G z‖ ≤ C) ∧
      ∀ y, physicalRowsProjectedMean U law g y = G (coveredJetAmbientTorus U 1 y) := by
  have he (a : Y) (y : EuclideanJetLayers U Row) :
      g a (physicalRowsToStandard U y) =
        F a (physicalRowsAmbientToStandard (coveredJetAmbientTorus U 1 y)) :=
    (hFv a (physicalRowsToStandard U y)).trans
      (congrArg (F a) (physicalRowsAmbientToStandard_eq U y).symm)
  obtain ⟨G, hG, hGb, hGv⟩ := finiteProbability_ambient_mean
    (X := EuclideanJetLayers U Row)
    (A := JetAmbientIndex Row J → UnitAddCircle)
    (B := JetAmbientIndex Std J → UnitAddCircle)
    law (fun a (y : EuclideanJetLayers U Row) => g a (physicalRowsToStandard U y)) F
    (physicalRowsAmbientToStandard (m := m) (dim := dim) (J := J))
    (coveredJetAmbientTorus (O := Row) U 1)
    physicalRowsAmbientToStandard_lipschitz hF hFb he
  refine ⟨G, ?_, hGb, hGv⟩
  convert hG using 1
  congr 1
  exact Subsingleton.elim _ _

end Erdos3.BooleanCubeKernel

end

end OAI
end


