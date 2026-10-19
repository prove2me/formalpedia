-- Prove2me | Definitions.Def_OAIE3v2B299
-- name    : OAIE3v2B299
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:28.205986+00:00
-- url     : https://prove2.me/theorems/a0b08bea-6d62-4342-a4f9-ce6f0f6b02fd
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 182 of 311
-- statement:
--   Definitions bundle 182 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B179` of this split.
--
--   Modules: `Dynamics/RestrictedSymbolGradeIteration.lean`, `Estimates/AllocatedAnchoredRecoveredSource.lean`, `Estimates/AllocatedIdealPhysicalCover.lean`, `Estimates/AllocatedRecoveredPreparedFreeze.lean`, `Estimates/MarkedShiftGeneratorBounds.lean`, `Estimates/NormalizedTwistNativeMembership.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/TranslationMajorCorrelationIdentity.lean`, `Geometry/DetectedTranslationLogCoordinates.lean`, `Geometry/MarkedDirectionCoordinates.lean`, `Geometry/RestrictedChartPrefixControl.lean`, `Lattices/AllocatedModularRankAffineFullWitness.lean`, `Lattices/AllocatedModularRankIntegerDecay.lean`, `Lattices/AllocatedRecoveredIntegerFullChart.lean`, `Lattices/IntegerFrozenChart.lean`, `Linear/AllocatedCenteredMeasurableFramedBadTail.lean`, `Linear/AllocatedModularRankBadProduct.lean`, `Linear/AllocatedModularRankCongruenceOutput.lean`, `Linear/AllocatedModularRankFullProductLaw.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/AllocatedShortRankWitnessWidth.lean`, `Polynomial/AllocatedModularRankTaggedPolynomials.lean`, `Polynomial/DetectedTranslationBasePolynomialBounds.lean`, `Polynomial/LowTaggedPolynomialCoordinates.lean`, `Polynomial/MajorPhaseVectorDecomposition.lean`, `Polynomial/PolynomialPatchMarkedChartRestoration.lean`, `Polynomial/TranslationPolynomialSymbolLiftHom.lean`, `Probability/PreparedModularGeneralCenteredLaw.lean`, `Sampling/AllocatedClippedFullGridIdealCover.lean`, `Sampling/AllocatedExternalCandidateSamplerFamily.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B179

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

noncomputable def restrictedMajorOuterFactors
    (pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    ℕ → F.RealPolynomialSymbolGroup w × F.RealPolynomialSymbolGroup w
  | 0 => (1, 1)
  | n + 1 =>
    let previous := restrictedMajorOuterFactors pS pR n
    (previous.1 * F.restrictedMajorCorrection b ω hF w U S (n + 1) (pS n),
      F.restrictedMajorCorrection b ω hF w U S (n + 1) (pR n) * previous.2)

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
open scoped TensorProduct BigOperators

section PrefixCongruence

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : Submodule ℚ F.AssociatedGraded)
    (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

theorem restrictedMajorOuterFactors_congr
    (pS pR qS qR : ℕ → VectorPolynomial σ ℚ
      (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (n : ℕ) (hleft : ∀ j < n, pS j = qS j) (hright : ∀ j < n, pR j = qR j) :
    F.restrictedMajorOuterFactors b ω hF w U S pS pR n =
      F.restrictedMajorOuterFactors b ω hF w U S qS qR n := by
  revert hleft hright
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro hleft hright
    have hprev := ih
      (fun j hj => hleft j (Nat.lt_succ_of_lt hj))
      (fun j hj => hright j (Nat.lt_succ_of_lt hj))
    simp only [restrictedMajorOuterFactors, hprev,
      hleft n (Nat.lt_succ_self n), hright n (Nat.lt_succ_self n)]

end PrefixCongruence

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

attribute [local irreducible] realChartSubstitute

attribute [local irreducible] polynomialOrbitRealChart

theorem polynomialOrbitRealChart_realEval
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) (x : τ → ℝ) :
    F.realification.polynomialOrbitRealEval v x (F.polynomialOrbitRealChart w v β hβ g) =
      F.realification.polynomialOrbitRealEval w (fun i => MvPolynomial.eval x (β i)) g := by
  apply NilpotentLieBCHGroup.ext
  simp only [polynomialOrbitRealEval_coord, polynomialOrbitRealChart_log]
  exact eval₂_realChartSubstitute β x g.log

end Erdos3.NilpotentLieFiltration

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

theorem markedShiftSubalgebra_contains_direction (t : ℕ) (h : RationalTorus.Algebra t) :
    (⟨0, h⟩ : F.associatedDegree.PolynomialShiftAlgebra t) ∈ markedShiftSubalgebra F v w marked t :=
  (markedPolynomialLayer v w marked 0 0 0).zero_mem

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

noncomputable def markedShiftDirection (h : Fin t → ℚ) : markedShiftSubalgebra F v w marked t :=
  ⟨⟨0, h⟩, markedShiftSubalgebra_contains_direction F v w marked t h⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MarkedDirectionCoordinates
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

noncomputable def markedShiftDirectionLinear :
    RationalTorus.Algebra t →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun := markedShiftDirection F v w marked t
  map_add' h k := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (zero_add (0 : VectorPolynomial (Fin t) ℚ L)).symm
    · rfl
  map_smul' a h := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (smul_zero a).symm
    · rfl

end Erdos3

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

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [Fintype X] in
theorem allocatedCenteredJointDensity_nonneg
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    0 ≤ allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z :=
  canonicalCoefficientDensity_nonneg U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S)
    (allocatedLayerWidths_pos B U b hR hσ S) _

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

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

noncomputable abbrev sides (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : LayerSamplerVariables G I n B → ℕ :=
  allocatedExternalCandidateSides B U b S

include A in
theorem widths_pos (i) : 0 < allocatedExternalCandidateWidths B U b S N τ ξ i :=
  narrowTrimmedSpatialWidths_pos (allocatedExternalCandidateRootBudget_nonneg B U b S)
    A.trim_pos A.narrow_pos N A.size_pos i

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

noncomputable def law : FiniteProbabilityWeights A.Path :=
  selectedJointFiniteLaw (trimmedIntegerBox N (spatialTrimMargin τ N)) A.bases_nonempty
    stride cells (allocatedExternalCandidateWidths B U b S N τ ξ) A.widths_pos A.smooth_mass_pos
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) A.center_mass_pos

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

abbrev AllocatedExternalCandidateSamplerFamily : Prop :=
  ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
    AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center

namespace AllocatedExternalCandidateSamplerFamily

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells}
    (A : AllocatedExternalCandidateSamplerFamily B U b S hb o hR hσ N poly hm τ ξ stride cells)

abbrev Path := (A 0).Path

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealPhysicalCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}

@[instance_reducible]
noncomputable def activeAmbientAxisDecidableEq : DecidableEq activeAxes := Classical.decEq _

attribute [local instance 2000] activeAmbientAxisDecidableEq

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridIdealCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

@[instance_reducible]
noncomputable def fullGridCoverAxisDecidableEq :
    DecidableEq {a // allocatedGridAxis (I := I) U b S.value a} := Classical.decEq _

attribute [local instance 2000] fullGridCoverAxisDecidableEq

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistNativeMembership
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

namespace NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def conjugate (W : NormalizedPolynomialTwist X Y periodCap coverCap L) :
    NormalizedPolynomialTwist X Y periodCap coverCap L :=
  { W with
    mask := fun z => star (W.mask z)
    mask_bound := fun z => by simpa only [norm_star] using W.mask_bound z
    smooth := fun z => star (W.smooth z)
    smooth_bound := fun z => by simpa only [norm_star] using W.smooth_bound z
    smooth_lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm, ← star_sub, norm_star] using W.smooth_lipschitz.dist_le_mul x y }

@[simp] theorem conjugate_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    W.conjugate.eval N poly u = star (W.eval N poly u) := by
  simp only [eval, conjugate, star_mul, mul_comm]
  rfl

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

def canonicalRankBlockEmbedding (h : D → ℕ) (d : D) (b : B d) :
    Fin (h d) ↪ SamplerTupleIndex G B h where
  toFun v := .inr ⟨d, b, v⟩
  inj' := by intro v w he; simpa only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
    Prod.mk.injEq, true_and] using he

def canonicalRankBlock (h : D → ℕ) (d : D) (b : B d) :
    Finset (SamplerTupleIndex G B h) :=
  Finset.univ.map (canonicalRankBlockEmbedding h d b)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

def kernelRankBlockEmbedding (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    Fin h ↪ SamplerTupleIndex G B degree where
  toFun v := .inl (e (a, v))
  inj' := by
    intro v w he
    exact congrArg Prod.snd (e.injective (Sum.inl.inj he))

@[simp] theorem kernelRankBlockEmbedding_apply (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) (v : Fin h) :
    kernelRankBlockEmbedding (B := B) degree e a v = .inl (e (a, v)) := rfl

def kernelRankBlock (degree : D → ℕ) (e : A × Fin h ↪ G) (a : A) :
    Finset (SamplerTupleIndex G B degree) :=
  Finset.univ.map (kernelRankBlockEmbedding degree e a)

noncomputable def kernelRankCoefficientSlot (degree : D → ℕ)
    (e : A × Fin h ↪ G) (a : A) :
    BoundedCoefficientExponent (SamplerTupleIndex G B degree) h :=
  ⟨productBlockExponent (kernelRankBlockEmbedding degree e a),
    (productBlockExponent_degree _).le⟩

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

abbrev SamplerLongVariables (inactive : D → Prop) (G : Type*) (B : D → Type*)
    (h : D → ℕ) :=
  SamplerTupleIndex G (fun d : {d // ¬ inactive d} => B d.val) (fun d => h d.val)

def samplerLongEmbedding (inactive : D → Prop) (h : D → ℕ) :
    SamplerLongVariables inactive G B h ↪ SamplerTupleIndex G B h :=
  Function.Embedding.sumMap (Function.Embedding.refl G)
    (Function.Embedding.sigmaMap (Function.Embedding.subtype (fun d => ¬ inactive d))
      (fun _ => Function.Embedding.refl _))

@[simp] theorem samplerLongEmbedding_common (inactive : D → Prop) (h : D → ℕ) (g : G) :
    samplerLongEmbedding (B := B) inactive h (.inl g) = .inl g := rfl

@[simp] theorem samplerLongEmbedding_dedicated (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) (b : B d.val) (v : Fin (h d.val)) :
    samplerLongEmbedding (G := G) inactive h (.inr ⟨d, b, v⟩) =
      .inr ⟨d.val, b, v⟩ := rfl

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev LayerSamplerLongVariables (inactive : LayerSamplerAxis I n → Prop)
    (G : Type*) (B : LayerSamplerAxis I n → Type*) :=
  SamplerLongVariables inactive G B (layerSamplerDegree I n)

def allocatedLongEmbedding (inactive : LayerSamplerAxis I n → Prop) :
    LayerSamplerLongVariables inactive G B ↪ LayerSamplerVariables G I n B :=
  samplerLongEmbedding inactive (layerSamplerDegree I n)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedDegreeActiveAxis (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  {a : I j ⊕ Fin (n j) // ¬ inactive ⟨j, a⟩}

abbrev AllocatedDegreeRankOutput (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  E j ⊕ AllocatedDegreeActiveAxis inactive j

def allocatedDegreeLongAxis (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (a : AllocatedDegreeActiveAxis inactive j) : {a // ¬ inactive a} :=
  ⟨⟨j, a.val⟩, a.property⟩

def allocatedDegreeRankBlock (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedDegreeRankOutput E inactive j → Fin L →
      Finset (LayerSamplerLongVariables inactive G B)
  | .inl _, l => kernelRankBlock (fun a : {a : LayerSamplerAxis I n // ¬ inactive a} => a.val.1.val + 1) kernel l
  | .inr a, l => canonicalRankBlock (fun a : {a : LayerSamplerAxis I n // ¬ inactive a} => a.val.1.val + 1)
      (allocatedDegreeLongAxis inactive j a) (block a l)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

noncomputable def canonicalPrincipalSubblockSlot (h : D → ℕ) (d : D) {J : ℕ}
    (block : Fin J ↪ B d) :
    Fin J → BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) :=
  fun j => principalCoefficientSlot h d (block j)

noncomputable def canonicalSelectedTopResidual (h : D → ℕ) (d : D) {J : ℕ}
    (block : Fin J ↪ B d)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → R) :
    MvPolynomial (SamplerTupleIndex G B h) R :=
  homogeneousComponent (h d) (modularUnselectedCoefficientPolynomial (h d)
    (canonicalPrincipalSubblockSlot h d block) fixed)

noncomputable def canonicalSelectedLongTopResidual (inactive : D → Prop) (h : D → ℕ)
    (d : {d // ¬ inactive d}) {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → R) :
    MvPolynomial (SamplerLongVariables inactive G B h) R :=
  killCompl (samplerLongEmbedding inactive h).injective
    (canonicalSelectedTopResidual h d.val block fixed)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedTaggedRankOutput (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  SpatialDegreeOutput X j ⊕ AllocatedDegreeRankOutput E inactive j

def allocatedSpatialRankBlock (inactive : LayerSamplerAxis I n → Prop)
    {L : ℕ} (spatial : Fin L ↪ G) (l : Fin L) :
    Finset (LayerSamplerLongVariables inactive G B) :=
  {.inl (spatial l)}

def allocatedTaggedRankBlock (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    {L : ℕ} (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j → Fin L →
      Finset (LayerSamplerLongVariables inactive G B)
  | .inl _, l => allocatedSpatialRankBlock inactive spatial l
  | .inr o, l => allocatedDegreeRankBlock inactive j kernel block o l

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

abbrev AllocatedCongruenceIntegerAxis (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  {i : Fin (n j) // ¬ inactive ⟨j, Sum.inr i⟩}

abbrev AllocatedCongruenceRankOutput (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :=
  SpatialDegreeOutput X j ⊕ (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)

def allocatedCongruenceIntegerEmbedding (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    AllocatedCongruenceIntegerAxis inactive j ↪ AllocatedDegreeActiveAxis inactive j where
  toFun i := ⟨Sum.inr i.val, i.property⟩
  inj' := by
    intro i k he
    apply Subtype.ext
    exact Sum.inr.inj (congrArg Subtype.val he)

def allocatedCongruenceOutputEmbedding (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    AllocatedCongruenceRankOutput X E inactive j ↪ AllocatedTaggedRankOutput X E inactive j :=
  Function.Embedding.sumMap (Function.Embedding.refl _)
    (Function.Embedding.sumMap (Function.Embedding.refl _)
      (allocatedCongruenceIntegerEmbedding inactive j))

@[simp] theorem allocatedCongruenceOutputEmbedding_spatial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) (x : SpatialDegreeOutput X j) :
    allocatedCongruenceOutputEmbedding (E := E) inactive j (.inl x) = .inl x := rfl

@[simp] theorem allocatedCongruenceOutputEmbedding_deck
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) (e : E j) :
    allocatedCongruenceOutputEmbedding (X := X) inactive j (.inr (.inl e)) = .inr (.inl e) := rfl

@[simp] theorem allocatedCongruenceOutputEmbedding_integer
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) (i : AllocatedCongruenceIntegerAxis inactive j) :
    allocatedCongruenceOutputEmbedding (X := X) (E := E) inactive j (.inr (.inr i)) =
      .inr (.inr ⟨Sum.inr i.val, i.property⟩) := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedProjectionCoefficientIndex (K : Type*) (I : Fin m → Type*) (n : Fin m → ℕ) :=
  Σ a : LayerSamplerAxis I n, BoundedCoefficientExponent K (a.1.val + 1)

abbrev AllocatedActualCoefficientIndex (G X : Type*) (I E : Fin m → Type*)
    (n : Fin m → ℕ) (B : LayerSamplerAxis I n → Type*) :=
  (Option (LayerSamplerVariables G I n B) × X) ⊕
    (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E ⊕
      AllocatedProjectionCoefficientIndex (LayerSamplerVariables G I n B) I n)

variable {R : Type*}

def allocatedReadNoise (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    Option (LayerSamplerVariables G I n B) × X → R :=
  fun t => f (.inl t)

def allocatedReadDeck (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    ∀ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → R :=
  fun j e i => f (.inr (.inl ⟨j, e, i⟩))

def allocatedReadProjection (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    ∀ a : LayerSamplerAxis I n,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (a.1.val + 1) → R :=
  fun a e => f (.inr (.inr ⟨a, e⟩))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedModularRankTaggedPolynomials
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedDegreeRankPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedDegreeRankOutput E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    AllocatedDegreeRankOutput E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl i => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i
          (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel) (c (.inl i))) j i))
  | .inr a => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1)
          (Function.extend (canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
            ⟨j,a.val⟩ (block a)) (c (.inr a)) (projection a))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedTaggedRankPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl x => homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (spatialRankPolynomial (Function.extend (spatialKernelRankSlot spatial)
          (c (.inl x)) (fun d => noise (d,x.val)))))
  | .inr o => allocatedDegreeRankPolynomial inactive j r projection kernel block
      (fun o => c (.inr o)) v o

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {L : ℕ}

noncomputable def allocatedTaggedRankIntegerResidual
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) ℤ
  | .inl x => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range
          (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) spatial)),
          MvPolynomial.monomial (spatialRankExponent d) (noise (d,x.val))))
  | .inr (.inl i) => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1)
          (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel) (fun q => r j q i)))
  | .inr (.inr a) => canonicalSelectedLongTopResidual inactive (layerSamplerDegree I n)
      (allocatedDegreeLongAxis inactive j a) (block a) (projection a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable def allocatedCongruenceRankPolynomial {N L : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (c : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N) :=
  allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block
    (Function.extend (allocatedCongruenceOutputEmbedding inactive j) c (fun _ _ => 0)) v
    (allocatedCongruenceOutputEmbedding inactive j o)

noncomputable def allocatedCongruenceRankFailureProbability {N L : ℕ} [NeZero N]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (c : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) : ℝ :=
  𝔼 u : Fin j.val → LayerSamplerLongVariables inactive G B → ZMod N,
    if polynomialLinearRow (polynomialIterDifference j.val
      (∑ o, w o • allocatedCongruenceRankPolynomial inactive j noise r projection
        spatial kernel block c v o) u) = 0 then 1 else 0

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

abbrev AllocatedCongruenceScalarIndex (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j × Fin L

def allocatedCongruenceRankBlockFamily (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩) :
    ∀ j, AllocatedCongruenceRankOutput X E inactive j → Fin L →
      Finset (LayerSamplerLongVariables inactive G B) :=
  fun j o => allocatedTaggedRankBlock inactive j spatial (kernel j) (block j)
    (allocatedCongruenceOutputEmbedding inactive j o)

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable def allocatedCongruenceRankIntegerResidualFamily
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩) :
    ∀ j, AllocatedCongruenceRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) ℤ :=
  fun j o => allocatedTaggedRankIntegerResidual inactive j noise r (projection j)
    spatial (kernel j) (block j) (allocatedCongruenceOutputEmbedding inactive j o)

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

def allocatedCongruenceModulusBad (C : ℝ) (N : ℕ) [NeZero N]
    (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N) : Prop :=
  ∃ v : LayerSamplerVariables G I n B → ZMod N, ∃ j : Fin m,
    ∃ w : AllocatedCongruenceRankOutput X E inactive j → ZMod N,
      (∃ o, IsUnit (w o)) ∧ (N : ℝ) ^ (-C) <
        allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod N))
          (fun j q i => (r j q i : ZMod N)) (fun b q => (projection j b q : ZMod N))
          spatial (kernel j) (block j) (fun o l => x ⟨j,(o,l)⟩) v w

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankFullProductLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

abbrev AllocatedFullSmoothCoefficientIndex (G X : Type*) (I : Fin m → Type*)
    (n : Fin m → ℕ) (B : LayerSamplerAxis I n → Type*) :=
  (Option (LayerSamplerVariables G I n B) × X) ⊕
    (Σ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) × Fin (n j))

abbrev AllocatedFullContinuousCoefficientIndex (G : Type*) (I : Fin m → Type*)
    (n : Fin m → ℕ) (B : LayerSamplerAxis I n → Type*) :=
  Σ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) × I j

def allocatedFullCoefficientSplit :
    AllocatedActualCoefficientIndex G X I E n B ≃
      AllocatedFullSmoothCoefficientIndex G X I n B ⊕
        (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E ⊕
          AllocatedFullContinuousCoefficientIndex G I n B) where
  toFun t := match t with
    | .inl x => .inl (.inl x)
    | .inr (.inl d) => .inr (.inl d)
    | .inr (.inr ⟨⟨j,.inl i⟩,q⟩) => .inr (.inr ⟨j,q,i⟩)
    | .inr (.inr ⟨⟨j,.inr i⟩,q⟩) => .inl (.inr ⟨j,q,i⟩)
  invFun t := match t with
    | .inl (.inl x) => .inl x
    | .inr (.inl d) => .inr (.inl d)
    | .inr (.inr ⟨j,q,i⟩) => .inr (.inr ⟨⟨j,.inl i⟩,q⟩)
    | .inl (.inr ⟨j,q,i⟩) => .inr (.inr ⟨⟨j,.inr i⟩,q⟩)
  left_inv := by rintro (x | d | ⟨⟨j,(i | i)⟩,q⟩) <;> rfl
  right_inv := by rintro ((x | ⟨j,q,i⟩) | d | ⟨j,q,i⟩) <;> rfl

def allocatedMixedFullArray {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) :
    AllocatedActualCoefficientIndex G X I E n B → R :=
  Sum.elim smooth (Sum.elim deck continuous) ∘ allocatedFullCoefficientSplit

@[simp] theorem allocatedMixedFullArray_noise {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (x) :
    allocatedReadNoise (allocatedMixedFullArray smooth deck continuous) x = smooth (.inl x) := rfl

@[simp] theorem allocatedMixedFullArray_deck {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (j) (q) (e) :
    allocatedReadDeck (allocatedMixedFullArray smooth deck continuous) j q e = deck ⟨j,q,e⟩ := rfl

@[simp] theorem allocatedMixedFullArray_integer {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (j) (q) (i) :
    allocatedReadProjection (allocatedMixedFullArray smooth deck continuous) ⟨j,.inr i⟩ q =
      smooth (.inr ⟨j,q,i⟩) := rfl

@[simp] theorem allocatedMixedFullArray_continuous {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (j) (q) (i) :
    allocatedReadProjection (allocatedMixedFullArray smooth deck continuous) ⟨j,.inl i⟩ q =
      continuous ⟨j,q,i⟩ := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

noncomputable def allocatedCongruenceIntegerSelectedCoefficients :
    AllocatedCongruenceScalarIndex X E inactive L → ℤ
  | ⟨_j, .inl x, l⟩ => noise (spatialKernelRankSlot spatial l, x.val)
  | ⟨j, .inr (.inl i), l⟩ => r j (kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l) i
  | ⟨j, .inr (.inr a), l⟩ => projection j (allocatedCongruenceIntegerEmbedding inactive j a)
      (canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
        ⟨j, Sum.inr a.val⟩ (block j (allocatedCongruenceIntegerEmbedding inactive j a)) l)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

def allocatedActualModulusBad
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M]
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  allocatedCongruenceModulusBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
    (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block C M
    (fun z => (allocatedCongruenceIntegerSelectedCoefficients inactive
      (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block z : ZMod M))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedReadCoefficientChartResidues {M : ℕ}
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod M) :
    CoefficientChartResidues (LayerSamplerVariables G I n B) n E M :=
  fun j q => Sum.elim (fun i => allocatedReadProjection f ⟨j,Sum.inr i⟩ q)
    (allocatedReadDeck f j q)

def allocatedChartActualResidues {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) :
    AllocatedActualCoefficientIndex G X I E n B → ZMod M :=
  allocatedMixedFullArray
    (Sum.elim noise (fun ⟨j,q,i⟩ => chart j q (Sum.inl i)))
    (fun ⟨j,q,i⟩ => chart j q (Sum.inr i)) (fun _ => 0)

@[simp] theorem allocatedChartActualResidues_noise {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) :
    allocatedReadNoise (allocatedChartActualResidues noise chart) = noise := rfl

@[simp] theorem allocatedChartActualResidues_deck {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) :
    allocatedReadDeck (allocatedChartActualResidues noise chart) =
      fun j q i => chart j q (Sum.inr i) := rfl

@[simp] theorem allocatedChartActualResidues_integer {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M)
    (j : Fin m) (i : Fin (n j)) :
    allocatedReadProjection (allocatedChartActualResidues noise chart) ⟨j,Sum.inr i⟩ =
      fun q => chart j q (Sum.inl i) := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAnchoredRecoveredSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

def allocatedReplaceReadNoise
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    AllocatedActualCoefficientIndex G X I E n B → ℤ :=
  Sum.elim z (fun i => read (.inr i))

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_noise
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadNoise (allocatedReplaceReadNoise B z read) = z := rfl

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_deck
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadDeck (allocatedReplaceReadNoise B z read) = allocatedReadDeck read := rfl

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_projection
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadProjection (allocatedReplaceReadNoise B z read) = allocatedReadProjection read := rfl

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_chart
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) (q : ℕ) :
    allocatedReadCoefficientChartResidues
      (fun i => (allocatedReplaceReadNoise B z read i : ZMod q)) =
      allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q)) := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedJointFrameRead {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    AllocatedActualCoefficientIndex G X I E n B → R
  | .inl (none,x) => a x + f (.inl (none,x))
  | .inl (some k,x) => f (.inl (some k,x))
  | .inr k => f (.inr k)

@[simp] theorem allocatedJointFrameRead_noise_some {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R)
    (k : LayerSamplerVariables G I n B) (x : X) :
    allocatedReadNoise (allocatedJointFrameRead a f) (some k,x) =
      allocatedReadNoise f (some k,x) := rfl

@[simp] theorem allocatedJointFrameRead_deck {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    allocatedReadDeck (allocatedJointFrameRead a f) = allocatedReadDeck f := rfl

@[simp] theorem allocatedJointFrameRead_projection {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    allocatedReadProjection (allocatedJointFrameRead a f) = allocatedReadProjection f := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped Classical

variable {G X : Type*} {I E J : Fin 0 → Type*} {n : Fin 0 → ℕ}
variable (B : LayerSamplerAxis I n → Type*)

def allocatedZeroLayerFramedRead (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    AllocatedActualCoefficientIndex G X I E n B → ℤ
  | .inl t => jointIntegerFrame (a, v) t.1 t.2
  | .inr (.inl ⟨j, _, _⟩) => Fin.elim0 j
  | .inr (.inr ⟨⟨j, _⟩, _⟩) => Fin.elim0 j

@[simp] theorem allocatedZeroLayerFramedRead_noise (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReadNoise (allocatedZeroLayerFramedRead (E := E) B a v) =
      fun t => jointIntegerFrame (a, v) t.1 t.2 := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

variable {X : Type*}

noncomputable def lowTaggedPolynomial (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (i : Fin (Fintype.card (LowTaggedIndex J d))) : MvPolynomial X ℝ :=
  coordinate (LinearMap.proj (lowTaggedIndex J d i).2 :
    (J (lowTaggedIndex J d i).1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
    (poly (lowTaggedIndex J d i).1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPolynomialSymbolLiftHom
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open NilpotentLieFiltration

variable {U B : Type*} [Fintype B]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)

noncomputable def translationPolynomialSymbolLiftHom :
    (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1) →*
      (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  ((weightedFiltration w d hwd).realification.polynomialOrbitCoordinates
    (fun _ : U => 1)).symm.toMonoidHom.comp
      ((weightedFiltration w d hwd).realHomogeneousPolynomialSymbolLiftHom
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd)
        (weightedBasis_homogeneous_brackets w d hw) (fun _ : U => 1))

@[simp] theorem translationPolynomialSymbolLiftHom_apply
    (g : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    translationPolynomialSymbolLiftHom w d hw hwd g =
      translationPolynomialSymbolLift w d hw hwd g := by
  unfold translationPolynomialSymbolLiftHom translationPolynomialSymbolLift
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    realHomogeneousPolynomialSymbolLiftHom_apply]

@[simp] theorem translationPolynomialSymbolLift_one :
    translationPolynomialSymbolLift w d hw hwd
      (1 : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) = 1 := by
  simpa only [translationPolynomialSymbolLiftHom_apply] using
    (translationPolynomialSymbolLiftHom (U := U) w d hw hwd).map_one

@[simp] theorem translationPolynomialSymbolLift_mul
    (g h : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    translationPolynomialSymbolLift w d hw hwd (g * h) =
      translationPolynomialSymbolLift w d hw hwd g * translationPolynomialSymbolLift w d hw hwd h := by
  simpa only [translationPolynomialSymbolLiftHom_apply] using
    (translationPolynomialSymbolLiftHom w d hw hwd).map_mul g h

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DetectedTranslationBasePolynomialBounds
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def detectedTranslationBasePolynomial
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) :
    VectorPolynomial σ ℝ (B → ℝ) :=
  ofCoordinates (Pi.basisFun ℝ B) (fun i =>
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial b ω hN (fun _ : σ => 1)
      (detectedTranslationBaseFunctional w d hw hwd M hM D i) g)

@[simp] theorem detectedTranslationBasePolynomial_coordinate
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (i : B) :
    coordinate (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) =
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial b ω hN (fun _ : σ => 1)
      (detectedTranslationBaseFunctional w d hw hwd M hM D i) g := by
  exact coordinate_ofCoordinates (Pi.basisFun ℝ B) _ i

@[simp] theorem detectedTranslationBasePolynomial_coefficients_apply
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)) (α : σ →₀ ℕ) (i : B) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) α i =
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial b ω hN (fun _ : σ => 1)
        (detectedTranslationBaseFunctional w d hw hwd M hM D i) g).coeff α := by
  rw [← detectedTranslationBasePolynomial_coordinate w d hw hwd M hM D b ω hN g i,
    coeff_coordinate]
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ L : Type} {U ι : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M) {e : ℕ}
    (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationSymbolProjection :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1) →*
      (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1) :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : U => 1))
    (hM := (weightedFiltration w d hwd).polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : U => 1))
    ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.filteredPolynomialSymbolMap (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1))

@[simp] theorem detectedTranslationSymbolProjection_coord
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationSymbolProjection w d hw hwd M hM D P).coord =
      realificationLieHom
        ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.filteredPolynomialSymbolMap (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
          (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1)) P.coord := rfl

noncomputable def detectedTranslationSymbolLift :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1) →*
      (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  (translationPolynomialSymbolLiftHom w d hw hwd).comp
    (detectedTranslationSymbolProjection w d hw hwd M hM D)

@[simp] theorem detectedTranslationSymbolLift_apply
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationSymbolLift w d hw hwd M hM D P =
      translationPolynomialSymbolLift w d hw hwd
        (detectedTranslationSymbolProjection w d hw hwd M hM D P) := by
  simp only [detectedTranslationSymbolLift, MonoidHom.comp_apply,
    translationPolynomialSymbolLiftHom_apply]

@[simp] theorem detectedTranslationSymbolLift_log
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationSymbolLift w d hw hwd M hM D P).log =
      (weightedFiltration w d hwd).realSymbolRepresentative (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
        (realificationLieHom
          ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.filteredPolynomialSymbolMap (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
            (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1)) P.coord) := by
  rw [detectedTranslationSymbolLift_apply, translationPolynomialSymbolLift_log,
    detectedTranslationSymbolProjection_coord]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationLogCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realSymbolCoordinate (x : F.RealPolynomialSymbol w) (i : ι) :
    MvPolynomial σ ℝ :=
  coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom
    (F.realSymbolRepresentative b ω hlayers w x)

@[simp] theorem coeff_realSymbolCoordinate (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) :
    (F.realSymbolCoordinate b ω hlayers w x i).coeff α =
      (b.baseChange ℝ).repr
        (coefficients (F.realSymbolRepresentative b ω hlayers w x) α) i := by
  simp only [realSymbolCoordinate, coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    Basis.coord_apply]

@[simp] theorem realSymbolCoordinate_coeff_symbol (x : F.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w ω) :
    (F.realSymbolCoordinate b ω hlayers w x z.val.2).coeff z.val.1 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z := by
  rw [F.coeff_realSymbolCoordinate]
  exact F.realSymbolRepresentative_coefficient b ω hlayers w x z

@[simp] theorem realSymbolCoordinate_coeff_zero (x : F.RealPolynomialSymbol w) (i : ι) :
    (F.realSymbolCoordinate b ω hlayers w x i).coeff 0 = 0 := by
  rw [F.coeff_realSymbolCoordinate, F.realSymbolRepresentative_constant b ω hlayers w x,
    map_zero, Finsupp.zero_apply]

@[simp] theorem realSymbolCoordinate_constantCoeff (x : F.RealPolynomialSymbol w) (i : ι) :
    MvPolynomial.constantCoeff (F.realSymbolCoordinate b ω hlayers w x i) = 0 := by
  exact F.realSymbolCoordinate_coeff_zero b ω hlayers w x i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

noncomputable def nativeTranslationLogCoordinate (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d)) (k : κ) :
    MvPolynomial U ℝ :=
  VectorPolynomial.coordinate ((b.baseChange ℝ).coord k).toAddMonoidHom p

omit [Fintype κ] in
@[simp] theorem nativeTranslationLogCoordinate_coeff (w : B → ℕ) (d : ℕ)
    (b : Basis κ ℚ (weightedSubalgebra w d))
    (p : VectorPolynomial U ℚ (ℝ ⊗[ℚ] weightedSubalgebra w d))
    (k : κ) (α : U →₀ ℕ) :
    (nativeTranslationLogCoordinate w d b p k).coeff α =
      (b.baseChange ℝ).repr (VectorPolynomial.coefficients p α) k :=
  VectorPolynomial.coeff_coordinate _ _ _

omit [Fintype κ] in
@[simp] theorem nativeTranslationLogCoordinate_symbol (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (b : Basis κ ℚ (weightedSubalgebra w d))
    (ω : κ → ℕ)
    (hb : ∀ j, (weightedFiltration w d hwd).layer j =
      Submodule.span ℚ (b '' {k | j ≤ ω k}))
    (v : U → ℕ) (g : (weightedFiltration w d hwd).RealPolynomialSymbolGroup v)
    (k : κ) :
    nativeTranslationLogCoordinate w d b
        ((weightedFiltration w d hwd).realPolynomialSymbolLift b ω hb v g).coord.val k =
      (weightedFiltration w d hwd).realSymbolCoordinate b ω hb v g.coord k := rfl

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct BigOperators

namespace PolynomialTranslationLie

open RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationLogCoordinatePolynomial
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) : MvPolynomial U ℝ :=
  coordinate (((weightedBasis w d hw).baseChange ℝ).coord k).toAddMonoidHom
    (detectedTranslationSymbolLift w d hw hwd M hM D E).log

theorem detectedTranslationLogCoordinate_eq_canonical
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k =
      (weightedFiltration w d hwd).realSymbolCoordinate (weightedBasis w d hw)
        (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
        (fun _ : U => 1) (detectedTranslationSymbolProjection w d hw hwd M hM D E).coord k := by
  simp only [detectedTranslationLogCoordinatePolynomial, detectedTranslationSymbolLift_log,
    NilpotentLieFiltration.realSymbolCoordinate, detectedTranslationSymbolProjection_coord]

@[simp] theorem detectedTranslationLogCoordinate_constant
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).coeff 0 = 0 := by
  rw [detectedTranslationLogCoordinate_eq_canonical]
  exact (weightedFiltration w d hwd).realSymbolCoordinate_coeff_zero
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) _ _ k

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseVectorDecomposition
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial Module PolynomialTranslationLie RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

variable {m : ℕ} {X L : Type} [Fintype X] [LieRing L] [LieAlgebra ℚ L]
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)

noncomputable def majorPhaseDetectedRealBase
    (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d)) :
    Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :=
  (fast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFrozenChart
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

theorem frozenCoordinate_support (keep : I → Prop) (fixed : {i // ¬keep i} → R) (i : I) :
    frozenCoordinate keep fixed i ∈ weightedSupportLE (fun _ => 1) 1 := by
  by_cases hi : keep i
  · simp only [frozenCoordinate, dif_pos hi]
    exact weightedSupportLE_X (R := R) (fun _ : {i // keep i} => 1) ⟨i, hi⟩
  · simp only [frozenCoordinate, dif_neg hi]
    exact weightedSupportLE_C (fun _ : {i // keep i} => 1) 1 (fixed ⟨i, hi⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {V : Type*} (Long : V → Prop) [DecidablePred Long]

namespace RationalFilteredNilmanifold.Niltest

variable [Fintype V] {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

noncomputable def liftLong (T : D.Niltest (fun _ : {i // Long i} => 1)) :
    D.Niltest (fun _ : V => 1) :=
  T.linearPullbackHom (longCoordinateProjection Long)

omit [DecidablePred Long] in
@[simp] theorem liftLong_normBound (T : D.Niltest (fun _ : {i // Long i} => 1)) :
    (T.liftLong Long).normBound = T.normBound := rfl

omit [DecidablePred Long] in
@[simp] theorem liftLong_complexityLE (T : D.Niltest (fun _ : {i // Long i} => 1))
    (p : ℝ) : (T.liftLong Long).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedRecoveredIntegerFullChart
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel _root_.MvPolynomial
open scoped BigOperators
variable {m : ℕ} {K X : Type*} [Fintype K] (J : Fin m → Type*)
    (a : X → ℤ) (v : Option K × X → ℤ)
    (tag : ∀ j, J j → MvPolynomial K ℤ)

noncomputable def jointIntegerFullChart : X ⊕ (Σ j, J j) → MvPolynomial K ℤ :=
  Sum.elim (affineFramePolynomial (jointIntegerFrame (a, v))) (fun z => tag z.1 z.2)

end Erdos3.VectorPolynomial

end

end OAI
end


