-- Prove2me | Definitions.Def_OAIE3v2B295
-- name    : OAIE3v2B295
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T09:27:13.238172+00:00
-- url     : https://prove2.me/theorems/c60a0ce1-c3c4-4db3-a2df-850d5ebb307e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 309 of 311
-- statement:
--   Definitions bundle 309 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B310`, `OAIE3v2B293` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidatePreparedPhysicalConclusion.lean`, `Estimates/AllocatedExternalCandidatePrimitiveFrontDescentData.lean`, `Estimates/AllocatedPrimitiveFrontInitialLong.lean`, `Estimates/PreparedRelativePositiveNativeRuleCanonical.lean`, `Geometry/AllocatedExternalCandidateSpatialNativePhysicalConclusion.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B310
import Definitions.Def_OAIE3v2B293

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePrimitiveFrontDescentData
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
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_primitive_sourceProfile_front
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile s p e)
    (hp : 0 ≤ p) (hcost0 : 0 ≤ cost) (hcost : cost ≤ p)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hD : D.GeometryComplexityLE p)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ accuracy) :
    ∃ front : P.CommonKeepPositiveKernelPreparation p e,
    let q := positiveKernelPreparationParameter (2 * p)
    let binLog := positiveKernelPreparationBinLog (2 * p) e
    let commonBudget := max source.front.nativeBudget 3
    let Qmodel := max commonBudget (2 * source.front.u + 4 * source.front.pModel + 20)
    let coefficientLog := Qmodel + 2
    let termLog := 2 * Qmodel + 2 * source.front.u + 4 * source.front.pModel + 34
    ∃ (retained : Finset A.Path), retained ⊆ front.prep.selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(p * (binLog + termLog))) * (A.law.mass front.prep.selected.retained / 2) ≤
        A.law.mass retained ∧
      Real.exp (-(2 * p + q + p * (binLog + termLog) + 2)) ≤ A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot front.prep.selected.code) D Fmark φ marked front.keep cost
          source.front.familyParameter q commonBudget (q + binLog + coefficientLog + 4)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩,
        F.sourceChart = front.problem.precenterChart front.prep.positive_mass ∧
        (∀ a, HEq (F.sourceCandidate a) (front.problem.precenterCandidate front.prep.positive_mass a)) ∧
        F.η = (fun k => front.prep.early.eta
          (kernelProjectionSelectedPivot front.prep.selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤ (F.sourceCandidate a).score
          (fun x => (front.prep.selected.tests x).observable) weight) := by
  obtain ⟨front⟩ := P.exists_commonKeepPositiveKernelPreparation p e hp hvariables hD
    ℓ hℓ hLip hpositive hweight hmass hscore source.front.narrow hnet
  exact ⟨front, front.exists_sourceProfile_spatialNativeFamily source hp hcost0 hcost
    hD hweight hmass⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

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
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_primitiveFrontQuotientData
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile s p e)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hcost0 : 0 ≤ cost) (hcost : cost ≤ p)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hD : D.GeometryComplexityLE p) (hFmark : FmarkNative.GeometryComplexityLE p)
    (hmark : ∀ i j, rationalLogHeight (FmarkNative.basis.repr (φ (D.basis j)) i) ≤ p)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hmass : Real.exp (-p) ≤ massThreshold)
    (hscore : Real.exp (-p) ≤ scoreThreshold)
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ accuracy) :
    Nonempty (P.PrimitiveFrontQuotientData FmarkNative source) := by
  classical
  obtain ⟨front, retained, hretained, hpos, _, hmassRaw, F,
    hchart, hcand, heta, hcorr, hpath, hcenter, hscore⟩ :=
    P.exists_primitive_sourceProfile_front source hp hcost0 hcost hvariables hD
      ℓ hℓ hLip hpositive hweight hmass hscore hnet
  have budget := source.front.familyBudget hp
  have hD' := hD.mono D budget.cost
  have hFmark' := hFmark.mono FmarkNative budget.cost
  have hmark' := fun i j => (hmark i j).trans budget.cost
  obtain ⟨hker, dQ, hdQ, Q, hQF, hQL, hQ, hprojection, hinduced, hdescended⟩ :=
    front.prep.exists_native_marked_descended_quotient FmarkNative source.front.familyParameter
      hs budget.hpFamily hD' hFmark' hmark' budget.projection
  have hpivot : (Fintype.card (KernelProjectionPresentPivot front.prep.selected.code) : ℝ) ≤
      source.front.familyParameter := by
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    have hdim := Submodule.finrank_le (D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap)
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at hdim
    exact (Nat.cast_le.mpr ((kernelProjectionPresentPivot_card_le front.prep.selected.code).trans hdim)).trans hD'.1
  exact ⟨{
    front := front
    retained := retained
    retained_subset := hretained
    mass_pos := hpos
    mass := (source.front.exp_neg_familyParameter_le_rawMassLoss hp).trans hmassRaw
    family_nonneg := budget.hpFamily
    source_geometry := hD'
    mark_geometry := hFmark'
    mark_height := hmark'
    pivot_card := hpivot
    rawFamily := F
    sourceChart_eq := hchart
    sourceCandidate_heq := hcand
    frequencies_eq := heta
    correlation := hcorr
    path_eq := hpath
    center_eq := hcenter
    score := hscore
    ideal_killed := hker
    quotientDimension := dQ
    quotientDimension_le := hdQ
    quotient := Q
    quotient_filtration := hQF
    quotient_lattice := hQL
    quotient_geometry := hQ
    quotient_projection := hprojection
    quotient_mark := hinduced
    descent := hdescended }⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

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
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrimitiveFrontQuotientData

variable {FmarkNative P} {p : ℝ} {e : ℕ} {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

include data in

theorem source_geometry_bound (hp : 0 ≤ p) : D.GeometryComplexityLE source.front.geometryBudget :=
  data.source_geometry.mono D (source.front.factorGeometryBudget hp).geometry_input

include data in
theorem mark_height_bound (hp : 0 ≤ p) (i j) : rationalLogHeight
    (FmarkNative.basis.repr (φ (D.basis j)) i) ≤ source.front.geometryBudget :=
  (data.mark_height i j).trans (source.front.factorGeometryBudget hp).geometry_input

include data in
theorem native_geometry_bound (hp : 0 ≤ p) :
    max source.front.nativeBudget 3 ≤ source.front.geometryBudget :=
  data.rawFamily.hnative.trans (source.front.factorGeometryBudget hp).geometry_input

theorem pivot_card_bound (hp : 0 ≤ p) :
    (Fintype.card (KernelProjectionPresentPivot data.front.prep.selected.code) : ℝ) ≤
      source.front.geometryBudget :=
  data.pivot_card.trans (source.front.factorGeometryBudget hp).geometry_input

theorem quotient_projection_bound (hp : 0 ≤ p) (i j) :
    rationalLogHeight (data.quotient.basis.repr
      (lieQuotientMap data.front.prep.nativeQuotientIdeal (D.basis j)) i) ≤ source.front.geometryBudget :=
  (data.quotient_projection i j).trans (source.front.factorGeometryBudget hp).geometry_descent

end PrimitiveFrontQuotientData
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

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
    {f : ℕ} {FmarkNative : RationalFilteredNilmanifold M t f} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData

variable {cost massThreshold scoreThreshold p : ℝ} {e : ℕ}
    {P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold}
    {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

theorem exists_descendedFamily :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 data.quotient.basis
    Nonempty data.DescendedFamily := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    realification_moduleTopology_t2 data.quotient.basis
  obtain ⟨tests, hunit, hnorm, hcomplexity, hLip, hrecovery, hcontract, hnets⟩ := data.descent
  exact ⟨{
    tests := tests
    unit := hunit
    norm1 := hnorm
    complexity := hcomplexity
    lipschitz := hLip
    recovery := hrecovery
    contract_original := hcontract
    member_nets := hnets }⟩

end AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPrimitiveFrontInitialLong
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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile

variable {degree : ℕ} (source : A.InnerSourceProfile degree)

noncomputable abbrev stageKeep (r : ℕ) (i : LayerSamplerVariables G I n B) : Prop :=
  Real.exp (allocatedCandidateStageSlice degree m source.Cprimitive
    (preparedFiniteForwardParameter source.scheduleExponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants r source.x)) ≤
    (A.sides i : ℝ)

theorem stageKeep_kept :
    ∀ r i, source.stageKeep r i →
      Real.exp (allocatedCandidateStageSlice degree m source.Cprimitive
        (preparedFiniteForwardParameter source.scheduleExponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants r source.x)) ≤
        (A.sides i : ℝ) :=
  fun _ _ h => h

theorem stageKeep_frozen :
    ∀ r i, ¬source.stageKeep r i →
      (A.sides i : ℝ) ≤
        Real.exp (allocatedCandidateStageSlice degree m source.Cprimitive
          (preparedFiniteForwardParameter source.scheduleExponent
            AllocatedExternalCandidateSampler.degreeSourceCountConstants r source.x)) := by
  intro r i hi
  exact (lt_of_not_ge hi).le

theorem stageKeep_subset_initialLong
    (initialLong : LayerSamplerVariables G I n B → Prop) {initialShortCost : ℝ}
    (hshortCost : initialShortCost ≤ (source.x + source.Cprimitive) ^ source.Cprimitive)
    (hshort : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp initialShortCost) :
    ∀ r i, source.stageKeep r i → initialLong i := by
  intro r
  exact allocatedCandidateStage_keep_subset_initialLong
    (fun i => (A.sides i : ℝ)) initialLong (source.stageKeep r)
    degree m source.Cprimitive source.scheduleExponent r source.x_nonneg
    hshortCost hshort (source.stageKeep_kept r)

theorem detectionLoss_le_retainedMass {massLog retainedLoss massH : ℝ}
    (hmass : Real.exp (-massLog) ≤ massH)
    (hbudget : retainedLoss + massLog ≤ source.gainLog) :
    ∀ r < degree, source.detectionLoss r ≤
      (9 / 10 : ℝ) * (Real.exp (-retainedLoss) * massH) := by
  have hexp : Real.exp (-source.gainLog) ≤ Real.exp (-retainedLoss) * massH := by
    calc
      _ ≤ Real.exp (-(retainedLoss + massLog)) :=
        Real.exp_le_exp.mpr (neg_le_neg hbudget)
      _ = Real.exp (-retainedLoss) * Real.exp (-massLog) := by
        rw [neg_add, Real.exp_add]
      _ ≤ Real.exp (-retainedLoss) * massH :=
        mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)
  have hpos := allocatedCandidate_retainedMass_pos (retainedLoss := retainedLoss) hmass
  intro r hr
  have hloss := source.loss_bound r hr
  linarith only [hloss, hexp, hpos]

theorem detectionLoss_le_spatialNativeMass
    {Pivot : Type*} [Fintype Pivot] {qVertical qCommon massLog massH : ℝ}
    (hmass : Real.exp (-massLog) ≤ massH)
    (hbudget : verticalDecompositionBudget qVertical * (Fintype.card Pivot : ℝ) +
      ((qCommon + 2) ^ 5 + qCommon) + massLog ≤ source.gainLog) :
    ∀ r < degree, source.detectionLoss r ≤
      (9 / 10 : ℝ) * (Real.exp (-(verticalDecompositionBudget qVertical *
        (Fintype.card Pivot : ℝ) + ((qCommon + 2) ^ 5 + qCommon))) * massH) :=
  source.detectionLoss_le_retainedMass hmass hbudget

theorem markHeight_bounds {markBudget : ℝ} (hmark : 0 ≤ markBudget)
    (hmarkInput : markBudget + 1 ≤ source.x) :
    1 ≤ ⌈Real.exp markBudget⌉₊ ∧
      (⌈Real.exp markBudget⌉₊ : ℝ) ≤ Real.exp source.x :=
  ⟨one_le_ceil_exp _,
    (ceil_exp_le_exp_add_one hmark).trans (Real.exp_le_exp.mpr hmarkInput)⟩

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

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
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrimitiveFrontQuotientData

variable {FmarkNative P} {p : ℝ} {e : ℕ} {source : A.DegreeSourceProfile s p e}
    (data : P.PrimitiveFrontQuotientData FmarkNative source)

theorem initialLong_nonempty [Nonempty G] {initialShort : ℝ}
    (hcost : cost < source.inner.x) (hshort : initialShort ≤ source.inner.x)
    (hscale : Real.exp source.inner.x ≤ (S.value : ℝ)) :
    Nonempty {i : LayerSamplerVariables G I n B //
      data.front.keep i ∧ Real.exp initialShort ≤ (A.sides i : ℝ)} := by
  obtain ⟨a, _⟩ := data.retained_nonempty
  let i : LayerSamplerVariables G I n B := .inl (Classical.choice inferInstance)
  have hside : Real.exp source.inner.x ≤ (A.sides i : ℝ) := hscale
  have hkeep : data.front.keep i := by
    by_contra hi
    exact (not_lt_of_ge (data.frozen_side a ⟨i, hi⟩))
      ((Real.exp_lt_exp.mpr hcost).trans_le hside)
  exact ⟨⟨i, hkeep, (Real.exp_le_exp.mpr hshort).trans hside⟩⟩

end PrimitiveFrontQuotientData
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativePhysicalConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG (s + 1) d₀}
    {dMark : ℕ} {Mmark : RationalFilteredNilmanifold LM (s + 1) dMark} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Mmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Mmark.filtration φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (keepLong : LayerSamplerVariables G I n B → Prop)
    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable (js : List Pivot) {dQ : ℕ}
    (Q : RationalFilteredNilmanifold
      (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) (s + 1) dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ z ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ z = 0)

local notation "LQuot" => LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js

variable
    {pGeometry adaptedBudget markInput markBudget : ℝ}
    (geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
      (optionProduct Q (fun j => (F.native j).model))
      (optionMarkedLieMap (L := fun j => (F.native j).L)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) ((pGeometry + 3) ^ 2) adaptedBudget)
    (markGeometry : (optionProduct Q (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
      (optionProduct Mmark (fun j => (F.native j).model)) geometry.target
      (optionMarkedLieMap (L := fun j => (F.native j).L)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
      markInput markBudget)

variable {scheduleExponent Cprimitive : ℕ} {x qVertical qCommon pProj : ℝ}

local notation "fullBudget" => nativePhysicalTerminalFullBudget
  (s + 1) m Cprimitive scheduleExponent x
local notation "affineBudget" => nativePhysicalTerminalAffineBudget (s + 1) scheduleExponent x
local notation "ordinaryBudget" => candidatePhysicalOrdinaryBudget fullBudget
local notation "backendBudget" => allocatedAffineCanonicalBudget s ordinaryBudget fullBudget
local notation "separation" => Real.exp (candidatePrimitiveFreezingCutoff s 1 backendBudget)
local notation "recursiveBudget" => finiteFreezingRecursiveParameter
  (candidatePrimitivePhysicalBudgetExponent s 1) backendBudget
local notation "factorMass" => Real.exp (-(verticalDecompositionBudget qVertical *
  Fintype.card Pivot + ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H

theorem conclusion_of_actualAdaptedPivotQuotientLongPhysicalTerminal
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ Mmark.filtration.layer k)
    (hsurj : ∀ k, ∀ y ∈ Mmark.filtration.layer k,
      ∃ z ∈ D.filtration.layer k, φ z = y)
    (hx : 0 ≤ x)
    (hgeometry : adaptedBudget ≤ fullBudget) (hmark : markBudget ≤ fullBudget)
    (hjoint : (pGeometry + 3) ^ 2 ≤ fullBudget)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ fullBudget)
    (hprojection : (pProj + 2) ^ 4 ≤ fullBudget)
    (hfactor : (pProj + 2) ^ 3 + qCommon ≤ fullBudget)
    (hcost : cost ≤ fullBudget)
    (hshort : ∀ i, ¬keepLong i → (A.sides i : ℝ) ≤ Real.exp fullBudget)
    (hweight : ∀ y, ‖weight y‖ ≤ Real.exp fullBudget)
    (hscoreBound : Real.exp (-fullBudget) ≤ scoreThreshold)
    (hmassBound : Real.exp (-fullBudget) ≤ factorMass)
    {e : ℕ}
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := Deck) weight s
      (refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2) recursiveBudget outputCost)
    (houtput : recursiveBudget ≤ outputCost) :
    ∀ [TopologicalSpace (ℝ ⊗[ℚ] LQuot)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LQuot)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LQuot)] [T2Space (ℝ ⊗[ℚ] LQuot)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQuot (fun j => (F.native j).L) i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQuot (fun j => (F.native j).L) i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQuot (fun j => (F.native j).L) i))] [T2Space (ℝ ⊗[ℚ] (∀ i : Option Pivot, optionLieSpace LQuot (fun j => (F.native j).L) i))]
    (descendedTests : (X → ℤ) → Q.Niltest (fullTaggedVariableWeight (X := X) J))
    (hrecovery : ∀ x (g : D.RealGroup),
      (descendedTests x).observable (QuotientGroup.mk
        (realificationMap (L := LG) (M := LQuot) (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        (observable : (X → ℤ) → D.Space → ℂ) x (QuotientGroup.mk g))
    (hpGeometry : 0 ≤ pGeometry) (hQgeometry : Q.GeometryComplexityLE pGeometry)
    (hunit : ∀ y, (descendedTests y).UnitIntervalValued)
    (hcomplexity : ∀ y, (descendedTests y).ComplexityLE pGeometry)
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((fullBudget + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ y ∈ integerBox N, ∃ i, ∀ z,
          ‖(fun x => (descendedTests x).observable) y z - (fun x => (descendedTests x).observable) (centers i).val z‖ ≤ accuracy),
    let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer Mmark
      (D.filtration.pivotAnnihilatorIdeal φ F.η js)
      (by rw [D.filtration.terminal]; exact bot_le) Q hQ
      (fun j => (F.native j).model) φ hker hφ geometry.target
    F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore geometry.source.basis geometry.source.weight
      geometry.source.layers js Q hQ hker (fun x => (descendedTests x).observable) hrecovery geometry.target
      markGeometry.target.basis markGeometry.target.weight
      (Mmark.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target) hmarkΦ
      scheduleExponent Cprimitive x separation qVertical qCommon pProj →
    ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
      (hmass : factorMass ≤ A.law.mass retained),
      0 < A.law.mass retained ∧
      let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore retained hsub hmass
      let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker (fun x => (descendedTests x).observable) hrecovery geometry.target
      Nonempty (target.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  intro _ _ _ _ _ _ _ _ descendedTests hrecovery hpGeometry hQgeometry hunit hcomplexity hnet
    hmarkΦ hterminal
  obtain ⟨ha, hw, hpFull⟩ :=
    nativePhysicalTerminalBudgets_nonneg (s + 1) m Cprimitive scheduleExponent hx
  have hcenterBudget : certifiedAffineCenterBudget affineBudget ≤ fullBudget :=
    (allocatedCandidateTerminalFullInput_bounds (s + 1) m Cprimitive hx hw ha).2.2.2.2.2.2.1
  have hordinary := candidatePhysicalOrdinaryBudget_bounds hpFull
  have hscalar := hordinary.2.1
  obtain ⟨retained, hsub, hmass, hpos, packet⟩ :=
    F.ordinaryData_of_actualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter
      hpath hcenter hfrozen observable weight scoreThreshold hscore js Q hQ hker (fun x => (descendedTests x).observable)
      hrecovery geometry markGeometry hφ hsurj hordinary.1
      (hgeometry.trans hscalar) (hmark.trans hscalar) (hjoint.trans hscalar)
      (hvariables.trans hscalar) (hprojection.trans hscalar) (hfactor.trans hscalar)
      (hcost.trans hscalar)
      (fun i hi => (hshort i hi).trans (Real.exp_le_exp.mpr hscalar)) hterminal
  obtain ⟨packet⟩ := packet
  obtain ⟨hpositive, _hnorm, hLip, hnetTransfer⟩ :=
    geometry.optionTarget_observable_regularity Q (fun j => (F.native j).model)
      descendedTests hpGeometry hQgeometry hunit hcomplexity
  have hnet' := hnetTransfer (integerBox N)
    (fun accuracy => Real.exp ((fullBudget + Real.log (1 / accuracy) + e) ^ e)) hnet
  refine ⟨retained, hsub, hmass, hpos, ?_⟩
  apply packet.conclusion_of_bounds rfl F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall F.hpoly
    (fun y => (hweight y).trans (Real.exp_le_exp.mpr hscalar))
    ((Real.exp_le_exp.mpr (neg_le_neg hscalar)).trans hscoreBound)
    (candidatePhysicalOrdinaryBudget_mass hpFull ha hcenterBudget hmassBound)
    F.hξ ⟨Real.exp (nativeOptionTargetObservableBudget pGeometry), Real.exp_nonneg _⟩
    (Real.exp_le_exp.mpr (candidatePhysicalOrdinaryBudget_observable hpFull hjoint))
    hLip hpositive ?_ outputCost lowerIH houtput
  intro accuracy haccuracy haccuracy1
  obtain ⟨count, hcount, centers, hcenters⟩ := hnet' accuracy haccuracy haccuracy1
  refine ⟨count, hcount.trans ?_, centers, hcenters⟩
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (1 / accuracy) :=
    Real.log_nonneg ((one_le_div haccuracy).mpr haccuracy1)
  exact pow_le_pow_left₀ (by positivity) (by linarith only [hscalar]) e

end AllocatedExternalCandidateSpatialNativeFamily
end
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePreparedPhysicalConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

section PrimitiveResult
variable {s : ℕ}
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
    {d : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M (s + 1) f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    {p : ℝ} {e : ℕ} (source : A.DegreeSourceProfile (s + 1) p e)
    (data : P₀.PrimitiveFrontQuotientData FmarkNative source)

theorem AllocatedExternalCandidateProblem.PrimitiveFrontQuotientData.conclusion_of_canonicalPhysicalTerminal
    {Cgeometry C Cbasis K T : ℕ}
    (hp : 0 ≤ p)
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ FmarkNative.filtration.layer k)
    (hsurj : ∀ k, ∀ y ∈ FmarkNative.filtration.layer k,
      ∃ z ∈ D.filtration.layer k, φ z = y)
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ y ∈ integerBox N, ∃ i, ∀ z,
          ‖observable y z - observable (centers i).val z‖ ≤ accuracy)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      source.inner.recursiveParameter outputCost)
    (houtput : source.inner.recursiveParameter ≤ outputCost)
    (produced : PrimitiveFrontQuotientCanonicalPhysicalTerminalAt FmarkNative P₀ source data
      Cgeometry C Cbasis K T hp hφ) :
    Nonempty (P₀.Conclusion (3 * outputCost + 2)
      (Real.exp (-(3 * outputCost + 2))) (Real.exp (-(3 * outputCost + 2)))) := by
  classical
  let F := data.factorFamily hp
  obtain ⟨hgeometry, hmark, hjoint, hvars, hproj, hnative, hcost, hshort,
    hscore, hmass, hpGeoFull, hfamilyFull, hmodels⟩ := produced
  let quotientTopology := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal))
  let quotientAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let quotientSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ data.front.prep.nativeQuotientIdeal)) :=
    inferInstance
  let quotientT2 := realification_moduleTopology_t2 data.quotient.basis
  let actualQuotientTopology : TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)) := quotientTopology
  let actualQuotientAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)) := quotientAdd
  let actualQuotientSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)) := quotientSMul
  let actualQuotientT2 : T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)) := quotientT2
  obtain ⟨desc, geometry, markGeometry, hphysical⟩ := hmodels
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    (∀ i : Option (KernelProjectionPresentPivot data.front.prep.selected.code),
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList) (fun j => (F.native j).L) i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (∀ i : Option (KernelProjectionPresentPivot data.front.prep.selected.code),
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList) (fun j => (F.native j).L) i)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ]
    (∀ i : Option (KernelProjectionPresentPivot data.front.prep.selected.code),
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η
        (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList)
        (fun j => (F.native j).L) i)) :=
    realification_moduleTopology_t2 geometry.target.basis
  have hpFull : p ≤ source.inner.physicalBudget :=
    source.input_inner.trans source.inner.input_le_physicalBudget
  have hweightFull (x) : ‖weight x‖ ≤ Real.exp source.inner.physicalBudget :=
    (hweight x).trans (Real.exp_le_exp.mpr hpFull)
  have hnetFull : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((source.inner.physicalBudget + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ y ∈ integerBox N, ∃ i, ∀ z,
          ‖(desc.tests y).observable z - (desc.tests (centers i).val).observable z‖ ≤ accuracy := by
    apply desc.member_nets
    intro accuracy haccuracy haccuracy1
    obtain ⟨count, hcount, centers, hcenters⟩ := hnet accuracy haccuracy haccuracy1
    refine ⟨count, hcount.trans ?_, centers, hcenters⟩
    apply Real.exp_le_exp.mpr
    have hlog : 0 ≤ Real.log (1 / accuracy) :=
      Real.log_nonneg ((one_le_div haccuracy).mpr haccuracy1)
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hpFull]) e
  have hfactorGeo := source.front.factorGeometryBudget hp
  obtain ⟨retained, hsub, hmassRetained, hpos, result⟩ :=
    F.conclusion_of_actualAdaptedPivotQuotientLongPhysicalTerminal
      (scheduleExponent := source.inner.scheduleExponent) (Cprimitive := source.inner.Cprimitive)
      (x := source.inner.x)
      _ data.retained P₀.centerLift (data.factorFamily_path_eq hp)
      (fun a _ => data.factorFamily_center_eq hp a) (fun a _ i => data.frozen_side a i)
      (fun x => (data.front.prep.selected.tests x).observable) weight
      (Real.exp (-AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p)))
      (data.factorFamily_score hp)
      (Finset.univ : Finset (KernelProjectionPresentPivot data.front.prep.selected.code)).toList
      data.quotient (data.factorFamily_quotient_filtration hp) data.ideal_killed
      geometry markGeometry hφ hsurj source.inner.x_nonneg
      hgeometry hmark hjoint hvars hproj hnative hcost hshort hweightFull hscore hmass
      outputCost lowerIH houtput desc.tests desc.recovery
      (by linarith only [hfactorGeo.geometry_two]) (data.quotient_geometry_bound hp)
      desc.unit (fun x => (desc.complexity x).mono hfactorGeo.geometry_descent) hnetFull hphysical
  obtain ⟨result⟩ := result
  exact data.front.conclusion_of_actualNativeQuotient F data.retained data.retained_subset
    (data.factorFamily_sourceChart_eq hp) P₀.centerLift (data.factorFamily_path_eq hp)
    (fun a _ => data.factorFamily_center_eq hp a) (fun a _ i => data.frozen_side a i)
    (data.factorFamily_score hp) retained hsub hmassRetained
    data.front.prep.nativeQuotientIdeal data.front.prep.nativeQuotientIdeal_terminal
    data.quotient data.quotient_filtration data.ideal_killed
    (fun x => (desc.tests x).observable) desc.recovery geometry.target
    (source.inner.recursiveParameter_nonneg.trans houtput) result
    (fun x => (hweight x).trans (Real.exp_le_exp.mpr
      (source.input_inner.trans (source.inner.input_le_recursiveParameter.trans houtput))))
    F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall F.hpoly

end PrimitiveResult
end
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativePositiveNativeRuleCanonical
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped BigOperators TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile
variable {s : ℕ} (source : A.InnerSourceProfile (s + 1))

theorem recursiveParameter_le_next_seed (Cprimitive exponent innerDepth outer : ℕ)
    {x : ℝ}
    (hExponent : candidateSourceRecursiveNextSeedExponent s Cprimitive ≤ exponent)
    (hdepth : s + 2 ≤ innerDepth) (hx : 0 ≤ x)
    (hprimitive : source.Cprimitive = Cprimitive)
    (hschedule : source.scheduleExponent = exponent)
    (hseed : source.x = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth outer x) :
    source.recursiveParameter ≤ candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (outer + 1) x := by
  have hlayers : (m : ℝ) ≤ candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth outer x := by
    rw [← hseed]
    exact source.layers_input
  apply source.recursiveParameter_polynomial.trans
  simpa only [physicalBudget, hprimitive, hschedule, hseed] using
    candidateSourceBackendPolynomial_le_next_seed s Cprimitive m exponent innerDepth outer
      hExponent hdepth hx hlayers

theorem recursiveParameter_le_next_degree_seed (Cprimitive exponent innerDepth j : ℕ)
    {x : ℝ}
    (hExponent : candidateSourceRecursiveNextSeedExponent s Cprimitive ≤ exponent)
    (hdepth : s + 2 ≤ innerDepth) (hx : 0 ≤ x)
    (hprimitive : source.Cprimitive = Cprimitive)
    (hschedule : source.scheduleExponent = exponent)
    (hseed : source.x = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * j + 1) x) :
    source.recursiveParameter ≤ candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * (j + 1)) x := by
  simpa only [show 2 * j + 1 + 1 = 2 * (j + 1) by omega] using
    source.recursiveParameter_le_next_seed Cprimitive exponent innerDepth (2 * j + 1)
      hExponent hdepth hx hprimitive hschedule hseed

theorem recursiveParameter_le_next_degree_seed_of_uniform
    (Cprimitive exponent innerDepth cutoff j : ℕ) {x : ℝ}
    (hs : s < cutoff)
    (hExponent : candidateSourceRecursiveUniformExponent cutoff Cprimitive ≤ exponent)
    (hdepth : cutoff + 1 ≤ innerDepth) (hx : 0 ≤ x)
    (hprimitive : source.Cprimitive = Cprimitive)
    (hschedule : source.scheduleExponent = exponent)
    (hseed : source.x = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * j + 1) x) :
    source.recursiveParameter ≤ candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * (j + 1)) x :=
  source.recursiveParameter_le_next_degree_seed Cprimitive exponent innerDepth j
    ((candidateSourceRecursiveNextSeedExponent_le_uniform Cprimitive hs).trans hExponent)
    (by omega) hx hprimitive hschedule hseed

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

noncomputable def preparedFiniteNestedFrontFitExponent
    (resourceLayers : ℕ) (Pdetect : Polynomial ℕ) (Cstep : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteNestedFrontFamily_polynomial_next_seed
    resourceLayers Pdetect ((Polynomial.X + 2) ^ Cstep))

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

theorem familyParameter_pow_le_next_seed
    (resourceLayers : ℕ) (Pdetect : Polynomial ℕ) (Cstep exponent Cdirect : ℕ)
    (constants : ℕ → ℕ) (outerDepth innerDepth cutoff : ℕ)
    (outer : Fin (outerDepth + 1)) (Bstruct pnum Qstride gainLog stageLog Plate : ℝ)
    (hExponent : preparedFiniteNestedFrontFitExponent resourceLayers Pdetect Cstep ≤ exponent)
    (hdepth : 1 ≤ innerDepth) (hB : 0 ≤ Bstruct)
    (hdegree : degree ≤ cutoff) (hresource : degree ≤ resourceLayers)
    (hnum : pnum ∈ Set.Icc 0 Bstruct) (hstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hm : (m : ℝ) ≤ Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct) (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hp : p ∈ Set.Icc 0
      (candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct))
    (hu : source.u = preparedFiniteForwardModelPrecision exponent constants 0
      (candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct) gainLog stageLog)
    (hmodel : source.pModel = preparedFiniteForwardWork exponent constants 0
      (candidateNestedForwardSeed exponent constants innerDepth outer.val Bstruct))
    (hnative : source.nativeBudget = preparedFiniteNestedSourceNative resourceLayers G
      (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X) Pdetect
      exponent Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate
      (outer, (0 : Fin (innerDepth + 1)), ⟨degree, Nat.lt_succ_of_le hdegree⟩, false)) :
    (source.familyParameter + 2) ^ Cstep ≤
      candidateNestedForwardSeed exponent constants innerDepth (outer.val + 1) Bstruct := by
  have hbound := (Classical.choose_spec
    (exists_preparedFiniteNestedFrontFamily_polynomial_next_seed resourceLayers Pdetect
      ((Polynomial.X + 2) ^ Cstep))).2
    exponent Cdirect constants outerDepth innerDepth cutoff m
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X) G
    outer ⟨degree, Nat.lt_succ_of_le hdegree⟩ Bstruct pnum Qstride gainLog stageLog Plate p
    hExponent hdepth hB hresource hnum hstride hg hs hm hvars hX hG hp
  dsimp only [familyParameter, familyCap]
  rw [hu, hmodel, hnative]
  simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat] using hbound

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

end OAI
end


