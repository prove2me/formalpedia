-- Prove2me | Definitions.Def_OAIE3v2B270
-- name    : OAIE3v2B270
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:46:14.868909+00:00
-- url     : https://prove2.me/theorems/5933e0e4-1d10-44ac-8b89-0577ed2cfde1
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 281 of 311
-- statement:
--   Definitions bundle 281 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B305`, `OAIE3v2B265` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidatePrimitivePhysicalBudget.lean`, `Dynamics/AllocatedExternalCandidateResetSuccessor.lean`, `Estimates/AllocatedExternalCandidateAdaptedOptionQuotientFactors.lean`, `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidateCoveredFamilySuccessor.lean`, `Estimates/AllocatedExternalCandidateFiniteFreezingDictionaryProducer.lean`, `Estimates/AllocatedExternalCandidateThresholdSuccessor.lean`, `Estimates/AllocatedExternalCandidateUniformSuccessor.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeBudget.lean`, `Lattices/CertifiedAffineCutoffCost.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B305
import Definitions.Def_OAIE3v2B265

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFiniteFreezingDictionaryProducer
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateProblem

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : (P₀.withKeep keep hkeep).productive,
      AllocatedExternalLocalCandidate ((P₀.withKeep keep hkeep).chart z) Dref Fref.filtration
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (localLeft localRight : (P₀.withKeep keep hkeep).productive →
      (D.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (localLeftMark localRightMark : (P₀.withKeep keep hkeep).productive →
      (Fmark.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (hfactor : ∀ z : (P₀.withKeep keep hkeep).productive,
      (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localLeft z) *
        (P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
          markedMiddle middle z *
        (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _ ((P₀.withKeep keep hkeep).candidate z).orbit)
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localRight z) = localRightMark z)
    (hleft : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) rightMark)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem exists_finite_freezing_refinement_of_dictionary
    {l : ℕ} {slow ε budget Bweight Bobs Lip frozenThreshold θ densityCost : ℝ}
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt l
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow ε budget)
    (hslowLeft : ∀ z, D.filtration.PolynomialSlowBound D.basis (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeft z))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeftMark z))
    (hrationalRight : ∀ z, D.filtration.PolynomialRationalGrid D.basis
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRight z))
    (hrationalMark : ∀ z, Fmark.filtration.PolynomialRationalGrid c
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRightMark z))
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * budget * max 1 budget) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip) (hε : 0 ≤ ε)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hthreshold : 0 ≤ frozenThreshold) (hθ : 0 < θ)
    (hbudget : frozenThreshold + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < scoreThreshold) :
    ∃ chosen : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∃ refinement : (P₀.withKeep keep hkeep).Refinement
        (max cost (densityCost +
          Real.log ((4 * dictionary.modulus * dictionary.Q * (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ)))
        (massThreshold / (Fintype.card ((Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) : ℝ))
        (frozenThreshold - Bweight * (Lip * ε)),
      ∀ z : refinement.problem.productive, frozenThreshold ≤
        refinement.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration
            (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left chosen.1))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration
            (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right chosen.2))
          markedMiddle (refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
  let grid := dictionary.grid
  let Q := dictionary.Q
  let modulus := dictionary.modulus
  let rightCount := dictionary.rightCount
  let left := dictionary.left
  let right := dictionary.right
  have hQ := dictionary.Q_pos
  have hQbound := dictionary.Q_bound
  have hmodulus := dictionary.modulus_pos
  have hrightCount := dictionary.rightCount_pos
  have hmodulusBound := dictionary.modulus_bound
  have hselect := dictionary.select
  let : Nonempty (Fin rightCount) := ⟨⟨0, hrightCount⟩⟩
  have hlength (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) :
      max 2 (2 * budget * max 1 budget) ≤ (((P₀.withKeep keep hkeep).chart z).slice.length i : ℝ) := by
    calc
      _ = Real.exp (-densityCost) *
          (Real.exp densityCost * max 2 (2 * budget * max 1 budget)) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (-densityCost) * (A.sides i.val : ℝ) :=
        mul_le_mul_of_nonneg_left (hfloor i) (Real.exp_nonneg _)
      _ ≤ _ := ((P₀.withKeep keep hkeep).chart z).slice.length_lower_of_dense ((P₀.withKeep keep hkeep).chart z).step_pos (hdensity z) i
  have htwo (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) : 2 ≤ ((P₀.withKeep keep hkeep).chart z).slice.length i := by
    exact_mod_cast (le_max_left (2 : ℝ) _).trans (hlength z i)
  have hlong (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) :
      2 * budget * max 1 budget ≤ (((P₀.withKeep keep hkeep).chart z).slice.length i : ℝ) :=
    (le_max_right (2 : ℝ) _).trans (hlength z i)
  have hlocal (z : (P₀.withKeep keep hkeep).productive) :=
    ((P₀.withKeep keep hkeep).chart z).finiteFreezing_of_selection ((P₀.withKeep keep hkeep).candidate z) sectionMap hSectionFilt
      (localLeftMark z) (localRightMark z)
      ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
      Q modulus hQ hmodulus left right tests weight hQbound hmodulusBound
      (htwo z) (hlong z) (hdensity z) hθ (mul_nonneg hBweight (mul_nonneg hLip hε))
      (by simpa only [htests] using (P₀.withKeep keep hkeep).score z)
      (by
        intro hNp hparent hwidth hlarge hindexed
        obtain ⟨_, hselected⟩ := hselect (localLeft z) (localLeftMark z)
          (localRight z) (localRightMark z) (hslowLeft z) (hslowMark z)
          (hrationalRight z) (hrationalMark z) (hprojLeft z) (hprojRight z)
        exact hselected tests ((P₀.withKeep keep hkeep).chart z).physical (fun u => weight (((P₀.withKeep keep hkeep).chart z).physical u))
          Bweight Bobs Lip hBweight hBobs hLip (fun u _ => hweight _) hnorm hlip
          (((P₀.withKeep keep hkeep).chart z).freezingNativeOrbit ((P₀.withKeep keep hkeep).candidate z))
          ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
          (hfactor z) ((P₀.withKeep keep hkeep).chart z).slice.length hNp
          (fun i => (((P₀.withKeep keep hkeep).chart z).slice.start i : ℤ)) ((P₀.withKeep keep hkeep).chart z).step
          hparent hwidth hlarge frozenThreshold θ scoreThreshold hthreshold hθ hindexed hbudget)
  choose slice hdense hinside ileft iright herror _hweighted hfrozen _hscore using hlocal
  have hvalue (z : (P₀.withKeep keep hkeep).productive) (i : Fin d → Fin (grid + 1)) (j : Fin rightCount)
      (u : ((P₀.withKeep keep hkeep).chart z).Variables → ℤ) (hu : u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints) :
      ((P₀.withKeep keep hkeep).chart z).freezingFrozenValue sectionMap hSectionFilt
        (localLeftMark z) (localRightMark z)
        ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
        tests (left i) (right j) u =
      (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref
        (D.filtration.frozenMarkedLeftOrbit Fmark.filtration
          (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (left i))
        (D.filtration.frozenMarkedRightOrbit Fmark.filtration
          (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (right j))
        (((P₀.withKeep keep hkeep).chart z).physical u)
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) := by
    symm
    simpa only [AllocatedExternalLocalChart.freezingFrozenValue,
      RationalFilteredNilmanifold.Niltest.markedFrozenValue, htests] using
      (P₀.withKeep keep hkeep).refilteredFrozenObservable_eq_localFrozen A Fmark φ hφ W Dref hDref Fref
        markedMiddle middle sectionMap hSectionFilt leftMark rightMark (left i) (right j)
        localLeftMark localRightMark hleft hright hσ1 H hH hchart hsmall hp z u hu
  obtain ⟨chosen, refinement, hscore⟩ :=
    (P₀.withKeep keep hkeep).exists_frozen_refinement_of_local_slices A Fmark φ hφ W Dref Fref markedMiddle middle
      sectionMap hSectionFilt leftMark rightMark
      (fun ij : (Fin d → Fin (grid + 1)) × Fin rightCount => left ij.1)
      (fun ij : (Fin d → Fin (grid + 1)) × Fin rightCount => right ij.2)
      (le_max_left cost _) hBweight (mul_nonneg hLip hε)
      (fun z => ((P₀.withKeep keep hkeep).chart z).step * modulus)
      (fun z => Nat.mul_pos ((P₀.withKeep keep hkeep).chart z).step_pos hmodulus)
      slice (fun z => (hdense z).mono (by
        exact le_max_right cost (densityCost +
          Real.log ((4 * modulus * Q *
            (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ)))) hinside
      (fun z => (ileft z, iright z))
      (fun z u _ => hweight (((P₀.withKeep keep hkeep).chart z).physical u))
      (by
        intro z u hu
        have he := herror z u hu
        rw [hvalue z (ileft z) (iright z) u (hinside z hu)] at he
        simpa only [htests] using he)
      (by
        intro z
        apply (hfrozen z).le.trans_eq
        apply congrArg Complex.re
        apply Finset.expect_congr rfl
        intro u hu
        rw [hvalue z (ileft z) (iright z) u (hinside z hu)])
  exact ⟨chosen, refinement, hscore⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateUniformSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateProblem

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : (P₀.withKeep keep hkeep).productive,
      AllocatedExternalLocalCandidate ((P₀.withKeep keep hkeep).chart z) Dref Fref.filtration
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (localLeft localRight : (P₀.withKeep keep hkeep).productive →
      (D.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (localLeftMark localRightMark : (P₀.withKeep keep hkeep).productive →
      (Fmark.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (hfactor : ∀ z : (P₀.withKeep keep hkeep).productive,
      (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localLeft z) *
        (P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
          markedMiddle middle z *
        (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _ ((P₀.withKeep keep hkeep).candidate z).orbit)
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localRight z) = localRightMark z)
    (hleft : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) rightMark)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

variable (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    {nQ nQF : ℕ}
    (Qquot : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQquot : Qquot.filtration = Dref.filtration.quotientTop)
    (Fquot : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hFquot : Fquot.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Qquot.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

include hQquot hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_dictionary_successor
    {l : ℕ} {slow ε budget Bweight Bobs Lip frozenThreshold θ densityCost : ℝ}
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt l
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow ε budget)
    (hslowLeft : ∀ z, D.filtration.PolynomialSlowBound D.basis (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeft z))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeftMark z))
    (hrationalRight : ∀ z, D.filtration.PolynomialRationalGrid D.basis
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRight z))
    (hrationalMark : ∀ z, Fmark.filtration.PolynomialRationalGrid c
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRightMark z))
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * budget * max 1 budget) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip) (hε : 0 ≤ ε)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hthreshold : 0 ≤ frozenThreshold) (hθ : 0 < θ)
    (hbudget : frozenThreshold + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < scoreThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (hmass : 0 ≤ massThreshold)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (hrecovery : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount, ∀ x, x ∈ integerBox N → ∀ source,
      positiveImageSlice
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot) K
        ((P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x)
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).2
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).1 =
        (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x source)
    (recursionParameter : ℝ)
    (hcostRec : (max cost (densityCost + Real.log ((4 * budget * max 1 budget * (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ))) ≤ recursionParameter)
    (hmassRec : Real.exp (-recursionParameter) ≤ massThreshold / budget ^ 2)
    (hscoreRec : Real.exp (-recursionParameter) ≤ frozenThreshold)
    {outputCost outputMass outputScore : ℝ}
    (recurse : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ lowerProblem : AllocatedExternalCandidateProblem (E := E) A Qquot Fquot.filtration
        (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref)) (Fref.topQuotientOrbit Fquot hFquot markedMiddle)
        ((P₀.withKeep keep hkeep).refilteredQuotientObservable A Fmark φ hφ W Dref Fref Qquot (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) markedMiddle K)
        weight recursionParameter (Real.exp (-recursionParameter)) (Real.exp (-recursionParameter)),
        Nonempty (lowerProblem.Conclusion outputCost outputMass outputScore)) :
    Nonempty (P₀.Conclusion outputCost outputMass outputScore) := by
  obtain ⟨chosen, refinement, hfrozen⟩ :=
    P₀.exists_finite_freezing_refinement_of_dictionary Fmark φ hφ keep hkeep W Dref hDref Fref
      markedMiddle middle sectionMap hSectionFilt c leftMark rightMark
      localLeft localRight localLeftMark localRightMark hfactor hprojLeft hprojRight
      hleft hright tests htests hσ1 H hH hchart hsmall hp
      dictionary hslowLeft hslowMark hrationalRight hrationalMark hdensity hfloor
      hBweight hBobs hLip hε hweight hnorm hlip hthreshold hθ hbudget
  let : Nonempty (Fin dictionary.rightCount) := ⟨⟨0, dictionary.rightCount_pos⟩⟩
  have hcostBound := finiteFreezing_cost_le_uniform
    (cost := cost) (densityCost := densityCost)
    (k := Fintype.card { i : LayerSamplerVariables G I n B // keep i })
    hθ dictionary.modulus_pos dictionary.Q_pos dictionary.modulus_bound dictionary.Q_bound
  have hmassBound : massThreshold / budget ^ 2 ≤
      massThreshold / (Fintype.card ((Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) : ℝ) :=
    div_le_div_of_nonneg_left hmass (by exact_mod_cast Fintype.card_pos) dictionary.pairCard_bound
  let uniform := refinement.mono (hcostBound.trans hcostRec) (hmassRec.trans hmassBound) le_rfl
  let leftOrbit := D.filtration.frozenMarkedLeftOrbit Fmark.filtration
    (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left chosen.1)
  let rightOrbit := D.filtration.frozenMarkedRightOrbit Fmark.filtration
    (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right chosen.2)
  have hscoreUniform : ∀ z : uniform.problem.productive, Real.exp (-recursionParameter) ≤
      uniform.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref leftOrbit rightOrbit
        markedMiddle (uniform.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
    intro z
    exact hscoreRec.trans (hfrozen z)
  have hphysical := fun (z : uniform.problem.productive) u hu =>
    (uniform.problem.chart z).physical_mem_integerBox hξ1 u hu
  have hrec := hrecovery chosen
  let lowerProblem := uniform.problem.refilteredQuotientScoredProblem_on A Fmark φ hφ W
    Dref hDref Fref hFref Qquot hQquot Fquot hFquot leftOrbit rightOrbit markedMiddle K
    hσ1 H hH hchart hsmall hp
    (uniform.refilteredMiddle hφ W Dref Fref markedMiddle middle)
    (fun x => x ∈ integerBox N) hphysical hrec hscoreUniform
  obtain ⟨lower⟩ := recurse chosen lowerProblem
  have hmark := uniform.nativeFrozen_mark_on_slice hφ W Dref hDref Fref
    markedMiddle middle sectionMap hSectionFilt hsection leftMark rightMark
    (dictionary.left chosen.1) (dictionary.right chosen.2)
    (dictionary.left_bounds chosen.1).1 (dictionary.right_bounds chosen.2).1
    localLeft localRight localLeftMark localRightMark hfactor hleft hright hprojLeft hprojRight
  obtain ⟨out⟩ := uniform.problem.conclusion_of_refilteredQuotientScored_on A Fmark φ hφ W
    Dref hDref Fref hFref Qquot hQquot Fquot hFquot leftOrbit rightOrbit markedMiddle K
    hσ1 H hH hchart hsmall hp
    (uniform.refilteredMiddle hφ W Dref Fref markedMiddle middle)
    (fun x => x ∈ integerBox N) hphysical hrec hscoreUniform hmark
    D.basis dw hdb c fw hfb hW hsurj lower
  exact ⟨P₀.conclusion_of_withKeep keep hkeep (uniform.conclusion out)⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateProblem

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : (P₀.withKeep keep hkeep).productive,
      AllocatedExternalLocalCandidate ((P₀.withKeep keep hkeep).chart z) Dref Fref.filtration
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (localLeft localRight : (P₀.withKeep keep hkeep).productive →
      (D.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (localLeftMark localRightMark : (P₀.withKeep keep hkeep).productive →
      (Fmark.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (hfactor : ∀ z : (P₀.withKeep keep hkeep).productive,
      (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localLeft z) *
        (P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
          markedMiddle middle z *
        (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _ ((P₀.withKeep keep hkeep).candidate z).orbit)
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localRight z) = localRightMark z)
    (hleft : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) rightMark)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

variable (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    {nQ nQF : ℕ}
    (Qquot : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQquot : Qquot.filtration = Dref.filtration.quotientTop)
    (Fquot : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hFquot : Fquot.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Qquot.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

include hQquot hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_uniform_dictionary_successor
    {l : ℕ} {slow Bweight Bobs Lip densityCost p budgetLog massLog : ℝ}
    (C : ℕ) (hp0 : 0 ≤ p) (hC : 2 ≤ C)
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt l
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (finiteFreezingInitialPrecision p) (Real.exp budgetLog))
    (hslowLeft : ∀ z, D.filtration.PolynomialSlowBound D.basis (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeft z))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeftMark z))
    (hrationalRight : ∀ z, D.filtration.PolynomialRationalGrid D.basis
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRight z))
    (hrationalMark : ∀ z, Fmark.filtration.PolynomialRationalGrid c
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRightMark z))
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * (Real.exp budgetLog) * max 1 (Real.exp budgetLog)) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hweightCap : Bweight ≤ Real.exp p) (hobsCap : Bobs ≤ Real.exp p)
    (hlipCap : Lip ≤ Real.exp p) (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ (p + C) ^ C) (hdensityInput : densityCost ≤ (p + C) ^ C)
    (hbudgetLog0 : 0 ≤ budgetLog) (hbudgetLog : budgetLog ≤ (p + C) ^ C)
    (hcount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ (p + C) ^ C)
    (hmassLog : massLog ≤ (p + C) ^ C) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (hrecovery : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount, ∀ x, x ∈ integerBox N → ∀ source,
      positiveImageSlice
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot) K
        ((P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x)
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).2
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).1 =
        (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x source)
    {outputCost outputMass outputScore : ℝ}
    (recurse : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ lowerProblem : AllocatedExternalCandidateProblem (E := E) A Qquot Fquot.filtration
        (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref)) (Fref.topQuotientOrbit Fquot hFquot markedMiddle)
        ((P₀.withKeep keep hkeep).refilteredQuotientObservable A Fmark φ hφ W Dref Fref Qquot (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) markedMiddle K)
        weight (finiteFreezingRecursiveParameter C p) (Real.exp (-(finiteFreezingRecursiveParameter C p))) (Real.exp (-(finiteFreezingRecursiveParameter C p))),
        Nonempty (lowerProblem.Conclusion outputCost outputMass outputScore)) :
    Nonempty (P₀.Conclusion outputCost outputMass outputScore) := by
  obtain ⟨hcostRec, hmassRec, hscoreRec⟩ :=
    finiteFreezing_uniform_recursive_budget
      (Fintype.card { i : LayerSamplerVariables G I n B // keep i })
      hp0 hC hcostInput hdensityInput hbudgetLog0 hbudgetLog hcount hmassLog hmassInput
  have hsurplus := finiteFreezing_initial_score_surplus hp0 hBobs hLip
    hweightCap hobsCap hlipCap hscoreInput
  exact P₀.conclusion_of_dictionary_successor Fmark φ hφ keep hkeep W Dref hDref Fref
    markedMiddle middle sectionMap hSectionFilt c leftMark rightMark
    localLeft localRight localLeftMark localRightMark hfactor hprojLeft hprojRight
    hleft hright tests htests hσ1 H hH hchart hsmall hp
    hFref Qquot hQquot Fquot hFquot K
    dictionary hslowLeft hslowMark hrationalRight hrationalMark hdensity hfloor
    hBweight hBobs hLip (finiteFreezing_initial_precision_pos p).le hweight hnorm hlip
    (by positivity) (finiteFreezing_initial_discard_pos p) hsurplus
    hsection ((Real.exp_nonneg _).trans hmassInput)
    dw hdb fw hfb hW hsurj hξ1 hrecovery
    (finiteFreezingRecursiveParameter C p) hcostRec hmassRec hscoreRec recurse

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateResetSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i})}
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    (slow : ℝ) (denominator : ℕ)

namespace AllocatedExternalGlobalNativeResetFamily

variable {Fmark φ hφ P keep hkeep W factors slow denominator}

variable (reset : AllocatedExternalGlobalNativeResetFamily
    Fmark φ hφ P keep hkeep W factors slow denominator)

theorem left_mark_values (z : (P.withKeep keep hkeep).productive) (u : {i // keep i} → ℤ) :
    Fmark.filtration.adaptedPolynomialRealValueHom (fun _ : {i // keep i} => 1)
      (fun i => (u i : ℝ))
      (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : {i // keep i} => 1)
        (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
        ((P.withKeep keep hkeep).chart z).integerChart_support factors.left) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight J)
        (fun i => (((P.withKeep keep hkeep).chart z).chartValues u i : ℝ)) reset.leftMark :=
  ((P.withKeep keep hkeep).chart z).globalOrbit_chart_values Fmark.filtration factors.left u

variable {nD nF : ℕ}
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

theorem candidate_factor (z : (P.withKeep keep hkeep).productive) :
    (show (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : ((P.withKeep keep hkeep).chart z).Variables => 1)).Group from reset.localLeft z) *
      (P.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
        (factors.markedMiddleOn Fref hFref) (reset.candidate Dref hDref Fref hFref) z *
      (show (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : ((P.withKeep keep hkeep).chart z).Variables => 1)).Group from reset.localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _
        ((P.withKeep keep hkeep).candidate z).orbit := by
  exact (P.withKeep keep hkeep).refilteredLocalCoordinates_factor_of_log A Fmark φ hφ W
    Dref hDref Fref (factors.markedMiddleOn Fref hFref)
    (reset.candidate Dref hDref Fref hFref) reset.localLeft reset.localMiddle reset.localRight
    (reset.candidate_included_log Dref hDref Fref hFref) reset.source_factor z

end AllocatedExternalGlobalNativeResetFamily
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateCoveredFamilySuccessor
namespace OAI

section

universe uL uM uX

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G : Type*} {X : Type uX} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateProblem

variable {L : Type uL} {M : Type uM} {ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = Dref.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hQF : QF.filtration = Fref.filtration.quotientTop)
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

variable
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]

theorem exists_refilteredQuotient_uniform_nets
    (r e : ℕ) (cap ℓ : ℝ≥0) {p dictBound : ℝ} {rightDenominator : ℕ}
    (rightDictionary : D.NativeGridRightDictionary rightDenominator dictBound)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hF : Fref.GeometryComplexityLE p)
    (hcap : 1 ≤ cap) (hcapBound : (cap : ℝ) ≤ Real.exp ((p + 2) ^ r))
    (hK : (K : ℝ) ≤ Real.exp p) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hcount : (rightDictionary.count : ℝ) ≤ Real.exp p)
    (hLip : ∀ x ∈ integerBox N, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x ∈ integerBox N, ∀ y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (hleft : ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) left).coord i| ≤ cap)
    (hright : ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) right).coord ∈ realDenominatorGrid rightDenominator)
    (hrecovery :
      letI := Q.metricSpace
      letI := Fref.metricSpace
      let diagram := Dref.markedTopQuotientDiagram Fref
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
      ∀ x ∈ integerBox N, ∀ a r₀ : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ cap) →
        (D.basis.baseChange ℝ).equivFun r₀.coord ∈
          realDenominatorGrid rightDictionary.denominator →
        let frozen := fun source : Dref.RealGroup => observable x (QuotientGroup.mk
          (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl source * r₀))
        ∀ source, positiveImageSlice diagram K frozen
          (diagram source).2 (diagram source).1 = frozen source) :
    letI := Q.metricSpace
    letI := Fref.metricSpace
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / ε) +
        RationalFilteredNilmanifold.refilteredQuotientNetExponent.{uL, uM, uX} s r e) ^
        RationalFilteredNilmanifold.refilteredQuotientNetExponent.{uL, uM, uX} s r e) ∧
      ∃ centers : Fin n → Q.Space → ℂ,
        (∀ i, LipschitzWith K (centers i)) ∧
        (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
        (∀ i y, ‖centers i y‖ ≤ 1) ∧
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q
            left right markedMiddle K x y - centers i y‖ ≤ ε := by
  let := Q.metricSpace
  let := Fref.metricSpace
  let sites := {x : X → ℤ // x ∈ integerBox N}
  let family : sites → D.Space → ℂ := fun x => observable x.val
  let inclusion : Dref.RealGroup → D.RealGroup :=
    realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra W).incl
  let diagram := Dref.markedTopQuotientDiagram Fref
    (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
  let leftAt (x : sites) : coordinateBox
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) cap :=
    ⟨D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x.val) left, hleft x.val x.property⟩
  let rightAt (x : sites) : D.RealGroup :=
    D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x.val) right
  obtain ⟨label, hlabel⟩ := rightDictionary.labeling rightAt
    (fun x => hright x.val x.property)
  have hmember η hη hη1 := hnet η hη hη1
  have hmember' : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → sites, ∀ x, ∃ i, ∀ y, ‖family x y - family (oc i) y‖ ≤ η := by
    intro η hη hη1
    obtain ⟨n, hn, oc, hoc⟩ := hmember η hη hη1
    exact ⟨n, hn, oc, fun x => hoc x.val x.property⟩
  have hrec (x : sites) (a : coordinateBox
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) cap)
      (j : Fin rightDictionary.count) :=
    exists_lipschitz_reconstruction_of_positiveImageSlice_eq diagram K
      (fun source => family x (QuotientGroup.mk (a.val * inclusion source * rightDictionary.representative j)))
      (fun _ => (hpositive x.val x.property _).2.1)
      (hrecovery x.val x.property a.val (rightDictionary.representative j) a.property
        (rightDictionary.representative_bounds j).2)
  have hfixed := (Classical.choose_spec
    (RationalFilteredNilmanifold.exists_uniform_controlled_native_external_nets.{uL, uM, uX, 0, uL, uL}
      (s + 1) (s + 1) r e)).2 D Fref cap K ℓ hp hD hF hcap hcapBound hK hℓ
    (by simpa only [Fintype.card_fin] using hcount)
    family inclusion rightDictionary.representative diagram
    (fun x => hLip x.val x.property) (fun x y => hpositive x.val x.property y) hmember' hrec
  dsimp only at hfixed ⊢
  intro ε hε hε1
  obtain ⟨n, hn, centers, hcentersLip, hunit, hnorm, _, hcover⟩ := hfixed ε hε hε1
  refine ⟨n, hn, centers, hcentersLip, hunit, hnorm, ?_⟩
  intro x hx
  let site : sites := ⟨x, hx⟩
  have hfrozen : P.refilteredFrozenObservable A Fmark φ W Dref left right x =
      fun source => family site (QuotientGroup.mk
        ((leftAt site).val * inclusion source * rightDictionary.representative (label site))) := by
    funext source
    exact congrArg (observable x) ((hlabel site).2 ((leftAt site).val * inclusion source))
  obtain ⟨i, hi⟩ := hcover site (leftAt site) (label site)
    (QuotientGroup.mk (Fref.filtration.realification.polynomialOrbitEval
      (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) markedMiddle))
  refine ⟨i, ?_⟩
  simpa only [refilteredQuotientObservable, hfrozen] using hi

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrimitivePhysicalBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold

theorem candidatePrimitivePhysicalScalarBounds (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    GeneratedPhysicalSuccessorScalarBounds s (candidateFreezingOuterExponent s a)
      (candidatePrimitivePhysicalBudgetExponent s a) p
      (candidatePrimitivePhysicalOuterParameter s a p) :=
  candidateGeneratedPhysicalScalarBounds s (candidateFreezingOuterExponent s a) hp
    (candidatePrimitivePhysicalOuterParameter_nonneg s a hp)
    (candidatePrimitivePhysicalOuterParameter_bound s a hp)

theorem candidatePrimitivePhysical_freezing_budget (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + nativeMarkedFreezingExponent (s + 1) a) ^ nativeMarkedFreezingExponent (s + 1) a ≤
      (p + candidatePrimitivePhysicalBudgetExponent s a) ^
        candidatePrimitivePhysicalBudgetExponent s a :=
  (nativeMarkedFreezingPhysicalParameter_bounds hp
    (nativeMarkedFreezingExponent (s + 1) a)).2.1.trans
      (candidatePrimitivePhysicalScalarBounds s a hp).outer_budget

theorem candidatePrimitivePhysical_input_budget (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ (p + candidatePrimitivePhysicalBudgetExponent s a) ^
      candidatePrimitivePhysicalBudgetExponent s a :=
  (nativeMarkedFreezingPhysicalParameter_bounds hp
    (nativeMarkedFreezingExponent (s + 1) a)).1.trans
      (candidatePrimitivePhysicalScalarBounds s a hp).outer_budget

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace AxisFreezing

variable {P} {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

theorem problem_slice_dense (z : P.productive) :
    IsDenseCommonStrideBox
      (fun i : (freezing.problem.chart z).Variables => A.sides i.val) cost
      (freezing.problem.chart z).slice.integerPoints :=
  (P.chart z).slice.comap_isDenseCommonStrideBox (P.chart z).step_pos (P.chart z).dense
    ((P.chart z).keptInclusion (keep z) (freezing.keep_subset z))

theorem problem_slice_inside (z : P.productive)
    {u : {i // keep z i} → ℤ}
    (hu : u ∈ (freezing.problem.chart z).slice.integerPoints) :
    (P.chart z).axisPoint (keep z) (freezing.fixed z) u ∈
      (P.chart z).slice.integerPoints :=
  (P.chart z).axisPoint_mem (keep z) (freezing.keep_subset z)
    (freezing.fixed z) (freezing.fixed_mem z) hu

end AxisFreezing

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] integerProgressionSupport IsDenseCommonStrideBox ResidueBoxSlice.integerPoints

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace AxisFreezing

variable {P} {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

noncomputable def extendSlice (z : P.productive) {step : ℕ}
    (slice : ResidueBoxSlice (fun i : {i // keep z i} => A.sides i.val) step) :
    ResidueBoxSlice (fun i : (P.chart z).Variables => A.sides i.val) step :=
  slice.extendAxes (N := A.sides) (oldKeep := (P.chart z).keep) (keep := keep z) (P.chart z).slice (freezing.fixed z) (freezing.fixed_mem z)

theorem conclusion_subset {outputCost outputMass outputScore : ℝ}
    (out : freezing.problem.Conclusion outputCost outputMass outputScore) :
    out.retained ⊆ P.productive := out.subset

end AxisFreezing
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
namespace OAI

section

universe u v

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateProblem

variable {Pivot : Type v} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    {s d : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold LG s d}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (partners : ∀ j, RationalFilteredNilmanifold (MG j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

variable (ideal : LieIdeal ℚ LG)
    (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    {dQ : ℕ} (Q : RationalFilteredNilmanifold (LG ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))

variable (adapted : (optionProduct Q partners).AdaptedModelData)

def adaptedOptionQuotient :=
  (P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).adaptedRebase adapted

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_mixed_long_coeff
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*}
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (α : LayerSamplerVariables G I n B →₀ ℕ)
    (htouches : ∃ i, H ≤ layerSamplerBox B U b S i ∧ α i ≠ 0) :
    Q (fun i => (((allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
      (Sum.inr ⟨j, i⟩)).coeff α : ℤ) : ℝ)) = 0 := by
  by_cases hdegree : α.degree ≤ j.val + 1
  · let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
      fun k z => (jointIntegerFrame (a, v) k z : ℝ)
    let d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) :=
      ⟨α, hdegree⟩
    have hc : canonicalCoefficientSample U b hb o sample =
        QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (centeredAffineCoefficientArray U poly hm c frame) :=
      h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
    change Q (fun i => (((coefficientIntegerFloorPolynomial U b o sample
      (centeredAffineCoefficientArray U poly hm c frame) j i).coeff d.val : ℤ) : ℝ)) = 0
    apply canonicalCoefficientSample_floor_coeff_separate U b hb o sample _ hc j d Q hQU hD hgrid
    let M : ℝ := C * (((Fintype.card (I j) : ℝ) + 1) * R j)
    let scale : ℝ := monomialScale (layerSamplerBox B U b S) α
    have hscale : 0 < scale := monomialScale_pos _
      (fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S i)) α
    have hM : 0 ≤ M := mul_nonneg hC (mul_nonneg (by positivity) (hR j).le)
    have hnorm : ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
        (b j) (o j) (sample j) d i‖ ≤ M / scale := by
      apply (pi_norm_le_iff_of_nonneg (div_nonneg hM hscale.le)).mpr
      intro i
      simpa only [Real.norm_eq_abs] using
        allocatedLayerLiftCoefficient_radius_bound B U b hR hσ S hσ1 o j hC hchart
          (sample j) (h.2.2.1 j).2 d i
    have hscaleH : H ≤ scale := by
      obtain ⟨i, hi, hαi⟩ := htouches
      exact hi.trans (le_monomialScale_of_coordinate _ (layerSamplerBox_one_le B U b S) i hαi)
    intro t
    calc
      _ ≤ CQ * ‖fun i => mixedLiftCoefficient (euclideanSubspace (U j))
          (b j) (o j) (sample j) d i‖ := hQ _ t
      _ ≤ CQ * (M / scale) := mul_le_mul_of_nonneg_left hnorm hCQ
      _ = (CQ * M) / scale := (mul_div_assoc CQ M scale).symm
      _ < 1 / D := (div_lt_div_iff₀ hscale hD).mpr (by
        simpa only [one_mul] using hthreshold.trans_le hscaleH)
  · have hzero (i : J j) : (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
        (Sum.inr ⟨j, i⟩)).coeff α = 0 :=
      coeff_eq_zero_of_totalDegree_lt ((allocatedRecoveredIntegerFullChart_tag_degree
        B U b o poly hm c a v sample j i).trans_lt (lt_of_not_ge hdegree))
    simp only [hzero, Int.cast_zero]
    exact map_zero Q

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_coeff
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*} (keep : LayerSamplerVariables G I n B → Prop)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (fixed : {i // ¬ keep i} → ℤ)
    (α : {i // keep i} →₀ ℕ) (hα : α ≠ 0) :
    Q (fun i => (MvPolynomial.map (Int.castRingHom ℝ)
      (freezePolynomial keep fixed (allocatedRecoveredIntegerFullChart B U b o poly hm
        c a v sample (Sum.inr ⟨j, i⟩)))).coeff α) = 0 := by
  apply frozenPolynomialFamily_coeff_mem _ keep fixed (LinearMap.ker Q) _ α hα
  intro d hd
  apply h.integerFullChart_mixed_long_coeff B U b hb o S hR hσ poly hm hσ1 c a v sample read
    j Q hQU hC hCQ hD hchart hQ hgrid hthreshold d
  obtain ⟨i, hi, hdi⟩ := hd
  exact ⟨i, hlong i hi, hdi⟩

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_affine_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*} (keep : LayerSamplerVariables G I n B → Prop)
    (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ)) (hQU : U j ≤ LinearMap.ker Q)
    (Ktarget : Submodule ℝ (J j → ℝ)) (hker : LinearMap.ker Q ≤ Ktarget)
    {C CQ D H : ℝ} (hC : 0 ≤ C) (hCQ : 0 ≤ CQ) (hD : 0 < D)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C * ‖x‖)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (hgrid : ∀ z : J j → ℤ, ∀ t, ∃ a : ℤ, D * Q (fun i => (z i : ℝ)) t = a)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : CQ * (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) * D < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i =>
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ)
        (freezePolynomial keep fixed (allocatedRecoveredIntegerFullChart B U b o poly hm
          c a v sample (Sum.inr ⟨j, i⟩)))) -
      MvPolynomial.eval 0 (MvPolynomial.map (Int.castRingHom ℝ)
        (freezePolynomial keep fixed (allocatedRecoveredIntegerFullChart B U b o poly hm
          c a v sample (Sum.inr ⟨j, i⟩))))) ∈ Ktarget := by
  apply hker
  apply polynomialFamily_eval_sub_zero_mem _ (LinearMap.ker Q) _ x
  exact h.integerFullChart_frozen_coeff B U b hb o S hR hσ poly hm hσ1 c a v sample read
    j keep Q hQU hC hCQ hD hchart hQ hgrid hlong hthreshold fixed

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_certified_frozen_affine_range
    (hσ1 : ∀ j, σ j ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {Bstage p M H : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K Bstage blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hBp : Bstage ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hM : 0 ≤ M) (hcap : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hlong : ∀ i, keep i → H ≤ layerSamplerBox B U b S i)
    (hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * M < H)
    (fixed : {i // ¬ keep i} → ℤ) (x : {i // keep i} → ℝ) :
    (fun i => MvPolynomial.eval x
      (integerSampledRealChart
        (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i) -
      MvPolynomial.eval 0
      (integerSampledRealChart
        (fun z => freezePolynomial keep fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i)) ∈ K := by
  obtain ⟨cs, _, hbudget, hK⟩ := hcertificate
  rw [hK]
  refine ⟨Set.mem_univ _, ?_⟩
  intro constraint hc
  have hspan : U constraint.tag ≤
      span ℝ (Set.range (fun q i => (constraint.generators q i : ℝ))) := by
    apply constraint.retained_le_span U hretained
    intro point hpoint
    rw [hK] at hpoint
    exact hpoint.2 constraint hc
  obtain ⟨d, _, Q, hker, hQ, D, hD, hDbound, hgrid⟩ :=
    exists_rationalTaggedSpanProjection constraint.generators hp (hJ constraint.tag)
      ((hbudget constraint hc).1.trans hBp)
      (fun q i => ((hbudget constraint hc).2 q i).trans hBp)
  have hQU : U constraint.tag ≤ LinearMap.ker Q := by
    rw [hker]
    exact hspan
  have hgrid' : ∀ z : J constraint.tag → ℤ, ∀ t,
      ∃ a : ℤ, (D : ℝ) * Q (fun i => (z i : ℝ)) t = a := by
    intro z t
    obtain ⟨w, hw⟩ := hgrid z
    exact ⟨w t, (hw t).symm⟩
  have hnumeric : Real.exp ((p + 2) ^ 9) *
      (C constraint.tag * (((Fintype.card (I constraint.tag) : ℝ) + 1) * R constraint.tag)) *
        (D : ℝ) < H := by
    have hE := Real.exp_nonneg ((p + 2) ^ 9)
    calc
      _ ≤ Real.exp ((p + 2) ^ 9) * M * (D : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcap constraint.tag) hE)
          (Nat.cast_nonneg D)
      _ ≤ Real.exp ((p + 2) ^ 9) * M * Real.exp ((p + 2) ^ 9) :=
        mul_le_mul_of_nonneg_left hDbound (mul_nonneg hE hM)
      _ = Real.exp ((p + 2) ^ 9) ^ 2 * M := by ring
      _ < H := hthreshold
  exact h.integerFullChart_frozen_affine_range B U b hb o S hR hσ poly hm hσ1 c a v sample read
    constraint.tag keep Q hQU _ (le_of_eq hker) (hC constraint.tag)
    (Real.exp_nonneg _) (by exact_mod_cast hD) (hchart constraint.tag) hQ hgrid'
    hlong hnumeric fixed x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateThresholdSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration RationalFilteredNilmanifold

theorem candidatePrimitiveFreezingCutoff_add_two_le_budget (s a : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    candidatePrimitiveFreezingCutoff s a p + 2 ≤
      (p + candidatePrimitivePhysicalBudgetExponent s a) ^
        candidatePrimitivePhysicalBudgetExponent s a :=
  (candidatePrimitiveFreezingCutoff_add_two_le_geometry s a hp).trans
    (candidatePrimitivePhysicalScalarBounds s a hp).geometry_budget

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

def localTest (a : Ω) (j : Pivot) : D.Niltest (fun _ : {i // keep i} => 1) :=
  (F.reference a j).withOrbit (F.candidate a).orbit

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end


