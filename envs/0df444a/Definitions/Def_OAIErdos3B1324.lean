-- Prove2me | Definitions.Def_OAIErdos3B1324
-- name    : OAIErdos3B1324
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T17:50:33.681333+00:00
-- url     : https://prove2.me/theorems/225d428e-f2b9-4169-8802-dbb51f07ce96
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1325 of 1331
-- statement:
--   Definitions bundle 1325 of 1331 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1323`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1325 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.physicalCubePositiveTest_rows`, `OAI.Erdos3.BooleanCubeKernel.physicalRowsStandardEquiv_symm_sample`, `OAI.Erdos3.BooleanCubeKernel.selectedJointFiniteLaw_collision_small_with_cap`, `OAI.Erdos3.BooleanCubeKernel.selectedJointFiniteLaw_noninjectivity_le`, `OAI.Erdos3.BooleanCubeKernel.selectedJointReference_collision`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredNarrowPrescribedMarginalOneCenterStatement`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredNarrowPrescribedMarginalPointwiseStatement`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredNarrowPrescribedMarginalStatement`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.Path`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.Site`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.bases`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.law`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.law_zero_layers`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.physical`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.physical_eq`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.sides`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.widths`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.widths_pos`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSamplerFamily`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSamplerFamily.Path`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSamplerFamily.Site`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSamplerFamily.law`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.B`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.I`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.J`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.Q`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.U`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.b`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.bW`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.lattice_full`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.n`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.o`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.poly`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredConditionalPolynomial`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredConditionalPolynomial_degree`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredConditionalPolynomial_density`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredConditionalPolynomial_mem`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredConditionalPolynomial_rank`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredJointDensity_zero_layers`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredJointFiniteLaw_weight_measurable`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredJoint_productivity`, `OAI.Erdos3.VectorPolynomial.allocatedExternalCandidateRootBudget`, `OAI.Erdos3.VectorPolynomial.allocatedExternalCandidateRootBudget_eq`, `OAI.Erdos3.VectorPolynomial.allocatedExternalCandidateRootBudget_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedExternalCandidateSides`, `OAI.Erdos3.VectorPolynomial.allocatedExternalCandidateSides_empty_layers`, `OAI.Erdos3.VectorPolynomial.allocatedExternalCandidateSides_zero_layers`, `OAI.Erdos3.VectorPolynomial.allocatedExternalCandidateWidths`, `OAI.Erdos3.VectorPolynomial.allocatedSlicedTupleValue`, `OAI.Erdos3.VectorPolynomial.allocatedSlicedTupleValue_select_base`, `OAI.Erdos3.VectorPolynomial.emptyLayerVariablesEquiv`, `OAI.Erdos3.VectorPolynomial.emptyLayerVariablesEquiv_inl`, `OAI.Erdos3.VectorPolynomial.emptyLayerVariablesEquiv_symm`, `OAI.Erdos3.VectorPolynomial.exists_allocated_centered_narrow_prescribed_marginal`, `OAI.Erdos3.VectorPolynomial.exists_allocated_centered_narrow_prescribed_marginal_oneCenter`, `OAI.Erdos3.VectorPolynomial.exists_allocated_centered_narrow_prescribed_marginal_pointwise`, `OAI.Erdos3.VectorPolynomial.exists_allocated_narrow_normalized_approximation`, `OAI.Erdos3.VectorPolynomial.exists_allocated_narrow_path_marginal`, `OAI.Erdos3.VectorPolynomial.exists_allocated_narrow_prescribed_marginal`, `OAI.Erdos3.VectorPolynomial.exists_allocated_sliced_projected_source`, `OAI.Erdos3.VectorPolynomial.exists_allocated_sliced_rows_projected_source`, `OAI.Erdos3.VectorPolynomial.scalarNativeDimension`, `OAI.Erdos3.VectorPolynomial.scalarNativeDimension_capacity`, `OAI.Erdos3.VectorPolynomial.scalarNativeDimension_selection_bound`, `OAI.Erdos3.VectorPolynomial.scalarNativeSelection`, `OAI.Erdos3.VectorPolynomial.scalarNativeSelection_val`, `OAI.Erdos3.VectorPolynomial.zeroLayerVariablesEquiv`, `OAI.Erdos3.VectorPolynomial.zeroLayerVariablesEquiv_inl`, `OAI.Erdos3.VectorPolynomial.zeroLayerVariablesEquiv_symm`, `OAI.Erdos3.VectorPolynomial.zeroLayerVariables_card`, `OAI.Erdos3.allocatedFixedScaleCollisionLog`, `OAI.Erdos3.centeredFiniteMarginal_siteLaw_excessMass_le_of_uniform`, `OAI.Erdos3.collision_error_of_exp_size_with_cap`, `OAI.Erdos3.exists_allocatedFixedScaleCollisionLog_bound`, `OAI.Erdos3.exists_large_vertex_of_cube_mixture`, `OAI.Erdos3.exists_site_twist_of_degree_zero_cube_mixture`, `OAI.Erdos3.selectedJointFiniteLaw_integral_productivity`, `OAI.Erdos3.unconditionedCollisionWidth`, `OAI.Erdos3.unconditionedResidueSiteBound`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B177
import Definitions.Def_OAIErdos3B1325

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedNarrowPathMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_path_marginal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-P) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x,
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((allocatedOriginalPathLaw B U basis hb o hR hσ S X p hm N hN _hW _hτ _hξ
          stride T hmass bases hbases hnormalizer.2.2.1).siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy P := by
  obtain ⟨A₁, hA₁, hone⟩ := exists_allocated_narrow_oneSite_domination m
  obtain ⟨A₂, hA₂, hnorm⟩ := exists_allocated_narrow_normalization m
  let A := max (max A₁ A₂) 256
  have hA : 256 ≤ A := le_max_right _ _
  have hA₁A : A₁ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hA₂A : A₂ ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  have hthreshold (a : ℕ) (ha : a ≤ A) :
      Real.exp ((P + a) ^ a) ≤ Real.exp ((P + A) ^ A) := by
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    have har : (a : ℝ) ≤ A := by exact_mod_cast ha
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P + (a : ℝ) ≤ P + A) a).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P + A) ha)
  obtain ⟨hwidths, hmass, hone⟩ := hone B U basis S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
    hW hWP hτ hτP hξ hξ1 hξP N
    (fun x => (hthreshold A₁ hA₁A).trans (hsize x)) hrank
    ((hthreshold A₁ hA₁A).trans hRank) T hT
  obtain ⟨_, _, _, hnorm⟩ := hnorm B U basis S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
    hW hWP hτ hτP hξ hξ1 hξP N
    (fun x => (hthreshold A₂ hA₂A).trans (hsize x)) hrank
    ((hthreshold A₂ hA₂A).trans hRank) T hT
  have hN (x) : 0 < N x := by exact_mod_cast (Real.exp_pos _).trans_le (hsize x)
  have hmarginSize (x) : 4 ≤ τ * (N x : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize x))
  have hproper := spatialTrimMargin_proper hτhalf N hN hmarginSize
  have hbases : bases.Nonempty := trimmedIntegerBox_nonempty N _ hproper
  have hbox : (integerBox N).Nonempty := by
    let : ∀ x, NeZero (N x) := fun x => ⟨(hN x).ne'⟩
    exact integerBox_nonempty N
  have hnormalizer : |Z - 1| ≤ Real.exp (-P) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 := hnorm bases hbases
  have hmargin (x) := (hproper x).le
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Sites _ _ root hroot hrootSum
  let : Nonempty (integerBox N) := hbox.to_subtype
  let e : integerBox N → X → ℝ := fun x i => (x.val i : ℝ)
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hc : (x.val i : ℝ) = (y.val i : ℝ) := congrFun hxy i
    exact_mod_cast hc
  have hloss : (∑ x, 2 * (spatialTrimMargin τ N x : ℝ) / N x) ≤ 1 / 2 := by
    have h := spatialTrimMargin_error_bound N hN hmarginSize
    linarith
  have hcard : (Fintype.card (integerBox N) : ℝ) / bases.card ≤ 2 := by
    simpa only [Fintype.card_coe] using trimmedIntegerBox_card_ratio_le_two N _ hproper hloss
  have hcap : 0 ≤ ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j) :=
    Finset.prod_nonneg (fun j _ => earlyConstantDensityCap_nonneg _ _ (hR j) (V j).coe_nonneg)
  have h := selectedJointFiniteLaw_site_excess bases hbases stride T widths hwidths hmass density
    (allocatedJointBaseDensity_nonneg B U basis hb o hR hσ S X p hm)
    hnormalizer.2.2.1 hnormalizer.2.1.1 e he root
    (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ1 N hN hmargin root hrootSum)
    (fun z t => narrowPhysicalSiteMap_cast (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ1 N hN hmargin root hrootSum z t)
    hcard hcap (fun a t φ hφ => hone a (root t) (hroot t) φ hφ)
  exact h.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowPrescribedMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_prescribed_marginal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x,
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((allocatedOriginalPathLaw B U basis hb o hR hσ S X p hm N hN _hW _hτ _hξ
          stride T hmass bases hbases hnormalizer.2.2.1).siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_narrow_path_marginal m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  have hPP : P ≤ max P E := le_max_left _ _
  have hEP : E ≤ max P E := le_max_right _ _
  have hexp := Real.exp_le_exp.mpr hPP
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hsite⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      (hP.trans hPP) (hmSize.trans hPP) (hK.trans hPP) (hX.trans hPP) (hdim.trans hPP)
      (fun j => (hRP j).trans hexp) (fun j => (hσP j).trans hexp)
      (fun j => (hcount j).trans hPP) (fun j => (hI j).trans hPP)
      (fun j => (hn j).trans hPP) (fun j => (hJ j).trans hPP)
      (hAP.trans hexp) (hLP.trans hexp) (fun j => (hCP j).trans hexp)
      (fun j => (hVP j).trans hexp) p hp hm stride hs (fun j => (hsP j).trans hexp)
      hW (hWP.trans hexp) hτ (hτP.trans hexp) hτhalf hτdim hξ hξ1 (hξP.trans hexp)
      N hsize hrank hRank T hT
  have hnormalizer' : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 :=
    ⟨hnormalizer.1.trans (Real.exp_le_exp.mpr (neg_le_neg hEP)), hnormalizer.2⟩
  refine ⟨hN, hbases, hbox, hmass, hnormalizer', hmargin, ?_⟩
  intro Sites _ _ root hroot hrootSum
  have h := hsite root (fun t k => (hroot t k).trans hexp) hrootSum
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 6)
  unfold positiveProjectionAccuracy
  exact Real.exp_le_exp.mpr (by linarith)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem centeredFiniteMarginal_siteLaw_excessMass_le_of_uniform
    {C Ω T X : Type*} [MeasurableSpace C] [Fintype Ω]
    [Fintype T] [Nonempty T] [Fintype X]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun c => (law c).weight z))
    (physical : Ω → T → X)
    (reference : FiniteProbabilityWeights X) (cap ε : ℝ)
    (h : ∀ c, reference.excessMass ((law c).siteLaw physical) cap ≤ ε) :
    reference.excessMass ((centeredFiniteMarginal μ law hweight).siteLaw physical) cap ≤ ε := by
  rw [centeredFiniteMarginal_siteLaw]
  exact centeredFiniteMarginal_excessMass_le_of_uniform μ _ _ reference cap ε h

namespace VectorPolynomial

open Module Submodule

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
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem allocatedCenteredJointFiniteLaw_weight_measurable
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
    (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z)
    (hDcenter : ∀ center, 0 < selectedJointDensityMass bases stride cells W
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center))
    (z : bases × rectangularWeightIndices 0 W 1) :
    Measurable (fun center =>
      (selectedJointFiniteLaw bases hbases stride cells W hW hmass
        (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
        (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center)
        (hDcenter center)).weight z) :=
  selectedJointFiniteLaw_weight_measurable bases hbases stride cells W hW hmass
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem)
    (allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hmem)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem) hDcenter z

end VectorPolynomial

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_normalized_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x,
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S X p hm N hN _hW _hτ _hξ
        stride T hmass bases hbases hnormalizer.2.2.1
      let physical := narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        _hW _hτ _hξ1 N hN hmargin root hrootSum
      let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
      ∀ {Tests : (bases × rectangularWeightIndices 0 widths 1) → Type*}
        [∀ z, Nonempty (Tests z)]
        (slices : ∀ z, Tests z → Finset Sites) (tests : ∀ z, Tests z → Sites → ℂ)
        (w : X → ℕ) (degree : ℕ) {u pModel budget K : ℝ}
        (_hu : 0 ≤ u) (_hpModel : 0 ≤ pModel) (_hbudget : 0 ≤ budget)
        (_hKmodel : 0 ≤ K) (_hKp : K ≤ Real.exp pModel) (_hCtail : Ctail ≤ Real.exp pModel)
        (_hsizeModel : ∀ z j, (Fintype.card Sites : ℝ) / (slices z j).card ≤ K)
        (_htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
        {periodCap coverCap : ℝ} {lip : ℝ≥0},
        u + 2 * pModel + budget + 30 ≤ E →
        (∀ signal : (X → ℤ) → ℂ, (∀ t, ‖signal t‖ ≤ 1) →
          (∀ t, t ∉ integerBox N → signal t = 0) →
          allocatedModelUnitThreshold u pModel K Ctail ≤ sampledSliceSeminorm pathLaw
            (fun z t => jointIntegerPhysicalSite (root t) (z.1.val, z.2.val)) slices tests signal →
          ∃ (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
            (F : integerBox N → ℂ),
            Nonempty (NativeSampleModel w degree budget (fun t : integerBox N => t.val) F) ∧
            Real.exp (-budget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
              (fun t => signal t.val) (fun t => star (twist.eval N p t.val) * F t)‖) →
        ∀ (input : integerBox N → ℂ), (∀ t, ‖input t‖ ≤ Real.exp pModel) →
        ∃ (nterms : ℕ) (_ : 0 < nterms)
          (Q : Fin nterms → (integerBox N → ℂ))
          (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
          (∀ i, Q i ∈ twistedNativeSampleFunctions w degree budget
            (fun t : integerBox N => t.val)
            (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
              (t : integerBox N) => twist.eval N p t.val)) ∧
          input = (∑ i, coeff i • Q i) + err ∧
          (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
          sampledSliceSeminorm pathLaw physical slices tests err ≤ Real.exp (-u) ∧
          (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * pModel + 30) := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_narrow_prescribed_marginal m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hsite⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
      hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize hrank hRank T hT
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Sites _ _ root hroot hrootSum pathLaw physical Ctail Tests _ slices tests
    w degree u pModel budget K hu hpModel hbudget hKmodel hKp hCtail hsizeModel htests
    periodCap coverCap lip htail hdetect input hinput
  let : ∀ i, NeZero (N i) := fun i => ⟨(hN i).ne'⟩
  have hCtail0 : 0 ≤ Ctail := by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    exact Finset.prod_nonneg (fun j _ =>
      earlyConstantDensityCap_nonneg _ _ (hR j) (V j).coe_nonneg)
  exact exists_normalizedTwist_native_approximation_with_budget N p pathLaw physical
    (fun z t => jointIntegerPhysicalSite (root t) (z.1.val, z.2.val)) (fun _ _ => rfl)
    slices tests w degree hu hpModel hbudget hKmodel hCtail0 hKp hCtail hsizeModel htests
    hdetect htail (hsite root hroot hrootSum) input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def AllocatedCenteredNarrowPrescribedMarginalStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    let Z := fun center => selectedJointDensityMass bases stride T widths (density center)
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x),
    ∃ hnormalizer : ∀ center, |Z center - 1| ≤ Real.exp (-E) ∧
      Z center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z center ∧ (Z center)⁻¹ ≤ 2,
    let law := fun center => selectedJointFiniteLaw bases hbases stride T widths
      (narrowTrimmedSpatialWidths_pos _hW _hτ _hξ N hN) hmass (density center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hnormalizer center).2.2.1
    ∃ hweight : ∀ z, Measurable (fun center => (law center).weight z),
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((centeredFiniteMarginal μ law hweight).siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
            _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E

def AllocatedCenteredNarrowPrescribedMarginalPointwiseStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    let Z := fun center => selectedJointDensityMass bases stride T widths (density center)
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x),
    ∃ hnormalizer : ∀ center, |Z center - 1| ≤ Real.exp (-E) ∧
      Z center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z center ∧ (Z center)⁻¹ ≤ 2,
    let law := fun center => selectedJointFiniteLaw bases hbases stride T widths
      (narrowTrimmedSpatialWidths_pos _hW _hτ _hξ N hN) hmass (density center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      (hnormalizer center).2.2.1
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      ∀ center,
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        ((law center).siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
            _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E

def AllocatedCenteredNarrowPrescribedMarginalOneCenterStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ (Z)⁻¹ ≤ 2,
    let law := selectedJointFiniteLaw bases hbases stride T widths
      (narrowTrimmedSpatialWidths_pos _hW _hτ _hξ N hN) hmass density
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
      hnormalizer.2.2.1
    ∀ {Sites : Type*} [Fintype Sites] [Nonempty Sites]
      (root : Sites → LayerSamplerVariables G I n B → ℤ)
      (_hroot : ∀ t k, |(root t k : ℝ)| ≤ Real.exp P)
      (hrootSum : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W),
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        (law.siteLaw
          (narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
            _hW _hτ _hξ1 N hN hmargin root hrootSum))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E

theorem exists_allocated_centered_narrow_prescribed_marginal_oneCenter (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedCenteredNarrowPrescribedMarginalOneCenterStatement m A := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_narrow_prescribed_marginal m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT
    center widths bases density Z
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  obtain ⟨hN, hbases, hbox, hmass, hnorm, hmargin, hsite⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV
      Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ
      hAP hLP hCP hVP (fun j => subtractConstant (c j).val (p j))
      (fun j => (hp j).subtractConstant (c j).val)
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j))
      stride hs hsP hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize
      (fun j => (hasLayerSamplingRank_subtractConstant_iff (Nat.succ_pos j.val)
        (fun d => (N d : ℝ)) rank (U j) (c j).val (p j)).mpr (hrank j)) hRank T hT
  have heq := allocatedJointBaseDensity_subtractConstant_centered B U basis hb o hR hσ
    S p hm center c hc
  have hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 := by
    simpa only [heq] using hnorm
  refine ⟨hN, hbases, hbox, hmass, hmargin, hnormalizer, ?_⟩
  intro law Sites _ _ root hroot hrootSum
  have h := hsite root hroot hrootSum
  have hlaw := allocatedOriginalPathLaw_subtractConstant_eq_centered B U basis hb o hR hσ S
    p hm N hN hW hτ hξ stride T hmass bases hbases center c hc hnorm.2.2.1
    hnormalizer.2.2.1
  rw [hlaw] at h
  exact h

theorem exists_allocated_centered_narrow_prescribed_marginal_pointwise (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedCenteredNarrowPrescribedMarginalPointwiseStatement m A := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_centered_narrow_prescribed_marginal_oneCenter m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  have hcenter := hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ
    hAP hLP hCP hVP p hp hm stride hs hsP hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP
    N hsize hrank hRank T hT
  obtain ⟨hN, hbases, hbox, hmass, hmargin, _, _⟩ := hcenter 0
  have hnormalizer (center) : |Z center - 1| ≤ Real.exp (-E) ∧
      Z center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z center ∧ (Z center)⁻¹ ≤ 2 := by
    obtain ⟨_, _, _, _, _, hn, _⟩ := hcenter center
    exact hn
  refine ⟨hN, hbases, hbox, hmass, hmargin, hnormalizer, ?_⟩
  intro law Sites _ _ root hroot hrootSum center
  obtain ⟨_, _, _, _, _, _, hsite⟩ := hcenter center
  exact hsite root hroot hrootSum

theorem exists_allocated_centered_narrow_prescribed_marginal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedCenteredNarrowPrescribedMarginalStatement m A := by
  obtain ⟨A, hA, hmarginal⟩ := exists_allocated_centered_narrow_prescribed_marginal_pointwise m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  obtain ⟨hN, hbases, hbox, hmass, hmargin, hnormalizer, hsite⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV
      Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ
      hAP hLP hCP hVP p hp hm stride hs hsP hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP
      N hsize hrank hRank T hT
  refine ⟨hN, hbases, hbox, hmass, hmargin, hnormalizer, ?_⟩
  intro law
  have hweight : ∀ z, Measurable (fun center => (law center).weight z) :=
    allocatedCenteredJointFiniteLaw_weight_measurable B U basis hb o hR hσ S p hm
      bases hbases stride T widths (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN)
      hmass (fun center => (hnormalizer center).2.2.1)
  refine ⟨hweight, ?_⟩
  intro Sites _ _ root hroot hrootSum
  exact centeredFiniteMarginal_siteLaw_excessMass_le_of_uniform μ law hweight _ _ _ _
    (hsite root hroot hrootSum)

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

noncomputable def allocatedExternalCandidateSides : LayerSamplerVariables G I n B → ℕ :=
  Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

noncomputable def allocatedExternalCandidateRootBudget : ℝ :=
  Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)

theorem allocatedExternalCandidateRootBudget_eq :
    allocatedExternalCandidateRootBudget B U b S =
      allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  simp only [allocatedExternalCandidateRootBudget, allocatedPhysicalRootBudget,
    Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add]

theorem allocatedExternalCandidateRootBudget_nonneg :
    0 ≤ allocatedExternalCandidateRootBudget B U b S :=
  mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

noncomputable def allocatedExternalCandidateWidths (N : X → ℕ) (τ ξ : ℝ) :
    Option (LayerSamplerVariables G I n B) × X → ℝ :=
  narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedExternalCandidateRootBudget B U b S) τ ξ N

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

noncomputable abbrev sides (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : LayerSamplerVariables G I n B → ℕ :=
  allocatedExternalCandidateSides B U b S

noncomputable abbrev widths (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Option (LayerSamplerVariables G I n B) × X → ℝ :=
  allocatedExternalCandidateWidths B U b S N τ ξ

noncomputable abbrev bases (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Finset (X → ℤ) :=
  trimmedIntegerBox N (spatialTrimMargin τ N)

abbrev Path (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Type _ :=
  trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 (allocatedExternalCandidateWidths B U b S N τ ξ) 1

abbrev Site (_A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
    N poly hm τ ξ stride cells center) : Type _ :=
  integerBox (allocatedExternalCandidateSides B U b S)

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

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
def physical (z : A.Path) (site : A.Site) : X → ℤ :=
  jointIntegerPhysicalSite site.val (z.1.val, z.2.val)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
@[simp] theorem physical_eq (z : A.Path) (site : A.Site) :
    A.physical z site = jointIntegerPhysicalSite site.val (z.1.val, z.2.val) := rfl

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

abbrev Site := (A 0).Site

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

noncomputable def law (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    FiniteProbabilityWeights A.Path :=
  (A center).law

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

end AllocatedExternalCandidateSamplerFamily

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

variable (N : X → ℕ) (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem AllocatedExternalCandidateSampler.law_zero_layers
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hm τ ξ stride cells center) :
    A.law = selectedJointReference (trimmedIntegerBox N (spatialTrimMargin τ N))
      A.bases_nonempty stride cells (allocatedExternalCandidateWidths B U b S N τ ξ)
      A.widths_pos A.smooth_mass_pos := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro z
  rw [AllocatedExternalCandidateSampler.law, selectedJointFiniteLaw,
    FiniteProbabilityWeights.reweightPositive_weight]
  simp only [allocatedCenteredJointDensity_zero_layers, FiniteProbabilityWeights.mean_const,
    mul_one, div_one]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedJointReference_collision {K I : Type*} [Fintype K] [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty) (r s : K → ℤ)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z) :
    (selectedJointReference A hA modulus T W hW hZ).mean
      (fun z => if jointIntegerPhysicalSite r (z.1.val,z.2.val) =
        jointIntegerPhysicalSite s (z.1.val,z.2.val) then 1 else 0) =
    (selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0) := by
  simp only [selectedJointReference, FiniteProbabilityWeights.mean_prod,
    jointIntegerPhysicalSite, add_right_inj]
  exact (FiniteProbabilityWeights.uniformFinset A hA).mean_const
    ((selectedResidueFiniteLaw modulus T W hW hZ).mean
      (fun z => if integerPhysicalSite r z.val = integerPhysicalSite s z.val then 1 else 0))

theorem selectedJointFiniteLaw_noninjectivity_le {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i))
    (D : (I → ℤ) → (Option K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (hlower : 1/2 ≤ selectedJointDensityMass A modulus T W D)
    {M : ℝ} (hM : 0 ≤ M) (hcap : ∀ a z, D a z ≤ M) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator (fun s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))) ≤
        2*M*((Fintype.card S : ℝ)^2*(2*(modulus i : ℝ)/L)) := by
  rw [selectedJointFiniteLaw]
  apply FiniteProbabilityWeights.reweightPositive_noninjectivity_le
    (selectedJointReference A hA modulus T W hW hZ)
    (fun z s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))
    (fun z => D z.1.val z.2.val) (fun z => hD0 z.1.val z.2.val)
    (by rw [selectedJointReference_densityMass]; exact hD) hM (fun z => hcap z.1.val z.2.val)
  · rwa [selectedJointReference_densityMass]
  · positivity
  · intro s t hst
    rw [selectedJointReference_collision]
    exact selectedResidue_distinct_collision_le (site s) (site t) (fun h => hst (hsite h)) i
      modulus hmodulus T hT W hW hZ hscale hL hwidth

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local irreducible] selectedJointReference selectedResidueFiniteLaw

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def unconditionedResidueSiteBound {K : Type*} [Fintype K] (P : K → ℕ) : ℝ :=
  ∑ k, (P k : ℝ)

noncomputable def unconditionedCollisionWidth {K : Type*} [Fintype K] [DecidableEq K]
    (P : K → ℕ) [∀ k, NeZero (P k)] (σ : ℝ) : ℝ :=
  32 * (Fintype.card (∀ k, ZMod (P k)) : ℝ) ^ 2 / σ

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

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

theorem zeroLayerVariables_card :
    Fintype.card (LayerSamplerVariables G I n B) = Fintype.card G :=
  Fintype.card_congr (zeroLayerVariablesEquiv B)

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

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def scalarNativeDimension (s : ℕ) : ℕ := (s + 1) * (s + 3)

theorem scalarNativeDimension_capacity {r s : ℕ} (hrs : r ≤ s) :
    (r + 1) * (r + 3) ≤ scalarNativeDimension s := by
  exact Nat.mul_le_mul (Nat.add_le_add_right hrs 1) (Nat.add_le_add_right hrs 3)

theorem scalarNativeDimension_selection_bound {r s : ℕ} (hrs : r ≤ s) :
    r + 1 ≤ scalarNativeDimension s := by
  exact (Nat.le_mul_of_pos_right (r + 1) (by omega : 0 < r + 3)).trans
    (scalarNativeDimension_capacity hrs)

def scalarNativeSelection {r s : ℕ} (hrs : r ≤ s) :
    Fin (r + 1) ↪ Fin (scalarNativeDimension s) where
  toFun a := ⟨a.val, a.isLt.trans_le (scalarNativeDimension_selection_bound hrs)⟩
  inj' := by
    intro a b hab
    exact Fin.ext (congrArg (fun z : Fin (scalarNativeDimension s) => z.val) hab)

@[simp] theorem scalarNativeSelection_val {r s : ℕ} (hrs : r ≤ s) (a : Fin (r + 1)) :
    (scalarNativeSelection hrs a).val = a.val := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

abbrev I (q : ℕ) (_ : Fin q) : Type := PEmpty
abbrev J (q : ℕ) (_ : Fin q) : Type := PEmpty
abbrev Q (q : ℕ) (_ : Fin q) : Type := PEmpty
abbrev n (q : ℕ) (_ : Fin q) : ℕ := 0

abbrev B (q : ℕ) (_ : LayerSamplerAxis (I q) (n q)) : Type := PEmpty

noncomputable def U (q : ℕ) (j : Fin q) : Submodule ℝ (J q j → ℝ) := ⊥

noncomputable def b (q : ℕ) (j : Fin q) :
    Basis (Fin (n q j)) ℝ (euclideanSubspace (U q j))ᗮ :=
  Basis.empty _

noncomputable def o (q : ℕ) (j : Fin q) :
    OrthonormalBasis (I q j) ℝ (euclideanSubspace (U q j)) :=
  (Basis.empty _).toOrthonormalBasis ⟨fun i => isEmptyElim i,
    fun i => isEmptyElim i⟩

noncomputable def bW (q : ℕ) (j : Fin q) :
    Basis (Q q j) ℤ
      (latticeSection (standardEuclideanLattice (J q j)) (euclideanSubspace (U q j))) :=
  Basis.empty _

instance lattice_full (q : ℕ) (j : Fin q) :
    IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J q j)) (euclideanSubspace (U q j))) := by
  constructor
  exact Subsingleton.elim _ _

noncomputable def poly (q : ℕ) (X : Type*) (j : Fin q) :
    VectorPolynomial X ℝ (J q j → ℝ) := 0

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedScaleCollisionBudget
namespace OAI

section

namespace Erdos3

theorem collision_error_of_exp_size_with_cap {F P C q ρ δ N : ℝ}
    (hC0 : 0 ≤ C) (hq0 : 0 ≤ q) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hC : C ≤ Real.exp (P*(P+5))) (hq : q ≤ Real.exp P)
    (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P)) (hδP : δ⁻¹ ≤ Real.exp P)
    (hN : Real.exp (F + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4) ≤ N) :
    2*Real.exp F*(C^2*(2*q/(ρ*N))) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hmain : (4*Real.exp F*C^2*q*(1/ρ))/δ ≤ N := by
    calc
      _ = 4*Real.exp F*C^2*q*(1/ρ)*δ⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4*Real.exp F*(Real.exp (P*(P+5)))^2*Real.exp P*
          Real.exp (spatialSamplingBudget P)*Real.exp P := by gcongr
      _ = Real.exp (F + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add, ← Real.exp_add]
        congr 1
        norm_num
        ring
      _ ≤ N := hN
  have hnum := (div_le_iff₀ hδ).mp hmain
  calc
    _ = (4*Real.exp F*C^2*q*(1/ρ))/N := by ring
    _ ≤ δ := (div_le_iff₀ hN0).mpr (by simpa only [mul_comm N δ] using hnum)

noncomputable def allocatedFixedScaleCollisionLog (m : ℕ) (P : ℝ) : ℝ :=
  VectorPolynomial.allocatedFourierLogBudget m P + 2*P*(P+5) +
    spatialSamplingBudget P + 2*P + 4

theorem exists_allocatedFixedScaleCollisionLog_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P → allocatedFixedScaleCollisionLog m P ≤ (P+A)^A := by
  obtain ⟨b, _, hb⟩ := VectorPolynomial.exists_allocatedFourierLogBudget_bound m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C b)^b +
    2*Polynomial.X*(Polynomial.X+5) + (4*Polynomial.X+128) + 2*Polynomial.X + 4
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget q
  refine ⟨A, hA, ?_⟩
  intro P hP
  have hpoly : (P+b)^b + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4 ≤ (P+A)^A := by
    simpa [q, spatialSamplingBudget, Polynomial.eval₂_pow] using hbound P hP
  apply le_trans _ hpoly
  unfold allocatedFixedScaleCollisionLog
  gcongr
  exact hb P hP

namespace BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedJointFiniteLaw_collision_small_with_cap {K X S : Type*}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    (A : Finset (X → ℤ)) (hA : A.Nonempty)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : X)
    {F P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hK : (Fintype.card K : ℝ) ≤ P) (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i) (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (T : Finset (ColumnResiduePattern (Option K) X modulus)) (hT : T.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (F + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4) ≤ N)
    (hwidth : ∀ k, ρ*N ≤ W (some k,i))
    (D : (X → ℤ) → (Option K × X → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (hlower : 1/2 ≤ selectedJointDensityMass A modulus T W D)
    (hcap : ∀ a z, D a z ≤ Real.exp F) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator (fun s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hcollision := selectedJointFiniteLaw_noninjectivity_le A hA site hsite i
    modulus hmodulus T hT W hW hZ hscale (mul_pos hρ hN0) hwidth D hD0 hD hlower
    (Real.exp_pos _).le hcap
  exact hcollision.trans (collision_error_of_exp_size_with_cap (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hρ hδ (integerSites_card_le_exp site hsite hP hK hbound)
    hmodP hρP hδP hN)

end BooleanCubeKernel

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredJointProductivity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

attribute [local irreducible] selectedJointFiniteLaw selectedJointReference selectedResidueFiniteLaw

theorem selectedJointFiniteLaw_integral_productivity
    {C B K I R Y : Type*} [MeasurableSpace C] [Fintype K] [Fintype I] [Fintype R]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (sites : FiniteProbabilityWeights R)
    (image : B → (K × I → ℤ) → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hmarginal : ∀ r,
      let F := fun c => (selectedJointFiniteLaw A hA modulus T W hW hZ (D c)
        (hD0 c) (hD c)).complexMean (fun z => (test (image z.1.val z.2.val r) : ℂ))
      Integrable F μ ∧ ‖(∫ c, F c ∂μ) - (parent : ℂ)‖ ≤ η)
    (hcollision : ∀ c,
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean
        (fun z => noninjectivityIndicator (image z.1.val z.2.val)) ≤ σ / 16) :
    σ / 4 ≤ ∫ c,
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mass
        (Finset.univ.filter (fun z => Function.Injective (image z.1.val z.2.val) ∧
          σ / 2 ≤ sites.mean (fun r => test (image z.1.val z.2.val r)))) ∂μ := by
  let law := fun c => selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)
  let sampledImage := fun (z : A × rectangularWeightIndices 0 W 1) r => image z.1.val z.2.val r
  have hi (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1) :
      Integrable (fun c => (law c).mean (fun z => f z.1.val z.2.val)) μ :=
    selectedJointFiniteLaw_realTest_integrable A hA modulus T W hW hZ μ D hDm hD0 hD f hf
  have hiBad : Integrable (fun c => (law c).mean
      (fun z => noninjectivityIndicator (sampledImage z))) μ := by
    apply hi (fun a z => noninjectivityIndicator (image a z))
    intro a z
    simp only [noninjectivityIndicator]
    split_ifs <;> norm_num
  have hiProd : Integrable (fun c => (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (sampledImage z) ∧ σ / 2 ≤
        sites.mean (fun r => test (sampledImage z r))))) μ := by
    simp only [← FiniteProbabilityWeights.mean_indicator, Finset.mem_filter,
      Finset.mem_univ, true_and]
    apply hi (fun a z => if Function.Injective (image a z) ∧
      σ / 2 ≤ sites.mean (fun r => test (image a z r)) then 1 else 0)
    intro a z
    split_ifs <;> norm_num
  have hbadmean : (∫ c, (law c).mean
      (fun z => noninjectivityIndicator (sampledImage z)) ∂μ) ≤ σ / 16 := by
    have h := integral_mono hiBad (integrable_const (σ / 16)) hcollision
    simpa only [integral_const, probReal_univ, one_smul] using h
  exact integral_productive_injective_mass_of_complex_marginals μ law sites sampledImage test
    hσ hη hparent htest (fun r => (hmarginal r).1) (fun r => (hmarginal r).2)
    hiBad hiProd hbadmean

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X Sites : Type*} [Fintype G] [Fintype X] [Fintype Sites] [Nonempty Sites]
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
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]

theorem allocatedCenteredJoint_productivity
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (widths : Option (LayerSamplerVariables G I n B) × X → ℝ)
    (hwidths : ∀ z, 0 < widths z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center))
    (site : Sites → LayerSamplerVariables G I n B → ℤ)
    (test : (X → ℤ) → ℝ) {gain error parent : ℝ}
    (hgain : 0 < gain) (herror : error ≤ gain / 8) (hparent : gain ≤ parent)
    (htest : ∀ y, test y ≤ 1) :
    let density := allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem
    let law := fun center => selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass
      (density center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) (hD center)
    (∀ q, Integrable (fun center => (law center).complexMean
      (fun z => (test (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) : ℂ))) μ ∧
      ‖(∫ center, (law center).complexMean
        (fun z => (test (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) : ℂ)) ∂μ) -
          (parent : ℂ)‖ ≤ error) →
    (∀ center, (law center).mean
      (fun z => noninjectivityIndicator (fun q => jointIntegerPhysicalSite (site q)
        (z.1.val,z.2.val))) ≤ gain / 16) →
    let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
      Function.Injective (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)) ∧
        gain / 2 ≤ 𝔼 q : Sites, test (jointIntegerPhysicalSite (site q) (z.1.val,z.2.val)))
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) | z.2 ∈ productive} ∧
      gain / 4 ≤ joint.real {z | z.2 ∈ productive} ∧
      (∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun s => c s.1))) ∧
        allocatedAffineDensity B U b hb o hR hσ S poly hmem c
          (fun k v => (jointIntegerFrame (z.2.1.val,z.2.2.val) k v : ℝ)) ≠ 0) := by
  intro density law hmarginal hcollision productive joint
  have hDm (a : X → ℤ) z : Measurable (fun center => density center a z) :=
    allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hmem a z
  have hD0 := allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem
  have hp := selectedJointFiniteLaw_integral_productivity bases hbases stride cells widths
    hwidths hmass μ density hDm hD0 hD (FiniteProbabilityWeights.uniform Sites)
    (fun a z q => jointIntegerPhysicalSite (site q) (a,z)) test
    hgain herror hparent htest hmarginal hcollision
  have hp' : gain / 4 ≤ ∫ center, (law center).mass productive ∂μ := by
    simpa only [FiniteProbabilityWeights.uniform_mean] using hp
  have hweight z : Measurable (fun center => (law center).weight z) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells widths hwidths hmass
      density hDm hD0 hD z
  apply centeredFiniteProbabilityMeasure_productive_family μ law hweight productive _ _ hp'
  intro center z hz
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  refine ⟨c, hc, ?_⟩
  have hd := (selectedJointFiniteLaw_support bases hbases stride cells widths hwidths hmass
    (density center) (hD0 center) (hD center) z hz).2
  change 0 < allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem
    center z.1.val z.2.val at hd
  rw [allocatedCenteredJointDensity_eq_affine B U b hb o hR hσ S poly hmem center c hc] at hd
  exact hd.ne'

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedRowsProjectedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {L H step : ℕ} (c : ℤ) (hL : 0 < L) (hH : 0 < H) (hstep : 0 < step)
variable (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})

theorem physicalRowsStandardEquiv_symm_sample {X : Type*}
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    (physicalRowsStandardEquiv U).symm (physicalCubeEuclideanSample U d p hm v) =
      physicalCubeRowSample U d (fun j => (Subtype.val : Row j → Finset (Fin q))) p hm v := by
  rw [← physicalRowsToStandard_sample U d p hp hm]
  rfl

theorem physicalCubePositiveTest_rows {X : Type*}
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (g : EuclideanJetLayers U Row → ℝ)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubePositiveTest U d p hm (fun z => g ((physicalRowsStandardEquiv U).symm z)) test v =
      physicalCubeSiteTest test v *
        (g (physicalCubeRowSample U d (fun j => (Subtype.val : Row j → Finset (Fin q))) p hm v) : ℂ) := by
  simp only [physicalCubePositiveTest, physicalRowsStandardEquiv_symm_sample U d p hp hm]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))


variable (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
variable (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ)
variable (hsubset : ∀ k : LayerSamplerVariables G I n B,
  integerProgressionSupport (c k) (step : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ)
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k : ℕ) : ℤ))


noncomputable def allocatedSlicedTupleValue
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) : ℂ :=
  (𝔼 base ∈ bases, ∑' z,
    ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
      (physicalCubeSiteTest (integerSelfSiteTest dim f)
        (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
        (baseDensity base z : ℂ))) /
    (selectedJointDensityMass bases stride cells widths baseDensity : ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "Z" => selectedJointDensityMass bases stride cells widths baseDensity

include hbases in
omit [DecidableEq G] [∀ index, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J index)) (euclideanSubspace (U index)))] in
theorem allocatedSlicedTupleValue_select_base
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin dim) (allocatedPrincipalSides B U b S)))
    (f : (X → ℤ) → ℂ) {κ : ℝ}
    (hsource : κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f)).re) :
    ∃ base ∈ bases,
      κ ≤ (law.complexMean (fun y => ∑' z,
        ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
          (physicalCubeSiteTest (integerSelfSiteTest dim f)
            (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
              (allocatedPhysicalCubeDirections B U b S x y) base z) * (baseDensity base z : ℂ))) /
        (Z : ℂ)).re := by
  let value := fun base => law.complexMean (fun y => ∑' z,
    ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
      (physicalCubeSiteTest (integerSelfSiteTest dim f)
        (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) * (baseDensity base z : ℂ))) / (Z : ℂ)
  have hmean : law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f) = 𝔼 base ∈ bases, value base := by
    simp only [allocatedSlicedTupleValue, FiniteProbabilityWeights.complexMean_div,
      FiniteProbabilityWeights.complexMean_finset_expect, Finset.expect_div, value]
  rw [hmean, ← FiniteProbabilityWeights.uniformFinset_complexMean bases hbases value] at hsource
  obtain ⟨base, _, hbase⟩ := (FiniteProbabilityWeights.uniformFinset bases hbases).exists_positive_weight_ge_complexMean_re
    (fun base => value base.val)
  exact ⟨base.val, base.property, hsource.trans hbase⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_sliced_projected_source (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (signal : (X → ℤ) → ℂ) (_hsignal : ∀ v, ‖signal v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y)),
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let Z := selectedJointDensityMass bases stride T widths (allocatedJointBaseDensity B U basis hb o hR hσ S X p hm)
    ∀ (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P) {κ : ℝ},
    κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S X p hm
      N hN _hW _hτ _hξ stride T hmass bases x y signal)).re →
    ∃ base ∈ bases,
      let projected := fun y => ∑' z,
        ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
          physicalCubePositiveTest U D p hm (f y) (integerSelfSiteTest q signal) (physicalCubeRootDifferences
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) base z)
      κ - Real.exp (-P) ≤ (law.complexMean projected / (Z : ℂ)).re := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_original_density_projection_law m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U _ basis R σ S x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P W hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm stride hs hsP τ ξ hτ hτP hξ hξ1 hξP
    N hN hsize rank hrank hRank signal hsignal T hT bases hbases D f density hproject widths hwidths hmass
    law Z hZ hZi κ hsource
  obtain ⟨base, hbase, hpositive⟩ := allocatedSlicedTupleValue_select_base B U basis hb o hR hσ S X p hm
    N hN hW hτ hξ stride T hmass bases hbases x law signal hsource
  have he := hprojection B U basis S (fun _ => 0) x hb o hR hσ C V hC hV hσ1
    Cinv hCinv hchart hsmall hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ hAP hCP hVP
    hperiod hX hdim p hp hm base stride hs hsP hτ hτP hξ hξ1 hξP N hsize hrank hRank
    (integerSelfSiteTest q signal) (integerSelfSiteTest_norm_le q signal hsignal) T hT D f hproject
    hZ hZi hwidths hmass law
  refine ⟨base, hbase, ?_⟩
  dsimp only at he ⊢
  have hdiff := (Complex.re_le_norm _).trans he
  rw [Complex.sub_re] at hdiff
  change κ ≤ _ at hpositive
  dsimp only [allocatedJointBaseDensity] at hpositive
  linarith only [hpositive, hdiff]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_sliced_rows_projected_source (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (signal : (X → ℤ) → ℂ) (_hsignal : ∀ v, ‖signal v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}) → ℝ),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (fun z => f y ((physicalRowsStandardEquiv U).symm z))),
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let Z := selectedJointDensityMass bases stride T widths (allocatedJointBaseDensity B U basis hb o hR hσ S X p hm)
    ∀ (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P) {κ : ℝ},
    κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S X p hm
      N hN _hW _hτ _hξ stride T hmass bases x y signal)).re →
    ∃ base ∈ bases,
      let projected := fun y => ∑' z,
        ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
          (physicalCubeSiteTest (integerSelfSiteTest q signal) (physicalCubeRootDifferences
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (f y (physicalCubeRowSample U D (fun j =>
            (Subtype.val : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} → Finset (Fin q))) p hm
            (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
              (allocatedPhysicalCubeDirections B U basis S x y) base z)) : ℂ))
      κ - Real.exp (-P) ≤ (law.complexMean projected / (Z : ℂ)).re := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_sliced_projected_source.{uX} m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U _ basis R σ S x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P W hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm stride hs hsP τ ξ hτ hτP hξ hξ1 hξP
    N hN hsize rank hrank hRank signal hsignal T hT bases hbases D f density hproject widths hwidths hmass
    law Z hZ hZi κ hsource
  obtain ⟨base, hbase, he⟩ := hprojection B U basis S x hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall
    hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ hAP hCP hVP hperiod hX hdim p hp hm
    stride hs hsP hτ hτP hξ hξ1 hξP N hN hsize hrank hRank signal hsignal T hT bases hbases D
    (fun y z => f y ((physicalRowsStandardEquiv U).symm z)) hproject hwidths hmass law hZ hZi hsource
  refine ⟨base, hbase, ?_⟩
  simpa only [physicalCubePositiveTest_rows U D p hp hm] using he

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedCenteredConditionalPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {X : Type*} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (c : ∀ j, U j) (a : X → ℤ)

noncomputable def allocatedCenteredConditionalPolynomial (j : Fin m) :
    VectorPolynomial X ℝ (J j → ℝ) :=
  translate (fun i => (a i : ℝ)) (subtractConstant (c j).val (poly j))

omit [∀ j, Fintype (J j)] in
include hmem in
theorem allocatedCenteredConditionalPolynomial_mem (j : Fin m) (e : X →₀ ℕ) :
    coefficients (allocatedCenteredConditionalPolynomial U poly c a j) e ∈ U j :=
  coefficients_translate_mem (U j) _ _
    (coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) e

omit [∀ j, Fintype (J j)] in
theorem allocatedCenteredConditionalPolynomial_degree
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) (j : Fin m) :
    DegreeLE (1 : X → ℕ) (j.val + 1) (allocatedCenteredConditionalPolynomial U poly c a j) :=
  degreeLE_translate _ (fun _ => by norm_num) _ _ ((hp j).subtractConstant _)

theorem allocatedCenteredConditionalPolynomial_rank
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (H : X → ℝ) (Rrank : ℝ) (j : Fin m) :
    HasLayerSamplingRank (j.val + 1) H Rrank (U j)
      (allocatedCenteredConditionalPolynomial U poly c a j) ↔
      HasLayerSamplingRank (j.val + 1) H Rrank (U j) (poly j) := by
  unfold allocatedCenteredConditionalPolynomial
  rw [hasLayerSamplingRank_translate_iff _ _ _ _ _ _ ((hp j).subtractConstant _),
    hasLayerSamplingRank_subtractConstant_iff (by omega)]

variable {G : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ x, Fintype (B x)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

omit [Fintype X] in
theorem allocatedCenteredConditionalPolynomial_density
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCoefficientDensity B U b hb o hR hσ S
      (affineSampleCoefficientTorus U (allocatedCenteredConditionalPolynomial U poly c a)
        (allocatedCenteredConditionalPolynomial_mem U poly hmem c a)
        (fun k x => (z (k,x) : ℝ))) =
      allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z := by
  exact congrFun (congrFun
    (allocatedJointBaseDensity_subtractConstant_centered B U b hb o hR hσ S poly hmem center c hc) a) z

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CubeMixtureVertex
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_large_vertex_of_cube_mixture
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (s : ℕ) {I : Type*} [Fintype I] (p : ℝ)
    (c : I → ℂ) (F : I → (Fin (s + 1) → Bool) → A → ℂ)
    (hF : ∀ i ω x, x ∈ Q → ‖F i ω x‖ ≤ 1)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p)
    (z : ℂ) (hz : Real.exp (-p) ≤ z.re)
    (herr : ‖z - ∑ i, c i * normalizedSupportedCubeSum (s + 1) Q (F i)‖ ≤ Real.exp (-p) / 2)
    (ω : Fin (s + 1) → Bool) :
    ∃ i, Real.exp (-(2 * p + 2)) ≤ finiteSupportGowersNorm (s + 1) Q (F i ω) := by
  have hlarge : Real.exp (-p) / 2 ≤
      ‖∑ i, c i * normalizedSupportedCubeSum (s + 1) Q (F i)‖ := by
    have h := norm_sub_norm_le z (∑ i, c i * normalizedSupportedCubeSum (s + 1) Q (F i))
    have hreal := Complex.re_le_norm z
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c
    (fun i => normalizedSupportedCubeSum (s + 1) Q (F i))
    (half_pos (Real.exp_pos _)) (Real.exp_pos p) hc hlarge
  have he : Real.exp (-(2 * p)) / 2 = (Real.exp (-p) / 2) / Real.exp p := by
    rw [div_right_comm, ← Real.exp_sub]
    congr 2
    ring
  have hsmall : Real.exp (-(2 * p + 2)) ≤ Real.exp (-(2 * p)) / 2 :=
    (Real.exp_le_exp.mpr (by linarith : -(2 * p + 2) ≤ -(2 * p) - 1)).trans
      (exp_sub_one_le_half_exp (-(2 * p)))
  rw [he] at hsmall
  exact ⟨i, (hsmall.trans hi).trans (normalizedSupportedCubeSum_le_vertex hφ s (F i) (hF i) ω)⟩

theorem exists_site_twist_of_degree_zero_cube_mixture
    {X : Type*} [Fintype X] [DecidableEq X] (N : X → ℕ) [∀ x, NeZero (N x)]
    {I : Type*} [Fintype I] (p : ℝ) (f : (X → ℤ) → ℂ) (c : I → ℂ)
    (twist : I → Finset (Fin 1) → (X → ℤ) → ℂ)
    (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (ht : ∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp p) (z : ℂ) (hz : Real.exp (-p) ≤ z.re)
    (herr : ‖z - ∑ i, c i *
      (𝔼 cube : SupportedCube 1 (integerBox N : Set (X → ℤ)),
        let u := (BooleanCubeKernel.physicalCubeParametersEquiv X 1).symm cube.val
        ∏ ω, conjugationPower ω.card (f (BooleanCubeKernel.physicalCubeVertexValue u ω)) *
          twist i ω (BooleanCubeKernel.physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2) :
    ∃ i, Real.exp (-(2 * p + 2)) ≤ ‖𝔼 x ∈ integerBox N, f x * twist i ∅ x‖ := by
  let F : I → (Fin 1 → Bool) → (X → ℤ) → ℂ := fun i ω x =>
    f x * conjugationPower (booleanWeight ω)
      (twist i (BooleanCubeKernel.vertexFinsetEquiv 1 ω) x)
  have hF : ∀ i ω x, x ∈ integerBox N → ‖F i ω x‖ ≤ 1 := by
    intro i ω x hx
    dsimp only [F]
    rw [norm_mul, conjugationPower_norm]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x hx)).trans (ht i _ x hx)
  simp_rw [BooleanCubeKernel.physical_twisted_cube_mean] at herr
  obtain ⟨i, hi⟩ := exists_large_vertex_of_cube_mixture (boxReduction_reflectsPairSums N)
    0 p c F hF hc z hz herr (fun _ => false)
  rw [finiteSupportGowersNorm_degree_one_of_embedding
    (boxReduction_reflectsPairSums N) (integerBox_nonempty N)] at hi
  refine ⟨i, ?_⟩
  simpa only [F, booleanWeight, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero,
    conjugationPower, RingHom.id_apply, BooleanCubeKernel.vertexFinsetEquiv,
    Equiv.coe_fn_mk, Finset.filter_false] using hi

end Erdos3

end

end OAI

end


