-- Prove2me | Definitions.Def_OAIE3v2B137
-- name    : OAIE3v2B137
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:14:18.371277+00:00
-- url     : https://prove2.me/theorems/de8cdbe8-6ec7-4f7a-a4a3-3f530012951f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 139 of 311
-- statement:
--   Definitions bundle 139 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B117`, `OAIE3v2B119`, `OAIE3v2B120`, `OAIE3v2B121`, `OAIE3v2B122`, `OAIE3v2B123`, `OAIE3v2B124` of this split.
--
--   Modules: `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/CurrentLayerPreservation.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/ProjectedNativeCoefficient.lean`, `Estimates/RationalCentralCircle.lean`, `Estimates/RealSymbolRepresentativeSplitting.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Estimates/SymbolFastMembership.lean`, `Estimates/VectorRealSubstitutionBound.lean`, `Fourier/PivotAnnihilatorFrequencyCode.lean`, `Geometry/PreparedDeterminingCoordinates.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Geometry/RelativePatchFiniteCoordinateReduction.lean`, `Lattices/AlgebraicMajorWeightedAffineTopPullback.lean`, `Lattices/ImageLatticeSubgroup.lean`, `Lattices/RealSymbolAffine.lean`, `Linear/ActualMarkedSlowKernelCells.lean`, `Linear/FixedKernelPatchFunction.lean`, `Linear/HomogeneousGradedProjectionBounds.lean`, `Linear/OrdinarySymbolBasisDimension.lean`, `Linear/RankPreparationProjectedAxisBudget.lean`, `Linear/RankPreparationSizes.lean`, `Linear/RationalTaggedSpanProjection.lean`, `Linear/WeightedTranslationBasisHeight.lean`, `Nilpotent/IdealInvariantNiltestBudget.lean`, `Nilpotent/NiltestProbabilityProjection.lean`, `Polynomial/ControlledLinearPolynomialRestriction.lean`, `Polynomial/MarkedPolynomialSectionSlow.lean`, `Polynomial/PolynomialBasisTransport.lean`, `Polynomial/PolynomialPatchShearOrbit.lean`, `Polynomial/PolynomialPatchShearOrbitConverse.lean`, `Polynomial/PolynomialShearObservableNet.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Polynomial/RealAdaptedPolynomialGroup.lean`, `Polynomial/SchmidtShortDualVector.lean`, `Polynomial/WeightedLinearPolynomialRestriction.lean`, `Polynomial/WeightedPolynomialPotentialExtension.lean`, `Probability/RelativeFullSliceLaw.lean`, `Sampling/ForecastPreparedScaleBudget.lean`, `Sampling/SamplingRankProjectedContainment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B117
import Definitions.Def_OAIE3v2B119
import Definitions.Def_OAIE3v2B120
import Definitions.Def_OAIE3v2B121
import Definitions.Def_OAIE3v2B122
import Definitions.Def_OAIE3v2B123
import Definitions.Def_OAIE3v2B124

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem topProjection_pure (w : σ → ℕ) (d : ℕ) (P : MvPolynomial σ ℚ) :
    topProjection w d ⟨0, P⟩ = P.coeff 0 • (constantDirection : PolynomialTranslationLie σ) := by
  apply PolynomialTranslationLie.ext
  · funext i
    simp [constantDirection]
  · simp [constantDirection, MvPolynomial.C_eq_smul_one]

theorem pure_constant_zero_of_top_frequency (w : σ → ℕ) (d : ℕ)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (P : MvPolynomial σ ℚ) (hP : (⟨0, P⟩ : PolynomialTranslationLie σ) ∈ U) :
    P.coeff 0 = 0 := by
  have h := hkill _ (hgraded _ hP) (topProjection_mem_top w d ⟨0, P⟩)
  rw [topProjection_pure, map_smul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_right hfrequency

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem polynomialLinearRestriction_monomial_homogeneous [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (a : σ →₀ ℕ) (c : ℚ) :
    (polynomialLinearRestriction A (monomial a c)).IsWeightedHomogeneous v (Finsupp.weight w a) := by
  rw [monomial_eq]
  simp only [map_mul, polynomialLinearRestriction_C, Finsupp.prod, map_prod,
    map_pow, polynomialLinearRestriction_X]
  have hprod := IsWeightedHomogeneous.prod a.support
    (fun i => linearCoordinatePolynomial A i ^ a i) (fun i => a i * w i)
    (fun i _ => by simpa only [nsmul_eq_mul, Nat.cast_id] using
      (linearCoordinatePolynomial_isWeightedHomogeneous A v w hA i).pow (a i))
  simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id] using hprod.C_mul c

theorem polynomialLinearRestriction_isWeightedHomogeneous [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P.IsWeightedHomogeneous w n) :
    (polynomialLinearRestriction A P).IsWeightedHomogeneous v n := by
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedHomogeneousSubmodule ℚ v n).sum_mem
  intro a ha
  have h := polynomialLinearRestriction_monomial_homogeneous A v w hA a (P.coeff a)
  change (polynomialLinearRestriction A (monomial a (P.coeff a))).IsWeightedHomogeneous v n
  simpa only [hP (MvPolynomial.mem_support_iff.mp ha)] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialPotentialExtension
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem polynomialLinearRestriction_leftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ))
    (hBA : ∀ x, B (A x) = x) (V : MvPolynomial τ ℚ) :
    polynomialLinearRestriction A (polynomialLinearRestriction B V) = V := by
  apply MvPolynomial.funext
  intro x
  rw [eval_polynomialLinearRestriction, eval_polynomialLinearRestriction, hBA]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ImageLatticeSubgroup
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

namespace NilpotentLieFiltration

theorem exists_image_lattice_cover (F : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (Δ : Subgroup F.Group)
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΔin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Δ)
    (hΔout : bchSubgroupCoordinates f Δ ⊆ denominatorGrid m)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H) :
    ∃ (B : ℕ) (Λ : Subgroup F.Group),
      0 < B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card κ ^ 3) *
        (m * (l * rationalKernelHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ))) ∧
      Λ ≤ Δ ∧ (Λ.subgroupOf Δ).Characteristic ∧ (Λ.subgroupOf Δ).Normal ∧
      (Λ.subgroupOf Δ).FiniteIndex ∧ Λ.relIndex Δ ≤ (m * B) ^ Fintype.card κ ∧
      scaledIntegerGrid ((m * B) * m) ⊆ bchSubgroupCoordinates f Λ ∧
      bchSubgroupCoordinates f Λ ⊆ denominatorGrid ((m * B) * m) ∧
      Λ.map realificationHom ⊓
        (realificationMap (hnil := hL) (hM := F.lowerCentralSeries_eq_bot) φ).range ≤
        (Γ.map realificationHom).map
          (realificationMap (hnil := hL) (hM := F.lowerCentralSeries_eq_bot) φ) := by
  obtain ⟨B, Λ₀, hB, _, hBb, _, hgrid, hlift⟩ := exists_image_lattice_subgroup e f φ Γ Δ
    l m H hl hm hH hΓ hΔin hentries hc
  obtain ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, hindex, hin, hout⟩ :=
    F.exists_sharp_normal_cover f Δ Λ₀ m B hm hB hΔin hΔout hgrid.ge
  refine ⟨B, Λ, hB, hBb, hΛ, hchar, hnormal, hfinite, hindex, hin, hout, ?_⟩
  exact le_trans (inf_le_inf_right _ (Subgroup.map_mono hΛ₀)) hlift

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeTruncation_quotient (j : ℕ) (x : ℝ ⊗[ℚ] L) :
    lieQuotientMap (F.realification.layerIdeal j) (basisBelowProjection (b.baseChange ℝ) w j x) =
      lieQuotientMap (F.realification.layerIdeal j) x := by
  have h := (lieQuotientMap_eq_zero (F.realification.layerIdeal j) _).mpr
    (F.sub_realGradeTruncation_mem b w hlayers j x)
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

include hlayers in
theorem truncateRealGrades_quotient (j : ℕ) (g : F.realification.Group) :
    NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (F.truncateRealGrades b w j g) =
      NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) g := by
  apply NilpotentLieBCHGroup.ext
  exact F.realGradeTruncation_quotient b w hlayers j g.coord

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (v : σ → ℕ)

theorem truncateRealSymbol_quotient (j : ℕ) (g : F.RealPolynomialSymbolGroup v) :
    NilpotentLieBCHGroup.quotientHom
        ((F.polynomialSymbolFiltration v).realification.layerIdeal j)
        (F.truncateRealSymbol b w hlayers v j g) =
      NilpotentLieBCHGroup.quotientHom ((F.polynomialSymbolFiltration v).realification.layerIdeal j) g :=
  (F.polynomialSymbolFiltration v).truncateRealGrades_quotient
    (F.polynomialSymbolBasis b w hlayers v) (fun z => w z.val.2)
    (F.polynomialSymbolFiltration_layer b w hlayers v) j g

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realificationLieSubalgebra_iInf {η L : Type*} [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] (U : η → LieSubalgebra ℚ L) :
    realificationLieSubalgebra (⨅ j, U j) = ⨅ j, realificationLieSubalgebra (U j) := by
  have hsub : (⨅ j, U j).toSubmodule = ⨅ j, (U j).toSubmodule := by
    ext x
    change x ∈ (⨅ j, U j) ↔ x ∈ (⨅ j, (U j).toSubmodule)
    rw [Submodule.mem_iInf]
    exact lieSubalgebra_mem_iInf U x
  ext x
  change x ∈ (⨅ j, U j).toSubmodule.baseChange ℝ ↔ _
  rw [hsub, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, lieSubalgebra_mem_iInf]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolRepresentativeSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

variable (w : σ → ℕ)

theorem realSymbolRepresentative_eval₂ (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realSymbolRepresentative b ω hlayers w x) =
      (F.gradedBasisSplitting b ω hlayers).toLinearMap.baseChange ℝ
        (eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) := by
  rw [F.realSymbolRepresentative_eq_map, VectorPolynomial.eval₂_map]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) {w : σ → ℕ}

theorem realQuotientPolynomialOrbit_surjective :
    Function.Surjective (F.realQuotientPolynomialOrbit I hI (w := w)) := by
  intro q
  let φ := realLieHomToRat (realificationLieHom (lieQuotientMap I))
  have hf : ∀ j, ∀ x ∈ F.realification.layer j,
      φ x ∈ (F.quotientLie I hI).realification.layer j := by
    intro j x hx
    exact F.realQuotientStep_mem_layer I hI hx
  have hsurj : ∀ j, ∀ y ∈ (F.quotientLie I hI).realification.layer j,
      ∃ x ∈ F.realification.layer j, φ x = y := by
    intro j y hy
    change y ∈ ((F.layer j).map (lieQuotientMap I).toLinearMap).baseChange ℝ at hy
    rw [realification_map] at hy
    exact hy
  obtain ⟨p, hp⟩ := F.realification.filteredPolynomialMap_surjective
    (F.quotientLie I hI).realification φ hf w hsurj
    ⟨q.log, ((F.quotientLie I hI).realification.mem_adaptedSubmodule w q.log).mpr q.adapted⟩
  let g : F.realification.PolynomialOrbit w :=
    polynomialOrbitOfLog p.val ((F.realification.mem_adaptedSubmodule w p.val).mp p.property)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.map φ.toLinearMap p.val = q.log
  exact congrArg Subtype.val hp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*}

variable [Fintype σ] {w : σ → ℕ} [Fintype (PolynomialShearIndex w)]

theorem polynomialShearLattice_inner_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    scaledIntegerGrid s.factorial ⊆
      bchSubgroupCoordinates (polynomialShearBasis w) (polynomialShearLattice w s hw) := by
  intro x hx
  let D := (polynomialShearBasis (R := ℚ) w).equivFun.symm x
  have hD : (polynomialShearBasis (R := ℚ) w).equivFun D ∈ scaledIntegerGrid s.factorial := by
    simpa only [D, LinearEquiv.apply_symm_apply] using hx
  have hI := polynomialShear_scaledGrid_normalize s.factorial (Nat.factorial_pos s) D hD
  have he := polynomialShear_factorial_exp_integral s hw ((s.factorial : ℚ)⁻¹ • D) hI
  have hc : (s.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero s)
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

theorem polynomialShearOrderedBasis_inner_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    scaledIntegerGrid s.factorial ⊆
      bchSubgroupCoordinates (polynomialShearOrderedBasis w) (polynomialShearLattice w s hw) :=
  bchSubgroup_inner_grid_reindex (polynomialShearBasis w) (polynomialShearIndexOrder w) _
    (polynomialShearLattice_inner_grid s hw)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)

theorem polynomialShearRealPointAction_rational
    (g : (polynomialShearFiltration w s hw).Group) (x : σ → ℚ) :
    polynomialShearRealPointAction w s hw (NilpotentLieBCHGroup.realificationHom g)
        (fun i => (x i : ℝ)) =
      fun i => (weightedLoweringPointAction w (polynomialShearBCHEquiv w s hw g) x i : ℝ) := by
  funext i
  have h :
      (polynomialShearRealAutEquiv w s hw (NilpotentLieBCHGroup.realificationHom g)).val.symm (X i) =
      MvPolynomial.map (algebraMap ℚ ℝ) ((polynomialShearBCHEquiv w s hw g).val.symm (X i)) := by
    simpa only [map_inv, MvPolynomial.map_X, Subgroup.coe_inv, AlgEquiv.aut_inv] using
      polynomialShearRealAutEquiv_rational w s hw g⁻¹ (X i)
  change aeval (fun j => (x j : ℝ))
      ((polynomialShearRealAutEquiv w s hw (NilpotentLieBCHGroup.realificationHom g)).val.symm (X i)) =
    (aeval x ((polynomialShearBCHEquiv w s hw g).val.symm (X i)) : ℝ)
  rw [h]
  exact polynomial_map_aeval (algebraMap ℚ ℝ) x _

theorem polynomialShearRealLattice_integer_permutation
    (γ : (polynomialShearFiltration w s hw).realification.Group)
    (hγ : γ ∈ polynomialShearRealLattice s hw) :
    ∃ e : Equiv.Perm (σ → ℤ), ∀ b,
      polynomialShearRealPointAction w s hw γ (fun i => (b i : ℝ)) =
        fun i => (e b i : ℝ) := by
  obtain ⟨g, hg, rfl⟩ := hγ
  let e := integerWeightedLoweringPointEquiv (polynomialShearBCHEquiv w s hw g) hg
  refine ⟨e, fun b => ?_⟩
  have h := congrArg (fun x : σ → ℚ => fun i => (x i : ℝ))
    (integerWeightedLoweringPointEquiv_cast (polynomialShearBCHEquiv w s hw g) hg b)
  have hr := polynomialShearRealPointAction_rational w s hw g (fun i => (b i : ℚ))
  simpa only [Rat.cast_intCast] using hr.trans h.symm

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)

theorem polynomialShearOrbitSum_lattice (K : (σ → ℝ) → ℝ)
    (g γ : (polynomialShearFiltration w s hw).realification.Group)
    (hγ : γ ∈ polynomialShearRealLattice s hw) :
    polynomialShearOrbitSum w s hw K (g * γ) = polynomialShearOrbitSum w s hw K g := by
  obtain ⟨e, he⟩ := polynomialShearRealLattice_integer_permutation w s hw γ hγ
  unfold polynomialShearOrbitSum
  simp_rw [map_mul, Equiv.Perm.mul_apply, he]
  exact e.tsum_eq (fun b : σ → ℤ => K (polynomialShearRealPointAction w s hw g (fun i => (b i : ℝ))))

noncomputable def polynomialShearQuotientSum (K : (σ → ℝ) → ℝ) :
    ((polynomialShearFiltration w s hw).realification.Group ⧸ polynomialShearRealLattice s hw) → ℝ :=
  Quotient.lift (polynomialShearOrbitSum w s hw K) (fun g h hgh => by
    have hi := polynomialShearOrbitSum_lattice w s hw K g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def shearObservable (A : PolynomialPatch σ s d) :
    ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) → ℝ :=
  polynomialShearQuotientSum A.weight s A.weight_le A.shearKernel

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {τ : Type*} [Fintype τ] (w : τ → ℕ)

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {v : Fin d → ℕ}

theorem shearGroupLift_coordinate (A : PolynomialSlots σ d v)
    (s : ℕ) (hv : ∀ i, v i ≤ s) (t : σ → ℝ) (a : PolynomialShearIndex v) :
    ((polynomialShearBasis (R := ℚ) v).baseChange ℝ).repr (A.shearGroupLift s hv t).coord a =
      -(polynomialShearBasis (R := ℝ) v).repr (polynomialShearLog (A.loweringAt t)) a := by
  change ((polynomialShearBasis (R := ℚ) v).baseChange ℝ).repr
    (((polynomialShearRealAutEquiv v s hv).symm (A.loweringAt t)⁻¹).coord) a = _
  rw [map_inv, NilpotentLieBCHGroup.coord_inv, map_neg, Finsupp.neg_apply]
  rw [← polynomialShearRealificationEquiv_repr, polynomialShearRealAutEquiv_symm_coord]

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem shearCoordinatePolynomial_eval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) (a : PolynomialShearIndex w) :
    aeval t (A.shearCoordinatePolynomial a) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr (A.shearGroupLift s hw t).coord a := by
  rw [shearGroupLift_coordinate, polynomialShearBasis_repr]
  unfold shearCoordinatePolynomial
  rw [map_neg, polynomialSlotCoefficient_eval]
  change -(patchParameterSpecialization t (A.symbolicLogSlot a.1)).coeff a.2.val = _
  rw [symbolicLogSlot_specialization]

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial Module VectorPolynomial
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ} [Fintype (PolynomialShearIndex w)]

theorem shearLogPolynomial_adapted (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.Adapted (fun _ : σ => 1) A.shearLogPolynomial := by
  rw [NilpotentLieFiltration.adapted_iff_coefficients]
  intro α
  apply ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
    (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
    (fun j => polynomialShearLayer_span w j) _ _).mpr
  intro a ha
  change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
    (VectorPolynomial.coefficients A.shearLogPolynomial α) = 0
  have hc := congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α)
    (A.shearLogPolynomial_coordinate a)
  rw [VectorPolynomial.coeff_coordinate] at hc
  apply hc.trans
  by_contra h
  have hb : Finsupp.weight (fun _ : σ => 1) α ≤ polynomialShearDeficit w a :=
    A.shearCoordinatePolynomial_degree a (MvPolynomial.mem_support_iff.mpr h)
  exact ha hb

theorem shearLogPolynomial_eval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) :
    VectorPolynomial.eval₂ t A.shearLogPolynomial = (A.shearGroupLift s hw t).coord := by
  apply ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr.injective
  ext a
  change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
    (VectorPolynomial.eval₂ t A.shearLogPolynomial) = _
  rw [VectorPolynomial.coordinate_eval₂, shearLogPolynomial_coordinate]
  exact A.shearCoordinatePolynomial_eval s hw t a

noncomputable def shearPolynomialOrbit (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1) :=
  NilpotentLieFiltration.polynomialOrbitOfLog A.shearLogPolynomial (A.shearLogPolynomial_adapted s hw)

theorem shearPolynomialOrbit_realEval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) :
    (polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
      (fun _ : σ => 1) t (A.shearPolynomialOrbit s hw) = A.shearGroupLift s hw t := by
  apply NilpotentLieBCHGroup.ext
  exact A.shearLogPolynomial_eval s hw t

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def shearOrbit (A : PolynomialPatch σ s d) :
    (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : σ => 1) := by
  letI := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.form.shearPolynomialOrbit s A.weight_le

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem realPolynomialMass_weightedComponent_le (w : σ → ℕ) (n : ℕ) (P : MvPolynomial σ ℝ) :
    realPolynomialMass (weightedHomogeneousComponent w n P) ≤ realPolynomialMass P := by
  classical
  unfold realPolynomialMass
  rw [support_weightedHomogeneousComponent]
  calc
    _ = ∑ α ∈ P.support.filter (fun α => Finsupp.weight w α = n), |P.coeff α| := by
      apply Finset.sum_congr rfl
      intro α hα
      rw [coeff_weightedHomogeneousComponent, if_pos (Finset.mem_filter.mp hα).2]
    _ ≤ ∑ α ∈ P.support, |P.coeff α| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _)

namespace PolynomialSlots

variable {d : ℕ} {w : Fin d → ℕ}

theorem topPart_specializeCenter_mass_le (A : PolynomialSlots σ d w) (i : Fin d) :
    realPolynomialMass (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) ≤
      realPolynomialMass (A.center i) := by
  apply (realPolynomialMass_rename_le _ _).trans
  have hs : A.topPart.specializeCenter 0 i =
      aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial (Fin i.val) ℝ)) X) (A.topPart.center i) := by
    simp only [specializeCenter, Pi.zero_apply, map_zero]
  rw [hs]
  exact (realPolynomialMass_zeroParameterEval_le _).trans
    (realPolynomialMass_weightedComponent_le _ _ _)

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearObservable_mem_Icc (A : PolynomialPatch σ s d)
    (x : (polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) : A.shearObservable x ∈ Set.Icc (0 : ℝ) 1 := by
  refine Quotient.inductionOn x ?_
  intro g
  change polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel g ∈ Set.Icc (0 : ℝ) 1
  rw [A.shearOrbitSum_eq_patchValue]
  exact TriangularSlots.patchValue_mem_Icc _ A.kernel

theorem abs_shearObservable_le_one (A : PolynomialPatch σ s d)
    (x : (polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) : |A.shearObservable x| ≤ 1 := by
  rw [abs_of_nonneg (A.shearObservable_mem_Icc x).1]
  exact (A.shearObservable_mem_Icc x).2

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualEquiv_X_mass (A : PolynomialSlots σ d w)
    {M : ℝ} (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) (i : Fin d) :
    realPolynomialMass (A.topResidualEquiv (X i)) ≤ 1 + M := by
  rw [A.topResidualEquiv_X]
  exact (realPolynomialMass_sub_le _ _).trans
    (by simpa only [realPolynomialMass_X] using
      add_le_add (le_refl (1 : ℝ)) ((A.topPart_specializeCenter_mass_le i).trans (hA i)))

theorem topResidualEquiv_inverse_mass (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    {n : ℕ} {P : MvPolynomial (Fin d) ℝ} (hP : P ∈ weightedSupportLE w n) :
    realPolynomialMass (A.topResidualEquiv.symm P) ≤ realPolynomialMass P * (1 + M) ^ (n * d) := by
  apply triangularPolynomialEquiv_inverse_mass w hpos _ A.topResidualShift_degree hM _ hP
  intro i
  rw [map_neg, realPolynomialMass_neg]
  exact (A.topPart_specializeCenter_mass_le i).trans (hA i)

theorem topResidualEquiv_inverse_X_mass (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) (i : Fin d) :
    realPolynomialMass (A.topResidualEquiv.symm (X i)) ≤ (1 + M) ^ (s * d) := by
  have h := A.topResidualEquiv_inverse_mass hpos hM hA (weightedSupportLE_X w i)
  rw [realPolynomialMass_X, one_mul] at h
  exact h.trans (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right d (hw i)))

theorem topResidualEquiv_inverse_eval_bound (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    (y : Fin d → ℝ) (hy : ∀ i, |y i| ≤ 1) (i : Fin d) :
    |aeval y (A.topResidualEquiv.symm (X i))| ≤ (1 + M) ^ (s * d) :=
  (mvPolynomial_eval_abs_le_sum_coeff (A.topResidualEquiv.symm (X i)) y hy).trans
    (A.topResidualEquiv_inverse_X_mass hpos s hw hM hA i)

theorem topResidualPoint_preimage_bound (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    (x : Fin d → ℝ) (hx : ∀ i, |aeval x (A.topResidualEquiv (X i))| ≤ 1) (i : Fin d) :
    |x i| ≤ (1 + M) ^ (s * d) := by
  have hinv : aeval (polynomialSubstitutionPoint A.topResidualEquiv.toAlgHom x)
      (A.topResidualEquiv.symm (X i)) = x i := by
    rw [polynomialSubstitutionPoint_aeval]
    change aeval x (A.topResidualEquiv (A.topResidualEquiv.symm (X i))) = x i
    rw [AlgEquiv.apply_symm_apply, aeval_X]
  rw [← hinv]
  exact A.topResidualEquiv_inverse_eval_bound hpos s hw hM hA _ hx i

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearKernel_support_bound (A : PolynomialPatch σ s d)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M)
    (x : Fin d → ℝ) (hx : A.shearKernel x ≠ 0) (i : Fin d) :
    |x i| ≤ (1 + M) ^ (s * d) := by
  apply A.form.topResidualPoint_preimage_bound A.weight_pos s A.weight_le hM hA x _ i
  intro j
  have h := A.kernel.support _ hx j
  exact h.trans (by norm_num)

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {X Y : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem shearPatchValue_dist (A : PolynomialSlots X d w) (B : PolynomialSlots Y d w)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hs : ∀ i, w i ≤ s)
    (Φ : PatchKernel d) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hsmall : ε < 1 / 4)
    (hA : ∀ i, realPolynomialMass (A.center i) ≤ M)
    (hB : ∀ i, realPolynomialMass (B.center i) ≤ M)
    (hclose : ∀ x : Fin d → ℝ, (∀ i, |x i| ≤ (1 + M) ^ (s * d)) →
      dist (polynomialSubstitutionPoint A.topResidualEquiv.toAlgHom x)
        (polynomialSubstitutionPoint B.topResidualEquiv.toAlgHom x) ≤ ε)
    (e : WeightedLoweringAut w ℝ) :
    dist ((A.shearTransformedSlots hw e).patchValue Φ)
      ((B.shearTransformedSlots hw e).patchValue Φ) ≤ Φ.lip * ε := by
  apply TriangularSlots.patchValue_dist_of_residuals_close _ _ Φ hε hsmall
  intro b hb
  let x := polynomialSubstitutionPoint e.val.toAlgHom (fun j => (b j : ℝ))
  have hx : ∀ i, |x i| ≤ (1 + M) ^ (s * d) := by
    rcases hb with hb | hb
    · apply A.topResidualPoint_preimage_bound hpos s hs hM hA x
      intro i
      have hi := Φ.support _ hb i
      rw [shearTransformedSlots_residual] at hi
      exact hi.trans (by norm_num)
    · apply B.topResidualPoint_preimage_bound hpos s hs hM hB x
      intro i
      have hi := Φ.support _ hb i
      rw [shearTransformedSlots_residual] at hi
      exact hi.trans (by norm_num)
  rw [shearTransformedSlots_residual, shearTransformedSlots_residual]
  exact hclose x hx

end Erdos3.PolynomialSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

theorem polynomialShearRealPointAction_displacement (s : ℕ)
    (hpos : ∀ i, 1 ≤ w i) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group) (B : ℝ≥0) (hB : 1 ≤ B)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hg : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w g.coord) a| ≤ δ)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) :
    dist (polynomialShearRealPointAction w s hw g x) x ≤
      (polynomialShearDisplacementBound s (Fintype.card σ) B : ℝ) * δ := by
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) hδ)).mpr
  intro i
  rw [Real.dist_eq, polynomialShearRealPointAction_eq_exp]
  have hgn (a) : |(polynomialShearBasis (R := ℝ) w).repr (-(polynomialShearRealificationEquiv w g.coord)) a| ≤ δ := by
    simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hg a
  have h := polynomialShearExp_X_displacement (-(polynomialShearRealificationEquiv w g.coord))
    hpos hw hδ hδone (show (1 : ℝ) ≤ B from hB) hgn x hx i
  convert h using 1
  simp only [polynomialShearDisplacementBound, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one,
    Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  ring

variable [Fintype (PolynomialShearIndex w)]

theorem polynomialShearRealification_ordered_repr
    (D : ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) (a : PolynomialShearIndex w) :
    (polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w D) a =
      ((polynomialShearOrderedBasis w).baseChange ℝ).repr D (polynomialShearIndexOrder w a) := by
  rw [polynomialShearRealificationEquiv_repr]
  have he : (polynomialShearOrderedBasis w).baseChange ℝ =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).reindex (polynomialShearIndexOrder w) := by
    ext j
    simp only [polynomialShearOrderedBasis, Basis.baseChange_apply, Basis.reindex_apply]
  rw [he, Basis.repr_reindex_apply, Equiv.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]

theorem polynomialShearRealPointAction_near_one (s : ℕ)
    (hpos : ∀ i, 1 ≤ w i) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group)
    (B : ℝ≥0) (hB : 1 ≤ B) (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) :
    letI := rightMetricSpace
      (hnil := (polynomialShearFiltration w s hw).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis w).baseChange ℝ)
    let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex w)) (2 * s + 1) 1
    (C : ℝ) * dist 1 g < 1 →
      dist (polynomialShearRealPointAction w s hw g x) x ≤
        (polynomialShearDisplacementBound s (Fintype.card σ) B * C : ℝ≥0) * dist 1 g := by
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration w s hw).realification.lowerCentralSeries_eq_bot)
    ((polynomialShearOrderedBasis w).baseChange ℝ)
  let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex w)) (2 * s + 1) 1
  dsimp only
  intro hnear
  have hc := polynomialShearOrderedBasis_structure_height w s (fun i => lt_of_lt_of_le Nat.zero_lt_one (hpos i)) hw
  have hlog : ‖basisHomeomorph ((polynomialShearOrderedBasis w).baseChange ℝ) g‖ ≤
      (C : ℝ) * dist 1 g := by
    have hr := norm_coordinates_le_of_near_one
      (hnil := (polynomialShearFiltration w s hw).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis w).baseChange ℝ)
      (lieStructureConstants (polynomialShearOrderedBasis w))
      (fun i j k => (realLieBasis_structure (polynomialShearOrderedBasis w) i j k).symm)
      hc 1 le_rfl g
    simp only [Fintype.card_fin, NNReal.coe_one] at hr
    exact hr hnear
  have hg (a : PolynomialShearIndex w) :
      |(polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w g.coord) a| ≤
        (C : ℝ) * dist 1 g := by
    rw [polynomialShearRealification_ordered_repr]
    have h := (norm_le_pi_norm
      (basisHomeomorph ((polynomialShearOrderedBasis w).baseChange ℝ) g)
      (polynomialShearIndexOrder w a)).trans hlog
    simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs] using h
  have h := polynomialShearRealPointAction_displacement w s hpos hw g B hB
    (mul_nonneg C.coe_nonneg dist_nonneg) hnear.le hg x hx
  simpa only [NNReal.coe_mul, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem topResidualPoint_lipschitzOn_box (A : PolynomialSlots σ d w)
    (hpos : ∀ i, 1 ≤ w i) (s : ℕ) (hw : ∀ i, w i ≤ s) (M B : ℝ≥0)
    (hB : 1 ≤ B) (hA : ∀ i, realPolynomialMass (A.center i) ≤ M) :
    LipschitzOnWith ((1 + M) * d * s * B ^ (s * (d + 1)))
      (polynomialSubstitutionPoint A.topResidualEquiv.toAlgHom)
      {x | ∀ i, |x i| ≤ B} := by
  have hmass (i : Fin d) : realPolynomialMass (A.topResidualEquiv (X i)) ≤ (1 + M : ℝ≥0) := by
    exact A.topResidualEquiv_X_mass hA i
  have hdegree (i : Fin d) : (A.topResidualEquiv (X i)).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport w hpos
      (A.topResidualEquiv_degree (weightedSupportLE_X w i))).trans (hw i)
  change LipschitzOnWith ((1 + M) * d * s * B ^ (s * (d + 1)))
    (fun x : Fin d → ℝ => fun i => aeval x (A.topResidualEquiv (X i))) _
  simpa only [Fintype.card_fin] using
    lipschitzOn_realPolynomialVector_mass_box (fun i : Fin d => A.topResidualEquiv (X i))
      (1 + M) B hB hmass hdegree

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearKernel_lipschitzOn_box (A : PolynomialPatch σ s d) (M B : ℝ≥0)
    (hB : 1 ≤ B) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    LipschitzOnWith (A.kernel.lip * ((1 + M) * d * s * B ^ (s * (d + 1)))) A.shearKernel
      {x | ∀ i, |x i| ≤ B} := by
  exact A.kernel.lipschitz.comp_lipschitzOnWith
    (A.form.topResidualPoint_lipschitzOn_box A.weight_pos s A.weight_le M B hB hA)

theorem shearKernel_lipschitz (A : PolynomialPatch σ s d) (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    LipschitzWith (A.shearKernelLipBound M) A.shearKernel := by
  unfold shearKernelLipBound
  apply lipschitzWith_of_unit_range_support_box A.shearKernel ((1 + M) ^ (s * d))
    (A.kernel.lip * ((1 + M) * d * s * ((1 + M) ^ (s * d) + 1) ^ (s * (d + 1))))
  · intro x
    exact A.kernel.nonneg _
  · intro x
    exact A.kernel.le_one _
  · intro x hx i
    simpa only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] using
      A.shearKernel_support_bound M.coe_nonneg hA x hx i
  · simpa only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] using
      A.shearKernel_lipschitzOn_box M ((1 + M) ^ (s * d) + 1) (le_add_of_nonneg_left zero_le) hA

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
  [Fintype (PolynomialShearIndex A.weight)]

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem shearSummand_lipschitz (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) (b : Fin d → ℝ) :
    letI := rightMetricSpace
      (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
    LipschitzWith (A.shearObservableLipBound M)
      (fun g => A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g b)) := by
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
    ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
  let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex A.weight)) (2 * s + 1) 1
  let R : ℝ≥0 := (1 + M) ^ (s * d)
  let T := polynomialShearDisplacementBound s d R
  let K := A.shearKernelLipBound M
  let ρ := polynomialShearRealPointAction A.weight s A.weight_le
  change LipschitzWith (max C (K * T * C)) (fun g => A.shearKernel (ρ g b))
  apply lipschitzWith_of_unit_range_near_nonzero _ C (K * T * C)
    (fun _ => A.kernel.nonneg _) (fun _ => A.kernel.le_one _)
  intro g h hg hnear
  let z := h * g⁻¹
  have hdist : dist 1 z = dist g h := by
    simpa only [mul_inv_cancel] using
      (rightMetricSpace_isometry_mul_right ((polynomialShearOrderedBasis A.weight).baseChange ℝ) g⁻¹).dist_eq g h
  have hR : 1 ≤ R := one_le_pow₀ (le_add_of_nonneg_right zero_le)
  have hx (i : Fin d) : |ρ g b i| ≤ R := by
    simpa only [R, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one] using
      A.shearKernel_support_bound M.coe_nonneg hA (ρ g b) hg i
  have hmove := polynomialShearRealPointAction_near_one A.weight s A.weight_pos A.weight_le
    z R hR (ρ g b) hx (by simpa only [hdist] using hnear)
  have hz : ρ z (ρ g b) = ρ h b := by
    simp only [z, map_mul, map_inv, Equiv.Perm.mul_apply]
    exact congrArg (ρ h) ((ρ g).symm_apply_apply b)
  change dist (ρ z (ρ g b)) (ρ g b) ≤
    (polynomialShearDisplacementBound s (Fintype.card (Fin d)) R * C : ℝ≥0) * dist 1 z at hmove
  rw [hz, hdist, Fintype.card_fin, dist_comm (ρ h b) (ρ g b)] at hmove
  have hkernel := (A.shearKernel_lipschitz M hA).dist_le_mul (ρ g b) (ρ h b)
  rw [Real.dist_eq] at hkernel
  apply hkernel.trans
  simpa only [NNReal.coe_mul, mul_assoc] using mul_le_mul_of_nonneg_left hmove K.coe_nonneg

theorem shearOrbitSum_lipschitz (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    letI := rightMetricSpace
      (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
      ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
    LipschitzWith (A.shearObservableLipBound M)
      (polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel) := by
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot)
    ((polynomialShearOrderedBasis A.weight).baseChange ℝ)
  exact separated_tsum_lipschitz
    (fun (b : Fin d → ℤ) g => A.shearKernel
      (polynomialShearRealPointAction A.weight s A.weight_le g (fun i => (b i : ℝ))))
    (fun b => A.shearSummand_lipschitz M hA (fun i => (b i : ℝ)))
    (fun _ _ => A.kernel.nonneg _)
    (fun g _ _ hb hc => A.shearSummand_unique g hb hc)

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AlgebraicMajorWeightedAffineTopPullback
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U : Type*}

theorem residueAffinePolynomial_homogeneousComponent_eval
    (q h : ℕ) (r : U → ℤ) (P : MvPolynomial U ℝ)
    (hP : P.totalDegree ≤ h) (v : U → ℝ) :
    eval v (homogeneousComponent h (residueAffinePolynomial q r P)) =
      eval (fun i => (q : ℝ) * v i) (homogeneousComponent h P) := by
  have hdil : C ((q : ℝ) ^ h) * homogeneousComponent h P =
      aeval (fun i => C (q : ℝ) * X i) (homogeneousComponent h P) := by
    classical
    ext α
    rw [coeff_C_mul, coeff_polynomial_dilation, coeff_homogeneousComponent]
    by_cases hα : α.degree = h
    · simp only [hα, ite_true]
    · simp only [hα, ite_false, mul_zero]
  rw [residueAffinePolynomial_homogeneousComponent q h r P hP, hdil]
  change (aeval v) (aeval (fun i => C (q : ℝ) * X i)
    (homogeneousComponent h P)) = _
  rw [comp_aeval_apply]
  simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    aeval_eq_eval]

theorem residueAffinePolynomial_weightedHomogeneousComponent_eval
    (q h : ℕ) (r : U → ℤ) (P : MvPolynomial U ℝ)
    (hP : P.totalDegree ≤ h) (v : U → ℝ) :
    eval v (weightedHomogeneousComponent (fun _ : U => 1) h
      (residueAffinePolynomial q r P)) =
      eval (fun i => (q : ℝ) * v i)
        (weightedHomogeneousComponent (fun _ : U => 1) h P) :=
  residueAffinePolynomial_homogeneousComponent_eval q h r P hP v

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial

variable {U B : Type*}

theorem algebraic_major_affine_top_dilation_identity
    (K : Submodule ℝ (B → ℝ)) (w : B → ℕ) (n : ℕ)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) n)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ)
    (q : ℕ) (r : U → ℤ) (T : U → ℝ)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim v b)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n
          (jointResidueAffinePolynomial q r D)) =
      eval (Sum.elim (fun i => v i / T i)
        (fun j => b j - eval v
          (majorTranslationTopCoordinates w (fun j => residueAffinePolynomial q r (A j)) j))) S +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (v : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim (fun i => (q : ℝ) * v i) b)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n D) =
    eval (Sum.elim (fun i => v i / T i)
      (fun j => b j - eval (fun i => (q : ℝ) * v i) (majorTranslationTopCoordinates w A j))) S +
    eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R := by
  have h := hsource v b hb
  rw [jointResidueAffinePolynomial_weightedHomogeneousComponent_eval w q n r D hD] at h
  simp only [majorTranslationTopCoordinates,
    residueAffinePolynomial_weightedHomogeneousComponent_eval q _ r _ (hA _)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem algebraic_major_weighted_affine_top_pullback_decomposition
    (K : Submodule ℝ (B → ℝ)) (w : B → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ)
    (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) n)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ)
    (q : ℕ) (hq : 0 < q) (r : U → ℤ)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim v b)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n
          (jointResidueAffinePolynomial q r D)) =
      eval (Sum.elim (fun i => v i / T i)
        (fun j => b j - eval v
          (majorTranslationTopCoordinates w (fun j => residueAffinePolynomial q r (A j)) j))) S +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (c C : ℝ) (hc : 1 ≤ c) (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i)
    (d l : ℕ)
    (hS : S ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hR : R ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hSmass : realPolynomialMass S ≤ C)
    (hRgrid : (fun α => R.coeff α) ∈ denominatorGrid l) :
    ∃ (S' : MvPolynomial (U ⊕ B) ℝ) (R' : MvPolynomial (U ⊕ B) ℚ),
      S' = majorSlowDilationPullback q H T S ∧
      R' = jointRationalPolynomialDilation q R ∧
      (∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b)
          (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) n D) =
          eval (Sum.elim (fun i => u i / H i)
            (fun j => b j - eval u (majorTranslationTopCoordinates w A j))) S' +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R') ∧
      realPolynomialMass S' ≤ c^d * C ∧
      S' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      R' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      S'.totalDegree ≤ d ∧ R'.totalDegree ≤ d ∧
      (fun α => R'.coeff α) ∈ denominatorGrid (q^d*l) :=
  algebraic_major_weighted_dilation_pullback_decomposition w hw K _ _ S R q hq H T hH hT
    (algebraic_major_affine_top_dilation_identity K w n D hD A hA S R q r T hsource)
    c C hc hHT d l hS hR hSmass hRgrid

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

open VectorPolynomial

theorem integerRowPolynomial_homogeneous_approximation_of_decomposition
    {σ J : Type*} [Fintype J] (h : ℕ) (T : σ → ℝ) (R S b : ℝ)
    (a : J → ℤ) (A E P Q : VectorPolynomial σ ℝ (J → ℝ))
    (q : ℕ) (hq : 0 < q) (hqR : (q : ℝ) ≤ R)
    (hT : ∀ i, 0 < T i) (hb : 0 ≤ b)
    (ha : ∀ j, |(a j : ℝ)| ≤ b)
    (hcost : (Fintype.card J : ℝ) * b * S ≤ R)
    (hA : A = E + P + Q)
    (hE : ∀ α j, |coefficients E α j| ≤ S / monomialScale T α)
    (hP : ∀ α, integerRowLinear a (coefficients P α) = 0)
    (hQ : ∀ α, coefficients Q α ∈ realDenominatorGrid q) :
    PolynomialRationalApproximation T R
      (MvPolynomial.homogeneousComponent h (integerRowPolynomial a A)) := by
  classical
  have hgrid := integerRowPolynomial_coefficientGrid a Q q hQ
  obtain ⟨Z, hZ⟩ := (realPolynomialCoefficientGrid_iff q _).mp hgrid
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hZcoeff (α : σ →₀ ℕ) :
      ((Z.coeff α : ℤ) : ℝ) / q = (integerRowPolynomial a Q).coeff α := by
    have hz := congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α) hZ
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hz
    change ((Z.coeff α : ℤ) : ℝ) = (q : ℝ) * (integerRowPolynomial a Q).coeff α at hz
    rw [hz, mul_div_cancel_left₀ _ hq0]
  have hR : 0 ≤ R := (Nat.cast_nonneg q).trans hqR
  refine ⟨q, hq, hqR, MvPolynomial.homogeneousComponent h Z, ?_⟩
  intro α
  by_cases hα : α.degree = h
  · simp only [MvPolynomial.coeff_homogeneousComponent, if_pos hα, hZcoeff]
    have heq : (integerRowPolynomial a A).coeff α - (integerRowPolynomial a Q).coeff α =
        ∑ j, (a j : ℝ) * coefficients E α j := by
      rw [hA]
      simp only [integerRowPolynomial_coeff, map_add, Finsupp.add_apply, Pi.add_apply,
        mul_add, Finset.sum_add_distrib]
      have hz := hP α
      rw [integerRowLinear_apply] at hz
      rw [hz]
      ring
    rw [heq]
    calc
      _ ≤ ∑ j, |(a j : ℝ) * coefficients E α j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : J, b * (S / monomialScale T α) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (ha j) (hE α j) (abs_nonneg _) hb
      _ = ((Fintype.card J : ℝ) * b * S) / monomialScale T α := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ ≤ R / monomialScale T α :=
        div_le_div_of_nonneg_right hcost (monomialScale_pos T hT α).le
  · simp only [MvPolynomial.coeff_homogeneousComponent, if_neg hα, Int.cast_zero,
      zero_div, sub_zero, abs_zero]
    exact div_nonneg hR (monomialScale_pos T hT α).le

theorem samplingRank_le_real_column_span_of_decomposition
    {σ J L : Type*} [Fintype J] [Fintype L]
    (B : Matrix J L ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ j i, RationalHeightLE (B j i) H)
    (h : ℕ) (T : σ → ℝ) (R S : ℝ) (W : Submodule ℝ (J → ℝ))
    (A E P Q : VectorPolynomial σ ℝ (J → ℝ))
    (q : ℕ) (hq : 0 < q) (hT : ∀ i, 0 < T i)
    (hrank : HasLayerSamplingRank h T R W A)
    (hA : A = E + P + Q)
    (hE : ∀ α j, |coefficients E α j| ≤ S / monomialScale T α)
    (hP : ∀ α, coefficients P α ∈ Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ))))
    (hQ : ∀ α, coefficients Q α ∈ realDenominatorGrid q)
    (hqR : (q : ℝ) ≤ R)
    (hrowR : (realSpanIntegerRowBound (Fintype.card L) (Fintype.card J) H : ℝ) ≤ R)
    (hcost : (Fintype.card J : ℝ) *
      (realSpanIntegerRowBound (Fintype.card L) (Fintype.card J) H : ℝ) * S ≤ R) :
    W ≤ Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ))) := by
  classical
  obtain ⟨C, hC, hker⟩ := exists_real_span_integer_defining_matrix B hH hB
  intro x hx
  apply (real_column_span_mem_iff B x).mpr
  rw [← hker]
  change (fun i j => (C i j : ℝ)) *ᵥ x = 0
  ext i
  by_contra hix
  have hkill (α : σ →₀ ℕ) : integerRowLinear (C i) (coefficients P α) = 0 := by
    have hp : coefficients P α ∈ LinearMap.ker
        (Matrix.mulVecLin (fun i j => (C i j : ℝ))) := by
      rw [hker]
      exact (real_column_span_mem_iff B _).mp (hP α)
    have hh := congrFun hp i
    change (∑ j, (C i j : ℝ) * coefficients P α j) = 0 at hh
    simpa only [integerRowLinear_apply] using hh
  apply hrank (C i) (fun j => (hC i j).trans hrowR) ⟨⟨x, hx⟩, hix⟩
  exact integerRowPolynomial_homogeneous_approximation_of_decomposition h T R S
    (realSpanIntegerRowBound (Fintype.card L) (Fintype.card J) H : ℝ)
    (C i) A E P Q q hq hqR hT (Nat.cast_nonneg _) (hC i) hcost hA hE hkill hQ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeFullSliceLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
namespace ResidueBoxSlice
variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q s d : ℕ}

theorem fullSliceLaw_mean (S : ResidueBoxSlice N q) (hlen : ∀ i, 0 < S.length i)
    (f : integerBox N → ℝ) :
    (S.fullSliceLaw hlen).mean f = 𝔼 u, f (S.fullSlicePointInIntegerBox u) := by
  let : ∀ i, Nonempty (Fin (S.length i)) := fun i => ⟨⟨0,hlen i⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_mean _ _

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def cell (k : Option I → Fin d.cellCount) (t : Option I → Fin d.cellLength) : Option I → ℝ :=
  residueCellPosition d.length d.cellLength d.cellCount d.modulus d.residue k t

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NormalizedScalarCubeSource

theorem baseLaw_coefficient_mean (s : NormalizedScalarCubeSource Empty) (f : ℤ → ℝ) :
    s.baseLaw.mean (fun x => f (x none : ℤ)) = 𝔼 z : s.CoefficientDomain, f z := by
  unfold baseLaw
  rw [scalarCubeResidueWeights_mean]
  exact Fintype.expect_equiv (emptyScalarCubeResidueEquiv s.length s.modulus s.residue) _ _ (fun _ => rfl)

theorem coefficientDensity_mean_one (s : NormalizedScalarCubeSource Empty) :
    (𝔼 z : s.CoefficientDomain, s.coefficientDensity z) = 1 := by
  have he := s.baseLaw_coefficient_mean (fun z => s.weight (fun _ => (z : ℝ) / s.length))
  have hn : s.baseLaw.mean (fun x => s.weight (fun _ => (x none : ℝ) / s.length)) = 1 := by
    have h := s.normalized
    simpa only [s.weight_empty_coordinate, baseLaw] using h
  exact he.symm.trans hn

noncomputable def coefficientWeights (s : NormalizedScalarCubeSource Empty) :
    FiniteProbabilityWeights s.CoefficientDomain :=
  FiniteProbabilityWeights.ofDensity s.coefficientDensity s.coefficientDensity_nonneg s.coefficientDensity_mean_one

end NormalizedScalarCubeSource

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem UnitIntervalValued.norm_le_one {T : D.Niltest w} (hT : T.UnitIntervalValued) (x : D.Space) :
    ‖T.observable x‖ ≤ 1 := by
  have heq : ((T.observable x).re : ℂ) = T.observable x := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (hT x).1.symm
  rw [← heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hT x).2.1]
  exact (hT x).2.2

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CurrentLayerPreservation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in

theorem real_corrected_middle_mem_next_layer
    (U : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U) (k : ℕ)
    (Y A D : F.realification.Group)
    (hY : Y.coord ∈ U ⊔ (F.realLayer k).toSubmodule)
    (hA : A.coord ∈ F.realification.layer k)
    (hD : D.coord ∈ F.realification.layer k)
    (hgrade : basisGradeProjection (b.baseChange ℝ) w k Y.coord -
      basisGradeProjection (b.baseChange ℝ) w k A.coord -
      basisGradeProjection (b.baseChange ℝ) w k D.coord ∈ U) :
    (A⁻¹ * Y * D⁻¹).coord ∈ U ⊔ (F.realLayer (k + 1)).toSubmodule := by
  let P := A⁻¹ * Y * D⁻¹
  have hAn : -A.coord ∈ F.realification.layer k := (F.realification.layer k).neg_mem hA
  have hDn : -D.coord ∈ F.realification.layer k := (F.realification.layer k).neg_mem hD
  have hrem : P.coord - (-A.coord + Y.coord + -D.coord) ∈
      F.realification.layer (k + 1) :=
    F.realification.bch_triple_sub_sum_mem_next_layer k _ _ _ hAn hDn
  have hsum : -A.coord + Y.coord + -D.coord ∈ U ⊔ (F.realLayer k).toSubmodule :=
    (U ⊔ (F.realLayer k).toSubmodule).add_mem
      ((U ⊔ (F.realLayer k).toSubmodule).add_mem (Submodule.mem_sup_right hAn) hY)
      (Submodule.mem_sup_right hDn)
  have hP : P.coord ∈ U ⊔ (F.realLayer k).toSubmodule := by
    have hsmall : P.coord - (-A.coord + Y.coord + -D.coord) ∈ (F.realLayer k).toSubmodule :=
      F.realification.antitone (Nat.le_succ k) hrem
    have h := (U ⊔ (F.realLayer k).toSubmodule).add_mem (Submodule.mem_sup_right hsmall) hsum
    simpa only [sub_add_cancel] using h
  have hPg : basisGradeProjection (b.baseChange ℝ) w k P.coord ∈ U := by
    have h := F.realGradeProjection_bch_triple b w hlayers k (-A.coord) Y.coord (-D.coord) hAn hDn
    change basisGradeProjection (b.baseChange ℝ) w k P.coord = _ at h
    rw [h, map_neg, map_neg]
    convert hgrade using 1
    abel
  rw [F.realLayer_eq_span_basis b k _ (hlayers k)] at hP
  change P.coord ∈ U ⊔ (F.realLayer (k + 1)).toSubmodule
  rw [F.realLayer_eq_span_basis b (k + 1) _ (hlayers (k + 1))]
  exact hU.mem_sup_higher_of_grade (b.baseChange ℝ) w U k P.coord hP hPg

theorem real_quotient_mem_subgroup_iff (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (k : ℕ) (g : F.realification.Group) :
    NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) g ∈
      (NilpotentLieBCHGroup.realLieSubgroup
        (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot)
          (F.realification.layerIdeal k)) ↔
      g.coord ∈ U.toSubmodule ⊔ (F.realLayer k).toSubmodule := by
  rw [NilpotentLieBCHGroup.realLieSubgroup,
    NilpotentLieBCHGroup.quotient_mem_map_subgroup_iff]
  change g.coord ∈ U.toSubmodule.restrictScalars ℚ ⊔
    (F.realLayer k).toSubmodule.restrictScalars ℚ ↔ _
  rw [← Submodule.restrictScalars_sup]
  rfl

include hlayers in

theorem simultaneous_real_grade_correction {η : Type*}
    (U : η → LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : ∀ i, BasisGradedSubmodule (b.baseChange ℝ) w (U i).toSubmodule)
    (k : ℕ) (X E₀ R₀ A D : F.realification.Group)
    (hY : ∀ i, (E₀⁻¹ * X * R₀⁻¹).coord ∈ (U i).toSubmodule ⊔ (F.realLayer k).toSubmodule)
    (hA : A.coord ∈ F.realification.layer k)
    (hD : D.coord ∈ F.realification.layer k)
    (hgrade : ∀ i, basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * X * R₀⁻¹).coord -
      basisGradeProjection (b.baseChange ℝ) w k A.coord -
      basisGradeProjection (b.baseChange ℝ) w k D.coord ∈ U i) :
    (E₀ * A) * (A⁻¹ * (E₀⁻¹ * X * R₀⁻¹) * D⁻¹) * (D * R₀) = X ∧
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (E₀ * A) =
        NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E₀ ∧
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (D * R₀) =
        NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R₀ ∧
      ∀ i, (A⁻¹ * (E₀⁻¹ * X * R₀⁻¹) * D⁻¹).coord ∈
        (U i).toSubmodule ⊔ (F.realLayer (k + 1)).toSubmodule := by
  have hqA : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) A = 1 := by
    apply NilpotentLieBCHGroup.ext
    exact (lieQuotientMap_eq_zero (F.realification.layerIdeal k) _).mpr hA
  have hqD : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) D = 1 := by
    apply NilpotentLieBCHGroup.ext
    exact (lieQuotientMap_eq_zero (F.realification.layerIdeal k) _).mpr hD
  refine ⟨by group, ?_, ?_, ?_⟩
  · rw [map_mul, hqA, mul_one]
  · rw [map_mul, hqD, one_mul]
  · intro i
    exact F.real_corrected_middle_mem_next_layer b w hlayers (U i).toSubmodule (hU i) k
      (E₀⁻¹ * X * R₀⁻¹) A D (hY i) hA hD (hgrade i)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedNativeCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realSquarePairHom :
    F.squareFiltration.realification.Group →* (pi (fun _ : Bool => F)).realification.Group :=
  realificationMap (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
    (hM := (pi (fun _ : Bool => F)).lowerCentralSeries_eq_bot) F.squarePairMap

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalCentralCircle
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)

theorem rationalDirectionPeriod_pos (v : L) : 0 < D.rationalDirectionPeriod v :=
  Nat.mul_pos D.grid_pos (arrayDenominator_pos _)

theorem periodicRealDirection_mem_top (v : L) (hv : v ∈ D.filtration.layer s) :
    (⟨D.periodicRealDirection v⟩ : D.RealGroup) ∈ D.filtration.realification.subgroup s := by
  change (1 : ℝ) ⊗ₜ[ℚ] ((D.rationalDirectionPeriod v : ℚ) • v) ∈
    (D.filtration.layer s).baseChange ℝ
  exact Submodule.tmul_mem_baseChange_of_mem 1 ((D.filtration.layer s).smul_mem _ hv)

theorem periodicRealDirection_span {ι : Type*} (v : ι → L) :
    Submodule.span ℝ (Set.range (fun i => D.periodicRealDirection (v i))) =
      Submodule.span ℝ (Set.range (fun i => rationalLieInclusion (v i))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change D.periodicRealDirection (v i) ∈ _
    rw [D.periodicRealDirection_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := Submodule.smul_mem
      (Submodule.span ℝ (Set.range (fun i => D.periodicRealDirection (v i))))
      (D.rationalDirectionPeriod (v i) : ℝ)⁻¹ (Submodule.subset_span ⟨i, rfl⟩)
    change (D.rationalDirectionPeriod (v i) : ℝ)⁻¹ • D.periodicRealDirection (v i) ∈ _ at h
    rw [D.periodicRealDirection_eq, smul_smul, inv_mul_cancel₀, one_smul] at h
    · exact h
    · exact_mod_cast (D.rationalDirectionPeriod_pos (v i)).ne'

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.HomogeneousGradedProjectionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

 theorem homogeneousGradedProjection_span {J : Type*}
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (fun j => F.homogeneousGradedProjection G c ν hG hc φ hφ (v j))) =
      (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)).toSubmodule := by
  change _ = W.toSubmodule.map (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap
  rw [← hv, Submodule.map_span]
  congr 1
  exact Set.range_comp _ _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolFastMembership
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

theorem realPolynomialSymbolDilation_mul (w : σ → ℕ) (a b : ℚ) (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolDilation w (a * b) x =
      F.realPolynomialSymbolDilation w a (F.realPolynomialSymbolDilation w b x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simp only [F.realPolynomialSymbolDilation_tmul, F.polynomialSymbolDilation_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3
open scoped Matrix

theorem exists_rationalTaggedSpanProjection
    {J : Type*} [Fintype J] {r : ℕ} (g : Fin r → J → ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hr : (r : ℝ) ≤ p) (hg : ∀ a j, rationalLogHeight (g a j) ≤ p) :
    ∃ d : ℕ, d ≤ Fintype.card J ∧
      ∃ Q : (J → ℝ) →ₗ[ℝ] (Fin d → ℝ),
        LinearMap.ker Q = Submodule.span ℝ (Set.range (fun a j => (g a j : ℝ))) ∧
        (∀ x i, |Q x i| ≤ Real.exp ((p + 2) ^ 9) * ‖x‖) ∧
        ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
          ∀ x : J → ℤ, ∃ z : Fin d → ℤ,
            ∀ i, (z i : ℝ) = (D : ℝ) * Q (fun j => (x j : ℝ)) i := by
  classical
  have hheight : ∀ j a, RationalHeightLE (g a j) ⌊Real.exp p⌋₊ := by
    intro j a
    obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff (g a j) p).mp (hg a j)
    exact ⟨Nat.le_floor hn, Nat.le_floor hd⟩
  obtain ⟨d, hd, M, S, hker, hMS, hM, hS⟩ :=
    exists_quotient_presentation_exp_height (fun j a => g a j)
      ((Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hp)) hheight
      hp hJ (by simpa using hr) (Nat.floor_le (Real.exp_nonneg p))
  have hdp : (Fintype.card (Fin d) : ℝ) ≤ p := by
    simpa using (Nat.cast_le.mpr hd).trans hJ
  let Q : (J → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    Matrix.mulVecLin (fun i j => (M i j : ℝ))
  have hentry : ∀ i j, |(M i j : ℝ)| ≤ Real.exp ((p + 2) ^ 7) :=
    fun i j => (rational_abs_real_le_numerator (M i j)).trans (hM i j).1
  have hbound : ∀ x i, |Q x i| ≤ Real.exp ((p + 2) ^ 9) * ‖x‖ := by
    intro x i
    have hb := abs_matrix_mulVec_le (fun i j => (M i j : ℝ))
      ⟨Real.exp ((p + 2) ^ 7), Real.exp_nonneg _⟩ hentry x i
    exact hb.trans (mul_le_mul_of_nonneg_right
      (matrix_weighted_factor_le_exp_power (Fintype.card J) hp hJ 7 (by decide))
      (norm_nonneg x))
  refine ⟨d, hd, Q, ?_, hbound, matrixDenominator M, matrixDenominator_pos M,
    matrixDenominator_le_exp_power M hp 7 hdp hJ (fun i j => (hM i j).2), ?_⟩
  · exact rationalMatrix_real_ker_eq_span (fun j a => g a j) M hker
  · intro x
    have hx : (fun j => (x j : ℝ)) ∈ realDenominatorGrid 1 :=
      ⟨x, by ext j; simp⟩
    obtain ⟨z, hz⟩ := real_matrix_denominator_grid M 1 (fun j => (x j : ℝ)) hx
    refine ⟨z, fun i => ?_⟩
    change (z i : ℝ) = (matrixDenominator M : ℝ) *
      ((fun i j => (M i j : ℝ)) *ᵥ (fun j => (x j : ℝ))) i
    simpa only [mul_one, Pi.smul_apply, smul_eq_mul] using congrFun hz i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommGroup L] [Module ℚ L] [AddCommGroup M] [Module ℚ M]

theorem realified_linear_coordinate_grid (b : Basis ι ℚ L) (c : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (l : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (c.baseChange ℝ).equivFun (φ.baseChange ℝ x) ∈
      realDenominatorGrid (matrixDenominator (LinearMap.toMatrix b c φ) * l) := by
  exact rational_coordinate_map_grid (b.baseChange ℝ) (c.baseChange ℝ) (φ.baseChange ℝ)
    (LinearMap.toMatrix b c φ) (realified_linear_coordinate_matrix b c φ) l x hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealSymbolAffine
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolOfPolynomial_translate (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF w (translate h p) = F.realSymbolOfPolynomial b ω hF w p := by
  let q : F.realification.adaptedLieSubalgebra w :=
    ⟨p, (F.realification.mem_adaptedSubmodule w p).mpr hp⟩
  let q' : F.realification.adaptedLieSubalgebra w :=
    ⟨translate h p, (F.realification.mem_adaptedSubmodule w _).mpr
      (F.realification.adapted_translate w hw h hp)⟩
  exact (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hF w q' q).mpr
    (F.realification.polynomialSymbolMap_translate w hw h q)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestProbabilityProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ α L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem averageCircles_unit_interval (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hT : T.UnitIntervalValued) : (T.averageCircles A is).UnitIntervalValued := by
  let := D.metricSpace
  exact iteratedCircleAverage_unit_interval A is T.lipschitz hT

theorem averageCircles_invariant (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hcomm : let := D.metricSpace; ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    (j : α) (hj : j ∈ is) (t : CircleFourier.Circle) (x : D.Space) :
    let := D.metricSpace
    (T.averageCircles A is).observable ((A j).act t x) = (T.averageCircles A is).observable x := by
  let := D.metricSpace
  exact iteratedCircleAverage_invariant A is hcomm T.observable j hj t x

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorRealSubstitutionBound
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

theorem scaled_substitution_coeff_bound {I J : Type*}
    (T : J → ℝ) (hT : ∀ j, 0 < T j)
    (f : I → MvPolynomial J ℝ) (p : MvPolynomial I ℝ)
    {A B : ℝ} {s : ℕ} (hB : 1 ≤ B)
    (hf : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (f i)) ≤ B)
    (hp : ∀ α, |p.coeff α| ≤ A) (hdegree : p.totalDegree ≤ s)
    (α : J →₀ ℕ) :
    |(eval₂Hom C f p).coeff α| ≤
      ((p.support.card : ℝ) * A * B ^ s) / monomialScale T α := by
  have hmass : realPolynomialMass p ≤ p.support.card * A := by
    unfold realPolynomialMass
    exact (Finset.sum_le_sum (fun β _ => hp β)).trans_eq (by simp)
  have hsub : realPolynomialMass (scaleMvPolynomialAxes T (eval₂Hom C f p)) ≤
      p.support.card * A * B ^ s := by
    rw [scaleMvPolynomialAxes_substitution]
    exact (realPolynomialMass_substitution_le p _ hB hf hdegree).trans
      (mul_le_mul_of_nonneg_right hmass (pow_nonneg (by linarith) _))
  have h := (realPolynomialMass_coeff_le
    (scaleMvPolynomialAxes T (eval₂Hom C f p)) α).trans hsub
  rw [scaleMvPolynomialAxes_coeff, abs_mul,
    abs_of_pos (monomialScale_pos T hT α)] at h
  exact (le_div_iff₀ (monomialScale_pos T hT α)).mpr h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrdinarySymbolBasisDimension
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem symbolBasisIndex_card_le_spanning_budget
    {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) [Fintype (SymbolBasisIndex w ω)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ (p + (s + 3)) ^ (s + 3) := by
  apply (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
    (F.adaptedBasis_weight_le_step b ω hF))).trans
  apply (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ).trans
  apply (pow_le_pow_left₀ (by positivity : 0 ≤ p + (s + 2))
    (by linarith : p + (s + 2 : ℝ) ≤ p + (s + 3)) (s + 2)).trans
  exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) s; linarith) (by omega)

theorem pointwiseSymbolSpanning_section_counts
    {σ ι κ ξ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype ξ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (SymbolBasisIndex w ω)] [Fintype (SymbolBasisIndex w τ)]
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hξ : (Fintype.card ξ : ℝ) ≤ p)
    (hσ : (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex w ω × ξ) : ℝ) ≤ pointwiseFastSectionInput s p ∧
    (Fintype.card (SymbolBasisIndex w ω ⊕ SymbolBasisIndex w τ) : ℝ) ≤
      pointwiseFastSectionInput s p ∧
    ((Fintype.card (SymbolBasisIndex w ω) *
      Fintype.card (SymbolBasisIndex w ω × ξ) : ℕ) : ℝ) ≤ pointwiseFastSectionInput s p := by
  let A : ℝ := (p + (s + 3)) ^ (s + 3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb := F.symbolBasisIndex_card_le_spanning_budget b ω hF w hw hp hι hσ
  have hc := G.symbolBasisIndex_card_le_spanning_budget c τ hG w hw hp hκ hσ
  have hv : (Fintype.card (SymbolBasisIndex w ω × ξ) : ℝ) ≤ A := by
    have hnat : Fintype.card (SymbolBasisIndex w ω × ξ) ≤
        Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s * Fintype.card ξ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ω s hw
        (F.adaptedBasis_weight_le_step b ω hF))
    exact (Nat.cast_le.mpr hnat).trans (symbol_spanning_count_bound s _ _ _ hp hι hσ hξ)
  have hrows : (Fintype.card (SymbolBasisIndex w ω ⊕ SymbolBasisIndex w τ) : ℝ) ≤ 2 * A := by
    rw [Fintype.card_sum, Nat.cast_add]
    dsimp only [A]
    linarith
  have hcols : ((Fintype.card (SymbolBasisIndex w ω) *
      Fintype.card (SymbolBasisIndex w ω × ξ) : ℕ) : ℝ) ≤ A ^ 2 := by
    rw [Nat.cast_mul, pow_two]
    exact mul_le_mul hb hv (Nat.cast_nonneg _) hA
  change _ ≤ 2 * A + A ^ 2 + p ∧ _ ≤ 2 * A + A ^ 2 + p ∧ _ ≤ 2 * A + A ^ 2 + p
  refine ⟨hv.trans ?_, hrows.trans ?_, hcols.trans ?_⟩ <;> nlinarith [sq_nonneg A]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PivotAnnihilatorFrequencyCode
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem exists_frequency_basis_code [FiniteDimensional ℚ V]
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    ∃ code : Fin (finrank ℚ P) → Option J,
      (∀ i j, code i = some j → j ∈ js) ∧
      finiteFrequencyKernel P eta js = frequencyCodeKernel P eta code := by
  obtain ⟨m, hm, index, hindex, hlin, hspan⟩ := exists_restricted_frequency_basis P eta js
  let code : Fin (finrank ℚ P) → Option J := fun i =>
    if hi : i.val < m then some (index ⟨i.val, hi⟩) else none
  have hkernel : finiteFrequencyKernel P eta js =
      finiteFrequencyKernel P (fun i => eta (index i)) (List.finRange m) := by
    apply finiteFrequencyKernel_eq_of_span_eq
    rw [restrictedFrequencySpan_finRange]
    exact hspan.symm
  refine ⟨code, ?_, ?_⟩
  · intro i j hij
    dsimp only [code] at hij
    split_ifs at hij with hi
    · cases hij
      exact hindex _
  · rw [hkernel]
    ext v
    rw [mem_finiteFrequencyKernel, mem_frequencyCodeKernel]
    simp only [List.mem_finRange, forall_true_left]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro h i j hij
      dsimp only [code] at hij
      split_ifs at hij with hi
      · cases hij
        exact h _
    · intro h i
      let k : Fin (finrank ℚ P) := ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
      apply h k (index i)
      simp only [code, k, i.isLt, dite_true]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialBasisTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (e : Basis κ ℚ L)
  (w : σ → ℕ)

theorem polynomialRationalGrid_change_basis (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) :
    F.PolynomialRationalGrid e w
      (matrixDenominator (fun i j => e.repr (b j) i) * l) g := by
  classical
  obtain ⟨z, hz⟩ := hg
  have hgrid (α : σ →₀ ℕ) :
      (fun i => (e.baseChange ℝ).repr
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i) ∈
        realDenominatorGrid (matrixDenominator (fun i j => e.repr (b j) i) * l) := by
    apply real_basis_coordinates_grid b e l
    exact ⟨fun j => z (α, j), funext fun j => congrFun hz (α, j)⟩
  choose a ha using hgrid
  exact ⟨fun z => a z.1 z.2, funext fun z => congrFun (ha z.1) z.2⟩

omit [Fintype κ] in
theorem polynomialSlowBound_change_basis_exp (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T (Real.exp p) g) :
    F.PolynomialSlowBound e w T (Real.exp ((p + 3) ^ 2)) g := by
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hdim' : (Fintype.card ι : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have hbound : (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p ≤ Real.exp ((p + 3) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (3 * p + 1) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  intro α i
  calc
    _ ≤ (Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * (Real.exp p / monomialScale T α) :=
      real_basis_coordinates_bound b e (fun i j => rationalHeightLE_ceil_exp (hentries j i)) _
        (fun j => hg α j) i
    _ = ((Fintype.card ι : ℝ) * ⌈Real.exp p⌉₊ * Real.exp p) / monomialScale T α := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbound (monomialScale_pos T hT α).le

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearObservableNet
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

theorem exists_shear_observable_net {X Ω : Type*} [Nonempty Ω] {d s N : ℕ} {w : Fin d → ℕ}
    (A : Ω → PolynomialSlots X d w) (hw : Monotone w)
    (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s) (Φ : PatchKernel d)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ a i, realPolynomialMass ((A a).center i) ≤ M)
    (hN : 0 < N) (hsmall : patchTopNetError d s N M < 1 / 4) :
    ∃ (code : Ω → PatchTopCoefficientIndex d s → Fin (N + 1))
      (rep : (PatchTopCoefficientIndex d s → Fin (N + 1)) → Ω),
      ∀ a e, dist (((A a).shearTransformedSlots hw e).patchValue Φ)
        (((A (rep (code a))).shearTransformedSlots hw e).patchValue Φ) ≤
        Φ.lip * patchTopNetError d s N M := by
  let coordinates : Ω → PatchTopCoefficientIndex d s → ℝ :=
    fun a j => ((A a).topResidualEquiv (MvPolynomial.X j.1)).coeff j.2.val
  have hbound (a) (j : PatchTopCoefficientIndex d s) : |coordinates a j| ≤ 1 + M :=
    (realPolynomialMass_coeff_le _ _).trans ((A a).topResidualEquiv_X_mass (hA a) j.1)
  obtain ⟨code, rep, hnet⟩ := exists_uniform_parameter_net coordinates (by linarith : 0 < 1 + M) hbound hN
  refine ⟨code, rep, fun a e => ?_⟩
  apply (A a).shearPatchValue_dist (A (rep (code a))) hw hpos s hs Φ hM
    (patchTopNetError_nonneg d s N hM) hsmall (hA a) (hA _) _ e
  intro x hx
  apply (dist_pi_le_iff (patchTopNetError_nonneg d s N hM)).mpr
  intro i
  have hdegree (a : Ω) : ((A a).topResidualEquiv (MvPolynomial.X i)).totalDegree ≤ s :=
    (totalDegree_le_of_positive_weightedSupport w hpos
      ((A a).topResidualEquiv_degree (weightedSupportLE_X w i))).trans (hs i)
  have hcoeff (m : BoundedIntegerExponent (Fin d) s) :
      |((A a).topResidualEquiv (MvPolynomial.X i)).coeff m.val -
        ((A (rep (code a))).topResidualEquiv (MvPolynomial.X i)).coeff m.val| ≤ 4 * (1 + M) / N := by
    exact (dist_le_pi_dist (coordinates a) (coordinates (rep (code a))) (i,m)).trans (hnet a)
  have h := bounded_coefficients_evaluation_error _ _ (hdegree a) (hdegree _)
    (by positivity : 0 ≤ 4 * (1 + M) / N)
    (one_le_pow₀ (by linarith : 1 ≤ 1 + M) : 1 ≤ (1 + M) ^ (s * d)) hcoeff x hx
  change |aeval x ((A a).topResidualEquiv (MvPolynomial.X i)) -
    aeval x ((A (rep (code a))).topResidualEquiv (MvPolynomial.X i))| ≤ patchTopNetError d s N M
  simpa only [Fintype.card_fin, patchTopNetError] using h

end PolynomialSlots
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialSlots

theorem exists_fixed_kernel_patch_function {X Ω T : Type*} [Fintype Ω] [Nonempty Ω] [Fintype T]
    {d s N : ℕ} {w : Fin d → ℕ}
    (A : Ω → PolynomialSlots X d w) (hw : Monotone w)
    (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s) (Φ : PatchKernel d)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ a i, realPolynomialMass ((A a).center i) ≤ M)
    (hN : 0 < N) (hsmall : patchTopNetError d s N M < 1 / 4)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℝ)
    (score : Ω → T → ℝ) (hscore : ∀ a t, |score a t| ≤ 1)
    {δ : ℝ} (_hδ : 0 < δ)
    (hpositive : ∀ a ∈ productive, δ ≤
      (localLaw a).mean (fun t => score a t * ((A a).slots (point a t)).patchValue Φ))
    (herror : Φ.lip * patchTopNetError d s N M ≤ δ / 2) :
    ∃ (B : PolynomialSlots X d w) (retained : Finset Ω),
      (∀ i, realPolynomialMass (B.center i) ≤ M) ∧
      retained ⊆ productive ∧
      outer.mass productive / ((N + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s) ≤ outer.mass retained ∧
      ∀ a ∈ retained, δ / 2 ≤ (localLaw a).mean (fun t => score a t *
        (B.shearTransformedSlots hw ((A a).loweringAt (point a t))).patchValue Φ) := by
  obtain ⟨code, rep, hnet⟩ := exists_shear_observable_net A hw hpos hs Φ hM hA hN hsmall
  obtain ⟨i, hi⟩ := outer.exists_code_fiber_mass productive code
  refine ⟨A (rep i), productive.filter (fun a => code a = i), hA _, Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard : outer.mass productive / ((N + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s) ≤
        outer.mass productive / Fintype.card (PatchTopCoefficientIndex d s → Fin (N + 1)) := by
      apply div_le_div_of_nonneg_left (outer.mass_nonneg productive)
      · exact_mod_cast Fintype.card_pos (α := PatchTopCoefficientIndex d s → Fin (N + 1))
      · exact_mod_cast patchTopCoefficientCode_card d s N
    apply hcard.trans
    convert hi using 1; try rfl
    congr 1
    ext a
    simp only [Finset.mem_filter]
  · intro a ha
    obtain ⟨ha, hcode⟩ := Finset.mem_filter.mp ha
    have hclose (t : T) :
        dist (((A a).slots (point a t)).patchValue Φ)
          (((A (rep i)).shearTransformedSlots hw ((A a).loweringAt (point a t))).patchValue Φ) ≤
            Φ.lip * patchTopNetError d s N M := by
      have h := hnet a ((A a).loweringAt (point a t))
      rw [hcode, loweringAt_patchValue] at h
      exact h
    let u := fun t => score a t * ((A a).slots (point a t)).patchValue Φ
    let v := fun t => score a t *
      ((A (rep i)).shearTransformedSlots hw ((A a).loweringAt (point a t))).patchValue Φ
    have he : |(localLaw a).mean (fun t => u t - v t)| ≤ Φ.lip * patchTopNetError d s N M := by
      apply (localLaw a).abs_mean_le_on_support
      intro t _
      change |score a t * _ - score a t * _| ≤ _
      rw [← mul_sub, abs_mul]
      exact (mul_le_mul_of_nonneg_right (hscore a t) (abs_nonneg _)).trans
        (by simpa only [one_mul, Real.dist_eq] using hclose t)
    rw [(localLaw a).mean_sub] at he
    have hp := hpositive a ha
    change δ ≤ (localLaw a).mean u at hp
    change δ / 2 ≤ (localLaw a).mean v
    linarith [le_abs_self ((localLaw a).mean u - (localLaw a).mean v)]

end PolynomialSlots
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationSizes
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct Matrix
open VectorPolynomial

attribute [instance] RankPreparationLayer.coordFinite RankPreparationLayer.columnFinite
  RankPreparationLayer.rowFinite

namespace RankPreparationLayer

variable {I J : Type}

def Valid (L : RankPreparationLayer I J) (degree H R : ℕ) : Prop :=
  DegreeLE (fun _ => 1) degree L.poly ∧
  (∀ α, coefficients L.poly α ∈ L.space) ∧
  (∀ i j, RationalHeightLE (L.basis i j) H) ∧
  (∀ i j, RationalHeightLE (L.rows i j) R)

theorem Valid.mono_height {L : RankPreparationLayer I J} {d H H' R : ℕ}
    (h : L.Valid d H R) (hHH' : H ≤ H') : L.Valid d H' R :=
  ⟨h.1, h.2.1, fun i j => (h.2.2.1 i j).mono hHH', h.2.2.2⟩

noncomputable def cut (L : RankPreparationLayer I J) (a : L.Coord → ℤ) (e : L.Coord → ℝ) :
    RankPreparationLayer I J where
  Coord := L.Coord
  Column := L.Column
  Row := Option L.Row
  coordFinite := L.coordFinite
  columnFinite := L.columnFinite
  rowFinite := inferInstance
  label := L.label
  basis := L.basis
  rows := appendRankCutRow L.rows a
  poly := map (samplingRankProjection a e) L.poly

theorem cut_space (L : RankPreparationLayer I J) (a : L.Coord → ℤ) (e : L.Coord → ℝ) :
    (L.cut a e).space = L.space ⊓ LinearMap.ker (integerRowLinear a) :=
  jointRationalSpace_appendRankCutRow L.basis L.rows a

theorem Valid.cut {L : RankPreparationLayer I J} {d H R : ℕ}
    (hL : L.Valid d H R) (hR : 1 ≤ R) (a : L.Coord → ℤ) (e : L.Coord → ℝ)
    (ha : ∀ i, |(a i : ℝ)| ≤ R) (he : e ∈ L.space) (hae : integerRowLinear a e = 1) :
    (L.cut a e).Valid d H R := by
  refine ⟨hL.1.map _, ?_, hL.2.2.1, ?_⟩
  · intro α
    rw [cut_space]
    change coefficients (map (samplingRankProjection a e) L.poly) α ∈ _
    rw [coefficients_map]
    exact samplingRankProjection_mem a e L.space he hae (hL.2.1 α)
  · exact appendRankCutRow_height L.rows a hR hL.2.2.2 ha

noncomputable def appendLine (L : RankPreparationLayer I J) {C : Type} [Fintype C]
    (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ) : RankPreparationLayer I J where
  Coord := L.Coord ⊕ C
  Column := Option L.Column
  Row := L.Row
  coordFinite := inferInstance
  columnFinite := inferInstance
  rowFinite := L.rowFinite
  label := Sum.elim L.label label
  basis := copiedLayerMatrix L.basis e
  rows := copiedLayerRows L.rows
  poly := copiedLayerPolynomial L.poly (l ⊗ₜ[ℝ] (fun i => (e i : ℝ)))

theorem appendLine_space (L : RankPreparationLayer I J) {C : Type} [Fintype C]
    (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ) :
    (L.appendLine label e l).space =
      copiedLayerSpace L.space (Submodule.span ℝ {fun i => (e i : ℝ)}) :=
  jointRationalSpace_copiedLayer L.basis L.rows e

theorem Valid.appendLine {L : RankPreparationLayer I J} {C : Type} [Fintype C]
    {d H R He : ℕ} (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R)
    (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ)
    (he : ∀ i, RationalHeightLE (e i) He) (hl : l.totalDegree ≤ d) :
    (L.appendLine label e l).Valid d (max H He) R := by
  refine ⟨copiedLayerPolynomial_degree hL.1 (degreeLE_tmul_totalDegree l _ hl), ?_,
    copiedLayerMatrix_height L.basis e hH hL.2.2.1 he,
    copiedLayerRows_height L.rows hR hL.2.2.2⟩
  intro α
  rw [appendLine_space]
  apply copiedLayerPolynomial_mem L.space _ L.poly _ hL.2.1
  intro β
  rw [coefficients_tmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

theorem empty_valid (d H R : ℕ) : (empty : RankPreparationLayer I J).Valid d H R := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α _
    change coefficients (0 : VectorPolynomial I ℝ (PEmpty → ℝ)) α = 0
    simp only [map_zero, Finsupp.zero_apply]
  · intro α
    change coefficients (0 : VectorPolynomial I ℝ (PEmpty → ℝ)) α ∈ _
    simp only [map_zero, Finsupp.zero_apply]
    exact Submodule.zero_mem _
  · intro i
    exact i.elim
  · intro i
    exact i.elim

end RankPreparationLayer
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

namespace RankPreparationFamily

variable {I J : Type} {s : ℕ}

noncomputable def value [DecidableEq J] (L : RankPreparationFamily I J s) (x : I → ℝ) : J → ℝ :=
  ∑ i, (L i).value x

noncomputable def potential (L : RankPreparationFamily I J s) : ℕ :=
  layerRankPotential (fun i => (L i).rank)

noncomputable def reindex (L : RankPreparationFamily I J s) (f : I → MvPolynomial I ℝ) :
    RankPreparationFamily I J s := fun i => (L i).reindex f

@[simp] theorem reindex_potential (L : RankPreparationFamily I J s) (f : I → MvPolynomial I ℝ) :
    (L.reindex f).potential = L.potential := rfl

noncomputable def descend (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ) :
    RankPreparationFamily I J s := fun i =>
  if i = upper then (L upper).cut a (fun i => (e i : ℝ))
  else if i = lower then (L lower).appendLine (L upper).label e l
  else L i

noncomputable def absorb (L : RankPreparationFamily I J s) (lowest : Fin s)
    (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ) : RankPreparationFamily I J s :=
  fun i => if i = lowest then (L lowest).cut a (fun i => (e i : ℝ)) else L i

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

variable {I J : Type} {s : ℕ}

def Sized (L : RankPreparationFamily I J s) (D t : ℕ) : Prop :=
  ∀ i, Fintype.card (L i).Coord ≤ D * (t + 1) ^ (s - 1 - i.val) ∧
    Fintype.card (L i).Column ≤ D + t ∧ Fintype.card (L i).Row ≤ t

theorem Sized.mono {L : RankPreparationFamily I J s} {D t u : ℕ}
    (h : L.Sized D t) (htu : t ≤ u) : L.Sized D u := by
  intro i
  obtain ⟨hc, hb, hr⟩ := h i
  refine ⟨hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)), by omega, by omega⟩

theorem Sized.uniform {L : RankPreparationFamily I J s} {D t T : ℕ}
    (h : L.Sized D t) (ht : t ≤ T) (i : Fin s) :
    Fintype.card (L i).Coord ≤ D * (T + 1) ^ s ∧
      Fintype.card (L i).Column ≤ D + T ∧ Fintype.card (L i).Row ≤ T := by
  have hm := h.mono ht
  refine ⟨(hm i).1.trans (Nat.mul_le_mul_left D ?_), (hm i).2⟩
  exact Nat.pow_le_pow_right (by omega) (by omega)

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

namespace RankPreparationFamily

def PreparedHeights {I J : Type} {s : ℕ} (L : RankPreparationFamily I J s) (p : ℝ) (R : ℕ) : Prop :=
  ∀ i, (L i).Valid (i.val + 1) (preparationHeight p (s - 1 - i.val)) R

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

namespace RankPreparationFamily

variable {I J : Type} {m q : ℕ}

noncomputable def pad (L : RankPreparationFamily I J m) (q : ℕ) :
    RankPreparationFamily I J q := fun j =>
  if hj : j.val < m then L ⟨j.val, hj⟩ else RankPreparationLayer.empty

@[simp] theorem pad_apply_lt (L : RankPreparationFamily I J m) (j : Fin q)
    (hj : j.val < m) : L.pad q j = L ⟨j.val, hj⟩ := by
  simp only [pad, dif_pos hj]

@[simp] theorem pad_apply_ge (L : RankPreparationFamily I J m) (j : Fin q)
    (hj : m ≤ j.val) : L.pad q j = RankPreparationLayer.empty := by
  simp only [pad, dif_neg (by omega : ¬j.val < m)]

@[simp] theorem pad_apply_castLE (L : RankPreparationFamily I J m) (hmq : m ≤ q)
    (j : Fin m) : L.pad q (j.castLE hmq) = L j := by
  simp only [pad, Fin.val_castLE, dif_pos j.isLt]

theorem PreparedHeights.pad {L : RankPreparationFamily I J m} {p : ℝ} {R : ℕ}
    (hL : L.PreparedHeights p R) (hmq : m ≤ q) (hp : 0 ≤ p) :
    (L.pad q).PreparedHeights p R := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact (hL ⟨j.val, hj⟩).mono_height
      (preparationHeight_mono hp (by change m - 1 - j.val ≤ q - 1 - j.val; omega))
  · rw [pad_apply_ge L j (by omega)]
    exact RankPreparationLayer.empty_valid _ _ _

theorem Sized.pad {L : RankPreparationFamily I J m} {D t : ℕ}
    (hL : L.Sized D t) (hmq : m ≤ q) : (L.pad q).Sized D t := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    obtain ⟨hc, hb, hr⟩ := hL ⟨j.val, hj⟩
    exact ⟨hc.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by omega)
      (by change m - 1 - j.val ≤ q - 1 - j.val; omega))), hb, hr⟩
  · rw [pad_apply_ge L j (by omega)]
    change Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _
    simp

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox

variable {X J : Type} (L : RankPreparationLayer X J)

noncomputable def shortIntegralBasisNormBound (H R : ℕ) : ℝ :=
  (L.rank : ℝ) * L.rank.factorial * minkowskiSecondConstant L.rank *
    ((Fintype.card L.Coord : ℝ) *
      (jointSpaceGeneratorHeight (Fintype.card L.Coord) (Fintype.card L.Column)
        (Fintype.card L.Row) H R : ℝ) ^ (Fintype.card L.Coord * Fintype.card L.Coord))

end Erdos3.RankPreparationLayer

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedDeterminingCoordinates
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ}

abbrev DeterminingIndex (_L : RankPreparationFamily X J m) (E : Fin m → Type) :=
  Sigma E

abbrev PreparedCoordinate (L : RankPreparationFamily X J m) :=
  (u : Fin m) × (L u).Coord

variable (L : RankPreparationFamily X J m) (E : Fin m → Type)

def determiningWeight (a : L.DeterminingIndex E) : ℕ := a.1.val + 1

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchFiniteCoordinateReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ}

@[simp] theorem coordinateEquiv_complexity (A : PolynomialPatch X s d) (e : X ≃ Y) :
    relativePatchComplexity (A.coordinateEquiv e) = relativePatchComplexity A := rfl

@[simp] theorem coordinateEquiv_distinctWeights (A : PolynomialPatch X s d) (e : X ≃ Y) :
    relativePatchDistinctWeights (A.coordinateEquiv e) = relativePatchDistinctWeights A := rfl

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialSectionSlow
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ)

theorem section_exponential_budget (a : ℕ) {p n : ℝ} (hp : 0 ≤ p)
    (hnp : n ≤ p) :
    n * Real.exp ((p + 2) ^ a) * Real.exp ((p + 2) ^ a) ≤
      Real.exp ((p + 2) ^ (a + 2)) := by
  have hp1 : 1 ≤ p + 2 := by linarith
  have hq1 : 1 ≤ (p + 2) ^ a := one_le_pow₀ hp1
  have hnexp : n ≤ Real.exp p := hnp.trans (by linarith [Real.add_one_le_exp p])
  have hsmall : p + 2 * (p + 2) ^ a ≤ (p + 2) * (p + 2) ^ a := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hq1)]
  have hlarge : (p + 2) * (p + 2) ^ a ≤ (p + 2) ^ (a + 2) := by
    rw [pow_add, pow_two]
    nlinarith [mul_nonneg (show 0 ≤ (p + 2) ^ a by positivity)
      (show 0 ≤ (p + 2) * (p + 2) - (p + 2) by nlinarith)]
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ a) * Real.exp ((p + 2) ^ a) := by
      gcongr
    _ = Real.exp (p + 2 * (p + 2) ^ a) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (hsmall.trans hlarge)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualMarkedSlowKernelCells
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem exists_slow_kernel_net_geometry_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d n H : ℕ) (p A : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      0 ≤ A → A ≤ Real.exp ((p + 2) ^ r) →
      ∃ B : ℝ≥0, 1 ≤ B ∧
        ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * A ≤ B ∧
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (bchBoxMetricConstant s d H B : ℝ) *
          (((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * A * n * s) ≤
            Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C s * (X + 1) + (X + 2) ^ r
  obtain ⟨a, _, hP⟩ := exists_natPolynomial_eval_budget P
  obtain ⟨b, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s a
  let Q := (X + Polynomial.C a + Polynomial.C b) ^ b + P + X + Polynomial.C s
  obtain ⟨C, hC, hQ⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro d n H p A hp hd hn hH hA hAp
  let q : ℝ := s * (p + 1) + (p + 2) ^ r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let B : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := Real.one_le_exp hq
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hAM : ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * A ≤ Real.exp q := by
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ r) :=
        mul_le_mul (mul_le_mul (Real.add_one_le_exp (s : ℝ))
          (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_pos _).le)
          hAp hA (by positivity)
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [q]
        ring
  have hpA : p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hBa : (B : ℝ) ≤ Real.exp (((p + a) + 2) ^ a) := by
    apply Real.exp_le_exp.mpr
    have h' : q ≤ (p + a) ^ a := by simpa [P, X, q, Polynomial.eval₂_pow] using hP p hp
    exact h'.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hBC : (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + a + b) ^ b) :=
    hbox d H B (p + a) (hp.trans hpA) (hd.trans hpA)
      (hH.trans (Real.exp_le_exp.mpr hpA)) hBa
  have hfinal : (p + a + b) ^ b + q + p + s ≤ (p + C) ^ C := by
    simpa [Q, P, X, q, Polynomial.eval₂_pow] using hQ p hp
  have hbase : 0 ≤ (p + a + b) ^ b := by positivity
  have hnexp : (n : ℝ) ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hsexp : (s : ℝ) ≤ Real.exp s := by linarith [Real.add_one_le_exp (s : ℝ)]
  refine ⟨B, hB, hAM, Real.exp_le_exp.mpr (by linarith),
    hBC.trans (Real.exp_le_exp.mpr (by linarith)), ?_⟩
  calc
    _ ≤ Real.exp ((p + a + b) ^ b) * (Real.exp q * Real.exp p * Real.exp s) := by
      apply mul_le_mul hBC
        (mul_le_mul (mul_le_mul hAM hnexp (Nat.cast_nonneg _) (Real.exp_pos _).le)
          hsexp (Nat.cast_nonneg _) (by positivity))
        (by positivity) (Real.exp_pos _).le
    _ = Real.exp (((p + a + b) ^ b) + q + p + s) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hfinal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

omit [Fintype σ] in

theorem map_polynomialLinearRestriction_ratCast
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) :
    map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P) =
      eval₂Hom C (fun i => map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i))
        (map (algebraMap ℚ ℝ) P) :=
  map_eval₂ (algebraMap ℚ ℝ) (linearCoordinatePolynomial A) P

omit [Fintype σ] [Fintype τ] in

theorem polynomialDenominator_coefficientGrid (P : MvPolynomial σ ℚ) :
    (fun m => P.coeff m) ∈ denominatorGrid (polynomialDenominator P) := by
  classical
  refine ⟨fun m => if hm : m ∈ P.support then
    clearedArray (fun n : P.support => P.coeff n.val) ⟨m, hm⟩ else 0, ?_⟩
  intro m
  change (polynomialDenominator P : ℚ) * P.coeff m = _
  by_cases hm : m ∈ P.support
  · simp only [dif_pos hm]
    exact (clearedArray_cast (fun n : P.support => P.coeff n.val) ⟨m, hm⟩).symm
  · simp [hm, notMem_support_iff.mp hm]

theorem polynomialLinearRestriction_denominatorGrid [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    (d : ℕ) (hd : P.totalDegree ≤ d) :
    (fun m => (polynomialLinearRestriction A P).coeff m) ∈
      denominatorGrid (polynomialDenominator P *
        matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d) := by
  apply (realPolynomialCoefficientGrid_ratCast_iff _ _).mp
  rw [map_polynomialLinearRestriction_ratCast]
  apply realPolynomialCoefficientGrid_substitute
  · apply le_trans (b := P.totalDegree) ?_ hd
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) P hm)
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr
      (polynomialDenominator_coefficientGrid P)
  · exact linearCoordinatePolynomial_realCoefficientGrid A

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem polynomialLinearRestriction_realMass_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d : ℕ} (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) :
    realPolynomialMass (map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P)) ≤
      (((Fintype.card σ + 1) ^ d * K) * (Fintype.card τ * H + 1) ^ d : ℕ) := by
  have he : map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P) =
      eval₂Hom C (fun i => map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i))
        (map (algebraMap ℚ ℝ) P) := map_eval₂ _ _ _
  rw [he]
  have hd' : (map (algebraMap ℚ ℝ) P).totalDegree ≤ d := by
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact (le_totalDegree (support_map_subset (algebraMap ℚ ℝ) P hm)).trans hd
  have hmass := realPolynomialMass_substitution_le (map (algebraMap ℚ ℝ) P)
    (fun i => map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i))
    (M := (Fintype.card τ * H + 1 : ℕ)) (by exact_mod_cast Nat.le_add_left 1 _)
    (fun i => (linearCoordinatePolynomial_realMass_le A hA i).trans
      (by exact_mod_cast Nat.le_succ (Fintype.card τ * H))) hd'
  refine hmass.trans ?_
  simpa only [Nat.cast_mul, Nat.cast_pow] using mul_le_mul_of_nonneg_right
    (rationalPolynomial_realMass_le P hP hd)
    (pow_nonneg (Nat.cast_nonneg (Fintype.card τ * H + 1)) d)

theorem polynomialLinearRestriction_coeff_abs_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d : ℕ} (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) (m : τ →₀ ℕ) :
    |(((polynomialLinearRestriction A P).coeff m : ℚ) : ℝ)| ≤
      (((Fintype.card σ + 1) ^ d * K) * (Fintype.card τ * H + 1) ^ d : ℕ) := by
  have h := (realPolynomialMass_coeff_le
    (map (algebraMap ℚ ℝ) (polynomialLinearRestriction A P)) m).trans
      (polynomialLinearRestriction_realMass_le A P hA hP hd)
  rw [coeff_map] at h
  exact h

theorem polynomialLinearRestriction_height
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ)
    {H K d : ℕ} (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H)
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) :
    RationalPolynomialHeightLE (polynomialLinearRestriction A P)
      (linearRestrictionHeight (Fintype.card σ) (Fintype.card τ) d H K) := by
  have hK : 0 < K := hP.one_le
  have hmasspos : 1 ≤ ((Fintype.card σ + 1) ^ d * K) *
      (Fintype.card τ * H + 1) ^ d := by
    change 0 < ((Fintype.card σ + 1) ^ d * K) * (Fintype.card τ * H + 1) ^ d
    positivity
  obtain ⟨z, hz⟩ := polynomialLinearRestriction_denominatorGrid A P d hd
  intro m
  exact rationalHeightLE_of_integral_mul_of_abs_le _
    (polynomialLinearRestriction_denominator_pos A P d)
    (polynomialLinearRestriction_denominator_le A P hd hP hA)
    hmasspos ⟨z m, hz m⟩ (polynomialLinearRestriction_coeff_abs_le A P hA hP hd m)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open Polynomial CircleFourier

def PolynomialIntervalPowerBound (k C d : ℕ) : Prop :=
      ∀ (P : Polynomial ℝ) (u v : ℤ) (δ : ℝ),
        P.natDegree ≤ k → 0 < (v - u).toNat → 0 < δ → δ ≤ 1 →
        (C : ℝ) ≤ δ ^ d * (v - u).toNat →
        δ * (v - u).toNat ≤
          ‖∑ n ∈ Finset.Ico u v, character ((P.eval (n : ℝ) : ℝ) : CircleFourier.Circle)‖ →
        ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C / δ ^ d ∧ ∃ p : ℤ,
          |(q : ℝ) * P.coeff k - p| ≤ C / (δ ^ d * ((v - u).toNat : ℝ) ^ k)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

abbrev PreparedSamplerContinuous (j : Fin m) := Fin (L j).rank

end Erdos3.VectorPolynomial

end

end OAI
end


