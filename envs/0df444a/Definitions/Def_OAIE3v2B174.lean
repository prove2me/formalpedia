-- Prove2me | Definitions.Def_OAIE3v2B174
-- name    : OAIE3v2B174
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:40:59.783668+00:00
-- url     : https://prove2.me/theorems/ea269f11-50b8-4ae7-b8a1-84b1b8d3c55b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 176 of 311
-- statement:
--   Definitions bundle 176 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B153`, `OAIE3v2B158`, `OAIE3v2B159` of this split.
--
--   Modules: `Estimates/CommonPivotQuotientTop.lean`, `Estimates/CommonPositivePartitionRefinement.lean`, `Estimates/CommonRefilteredMappedOrbitFactors.lean`, `Estimates/ControlledSingleRefilteredReconstruction.lean`, `Estimates/ExternalPhysicalMemberPivotMasks.lean`, `Estimates/FormalMarkedOrbitTranslation.lean`, `Estimates/FrozenMarkedLeftOrbitBound.lean`, `Estimates/MarkedRefilteredLowerNativeDiagram.lean`, `Estimates/NativeMarkedDiagramOrbitLift.lean`, `Estimates/NativeModelOrbit.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/NativeOptionOriginalOrbit.lean`, `Estimates/PositiveShiftProductData.lean`, `Estimates/RealifiedTopQuotient.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/JoinedFrequencyRefilteredTop.lean`, `Geometry/PositiveCyclicCoordinateProduct.lean`, `Geometry/TerminalChartSlowEvaluation.lean`, `Lattices/FixedAffineResidueDescent.lean`, `Lattices/RetainedPhysicalCRT.lean`, `Linear/ActualOrdinaryPointwiseSpanning.lean`, `Linear/ExternalFamilyPrecenterProjectionData.lean`, `Linear/KernelProjectionPresentPivotIdeal.lean`, `Linear/RefilteredKernelConstantBounds.lean`, `Linear/ShiftFailurePositiveBasis.lean`, `Linear/SingleRefilteredKernel.lean`, `Nilpotent/PositiveShiftTestingNiltests.lean`, `Polynomial/ControlledPolynomialGroupMapBounds.lean`, `Polynomial/NativeMarkedPolynomialFreezing.lean`, `Polynomial/RefilteredPolynomialProjection.lean`, `Sampling/PrecenterForecastNativeAtomDictionary.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B153
import Definitions.Def_OAIE3v2B158
import Definitions.Def_OAIE3v2B159

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct NNReal

theorem exists_bottom_quotient_character :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d : ℕ)
      [TopologicalSpace (ℝ ⊗[ℚ] BottomQuotient d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] BottomQuotient d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] BottomQuotient d)]
      [T2Space (ℝ ⊗[ℚ] BottomQuotient d)] (i₀ : Fin d) {p : ℝ},
      0 ≤ p → (d : ℝ) ≤ p →
      ∃ (e : ℕ) (E : RationalFilteredNilmanifold (BottomQuotient d) 1 e),
        E.GeometryComplexityLE p ∧
        (∀ i j, rationalLogHeight (E.basis.repr
          (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) (basis d j)) i) ≤ p) ∧
        ∃ (η : BottomQuotient d →ₗ[ℚ] ℚ) (V : E.Space → ℂ),
          (∀ x, η (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) x) = x i₀) ∧
          (letI := E.metricSpace;
            LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ V) ∧
          (∀ x, ‖V x‖ = 1) ∧
          ∀ z : E.RealGroup, V (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z := by
  obtain ⟨C, hC, hcharacter⟩ := exists_native_step_one_character
  refine ⟨C, hC, ?_⟩
  intro d _ _ _ _ i₀ p hp hd
  classical
  have hI : (filtration d).layer (1 + 1) ≤ (⊥ : LieIdeal ℚ (Algebra d)).toSubmodule := by
    rw [(filtration d).terminal]
    exact bot_le
  have hspan : (⊥ : LieIdeal ℚ (Algebra d)).toSubmodule =
      Submodule.span ℚ (basis d '' (∅ : Set (Fin d))) := by simp
  let E := (filtration d).coordinateQuotientModel (basis d) (fun _ => 1) (basis_layers d)
    (⊥ : LieIdeal ℚ (Algebra d)) hI ∅ hspan (lattice d) 1 (by decide)
    (lattice_inner_grid d) (lattice_outer_grid d)
  have hE : E.GeometryComplexityLE p := by
    apply (filtration d).coordinateQuotientModel_geometry (basis d) (fun _ => 1) (basis_layers d)
      (⊥ : LieIdeal ℚ (Algebra d)) hI ∅ hspan (lattice d) 1 (by decide)
      (lattice_inner_grid d) (lattice_outer_grid d) hp
    · simpa only [Fintype.card_fin] using hd
    · simpa only [Nat.cast_one] using Real.one_le_exp hp
    · intro i j k
      simpa [lieStructureConstants, lie_eq_zero, rationalLogHeight] using hp
  let η : BottomQuotient d →ₗ[ℚ] ℚ :=
    (⊥ : Submodule ℚ (Algebra d)).liftQ ((basis d).coord i₀) bot_le
  have hη (x : Algebra d) : η (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) x) = x i₀ :=
    basis_repr d x i₀
  have hproj (i) (j) : rationalLogHeight (E.basis.repr
      (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) (basis d j)) i) ≤ p := by
    change rationalLogHeight (((supportedQuotientBasis (basis d)
      (⊥ : Submodule ℚ (Algebra d)) ∅ hspan).reindex (Fintype.equivFin _)).repr
        ((⊥ : Submodule ℚ (Algebra d)).mkQ (basis d j)) i) ≤ p
    rw [Basis.repr_reindex_apply, supportedQuotientBasis_repr_mk]
    exact rationalLogHeight_le_of_height (basis_repr_height_one _ _ _)
      (by simpa only [Nat.cast_one] using Real.one_le_exp hp)
  have hheight (i) : rationalLogHeight (η (E.basis i)) ≤ p := by
    change rationalLogHeight (η (((supportedQuotientBasis (basis d)
      (⊥ : Submodule ℚ (Algebra d)) ∅ hspan).reindex (Fintype.equivFin _)) i)) ≤ p
    rw [Basis.reindex_apply, supportedQuotientBasis_apply]
    change rationalLogHeight ((basis d).repr (basis d _) i₀) ≤ p
    exact rationalLogHeight_le_of_height (basis_repr_height_one _ _ _)
      (by simpa only [Nat.cast_one] using Real.one_le_exp hp)
  have hint : ∀ z : E.RealGroup, z ∈ E.realLattice →
      ∃ n : ℤ, realifyFunctional η z.coord = n := by
    apply E.realLattice_functional_integral η
    intro z hz
    obtain ⟨g, hg, rfl⟩ := hz
    obtain ⟨a, ha⟩ := hg
    refine ⟨a i₀, ?_⟩
    change η (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) g.coord) = _
    rw [hη]
    exact ha i₀
  obtain ⟨V, hLip, hnorm, heq⟩ := hcharacter E hp hE η hheight hint
  exact ⟨_, E, hE, hproj, η, V, hη, hLip, hnorm, heq⟩

end Erdos3.RationalTorus

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem exists_native_refiltered_orbit (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ q : (F.gradedRefiltration W).realification.PolynomialOrbit w,
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧ coefficients q.log 0 = 0 := by
  obtain ⟨q₀, _, hq₀, hz₀⟩ := F.exists_refiltered_polynomial_of_coefficients w W hw p hp hzero
  let H := F.gradedRefiltrationSubalgebra W
  let inc := (realLieHomToRat (realificationLieHom H.incl)).toLinearMap
  let lift : F.realGradedRefiltrationSubalgebra W →ₗ[ℚ] (ℝ ⊗[ℚ] H) :=
    (realificationSubmoduleEquiv H.toSubmodule).symm.toLinearMap.restrictScalars ℚ
  have hcomp : inc.comp lift = (F.realGradedRefiltrationSubalgebra W).incl.toLinearMap := by
    ext x
    exact congrArg Subtype.val ((realificationSubmoduleEquiv H.toSubmodule).apply_symm_apply x)
  let q := VectorPolynomial.map lift q₀
  have hmap : VectorPolynomial.map inc q = p := by
    apply coefficients.injective
    ext α
    dsimp only [q]
    rw [coefficients_map, coefficients_map]
    change (inc.comp lift) (coefficients q₀ α) = coefficients p α
    rw [hcomp]
    simpa only [coefficients_map] using congrArg (fun r => coefficients r α) hq₀
  have hadapted : (F.gradedRefiltration W).realification.Adapted w q := by
    apply ((F.gradedRefiltration W).realification.adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_native_refiltration_layer]
    have h := congrArg (fun r => coefficients r α) hmap
    rw [coefficients_map] at h
    change inc (coefficients q α) ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α)
    rw [h]
    exact hp α
  refine ⟨polynomialOrbitOfLog q hadapted, hmap, ?_⟩
  change coefficients (VectorPolynomial.map lift q₀) 0 = 0
  rw [coefficients_map, hz₀, map_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t e : ℕ} (F : NilpotentLieFiltration L s)
  (W : LieSubalgebra ℚ F.AssociatedGraded)
  (E : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s e)
  (hEF : E.filtration = F.gradedRefiltration W) (w : σ → ℕ)

include hEF in
theorem exists_model_refiltered_polynomial (hw : ∀ i, 0 < w i)
    (b : (F.realification.adaptedPolynomialFiltration w).Group)
    (hb : ∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hb0 : coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0) :
    ∃ g : E.filtration.realification.PolynomialOrbit w,
      ∀ x : σ → ℤ,
        realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
          (E.filtration.realification.polynomialOrbitEval w x g) =
            F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b := by
  rw [hEF]
  obtain ⟨g, hg, _⟩ := F.exists_native_refiltered_orbit W w hw
    (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) hb hb0
  refine ⟨g, ?_⟩
  intro x
  rw [← polynomialOrbitRealEval_integer]
  exact F.native_refiltered_orbit_real_value W w g _ hg _

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTopQuotient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1))

theorem realificationTopQuotientEquiv_mem_layer_iff (j : ℕ)
    (x : (ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) :
    F.realificationTopQuotientEquiv x ∈ F.quotientTop.realification.layer j ↔
      x ∈ F.realification.quotientTop.layer j := by
  change F.realificationTopQuotientEquiv x ∈
    ((F.layer j).map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap).baseChange ℝ ↔ _
  rw [realification_map]
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨a, ha, F.realificationTopQuotientEquiv.injective ?_⟩
    exact he
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem realificationTopQuotientEquiv_projection {M : Type*}
    [LieRing M] [LieAlgebra ℚ M] (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (x : (ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) :
    G.realificationTopQuotientEquiv
      (lieQuotientProjection (F.realification.layerIdeal (s + 1))
        (G.realification.layerIdeal (s + 1))
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ (s + 1)) x) =
      realificationLieHom
        (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ (hφ (s + 1)))
        (F.realificationTopQuotientEquiv x) := by
  obtain ⟨v, rfl⟩ := lieQuotientMap_surjective (F.realification.layerIdeal (s + 1)) x
  change realificationLieHom (lieQuotientMap (G.layerIdeal (s + 1)))
      (realificationLieHom φ v) =
    realificationLieHom
      (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ (hφ (s + 1)))
      (realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) v)
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul r v => rfl
  | add v z hv hz => simp only [map_add, hv, hz]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (b : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem gradedRefiltrationLayer_top_kernel_eq_zero
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (htop : ∀ a ∈ U,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω s a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0)
    (x : L) (hx : x ∈ F.gradedRefiltrationLayer U s) (hzero : φ x = 0) : x = 0 := by
  obtain ⟨hxF, hxU⟩ := (F.mem_gradedRefiltrationLayer U s x).mp hx
  have hpiece : F.associatedGradedPieceMap s ⟨x, hxF⟩ = 0 := by
    apply htop _ hxU (F.associatedGradedPieceMap_grade_fixed e ω hF s ⟨x, hxF⟩)
    rw [F.associatedGradedMap_piece]
    have he : (⟨φ x, hφ s x hxF⟩ : G.layer s) = 0 := Subtype.ext hzero
    rw [he, map_zero]
  have hmem := (F.associatedGradedPieceMap_eq_zero_iff s ⟨x, hxF⟩).mp hpiece
  rw [F.terminal] at hmem
  exact hmem

theorem gradedRefiltrationMap_mem_layer (U : LieSubalgebra ℚ F.AssociatedGraded)
    (j : ℕ) (x : F.gradedRefiltrationSubalgebra U)
    (hx : x ∈ (F.gradedRefiltration U).layer j) :
    F.gradedRefiltrationMap G φ hφ U x ∈
      (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layer j :=
  F.gradedRefiltrationLayer_map_mem G φ hφ U j x hx

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyRefilteredTop
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem graded_top_kernel_iff_refiltered_top_kernel
    {ι L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (U : LieSubalgebra ℚ F.AssociatedGraded) :
    (∀ a ∈ U, basisGradeProjection (F.associatedGradedBasis e ω hF) ω s a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0) ↔
    (∀ x ∈ F.gradedRefiltrationLayer U s, φ x = 0 → x = 0) := by
  constructor
  · exact fun htop => F.gradedRefiltrationLayer_top_kernel_eq_zero G e ω hF φ hφ U htop
  · intro htop a ha hpure hzero
    obtain ⟨x, hx⟩ := F.exists_associatedGradedPieceMap_of_pure e ω hF s a hpure
    have hxU : (x : L) ∈ F.gradedRefiltrationLayer U s := by
      apply (F.mem_gradedRefiltrationLayer U s x).mpr
      exact ⟨x.property, hx.symm ▸ ha⟩
    have hpiece : G.associatedGradedPieceMap s ⟨φ x, hφ s x x.property⟩ = 0 := by
      rw [← F.associatedGradedMap_piece G φ hφ s x, hx]
      exact hzero
    have hφzero : φ x = 0 := by
      have hmem := (G.associatedGradedPieceMap_eq_zero_iff s
        ⟨φ x, hφ s x x.property⟩).mp hpiece
      rw [G.terminal] at hmem
      exact hmem
    have hxzero : x = 0 := Subtype.ext (htop x hxU hφzero)
    rw [← hx, hxzero, map_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonPivotQuotientTop
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem frequency_zero_on_refilteredLayer_of_real
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s : ℕ}
    (H : NilpotentLieFiltration V s) (U : LieSubalgebra ℚ H.AssociatedGraded)
    (η : V →ₗ[ℚ] ℚ) (k : ℕ)
    (hzero : ∀ x ∈ H.realGradedRefiltrationLayer U k, realifyFunctional η x = 0)
    (x : V) (hx : x ∈ H.gradedRefiltrationLayer U k) : η x = 0 := by
  have hz := hzero ((1 : ℝ) ⊗ₜ[ℚ] x) (Submodule.tmul_mem_baseChange_of_mem 1 hx)
  simp only [realifyFunctional_tmul, one_mul] at hz
  exact_mod_cast hz

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonPositivePartitionRefinement
namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

theorem PositiveCyclicNiltest.model_nonempty {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} degree N p f) (hp : 0 ≤ p) :
    Nonempty (PositiveCyclicModel.{u} degree N (raisedNiltestBudget p) f) := by
  rcases hf with @⟨L, lie, algebra, s, dim, topology, topologicalAdd, continuousSMul,
    hausdorff, D, hdegree, T, hpositive, hcomplexity, heval⟩
  refine ⟨{
    L := L
    lie := lie
    algebra := algebra
    dim := dim
    topology := topology
    topologicalAdd := topologicalAdd
    continuousSMul := continuousSMul
    hausdorff := hausdorff
    model := D.raiseStep hdegree
    test := T.raiseStep hdegree
    positive := T.raiseStep_unit_interval hdegree hpositive
    complexity := T.raiseStep_complexity hdegree hp hcomplexity
    eval := ?_ }⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
  exact heval x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RefilteredKernelConstantBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

include hφ in

theorem realificationLieHom_layer_surjective
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (j : ℕ) (y : ℝ ⊗[ℚ] M) (hy : y ∈ G.realification.layer j) :
    ∃ x ∈ F.realification.layer j, realificationLieHom φ x = y := by
  have hmap : (F.layer j).map φ.toLinearMap = G.layer j := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hφ j x hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hsurj j y hy
      exact ⟨x, hx, hxy⟩
  have hreal : ((F.layer j).baseChange ℝ).map (φ.toLinearMap.baseChange ℝ) =
      (G.layer j).baseChange ℝ := by
    rw [← realification_map, hmap]
  change y ∈ (G.layer j).baseChange ℝ at hy
  rw [← hreal] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨x, hx, hxy⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelProjectionPresentPivotIdeal
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

namespace NilpotentLieFiltration

variable {L Y : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing Y] [LieAlgebra ℚ Y] {s r : ℕ}
    (F : NilpotentLieFiltration L s) (φ : L →ₗ⁅ℚ⁆ Y)
    (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J)

theorem pivotAnnihilatorIdeal_presentPivots_toSubmodule :
    (F.pivotAnnihilatorIdeal φ (fun k => eta (kernelProjectionSelectedPivot code k))
      (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList).toSubmodule =
      frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code := by
  exact finiteFrequencyKernel_presentPivots
    (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code

theorem pivotAnnihilatorIdeal_presentPivots
    (hK : frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code ≤
      F.layer s) :
    F.pivotAnnihilatorIdeal φ (fun k => eta (kernelProjectionSelectedPivot code k))
      (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList =
      F.topSubspaceIdeal
        (frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code) hK := by
  ext x
  change x ∈ (F.pivotAnnihilatorIdeal φ
    (fun k => eta (kernelProjectionSelectedPivot code k))
    (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList).toSubmodule ↔
    x ∈ frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code
  rw [F.pivotAnnihilatorIdeal_presentPivots_toSubmodule φ eta code]

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExternalPhysicalMemberPivotMasks
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_uniform_controlled_vertical_operators {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (δ : ℝ) (hδ : 0 < δ) (hδp : δ⁻¹ ≤ Real.exp p) :
    letI := D.metricSpace
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (η : J → L →ₗ[ℚ] ℚ) (V : J → (D.Space → ℂ) → D.Space → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j (f g : D.Space → ℂ) (K H : ℝ≥0), LipschitzWith K f → LipschitzWith H g →
        ∀ ε : ℝ, (∀ x, ‖f x - g x‖ ≤ ε) → ∀ x, ‖V j f x - V j g x‖ ≤ ε) ∧
      ∀ (f : D.Space → ℂ) (K B : ℝ≥0), LipschitzWith K f → (∀ x, ‖f x‖ ≤ B) →
        (K : ℝ) ≤ Real.exp p →
        (∀ j, LipschitzWith K (V j f) ∧ (∀ x, ‖V j f x‖ ≤ B)) ∧
        (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          V j f (z • x) = character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * V j f x) ∧
        (∀ (z : D.RealGroup) (c : ℂ), (∀ x, f (z • x) = c * f x) →
          ∀ j x, V j f (z • x) = c * V j f x) ∧
        ∀ x, ‖(∑ j, V j f x) - f x‖ ≤ δ := by
  classical
  let := D.metricSpace
  obtain ⟨b, w, N, hlayers, _, hbinv, hN, hNp, _, _, A, hcomm, horbit, hact⟩ :=
    D.exists_controlled_central_actions hp hD
  let S : Set (Fin (finrank ℚ L)) := {j | s ≤ w j}
  let q := centralActionBudget p
  have hq : 0 ≤ q := centralActionBudget_nonneg hp
  have hpq : p ≤ q := le_centralActionBudget hp
  have hd : (Fintype.card S : ℝ) ≤ p := by
    apply (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hD.1
  let O : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos q).le⟩
  obtain ⟨J, inst, ν, V, hcard, hν, hcontract, hdecomp⟩ :=
    exists_uniform_controlled_commuting_circle_operators A hcomm O horbit δ q hδ hq
      (hd.trans hpq) le_rfl (hδp.trans (Real.exp_le_exp.mpr hpq))
  let η : J → L →ₗ[ℚ] ℚ := fun j => basisFrequency b S N (ν j)
  let R : ℝ := (2 * q + 2) ^ 4 + q + (p + 3) ^ 5
  have hpow : 0 ≤ (p + 3) ^ 5 := by positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hqR : q ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hfreq : (2 * q + 2) ^ 4 ≤ R := by dsimp [R]; linarith
  have hbas : (p + 3) ^ 5 ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hNq : (p + 3) ^ 9 ≤ q := by dsimp [q, centralActionBudget]; linarith
  have hterm : 2 * q * (2 * q + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ _ + (R + 2) ^ 4
    exact le_add_of_nonneg_right (by positivity)
  have hheight : (R + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ 2 * q * (2 * q + 2) ^ 4 + _
    have h : 0 ≤ 2 * q * (2 * q + 2) ^ 4 := by positivity
    linarith
  have hcentral (i : S) (z : L) : ⁅b i, z⁆ = 0 := by
    apply D.filtration.top_layer_central
    rw [hlayers s]
    exact Submodule.subset_span ⟨i, i.property, rfl⟩
  have hucentral (i : S) (z : ℝ ⊗[ℚ] L) : ⁅(N : ℝ) • b.baseChange ℝ i, z⁆ = 0 :=
    scaled_real_basis_central b i (hcentral i) N z
  refine ⟨J, inst, η, V, hcard.trans (Real.exp_le_exp.mpr hterm), ?_, hcontract, ?_⟩
  · intro j i
    exact (basisFrequency_logHeight_le D.basis b S N hN (ν j) hR (hd.trans (hpq.trans hqR))
      (hNp.trans (Real.exp_le_exp.mpr (hNq.trans hqR)))
      (fun a => (hν j a).trans (Real.exp_le_exp.mpr hfreq))
      (fun a c => (hbinv a c).trans hbas) i).trans hheight
  · intro f K B hf hb hK
    obtain ⟨hv, hchar, hpres, herr⟩ :=
      hdecomp f K B hf hb (hK.trans (Real.exp_le_exp.mpr hpq))
    refine ⟨hv, ?_, ?_, herr⟩
    · intro j z hz x
      apply central_span_character (fun i : S => (N : ℝ) • b.baseChange ℝ i) hucentral
        (realifyFunctional (η j)) (V j f) ?_ ?_ x
      · intro i r y
        have h := hchar j i (r : CircleFourier.Circle) y
        rw [hact] at h
        change _ = character ((r * realifyFunctional (basisFrequency b S N (ν j))
          ((N : ℝ) • b.baseChange ℝ i) : ℝ) : CircleFourier.Circle) * _
        rw [realify_basisFrequency_direction b S N hN (ν j) i]
        simpa only [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm] using h
      · exact D.filtration.realLayer_le_span_scaled_basis b s S (hlayers s) N hN hz
    · intro z c hc
      apply hpres (fun x => z • x) c ?_ hc
      intro i t x
      obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
      rw [hact, hact, ← mul_smul, ← mul_smul]
      rw [(realBCHLine_commute _ (hucentral i) r z).eq]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem contractiveFamily_integer_error {J : Type*} [Fintype J]
    (T : X → D.Niltest w) (U : J → X → D.Niltest w)
    (hU : ∀ j a, (U j a).orbit = (T a).orbit) (δ : ℝ)
    (herr : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) :
    ∀ a (x : σ → ℤ), ‖(T a).eval x - ∑ j, (U j a).eval x‖ ≤ δ := by
  intro a x
  simpa only [Niltest.eval, hU] using
    herr a (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x (T a).orbit))

theorem contractiveFamily_real_error {J : Type*} [Fintype J]
    (T : X → D.Niltest w) (U : J → X → D.Niltest w)
    (hU : ∀ j a, (U j a).orbit = (T a).orbit) (δ : ℝ)
    (herr : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) :
    ∀ a (x : σ → ℝ), ‖(T a).evalReal x - ∑ j, (U j a).evalReal x‖ ≤ δ := by
  intro a x
  simpa only [Niltest.evalReal, hU] using
    herr a (QuotientGroup.mk (D.filtration.realification.polynomialOrbitRealEval w x (T a).orbit))

theorem exists_externalFamily_contractive_vertical_expansion {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (T : X → D.Niltest w)
    (hT : ∀ a, (T a).ComplexityLE p) (δ : ℝ) (hδ : 0 < δ)
    (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j a, (U j a).ComplexityLE p ∧ (U j a).orbit = (T a).orbit ∧
        (U j a).normBound = (T a).normBound ∧ (U j a).lipBound = (T a).lipBound) ∧
      (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j a).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
            (U j a).observable x) ∧
      (∀ j a, (∃ x, (U j a).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (eta j) z.coord = n) ∧
      (∀ a (z : D.RealGroup) (c : ℂ),
        (∀ x, (T a).observable (z • x) = c * (T a).observable x) →
          ∀ j x, (U j a).observable (z • x) = c * (U j a).observable x) ∧
      (∀ j a b (ε : ℝ), (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
        ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε) ∧
      (∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ) ∧
      (∀ a (x : σ → ℤ), ‖(T a).eval x - ∑ j, (U j a).eval x‖ ≤ δ) ∧
      ∀ a (x : σ → ℝ), ‖(T a).evalReal x - ∑ j, (U j a).evalReal x‖ ≤ δ := by
  classical
  let := D.metricSpace
  obtain ⟨J, inst, eta, V, hcard, hheight, hcontract, hdecomp⟩ :=
    D.exists_uniform_controlled_vertical_operators hp hD δ hδ hδp
  have hK (a : X) : ((T a).lipBound : ℝ) ≤ Real.exp p := by
    have h := Niltest.observable_budget (hT a)
    have hB := (T a).normBound.coe_nonneg
    linarith
  have hprops := fun a =>
    hdecomp (T a).observable (T a).lipBound (T a).normBound
      (T a).lipschitz (T a).norm_le (hK a)
  let v : X → J → D.Space → ℂ := fun a j => V j (T a).observable
  have hv := fun a => (hprops a).1
  have hchar := fun a => (hprops a).2.1
  have hpres := fun a => (hprops a).2.2.1
  have herr := fun a => (hprops a).2.2.2
  let U : J → X → D.Niltest w := fun j a =>
    { orbit := (T a).orbit
      observable := v a j
      normBound := (T a).normBound
      lipBound := (T a).lipBound
      norm_le := (hv a j).2
      lipschitz := (hv a j).1 }
  have herror : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ δ := by
    intro a x
    simpa only [norm_sub_rev] using herr a x
  refine ⟨J, inst, eta, U, hcard, hheight, fun _ a => ⟨hT a, rfl, rfl, rfl⟩,
    fun j a => hchar a j, ?_, hpres, ?_, herror,
    contractiveFamily_integer_error D T U (fun _ _ => rfl) δ herror,
    contractiveFamily_real_error D T U (fun _ _ => rfl) δ herror⟩
  · intro j a hne z hz hGamma
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v a j)
      (hchar a j) hne z hz hGamma
  · intro j a b ε hab x
    exact hcontract j (T a).observable (T b).observable (T a).lipBound (T b).lipBound
      (T a).lipschitz (T b).lipschitz ε hab x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyPrecenterProjectionData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L σ G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem kernelProjection_orbit (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) :
    (T.kernelProjection K hK).orbit = T.orbit := rfl

theorem kernelProjection_congr (T : D.Niltest w) {K K' : Submodule ℚ L}
    (hK : K ≤ D.filtration.layer s) (hK' : K' ≤ D.filtration.layer s) (h : K = K') :
    T.kernelProjection K hK = T.kernelProjection K' hK' := by
  subst K'
  rfl

theorem kernelProjection_complexity (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.kernelProjection K hK).ComplexityLE p := hT

theorem kernelProjection_unitInterval (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) (hT : T.UnitIntervalValued) :
    (T.kernelProjection K hK).UnitIntervalValued := by
  unfold kernelProjection
  exact T.averageCircles_unit_interval _ _ hT

theorem kernelProjection_invariant (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (z : D.RealGroup) (hz : z.coord ∈ K.baseChange ℝ) (x : D.Space) :
    (T.kernelProjection K hK).observable (z • x) = (T.kernelProjection K hK).observable x := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  apply D.invariant_of_kernel_circles K hK b _ _ z hz x
  intro i t y
  apply T.averageCircles_invariant
  · dsimp only
    intro j _ k _
    exact D.centralRationalCircle_commutes (b j).val (b k).val (hK (b j).property) (hK (b k).property)
  · simp

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators

variable {L σ X G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_external_family_centralRationalCircle_frequency
    (v : L) (hv : v ∈ D.filtration.layer s)
    (eta : L →ₗ[ℚ] ℚ) (f : X → D.Space → ℂ)
    (hf : ∀ a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      f a (z • x) =
        character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * f a x) :
    let := D.metricSpace
    ∃ n : ℤ,
      (∀ a t x, f a ((D.centralRationalCircle v hv).act t x) =
        character (n • t) * f a x) ∧
      (eta v = 0 → n = 0) := by
  classical
  let := D.metricSpace
  by_cases hz : ∀ a x, f a x = 0
  · exact ⟨0, fun a t x => by simp [hz], fun _ => rfl⟩
  push Not at hz
  obtain ⟨a, x, hax⟩ := hz
  obtain ⟨n, hn⟩ := vertical_frequency_integral_on_lattice D.filtration D.realLattice
    eta (f a) (hf a) ⟨x, hax⟩ (⟨D.periodicRealDirection v⟩ : D.RealGroup)
    (D.periodicRealDirection_mem_top v hv) (D.periodicRealDirection_mem_lattice v)
  refine ⟨n, ?_, ?_⟩
  · intro a t x
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [D.centralRationalCircle_act_coe]
    have hr : realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.periodicRealDirection v) r ∈ D.filtration.realification.subgroup s := by
      change r • D.periodicRealDirection v ∈ D.filtration.realLayer s
      exact (D.filtration.realLayer s).smul_mem r (D.periodicRealDirection_mem_top v hv)
    rw [hf a _ hr]
    apply congrArg (fun z : CircleFourier.Circle => character z * f a x)
    change ((realifyFunctional eta (r • D.periodicRealDirection v) : ℝ) : CircleFourier.Circle) =
      n • (r : CircleFourier.Circle)
    rw [map_smul, hn, ← AddCircle.coe_zsmul]
    congr 1
    simp only [smul_eq_mul, zsmul_eq_mul, mul_comm]
  · intro heta
    have hzero : realifyFunctional eta (D.periodicRealDirection v) = 0 := by
      simp [periodicRealDirection, realifyFunctional_tmul, heta]
    have hn0 : (n : ℝ) = 0 := hn.symm.trans hzero
    exact_mod_cast hn0

namespace Niltest

theorem external_family_kernelProjection_tested_error [Fintype G]
    (T : X → D.Niltest w) (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    {J : Type*} [Fintype J] (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
    (hvertical : ∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j a).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
          (U j a).observable x)
    (law : FiniteProbabilityWeights G) (physical : G → X)
    (path : G → D.Space) (weight : G → ℂ)
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ rho)
    (js : List J)
    (hsignificant : ∀ j,
      tau < ‖law.complexMean (fun x => weight x * (U j (physical x)).observable (path x))‖ →
        j ∈ js) :
    ‖law.complexMean (fun x => weight x * (T (physical x)).observable (path x)) -
      law.complexMean (fun x => weight x *
        ((T (physical x)).kernelProjection (finiteFrequencyKernel P eta js)
          ((finiteFrequencyKernel_le P eta js).trans hP)).observable (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let K := finiteFrequencyKernel P eta js
  have hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P eta js).trans hP
  let b := Module.finBasis ℚ K
  let A := fun i => D.centralRationalCircle (b i).val (hK (b i).property)
  have hfreq (j : J) (i : Fin (finrank ℚ K)) : ∃ n : ℤ,
      (∀ a t x, (U j a).observable ((A i).act t x) =
        character (n • t) * (U j a).observable x) ∧
      (eta j (b i).val = 0 → n = 0) :=
    exists_external_family_centralRationalCircle_frequency (b i).val (hK (b i).property)
      (eta j) (fun a => (U j a).observable) (hvertical j)
  choose n heigen hzero using hfreq
  apply iteratedCircleAverage_family_tested_weighted_error law A
    (List.finRange (finrank ℚ K)) (fun a => (T a).observable)
    (fun j a => (U j a).observable) n physical path weight
    (fun a => (T a).lipBound) (fun j a => (U j a).lipBound)
    (fun a => (T a).lipschitz) (fun j a => (U j a).lipschitz)
    hB htau hweight happrox (fun j i _ t a x => heigen j i a t x)
  intro j hj
  apply le_of_not_gt
  intro hlarge
  apply hj
  intro i _
  apply hzero j i
  exact ((mem_finiteFrequencyKernel P eta js (b i).val).mp (b i).property).2 j
    (hsignificant j hlarge)

end Niltest

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier MeasureTheory
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def kernelProjectionCircleFamily (K : Submodule ℚ L)
    (hK : K ≤ D.filtration.layer s) :
    let := D.metricSpace
    Fin (finrank ℚ K) → IsometricCircleAction D.Space := by
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact fun i => D.centralRationalCircle (Module.finBasis ℚ K i)
    (hK (Module.finBasis ℚ K i).property)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_external_family_common_positive_kernel_projection
    {L σ X Ω G J : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype G] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : X → D.Niltest w) (hT : ∀ x, (T x).UnitIntervalValued)
    {p : ℝ} (hTc : ∀ x, (T x).ComplexityLE p)
    (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s)
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
    (hvertical : ∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j a).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
          (U j a).observable x)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
    (path : Ω → G → D.Space) (weight : Ω → G → ℂ)
    {B rho tau delta : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ a x, ‖weight a x‖ ≤ B)
    (happrox : ∀ a x, ‖(T a).observable x - ∑ j, (U j a).observable x‖ ≤ rho)
    (hscore : ∀ a ∈ productive,
      delta ≤ ((localLaw a).complexMean (fun x =>
        weight a x * (T (physical a x)).observable (path a x))).re)
    (hsmall : 2 * B * rho + Fintype.card J * tau ≤ delta / 2) :
    ∃ (code : Fin (finrank ℚ P) → Option J) (S : X → D.Niltest w)
      (retained : Finset Ω),
      (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
        ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
      (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE p ∧ (S x).orbit = (T x).orbit) ∧
      (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
        ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
      retained ⊆ productive ∧
      outer.mass productive / (Fintype.card J + 1) ^ finrank ℚ P ≤ outer.mass retained ∧
      ∀ a ∈ retained,
        (∀ i j, code i = some j →
          tau < ‖(localLaw a).complexMean (fun x =>
            weight a x * (U j (physical a x)).observable (path a x))‖) ∧
        delta / 2 ≤ ((localLaw a).complexMean (fun x =>
          weight a x * (S (physical a x)).observable (path a x))).re := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let js : Ω → List J := fun a => (Finset.univ.filter (fun j =>
    tau < ‖(localLaw a).complexMean (fun x =>
      weight a x * (U j (physical a x)).observable (path a x))‖)).toList
  obtain ⟨code, retained, hretained, hmass, hcode⟩ :=
    exists_common_frequency_kernel outer productive P eta js
  let K := frequencyCodeKernel P eta code
  have hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans hP
  let S := fun x => (T x).kernelProjection K hK
  refine ⟨code, S, retained, fun _ => rfl, ?_, ?_, hretained, hmass, ?_⟩
  · intro x
    exact ⟨(T x).kernelProjection_unitInterval K hK (hT x),
      (T x).kernelProjection_complexity K hK (hTc x), (T x).kernelProjection_orbit K hK⟩
  · intro a z hz x
    exact (T a).kernelProjection_invariant K hK z hz x
  · intro a ha
    obtain ⟨hpivots, hk⟩ := hcode a ha
    have hsignificant (j : J)
        (hj : tau < ‖(localLaw a).complexMean (fun x =>
          weight a x * (U j (physical a x)).observable (path a x))‖) : j ∈ js a := by
      simpa only [js, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    have herr := external_family_kernelProjection_tested_error T P hP eta U hvertical
      (localLaw a) (physical a) (path a) (weight a) hB htau (hweight a) happrox
      (js a) hsignificant
    have hproj (x : X) : (T x).kernelProjection (finiteFrequencyKernel P eta (js a))
        ((finiteFrequencyKernel_le P eta (js a)).trans hP) = S x :=
      (T x).kernelProjection_congr _ hK hk
    simp_rw [hproj] at herr
    refine ⟨?_, ?_⟩
    · intro i j hij
      simpa only [js, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
        using hpivots i j hij
    · have hr := Complex.re_le_norm
        ((localLaw a).complexMean (fun x => weight a x * (T (physical a x)).observable (path a x)) -
          (localLaw a).complexMean (fun x => weight a x * (S (physical a x)).observable (path a x)))
      rw [Complex.sub_re] at hr
      have hs := hscore a (hretained ha)
      linarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3
open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_external_family_precenter_kernel_projection_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : X → D.Niltest w) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (∀ x, (T x).UnitIntervalValued) → (∀ x, (T x).ComplexityLE p) →
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j x, (U j x).ComplexityLE ((p + 2) ^ C) ∧
          (U j x).orbit = (T x).orbit ∧ (U j x).normBound = (T x).normBound ∧
          (U j x).lipBound = (T x).lipBound) ∧
        (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j a).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
              (U j a).observable x) ∧
        (∀ j a b (ε : ℝ),
          (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
          ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε) ∧
      ∀ {Ω G : Type*} [Fintype Ω] [Fintype G],
      ∀ (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s),
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
        (path : Ω → G → D.Space) (weight : Ω → G → ℂ),
      (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
      (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
        (fun x => weight a x * (T (physical a x)).observable (path a x))).re) →
      ∃ (code : Fin (finrank ℚ P) → Option J) (S : X → D.Niltest w)
        (retained : Finset Ω),
        (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE ((p + 2) ^ C) ∧
          (S x).orbit = (T x).orbit) ∧
        (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
          ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
        (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
          ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained,
          (∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
            ‖(localLaw a).complexMean (fun x =>
              weight a x * (U j (physical a x)).observable (path a x))‖) ∧
          Real.exp (-((p + 2) ^ C)) ≤ ((localLaw a).complexMean
            (fun x => weight a x * (S (physical a x)).observable (path a x))).re := by
  let R : Polynomial ℕ := Polynomial.X
  let Q := 2 * R + 8
  let A := (Q + 3) ^ 9 + 2 * Q + 2
  let V := 2 * A * (2 * A + 2) ^ 4 + ((2 * A + 2) ^ 4 + A + (Q + 3) ^ 5 + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Q + 2 * V + R + 10 + R * (V + 1))
  refine ⟨C, hC, ?_⟩
  intro L σ X _ _ s d _ _ _ _ D w T p hp hD hT hTc
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let q := 2 * p + 8
  let v := verticalDecompositionBudget q
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hv : 0 ≤ v := verticalDecompositionBudget_nonneg hq
  have hprod : 0 ≤ p * (v + 1) := by positivity
  have hb : q + 2 * v + p + 10 + p * (v + 1) ≤ (p + 2) ^ C := by
    simpa [R, Q, A, V, q, v, verticalDecompositionBudget, centralActionBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  have hvC : v ≤ (p + 2) ^ C := by linarith
  have htC : p + v + 8 ≤ (p + 2) ^ C := by linarith
  have hnC : p * (v + 1) ≤ (p + 2) ^ C := by linarith
  have hsC : p + 1 ≤ (p + 2) ^ C := by linarith
  obtain ⟨J, inst, eta, U, hJ, hheight, hU, hvert, hint, hchar, hcontract, happrox, hintError, hrealError⟩ :=
    D.exists_externalFamily_contractive_vertical_expansion hq (hD.mono D hpq) T
      (fun x => (hTc x).mono hpq) (Real.exp (-q)) (Real.exp_pos (-q))
      (by rw [Real.exp_neg, inv_inv])
  let _ := inst
  refine ⟨J, inst, eta, U,
    hJ.trans (Real.exp_le_exp.mpr hvC), fun j i => (hheight j i).trans hvC,
    fun j x => ⟨(hU j x).1.mono hqC, (hU j x).2⟩, hvert, hcontract, ?_⟩
  intro Ω G _ _ P hP outer productive localLaw physical path weight hweight hscore
  have hsmall := frequency_projection_error_bound hp hJ
  obtain ⟨code, S, retained, hidentity, hS, hSinv, hretained, hmass, hlocal⟩ :=
    RationalFilteredNilmanifold.Niltest.exists_external_family_common_positive_kernel_projection
      T hT hTc P hP eta U hvert outer productive localLaw physical path weight
      (Real.exp_nonneg p) (Real.exp_nonneg (-(p + v + 8))) hweight happrox hscore hsmall
  have hdim : (finrank ℚ P : ℝ) ≤ p := by
    have h := Submodule.finrank_le P
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at h
    exact (Nat.cast_le.mpr h).trans hD.1
  refine ⟨code, S, retained,
    fun x => ⟨(hS x).1, (hS x).2.1.mono (hpq.trans hqC), (hS x).2.2⟩,
    hidentity, hSinv, hretained, ?_, ?_⟩
  · exact (mass_div_frequency_count (outer.mass_nonneg productive) hp hv hdim hJ hnC).trans hmass
  · intro a ha
    obtain ⟨hpivot, hpositive⟩ := hlocal a ha
    refine ⟨fun i j hij => (Real.exp_le_exp.mpr (neg_le_neg htC)).trans_lt (hpivot i j hij), ?_⟩
    exact ((Real.exp_le_exp.mpr (by linarith : -((p + 2) ^ C) ≤ -p - 1)).trans
      (exp_sub_one_le_half_exp (-p))).trans hpositive

end Erdos3

end

section

namespace Erdos3
open Module CircleFourier
open scoped TensorProduct BigOperators Classical

attribute [instance] ExternalFamilyPrecenterProjectionData.instFintype

theorem exists_externalFamilyPrecenterProjectionData :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : X → D.Niltest w) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (∀ x, (T x).UnitIntervalValued) → (∀ x, (T x).ComplexityLE p) →
      Nonempty (ExternalFamilyPrecenterProjectionData T p ((p + 2) ^ C)) := by
  obtain ⟨C, hC, hproduce⟩ := exists_external_family_precenter_kernel_projection_budget
  refine ⟨C, hC, ?_⟩
  intro L σ X _ _ s d _ _ _ _ D w T p hp hD hT hTc
  obtain ⟨J, inst, eta, U, hJ, hheight, hU, hvert, hcontract, hselect⟩ :=
    hproduce T p hp hD hT hTc
  exact ⟨{
    Freq := J
    instFintype := inst
    eta := eta
    U := U
    card_bound := hJ
    eta_height := hheight
    U_bounds := hU
    vertical := hvert
    contractive := hcontract
    select := hselect }⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration VectorPolynomial

variable {L M ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d f nE nF : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (Fmark : RationalFilteredNilmanifold M (s + 1) f)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nE)
  (hE : E.filtration = D.filtration.gradedRefiltration W)
  (EF : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
  (hEF : EF.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

include hE hEF

theorem refilteredMarkedMap_mem_layer (j : ℕ)
    (x : D.filtration.gradedRefiltrationSubalgebra W) (hx : x ∈ E.filtration.layer j) :
    D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W x ∈ EF.filtration.layer j := by
  rw [hE] at hx
  rw [hEF]
  exact D.filtration.gradedRefiltrationMap_mem_layer Fmark.filtration φ hφ W j x hx

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

noncomputable def markedTopQuotientDiagram (x : D.RealGroup) : Q.Space × E.Space :=
  (QuotientGroup.mk (realificationMap
    (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := Q.filtration.lowerCentralSeries_eq_bot)
    (lieQuotientMap (D.filtration.layerIdeal (s + 1))) x),
   QuotientGroup.mk (realificationMap
    (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ x))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionOriginalOrbit
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration
open scoped TensorProduct BigOperators

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
  [T2Space (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]

theorem optionOriginalSpaceProjection_lipschitz :
    letI := (optionProduct D₀ D).metricSpace
    letI := D₀.metricSpace
    LipschitzWith (coordinateLipschitzBound d₀
      (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1)
      (optionOriginalSpaceProjection D₀ D) := by
  exact productProjection_lipschitz (optionFactors D₀ D) none

end Metric

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
    {s d₀ : ℕ} {d : ι → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    {P : Type*} (observable : P → D₀.Space → ℂ)

theorem optionOriginalObservable_unit_interval
    (hunit : ∀ a y, (observable a y).im = 0 ∧
      0 ≤ (observable a y).re ∧ (observable a y).re ≤ 1) :
    ∀ a y, (optionOriginalObservable D₀ D observable a y).im = 0 ∧
      0 ≤ (optionOriginalObservable D₀ D observable a y).re ∧
      (optionOriginalObservable D₀ D observable a y).re ≤ 1 := by
  intro a y
  exact hunit a (optionOriginalSpaceProjection D₀ D y)

theorem optionOriginalObservable_member_net (sites : Set P) {n : ℕ}
    (centers : Fin n → {a : P // a ∈ sites}) (η : ℝ)
    (hnet : ∀ a ∈ sites, ∃ i, ∀ y,
      ‖observable a y - observable (centers i).val y‖ ≤ η) :
    ∀ a ∈ sites, ∃ i, ∀ y,
      ‖optionOriginalObservable D₀ D observable a y -
        optionOriginalObservable D₀ D observable (centers i).val y‖ ≤ η := by
  intro a ha
  obtain ⟨i, hi⟩ := hnet a ha
  exact ⟨i, fun y => hi (optionOriginalSpaceProjection D₀ D y)⟩

theorem optionOriginalObservable_member_nets (sites : Set P) (entropy : ℝ → ℝ)
    (hnets : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y,
          ‖observable a y - observable (centers i).val y‖ ≤ η) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ entropy η ∧ ∃ centers : Fin n → {a : P // a ∈ sites},
        ∀ a ∈ sites, ∃ i, ∀ y,
          ‖optionOriginalObservable D₀ D observable a y -
            optionOriginalObservable D₀ D observable (centers i).val y‖ ≤ η := by
  intro η hη hη1
  obtain ⟨n, hn, centers, hnet⟩ := hnets η hη hη1
  exact ⟨n, hn, centers,
    optionOriginalObservable_member_net D₀ D observable sites centers η hnet⟩

noncomputable def optionOriginalAdaptedLipschitzBound (ℓ : ℝ≥0) (H : ℕ) : ℝ≥0 :=
  ℓ * coordinateLipschitzBound d₀
      (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1 *
    coordinateLipschitzBound
      (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)))
      (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) H

include D₀ D in

theorem optionOriginalAdaptedLipschitzBound_le_exp (ℓ : ℝ≥0) (H : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hd₀ : (d₀ : ℝ) ≤ p)
    (htotal : (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)) : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (optionOriginalAdaptedLipschitzBound (L₀ := L₀) (L := L)
      (d₀ := d₀) (d := d) ℓ H : ℝ) ≤ Real.exp (p + 2 * (p + 2) ^ 2) := by
  have hfin : (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i) : ℝ) ≤ p := by
    simpa only [finrank_eq_card_basis (optionProduct D₀ D).basis, Fintype.card_fin] using htotal
  have hproj := coordinateLipschitzBound_le_exp d₀
    (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1 hp hd₀ htotal
    (by simpa only [NNReal.coe_one] using Real.one_le_exp_iff.mpr hp)
  have hbase := coordinateLipschitzBound_le_exp
    (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i)))
    (finrank ℚ (∀ i : Option ι, optionLieSpace L₀ L i)) H hp htotal hfin hH
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 2) * Real.exp ((p + 2) ^ 2) := by
      exact mul_le_mul (mul_le_mul hℓ hproj (NNReal.coe_nonneg _) (Real.exp_pos _).le)
        hbase (NNReal.coe_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    [TopologicalSpace (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]
    [T2Space (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i))]

theorem optionOriginalObservable_lipschitz (ℓ : ℝ≥0)
    (hLip : ∀ a, letI := D₀.metricSpace; LipschitzWith ℓ (observable a)) :
    ∀ a, letI := (optionProduct D₀ D).metricSpace
      LipschitzWith (ℓ * coordinateLipschitzBound d₀
        (Fintype.card (Σ i : Option ι, Fin (optionDimension d₀ d i))) 1)
        (optionOriginalObservable D₀ D observable a) := by
  intro a
  let := D₀.metricSpace
  let := (optionProduct D₀ D).metricSpace
  exact (hLip a).comp (optionOriginalSpaceProjection_lipschitz D₀ D)

end Metric

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeModelOrbit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s d)

structure NativeModelEquiv where
  toLieEquiv : L ≃ₗ⁅ℚ⁆ M
  map_basis : ∀ i, toLieEquiv (D.basis i) = E.basis i
  mem_layer : ∀ n x, toLieEquiv x ∈ E.filtration.layer n ↔ x ∈ D.filtration.layer n
  mem_lattice : ∀ g : D.filtration.Group,
    NilpotentLieBCHGroup.map toLieEquiv.toLieHom g ∈ E.lattice ↔ g ∈ D.lattice

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShiftFailurePositiveBasis
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def mono {s N : ℕ} [NeZero N] {p q : ℝ} {a J : ZMod N → ℝ}
    (B : PositiveShiftBasis s N p a J) (hpq : p ≤ q) : PositiveShiftBasis s N q a J where
  L := B.L
  lie := B.lie
  algebra := B.algebra
  dim := B.dim
  topology := B.topology
  topologicalAdd := B.topologicalAdd
  continuousSMul := B.continuousSMul
  hausdorff := B.hausdorff
  model := B.model
  geometry := B.geometry.mono B.model hpq
  count := B.count
  count_le_dim := B.count_le_dim
  shifts := B.shifts
  shifts_nonempty := B.shifts_nonempty
  shifts_large := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg N)).trans B.shifts_large
  frequency := B.frequency
  mode := B.mode
  test := B.test
  frequency_height := fun h hh j i => (B.frequency_height h hh j i).trans hpq
  mode_complexity := fun h hh j => (B.mode_complexity h hh j).mono hpq
  mode_orbit := B.mode_orbit
  mode_norm := B.mode_norm
  mode_vertical := B.mode_vertical
  mode_bias := fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans_lt (B.mode_bias h hh j)
  independent := B.independent
  test_positive := B.test_positive
  test_complexity := fun h hh => (B.test_complexity h hh).mono hpq
  test_invariant := B.test_invariant
  test_violation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans_lt (B.test_violation h hh)

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open scoped BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}

noncomputable def testingFamily (B : PositiveShiftBasis s N q a J) :
    ZMod N × Fin B.count → ZMod N → ℂ := by
  classical
  exact fun hk n => if hk.1 ∈ B.shifts then (B.mode hk.1 hk.2).evalCyclic N (fun _ => n) else 0

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftProductData
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold

variable {J σ : Type*} {L : Option (Option J ⊕ J) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : Option (Option J ⊕ J) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  {D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)} {w : σ → ℕ}

noncomputable def anchoredOptionReferenceData
    (P : (D none).Niltest w) (P₀ : (D (some (.inl none))).Niltest w)
    (A : ∀ j, (D (some (.inl (some j)))).Niltest w) (B : ∀ j, (D (some (.inr j))).Niltest w) :
    ∀ i, (D i).Niltest w
  | none => P
  | some (.inl none) => P₀
  | some (.inl (some j)) => A j
  | some (.inr j) => B j

end RationalFilteredNilmanifold
end Erdos3

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  (B : PositiveShiftBasis.{u} s N q a J)

abbrev anchoredLieSpace (L M : Fin B.count → Type u) :=
  optionLieSpace B.L (sumLieSpace (optionLieSpace B.L L) M)

abbrev anchoredDimension (d e : Fin B.count → ℕ) :=
  optionDimension B.dim (Sum.elim (optionDimension B.dim d) e)

variable {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))

noncomputable def anchoredFactors : ∀ i : Option (Option (Fin B.count) ⊕ Fin B.count),
    RationalFilteredNilmanifold (B.anchoredLieSpace L M i) s (B.anchoredDimension d e i) :=
  optionFactors B.model (sumFactors (optionFactors B.model D) E)

def anchoredWeights (w : Fin B.dim → ℕ) (v : ∀ j, Fin (d j) → ℕ) (v' : ∀ j, Fin (e j) → ℕ) :
    ∀ i, Fin (B.anchoredDimension d e i) → ℕ
  | none => w
  | some (.inl none) => w
  | some (.inl (some j)) => v j
  | some (.inr j) => v' j

theorem anchoredFactors_layers (w : Fin B.dim → ℕ) (v : ∀ j, Fin (d j) → ℕ) (v' : ∀ j, Fin (e j) → ℕ)
    (hw : ∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i}))
    (hv : ∀ j k, (D j).filtration.layer k = Submodule.span ℚ ((D j).basis '' {i | k ≤ v j i}))
    (hv' : ∀ j k, (E j).filtration.layer k = Submodule.span ℚ ((E j).basis '' {i | k ≤ v' j i})) :
    ∀ i k, (B.anchoredFactors D E i).filtration.layer k =
      Submodule.span ℚ ((B.anchoredFactors D E i).basis '' {j | k ≤ B.anchoredWeights w v v' i j}) := by
  intro i k
  rcases i with _ | ((_ | j) | j)
  · exact hw k
  · exact hw k
  · exact hv j k
  · exact hv' j k

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPolynomialGroupMapBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ)

theorem polynomialRationalGrid_inv (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w l g) :
    F.PolynomialRationalGrid b w l g⁻¹ := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun z => -a z, funext fun z => ?_⟩
  change ((-a z : ℤ) : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
    (coefficients ((g⁻¹).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [coord_inv]
  change ((-a z : ℤ) : ℝ) = (l : ℝ) * (b.baseChange ℝ).repr
    (coefficients (-(g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))) z.1) z.2
  simp only [map_neg, Finsupp.neg_apply, Int.cast_neg, mul_neg]
  exact congrArg Neg.neg (congrFun ha z)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
namespace OAI

section

namespace Erdos3

open Module

theorem exists_weighted_common_positive_nat {Ω : Type*} [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < outer.mass S)
    (n : Ω → ℕ) {p : ℝ} (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, n a = n a₀) ∧
      Real.exp (-p) * outer.mass S ≤ outer.mass T := by
  let A := Finset.Icc 1 ⌊Real.exp p⌋₊
  have hA : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp p := by
    simpa only [A, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] using
      (Nat.floor_le (Real.exp_nonneg p))
  obtain ⟨k, _, T, hTS, hT, hk, hlarge⟩ := exists_weighted_exponential_constant_fiber
    outer S hS n (A : Set ℕ) A.finite_toSet
    (fun a ha => Finset.mem_Icc.mpr ⟨(hn a ha).1, Nat.le_floor (hn a ha).2⟩) hA
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀,
    fun a ha => (hk a ha).trans (hk a₀ ha₀).symm, hlarge⟩

theorem exists_weighted_common_fast_subalgebra
    {Ω ι L : Type*} [Fintype Ω] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (outer : FiniteProbabilityWeights Ω)
    (S : Finset Ω) (hS : 0 < outer.mass S)
    (K : Ω → LieSubalgebra ℚ L) (m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      Real.exp (-((p + 2) ^ 5)) * outer.mass S ≤ outer.mass T := by
  have hmem : ∀ a ∈ S, K a ∈ heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊ := by
    intro a ha
    obtain ⟨v, hv, hh⟩ := hK a ha
    exact (mem_heightBoundedSubspaces e m ⌈Real.exp p⌉₊ (K a).toSubmodule).mpr
      ⟨v, hv, fun i j => rationalHeightLE_ceil_exp (hh i j)⟩
  have hcount : ((heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊).ncard : ℝ) ≤
      Real.exp ((p + 2) ^ 5) :=
    (heightBoundedLieSubalgebras_ncard_exp_bound e m hp).trans
      (Real.exp_le_exp.mpr (common_subalgebra_cost_le_budget m (Fintype.card ι)
        hp hm hd hp le_rfl))
  obtain ⟨U, _, T, hTS, hT, hU, hlarge⟩ := exists_weighted_exponential_constant_fiber
    outer S hS K (heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊)
    (finite_card_heightBoundedLieSubalgebras e m ⌈Real.exp p⌉₊).1 hmem hcount
  obtain ⟨a₀, ha₀⟩ := hT
  exact ⟨a₀, hTS ha₀, T, hTS, ha₀,
    fun a ha => (hU a ha).trans (hU a₀ ha₀).symm, hlarge⟩

theorem exists_weighted_common_fast_subalgebra_and_denominator
    {Ω ι L : Type*} [Fintype Ω] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (outer : FiniteProbabilityWeights Ω)
    (S : Finset Ω) (hS : 0 < outer.mass S)
    (K : Ω → LieSubalgebra ℚ L) (n : Ω → ℕ) (m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → L,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p)
    (hn : ∀ a ∈ S, 0 < n a ∧ (n a : ℝ) ≤ Real.exp p) :
    ∃ a₀ ∈ S, ∃ T : Finset Ω, T ⊆ S ∧ a₀ ∈ T ∧
      (∀ a ∈ T, K a = K a₀ ∧ n a = n a₀) ∧
      Real.exp (-((p + 2) ^ 5 + p)) * outer.mass S ≤ outer.mass T := by
  obtain ⟨b, _, U, hUS, hbU, hKsame, hUlarge⟩ :=
    exists_weighted_common_fast_subalgebra e outer S hS K m hp hm hd hK
  have hUpos : 0 < outer.mass U := (mul_pos (Real.exp_pos _) hS).trans_le hUlarge
  obtain ⟨a₀, haU, T, hTU, haT, hnsame, hTlarge⟩ :=
    exists_weighted_common_positive_nat outer U hUpos n (fun a ha => hn a (hUS ha))
  refine ⟨a₀, hUS haU, T, hTU.trans hUS, haT, ?_, ?_⟩
  · intro a ha
    exact ⟨(hKsame a (hTU ha)).trans (hKsame a₀ haU).symm, hnsame a ha⟩
  · calc
      Real.exp (-((p + 2) ^ 5 + p)) * outer.mass S =
          Real.exp (-p) * (Real.exp (-((p + 2) ^ 5)) * outer.mass S) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-p) * outer.mass U :=
        mul_le_mul_of_nonneg_left hUlarge (Real.exp_pos _).le
      _ ≤ outer.mass T := hTlarge

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {ι J σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (a : ι)

def HasFixedProductOrbitFactors
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (eta : J → L a →ₗ[ℚ] ℚ) (side : σ → ℝ) (p : ℝ) (m : ℕ)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) : Prop :=
  ∃ freq : J → ∀ i, L i →ₗ[ℚ] ℚ,
    (∀ j, freq j a = eta j) ∧
    (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional (piFrequency (freq j)) x = 0) ∧
    ∃ (κ : (pi D).RealGroup)
      (slow middle rat : ((pi D).filtration.realification.adaptedPolynomialFiltration
        (fun _ : σ => 1)).Group),
      κ ∈ (pi D).realLattice ∧
      slow * middle * rat * (pi D).filtration.realification.adaptedConstantGroupHom
        (fun _ : σ => 1) κ =
          ⟨⟨(piRealOrbit (fun i => (D i).filtration) g).log,
            (piRealOrbit (fun i => (D i).filtration) g).property⟩⟩ ∧
      (pi D).filtration.PolynomialSlowBound (pi D).basis (fun _ : σ => 1)
        side (Real.exp p) slow ∧
      (pi D).filtration.PolynomialRationalGrid (pi D).basis (fun _ : σ => 1) m rat ∧
      coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      coefficients (rat.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      (∀ α, coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
      (∀ t : σ → ℝ, eval₂ t (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) ∈
        realificationLieSubalgebra ((pi D).filtration.gradedRefiltrationSubalgebra W))

theorem HasFixedProductOrbitFactors.mono
    {g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1)}
    {eta : J → L a →ₗ[ℚ] ℚ} {side : σ → ℝ} {p q : ℝ} {m : ℕ}
    {W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded}
    (h : HasFixedProductOrbitFactors D a g eta side p m W)
    (hpq : p ≤ q) (hside : ∀ i, 0 < side i) :
    HasFixedProductOrbitFactors D a g eta side q m W := by
  obtain ⟨freq, hf, hv, κ, slow, middle, rat, hκ, heq, hs, hr, hm0, hr0, hc, ht⟩ := h
  exact ⟨freq, hf, hv, κ, slow, middle, rat, hκ, heq,
    (pi D).filtration.polynomialSlowBound_mono (pi D).basis (fun _ => 1) side hside
      (Real.exp_le_exp.mpr hpq) slow hs, hr, hm0, hr0, hc, ht⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PositiveCyclicCoordinateProduct
namespace OAI

section

universe u

namespace Erdos3.PositiveCyclicModel

open scoped TensorProduct

attribute [local instance] PositiveCyclicModel.lie PositiveCyclicModel.algebra
  PositiveCyclicModel.topology PositiveCyclicModel.topologicalAdd
  PositiveCyclicModel.continuousSMul PositiveCyclicModel.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℝ}
  (R : PositiveCyclicModel.{u} s N p f) {σ : Type*} [Fintype σ]

noncomputable def coordinateTest (i : σ) : R.model.Niltest (fun _ : σ => 1) :=
  R.test.linearPullbackHom (fun _ : Unit =>
    { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl })

theorem coordinateTest_eval (i : σ) (x : σ → ℤ) :
    (R.coordinateTest i).eval x = R.test.eval (fun _ => x i) := by
  exact R.test.eval_linearPullbackHom _ x

theorem coordinateTest_complexity (i : σ) :
    (R.coordinateTest i).ComplexityLE p := R.complexity

theorem coordinateTest_evalCyclic (i : σ) (x : σ → ZMod N) :
    (R.coordinateTest i).evalCyclic N x = (f (x i) : ℂ) := by
  change (R.coordinateTest i).eval (fun j => ((x j).val : ℤ)) = _
  rw [R.coordinateTest_eval]
  apply Complex.ext
  · exact (R.eval (x i)).symm
  · simpa only [Complex.ofReal_im] using
      (R.test.unit_interval_eval R.positive (fun _ => ((x i).val : ℤ))).1

end Erdos3.PositiveCyclicModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SingleRefilteredKernel
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)

noncomputable def refilteredComponentMap (b : ι) :
    ((pi D).filtration.gradedRefiltrationSubalgebra W) →ₗ⁅ℚ⁆ L b :=
  (liePiEval b).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl

noncomputable def nativeRefilteredTarget
    (Q : RationalFilteredNilmanifold
      (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n) :=
  optionProduct (Q.raiseStep (Nat.le_succ s)) (fun i : {i : ι // i ≠ a} => D i.val)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledSingleRefilteredReconstruction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def FixedPositiveNiltestRealization {σ K : Type*} [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {t d : ℕ}
    (V : RationalFilteredNilmanifold K t d) {w : σ → ℕ}
    (g : V.filtration.realification.PolynomialOrbit w) (cost : ℝ) (f : (σ → ℤ) → ℂ) : Prop :=
  ∃ U : V.Niltest w, U.orbit = g ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
    ∀ x, U.eval x = f x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalMarkedOrbitTranslation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}

theorem map_log_constantGroupOrbit_mul_of_realificationMap_eq_one
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ)
    (orbit : F.realification.PolynomialOrbit w) (z : F.realification.Group)
    (hz : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ z = 1) :
    VectorPolynomial.map (realLieHomToRat (realificationLieHom φ)).toLinearMap
        (F.realification.constantGroupOrbit w z * orbit).log =
      VectorPolynomial.map (realLieHomToRat (realificationLieHom φ)).toLinearMap orbit.log := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ
        (F.realification.polynomialOrbitRealEval w x
          (F.realification.constantGroupOrbit w z * orbit)) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
          (F.realification.polynomialOrbitRealEval w x orbit) := by
    rw [map_mul, polynomialOrbitRealEval_constantGroupOrbit, map_mul, hz, one_mul]
  have hc := congrArg NilpotentLieBCHGroup.coord he
  calc
    _ = realificationLieHom φ
        (eval₂ x (F.realification.constantGroupOrbit w z * orbit).log) :=
      eval₂_map (realificationLieHom φ).toLinearMap x _
    _ = realificationLieHom φ (eval₂ x orbit.log) := hc
    _ = _ := (eval₂_map (realificationLieHom φ).toLinearMap x orbit.log).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeMarkedPolynomialFreezing
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module NilpotentLieBCHGroup
open scoped TensorProduct
variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

theorem real_linear_section_rightInverse (φ : L →ₗ⁅ℚ⁆ M) (S : M →ₗ[ℚ] L)
    (hS : Function.RightInverse S φ) :
    Function.RightInverse (fun y : G.realification.Group =>
      (⟨S.baseChange ℝ y.coord⟩ : F.realification.Group))
      (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ) := by
  have hcomp : φ.toLinearMap.comp S = LinearMap.id := LinearMap.ext hS
  have hcompR := congrArg (fun f : M →ₗ[ℚ] M => f.baseChange ℝ) hcomp
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hcompR
  intro y
  apply NilpotentLieBCHGroup.ext
  exact DFunLike.congr_fun hcompR y.coord

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenMarkedLeftOrbitBound
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (w : σ → ℕ) (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)

theorem nativeFrozenMarkedOrbitCoordinates_realValue
    (g : F.realification.PolynomialOrbit w) (x : σ → ℝ) :
    F.adaptedPolynomialRealValueHom w x (F.realification.polynomialOrbitCoordinates w g) =
      F.realification.polynomialOrbitRealEval w x g := rfl

theorem nativeFrozenMarkedOrbitCoordinates_symm_realEval
    (g : (F.realification.adaptedPolynomialFiltration w).Group) (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      ((F.realification.polynomialOrbitCoordinates w).symm g) =
      F.adaptedPolynomialRealValueHom w x g := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem pointwiseSpanningIndex_card_le
    {σ κ γ M : Type*} [Fintype σ] [Fintype κ] [Fintype γ]
    [LieRing M] [LieAlgebra ℚ M] {t : ℕ}
    (G : NilpotentLieFiltration M t) (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) [Fintype (SymbolBasisIndex w ν)]
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p) :
    (Fintype.card (SymbolBasisIndex w ν × γ) : ℝ) ≤ pointwiseFastSectionInput t p :=
  (G.pointwiseSymbolSpanning_section_counts (ξ := γ) G c ν hG c ν hG w hw
    hp hκ hκ hγ hσ).1

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedRefilteredLowerNativeDiagram
namespace OAI


section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure AllocatedMarkedCoveredLowerDiagram (k q : ℕ) (p cost : ℝ) where
  Dref : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W)
    (s + 1) (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W))
  Dref_filtration : Dref.filtration = D.filtration.gradedRefiltration W
  Dref_lattice : Dref.lattice = D.lattice.comap
    (NilpotentLieBCHGroup.map
      (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra W).incl)
  Dref_geometry : Dref.GeometryComplexityLE cost
  inclusion_height : ∀ i j, rationalLogHeight (D.basis.repr (Dref.basis j : L) i) ≤ cost
  Fbase : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1)
    (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  Fbase_filtration : Fbase.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))
  Fbase_lattice : Fbase.lattice = Fmark.lattice.comap
    (NilpotentLieBCHGroup.map
      (hnil := (Fmark.filtration.gradedRefiltration
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).lowerCentralSeries_eq_bot)
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl)
  nQ : ℕ
  nQ_le : nQ ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)
  Qbase : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ
  Qbase_filtration : Qbase.filtration = Dref.filtration.quotientTop
  Qbase_lattice : Qbase.lattice = Dref.lattice.map
    (Dref.filtration.quotientStepHom (Dref.filtration.layerIdeal (s + 1)) le_rfl)
  Fref : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1)
    (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  Fref_filtration : Fref.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))
  Fref_basis : Fref.basis = Fbase.basis
  Fref_lattice : Fref.lattice ≤ Fbase.lattice
  Fref_geometry : Fref.GeometryComplexityLE cost
  marked_inclusion_height : ∀ i j,
    rationalLogHeight (Fmark.basis.repr (Fref.basis j : M) i) ≤ cost
  restricted_mark_height : ∀ i j, rationalLogHeight (Fref.basis.repr
    (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W (Dref.basis i)) j) ≤ cost
  Q : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ
  Q_filtration : Q.filtration = Dref.filtration.quotientTop
  Q_basis : Q.basis = Qbase.basis
  Q_lattice : Q.lattice ≤ Qbase.lattice
  Q_geometry : Q.GeometryComplexityLE cost
  quotient_height : ∀ i j, rationalLogHeight (Q.basis.repr
    (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)) (Dref.basis j)) i) ≤ cost
  refiltered_mark_strong : ∀ j, ∀ y ∈ Fref.filtration.layer j,
    ∃ x ∈ Dref.filtration.layer j,
      D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W x = y
  nQF : ℕ
  nQF_le : nQF ≤ finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
  Fquot : RationalFilteredNilmanifold
    ((Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
      Fref.filtration.layerIdeal (s + 1)) s nQF
  Fquot_filtration : Fquot.filtration = Fref.filtration.quotientTop
  Fquot_lattice : Fquot.lattice = Fref.lattice.map
    (Fref.filtration.quotientStepHom (Fref.filtration.layerIdeal (s + 1)) le_rfl)
  Fquot_geometry : Fquot.GeometryComplexityLE cost
  marked_quotient_height : ∀ i j, rationalLogHeight (Fquot.basis.repr
    (lieQuotientMap (Fref.filtration.layerIdeal (s + 1)) (Fref.basis j)) i) ≤ cost
  lower_mark_height : ∀ i j, rationalLogHeight (Fquot.basis.repr
    (Dref.topQuotientMarkedMap Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref Dref_filtration Fref Fref_filtration)
      (Q.basis i)) j) ≤ cost
  lower_mark_filtered : ∀ j, ∀ x ∈ Q.filtration.layer j,
    Dref.topQuotientMarkedMap Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref Dref_filtration Fref Fref_filtration)
      x ∈ Fquot.filtration.layer j
  lower_mark_strong : ∀ j, ∀ y ∈ Fquot.filtration.layer j,
    ∃ x ∈ Q.filtration.layer j, Dref.topQuotientMarkedMap Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref Dref_filtration Fref Fref_filtration)
      x = y
  pCover : ℝ
  pCover_nonneg : 0 ≤ pCover
  pCover_le : pCover ≤ cost
  recovery :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 Fref.basis
    letI := moduleTopology ℝ (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 Q.basis
    letI := Q.metricSpace
    letI := Fref.metricSpace
    let diagram := Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
    let K : ℝ≥0 := ⟨Real.exp pCover, (Real.exp_pos _).le⟩
    ∀ a r : D.RealGroup,
      (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
      ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
        (letI := D.metricSpace; LipschitzWith ℓ S) →
        (∀ y, (S y).im = 0 ∧ 0 ≤ (S y).re ∧ (S y).re ≤ 1) →
        let frozen := fun x : Dref.RealGroup => S (QuotientGroup.mk
          (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl x * r))
        ∀ x : Dref.RealGroup,
          positiveImageSlice diagram K frozen (diagram x).2 (diagram x).1 = frozen x

end Erdos3.RationalFilteredNilmanifold

end


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PositiveShiftTestingNiltests
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open scoped TensorProduct NNReal

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}

noncomputable def testingNiltest (B : PositiveShiftBasis s N q a J)
    (hk : ZMod N × Fin B.count) : B.model.Niltest (fun _ : Fin 1 => 1) := by
  classical
  exact if hk.1 ∈ B.shifts then
    (B.mode hk.1 hk.2).linearPullbackHom (fun _ : Unit =>
      { toFun := fun x => x 0, map_zero' := rfl, map_add' := fun _ _ => rfl })
  else RationalFilteredNilmanifold.Niltest.const B.model (fun _ : Fin 1 => 1) 0

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem realPolynomialMass_constant_specialization {σ τ : Type*}
    (T : τ → ℝ) (x : σ → ℝ) (P : MvPolynomial σ ℝ) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (MvPolynomial.aeval (fun i => (MvPolynomial.C (x i) : MvPolynomial τ ℝ)) P)) =
      |MvPolynomial.eval x P| := by
  have hC : MvPolynomial.aeval (fun i => (MvPolynomial.C (x i) : MvPolynomial τ ℝ)) P =
      MvPolynomial.C (MvPolynomial.eval x P) := by
    simpa only [Function.comp_def, MvPolynomial.aeval_eq_eval] using
      (MvPolynomial.aeval_C_comp_left (R := ℝ) x P :
        MvPolynomial.aeval (MvPolynomial.C (σ := τ) ∘ x) P =
          MvPolynomial.C (MvPolynomial.aeval x P))
  rw [hC]
  have hscale : scaleMvPolynomialAxes T (MvPolynomial.C (MvPolynomial.eval x P)) =
      MvPolynomial.C (MvPolynomial.eval x P) := by
    apply MvPolynomial.funext
    intro y
    rw [scaleMvPolynomialAxes_eval, MvPolynomial.eval_C, MvPolynomial.eval_C]
  rw [hscale, realPolynomialMass_C]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

noncomputable def scalarAffineAdaptedHom {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ) :
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group →*
      (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
  (F.polynomialOrbitCoordinates (fun _ => 1)).toMonoidHom.comp
    ((F.polynomialOrbitSubstitute (scalarAffinePolynomial r h) (scalarAffinePolynomial_support r h)).comp
      (F.polynomialOrbitCoordinates (fun _ => 1)).symm.toMonoidHom)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

noncomputable def affineSampleParameterKernel (π : FiniteProbabilityWeights (J → ZMod q))
    (z : Option J × I → ZMod q) : FiniteProbabilityWeights (I → ZMod q) :=
  π.fiberLaw (fun t => (affineSampleAlphabetEquiv z).2 +
    residueColumnMap (q := q) (affineSampleAlphabetEquiv z).1 t)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PrecenterForecastNativeAtomDictionary
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

structure PrecenterForecastNativeAtomDictionary
    {X Branch σ Θ : Type*} (models : Branch → CenteredForecastModel X)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ) where
  twistIndex : PrecenterForecastNativeAtomLabel models → Θ
  nativeValue : PrecenterForecastNativeAtomLabel models → X → ℂ
  native : ∀ label, NativeSampleModel nativeWeight degree budget sample (nativeValue label)
  realizes : ∀ label,
    (models label.val.1).models label.val.2 =
      fun x => star (twist (twistIndex label) x) * nativeValue label x

end Erdos3

end

end OAI
end


