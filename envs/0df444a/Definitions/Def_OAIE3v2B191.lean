-- Prove2me | Definitions.Def_OAIE3v2B191
-- name    : OAIE3v2B191
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:53:26.010593+00:00
-- url     : https://prove2.me/theorems/d6c53150-4272-4f54-ba33-964f3c411198
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 194 of 311
-- statement:
--   Definitions bundle 194 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B164`, `OAIE3v2B167`, `OAIE3v2B172`, `OAIE3v2B173`, `OAIE3v2B174` of this split.
--
--   Modules: `Dynamics/PhysicalEpochComparison.lean`, `Dynamics/ScheduledPhysicalEpochStack.lean`, `Estimates/AdaptedDiagramNativeExternalNet.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/CommonRefilteredMappedOrbitFactors.lean`, `Estimates/ControlledRefilteredRecoveredExpansion.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/NativeFrozenMarkedLocalMark.lean`, `Estimates/NativeMarkedDiagramOrbitLift.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/PhysicalStabilityParameters.lean`, `Estimates/PositiveShiftRefilteredExpansionSpec.lean`, `Estimates/PreparedLayerFreezing.lean`, `Estimates/RealifiedTopQuotient.lean`, `Estimates/RelativePatchWeightDescent.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Estimates/UniformPhysicalVisitBounds.lean`, `Linear/ActualOrdinaryPointwiseSpanning.lean`, `Linear/UniformPhysicalFrameConstruction.lean`, `Linear/VaryingRankFixedPatchFunction.lean`, `Nilpotent/PolynomialPatchWeightedChartNiltest.lean`, `Polynomial/ControlledMarkedPolynomialFactorization.lean`, `Polynomial/ControlledPolynomialGroupMapBounds.lean`, `Polynomial/OrdinaryPolynomialPhaseCanonicalTopology.lean`, `Polynomial/PolynomialPatchMarkedChartRestoration.lean`, `Sampling/FixedPatchShearFiberCandidateScore.lean`, `Sampling/MarkedKernelRationalGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B167
import Definitions.Def_OAIE3v2B172
import Definitions.Def_OAIE3v2B173
import Definitions.Def_OAIE3v2B174

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTopQuotient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_quotient_fiber_polynomialOrbit_lift
    {r : ℕ} (F : NilpotentLieFiltration L (r + 1)) (G : NilpotentLieFiltration M (r + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (honto : ∀ y ∈ G.layer (r + 1), ∃ x ∈ F.layer (r + 1), φ x = y)
    (w : σ → ℕ) (pbar : F.quotientTop.PolynomialOrbit w) (q : G.PolynomialOrbit w)
    (hcompat : map (lieQuotientProjection (F.layerIdeal (r + 1)) (G.layerIdeal (r + 1))
      φ (hφ (r + 1))).toLinearMap pbar.log =
        map (lieQuotientMap (G.layerIdeal (r + 1))).toLinearMap q.log) :
    ∃ p : F.PolynomialOrbit w,
      map (lieQuotientMap (F.layerIdeal (r + 1))).toLinearMap p.log = pbar.log ∧
        map φ.toLinearMap p.log = q.log := by
  have hpbar : ∀ a, coefficients pbar.log a ∈
      (F.layer (Finsupp.weight w a)).map
        (lieQuotientMap (F.layerIdeal (r + 1))).toLinearMap :=
    (F.quotientTop.adapted_iff_coefficients w pbar.log).mp pbar.adapted
  obtain ⟨p, hp, heq, hproj⟩ := F.exists_adapted_quotient_fiber_polynomial_lift G φ hφ honto
    w pbar.log q.log hcompat hpbar q.adapted
  exact ⟨polynomialOrbitOfLog p hp, heq, hproj⟩

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

include e ω hF b ν hG in

theorem gradedRefiltrationMap_layer_surjective (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (j : ℕ) (y : G.gradedRefiltrationSubalgebra (U.map (F.associatedGradedMap G φ hφ)))
    (hy : y ∈ (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layer j) :
    ∃ x ∈ (F.gradedRefiltration U).layer j, F.gradedRefiltrationMap G φ hφ U x = y := by
  have lift (i : ℕ) (hi : 1 ≤ i)
      (hy' : (y : M) ∈ G.gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) i) :
      ∃ x ∈ (F.gradedRefiltration U).layer i, F.gradedRefiltrationMap G φ hφ U x = y := by
    rw [← F.gradedRefiltrationLayer_map G e ω hF b ν hG φ hφ U hU hsurj] at hy'
    obtain ⟨x, hx, hxy⟩ := hy'
    let x' : F.gradedRefiltrationSubalgebra U :=
      ⟨x, F.gradedRefiltrationLayer_antitone U hi hx⟩
    exact ⟨x', hx, Subtype.ext hxy⟩
  by_cases hj : 1 ≤ j
  · exact lift j hj hy
  · have hj0 : j = 0 := by omega
    subst j
    obtain ⟨x, hx, hxy⟩ := lift 1 le_rfl y.property
    exact ⟨x, (F.gradedRefiltration U).antitone (by omega : 0 ≤ 1) hx, hxy⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_real_quotient_fiber_polynomialOrbit_lift
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (w : σ → ℕ) (pbar : F.quotientTop.realification.PolynomialOrbit w)
    (q : G.realification.PolynomialOrbit w)
    (hcompat : map
      (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ
          (hφ (s + 1))))).toLinearMap pbar.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (G.layerIdeal (s + 1))))).toLinearMap q.log) :
    ∃ p : F.realification.PolynomialOrbit w,
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (F.layerIdeal (s + 1))))).toLinearMap p.log = pbar.log ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap p.log = q.log := by
  let e := F.realificationTopQuotientEquiv
  let φR := realLieHomToRat (realificationLieHom φ)
  let hφR := F.realificationLieHom_mem_layer G φ hφ
  let pbar' : F.realification.quotientTop.PolynomialOrbit w :=
    polynomialOrbitOfLog (map e.symm.toLinearEquiv.toLinearMap pbar.log)
      (F.quotientTop.realification.adapted_map F.realification.quotientTop
        e.symm.toLinearEquiv.toLinearMap
        (fun j x hx => (F.realificationTopQuotientEquiv_mem_layer_iff j (e.symm x)).mp
          (by simpa only [e, LieEquiv.apply_symm_apply] using hx)) w pbar.adapted)
  have hcompat' : map
      (lieQuotientProjection (F.realification.layerIdeal (s + 1))
        (G.realification.layerIdeal (s + 1)) φR (hφR (s + 1))).toLinearMap pbar'.log =
      map (lieQuotientMap (G.realification.layerIdeal (s + 1))).toLinearMap q.log := by
    apply coefficients.injective
    ext a
    rw [coefficients_map, coefficients_map]
    apply G.realificationTopQuotientEquiv.injective
    change G.realificationTopQuotientEquiv
      (lieQuotientProjection (F.realification.layerIdeal (s + 1))
        (G.realification.layerIdeal (s + 1))
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ (s + 1)) (coefficients pbar'.log a)) =
      G.realificationTopQuotientEquiv
        (lieQuotientMap (G.realification.layerIdeal (s + 1)) (coefficients q.log a))
    rw [F.realificationTopQuotientEquiv_projection G φ hφ,
      G.realificationTopQuotientEquiv_mk]
    have he : e (coefficients pbar'.log a) = coefficients pbar.log a := by
      change e (coefficients (map e.symm.toLinearEquiv.toLinearMap pbar.log) a) = _
      rw [coefficients_map]
      exact e.apply_symm_apply _
    change realificationLieHom
      (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ (hφ (s + 1)))
      (e (coefficients pbar'.log a)) = _
    rw [he]
    have ha := congrArg (fun P => coefficients P a) hcompat
    simp only [coefficients_map] at ha
    exact ha
  obtain ⟨p, hpbar, hpq⟩ :=
    F.realification.exists_quotient_fiber_polynomialOrbit_lift G.realification φR hφR
      (F.realificationLieHom_layer_surjective G φ hφ hsurj (s + 1)) w pbar' q hcompat'
  have hreal : map (realLieHomToRat (realificationLieHom
      (lieQuotientMap (F.layerIdeal (s + 1))))).toLinearMap p.log = pbar.log := by
    apply coefficients.injective
    ext a
    rw [coefficients_map]
    have ha := congrArg (fun P => e (coefficients P a)) hpbar
    simp only [coefficients_map] at ha
    change realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1)))
      (coefficients p.log a) = _
    refine ha.trans ?_
    change e (coefficients (map e.symm.toLinearEquiv.toLinearMap pbar.log) a) = _
    rw [coefficients_map]
    exact e.apply_symm_apply _
  exact ⟨p, hreal, hpq⟩

end Erdos3.NilpotentLieFiltration

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

namespace AdaptedModelData

variable {D : RationalFilteredNilmanifold L s d}

theorem model_layers (F : D.AdaptedModelData) (j : ℕ) :
    F.model.filtration.layer j = Submodule.span ℚ (F.model.basis '' {i | j ≤ F.weight i}) := F.layers j

end AdaptedModelData

end Erdos3.RationalFilteredNilmanifold

end

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

theorem optionOriginalObservable_adapted_unit_interval
    (adapted : (optionProduct D₀ D).AdaptedModelData)
    (hunit : ∀ a y, (observable a y).im = 0 ∧
      0 ≤ (observable a y).re ∧ (observable a y).re ≤ 1) :
    ∀ a (y : adapted.model.Space),
      (optionOriginalObservable D₀ D observable a y).im = 0 ∧
      0 ≤ (optionOriginalObservable D₀ D observable a y).re ∧
      (optionOriginalObservable D₀ D observable a y).re ≤ 1 :=
  optionOriginalObservable_unit_interval D₀ D observable hunit

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (W : LieSubalgebra ℚ F.AssociatedGraded)

theorem exists_native_refiltration_layer_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : Basis ι ℚ L) (b : Basis κ ℚ (F.gradedRefiltrationSubalgebra W))
    (j : ℕ) (hj : 1 ≤ j)
    (a : Basis (Fin (finrank ℚ (F.gradedRefiltrationLayer W j))) ℚ (F.gradedRefiltrationLayer W j))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (e.repr (b i : L) k) H)
    (ha : ∀ i k, RationalHeightLE (e.repr (a i : L) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ a' : Basis (Fin (finrank ℚ ((F.gradedRefiltration W).layer j))) ℚ
        ((F.gradedRefiltration W).layer j),
      ∀ i k, rationalLogHeight (b.repr (a' i : F.gradedRefiltrationSubalgebra W) k) ≤ (p + 2) ^ 8 := by
  let E := F.nativeRefiltrationLayerEquiv W j hj
  let a' := (a.map E.symm).reindex (finCongr E.finrank_eq.symm)
  have hval (i) : ((a' i : F.gradedRefiltrationSubalgebra W) : L) =
      (a ((finCongr E.finrank_eq.symm).symm i) : L) := by
    simp only [a', Basis.reindex_apply, Basis.map_apply, E, nativeRefiltrationLayerEquiv]
    rfl
  refine ⟨a', fun i k => ?_⟩
  apply rationalLogHeight_le_of_height
    (embedding_basis_coordinate_height b e (F.gradedRefiltrationSubalgebra W).incl.toLinearMap
      (fun _ _ h => Subtype.ext h) hH (fun k i => hb i k)
      (a' i : F.gradedRefiltrationSubalgebra W) (K := H) (fun k => by
        change RationalHeightLE (e.repr ((a' i : F.gradedRefiltrationSubalgebra W) : L) k) H
        rw [hval]
        exact ha _ k) k)
  exact embedding_coordinate_height_budget _ _ H H hp hι hκ hHp hHp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalEpochComparison
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

attribute [instance] PhysicalEpochSource.lieRing PhysicalEpochSource.lieAlgebra
  PhysicalEpochSource.topology PhysicalEpochSource.topologicalAddGroup
  PhysicalEpochSource.continuousSMul PhysicalEpochSource.t2Space

structure PhysicalEpochRecords {σ : Type u} [Fintype σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ s bound) where
  records : List (EpochSymbolRecord base.model base.weights base.adapted base.fixedMap)
  history : EpochRecordHistory records
  controlled : ∀ r ∈ records, r.Controlled (fun i => (base.sides i : ℝ)) base.recordBudget

namespace PhysicalEpochRecords

variable {σ : Type u} [Fintype σ] {s bound : ℕ} {base : PhysicalEpochSource.{u, v} σ s bound}

def empty (base : PhysicalEpochSource.{u, v} σ s bound) : PhysicalEpochRecords base where
  records := []
  history := .nil
  controlled := by simp

noncomputable def dimension (state : PhysicalEpochRecords base) : ℕ :=
  finrank ℚ (epochRecordIntersection state.records)

end PhysicalEpochRecords

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v

structure PhysicalEpochComparison {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ s bound) (m a J : ℕ) (gap : ℝ) where
  selected_pos : 0 < m
  auxiliary_pos : 0 < a
  pending_pos : 0 < J
  lower : σ → ℤ
  sides : σ → ℕ
  sides_pos : ∀ i, 0 < sides i
  contained : ∀ i, base.lower i ≤ lower i ∧ lower i + sides i ≤ base.lower i + base.sides i
  anchor : σ → ℤ
  refined : σ → ℤ
  anchor_inside : ∀ i, lower i ≤ anchor i ∧ anchor i < lower i + sides i
  refined_inside : ∀ i, lower i ≤ refined i ∧ refined i < lower i + sides i
  compatible : ∀ i, refined i ≡ anchor i [ZMOD (m * a : ℕ)]
  test : base.model.Niltest (fun _ : σ => 1)
  orbit : test.orbit = (base.fixedMap.scalarAffinePullback (m * a : ℕ) (fun i => (anchor i : ℚ))).orbit
  positive : test.UnitIntervalValued
  complexity : test.ComplexityLE base.incomingBudget
  gap_pos : 0 < gap
  gap_le_one : gap ≤ 1
  gap_inverse : gap⁻¹ ≤ Real.exp base.incomingBudget
  discrepancy : gap ≤ ‖residuePairMean test.eval lower sides (m * a) anchor refined (fun _ => J) false -
    residuePairMean test.eval lower sides (m * a) anchor refined (fun _ => J) true‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.UniformPhysicalFrameConstruction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

structure PhysicalEpochFrame {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ (s + 1) bound) where
  state : PhysicalEpochRecords base
  modulus : ℕ
  modulus_pos : 0 < modulus
  anchor : σ → ℤ
  anchor_inside : ∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i
  record_moduli : ∀ r ∈ state.records, r.modulus ∣ modulus
  work : ℝ
  incoming_le_work : base.incomingBudget + 16 ≤ work
  record_le_work : base.recordBudget + 16 ≤ work
  period : ℕ
  period_pos : 0 < period
  freezePower : ℕ
  eventPower : ℕ
  period_le : (period : ℝ) ≤ Real.exp ((work + 2) ^ freezePower)
  child : PhysicalEpochSource.{u, v} σ s bound
  child_lower : child.lower = base.lower
  child_sides : child.sides = base.sides
  child_dimension_le : child.dimension ≤ base.dimension
  childCost : ℝ
  childCost_nonneg : 0 ≤ childCost
  childCost_le : childCost ≤ child.incomingBudget
  incoming_le_child : base.incomingBudget + 16 ≤ child.incomingBudget
  work_le_child : work ≤ child.incomingBudget
  transition : FixedAffineEpochTransition base.model base.weights base.adapted
    (epochRecordIntersection state.records)
    (base.fixedMap.scalarAffinePullback (modulus : ℚ) (fun i => (anchor i : ℚ)))
    (fun i => (base.sides i : ℝ) / modulus)
    child.model (child.fixedMap.scalarAffinePullback (modulus : ℚ) (fun i => (anchor i : ℚ))).orbit
    work childCost period freezePower eventPower

end Erdos3

end

section

namespace Erdos3

universe u v

def PhysicalFrameConstructionBound (s K : ℕ) : Prop :=
  ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ (s + 1) bound) (state : PhysicalEpochRecords base)
    (M : ℕ), 0 < M → ∀ anchor : σ → ℤ,
    (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
    (∀ r ∈ state.records, r.modulus ∣ M) →
    ∀ inflate : ℝ → ℝ, (∀ p, 0 ≤ p → p ≤ inflate p) →
    (∀ i, Real.exp ((base.recordBudget + 2) ^ K) ≤ (base.sides i : ℝ) / M) →
    ∃ frame : PhysicalEpochFrame base,
      frame.state = state ∧ frame.modulus = M ∧ frame.anchor = anchor ∧
      frame.work ≤ (base.recordBudget + 2) ^ K ∧
      frame.child.incomingBudget ≤ (base.recordBudget + 2) ^ K ∧
      frame.child.recordBudget = inflate frame.child.incomingBudget ∧
      (frame.period : ℝ) ≤ Real.exp ((base.recordBudget + 2) ^ K) ∧
      frame.freezePower ≤ K ∧ frame.eventPower ≤ K

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScheduledPhysicalEpochStack
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

inductive PhysicalEpochStack {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ} :
    {s : ℕ} → PhysicalEpochSource.{u, v} σ s bound → Type (max u (v + 1))
  | zero (base : PhysicalEpochSource.{u, v} σ 0 bound) : PhysicalEpochStack base
  | succ {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base) (tail : PhysicalEpochStack frame.child) : PhysicalEpochStack base

namespace PhysicalEpochStack

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

noncomputable def dimensions : {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} →
    PhysicalEpochStack base → List ℕ
  | _, _, .zero _ => []
  | _, _, .succ frame tail => frame.state.dimension :: dimensions tail

inductive Event : {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} →
    PhysicalEpochStack base → PhysicalEpochStack base → Prop
  | head {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      {oldFrame newFrame : PhysicalEpochFrame base}
      (record : EpochSymbolRecord base.model base.weights base.adapted base.fixedMap)
      (records : newFrame.state.records = record :: oldFrame.state.records)
      (modulus : oldFrame.modulus ∣ newFrame.modulus)
      (anchor : ∀ i, newFrame.anchor i ≡ oldFrame.anchor i [ZMOD (oldFrame.modulus : ℤ)])
      (oldTail : PhysicalEpochStack oldFrame.child) (newTail : PhysicalEpochStack newFrame.child) :
      Event (.succ oldFrame oldTail) (.succ newFrame newTail)
  | tail {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base)
      {oldTail newTail : PhysicalEpochStack frame.child} (event : Event oldTail newTail) :
      Event (.succ frame oldTail) (.succ frame newTail)

end PhysicalEpochStack

end Erdos3

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def RootState (state : PhysicalEpochRecords base) : PhysicalEpochStack base → Prop
  | .zero _ => True
  | .succ frame _ => frame.state = state

def UniformAt (A M : ℕ) (anchor : σ → ℤ) (budget : ℝ) (power : ℕ) :
    {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → Prop
  | _, base, .zero _ => base.incomingBudget ≤ budget ∧ base.recordBudget ≤ budget
  | _, base, .succ frame tail =>
    base.incomingBudget ≤ budget ∧ base.recordBudget ≤ budget ∧
    frame.modulus = M ∧ frame.anchor = anchor ∧ frame.work ≤ budget ∧
    (frame.period : ℝ) ≤ Real.exp budget ∧ frame.freezePower ≤ power ∧ frame.eventPower ≤ power ∧
    frame.child.recordBudget = (frame.child.incomingBudget + 2) ^ A ∧
    UniformAt A M anchor budget power tail

end Erdos3.PhysicalEpochStack

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def AlignedAt (M : ℕ) (anchor : σ → ℤ) :
    {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → Prop
  | _, _, .zero _ => True
  | _, _, .succ frame tail =>
    frame.modulus ∣ M ∧
    (∀ i, anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)]) ∧ AlignedAt M anchor tail

def BudgetedAt (A : ℕ) (budget : ℝ) (power : ℕ) :
    {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → Prop
  | _, base, .zero _ => base.recordBudget ≤ budget ∧ (base.incomingBudget + 2) ^ A ≤ base.recordBudget
  | _, base, .succ frame tail =>
    base.recordBudget ≤ budget ∧ (base.incomingBudget + 2) ^ A ≤ base.recordBudget ∧
    frame.work ≤ budget ∧ (frame.period : ℝ) ≤ Real.exp budget ∧
    frame.freezePower ≤ power ∧ frame.eventPower ≤ power ∧ BudgetedAt A budget power tail

end Erdos3.PhysicalEpochStack

end

section

namespace Erdos3.PhysicalEpochStack

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def RootCreatedAt (M : ℕ) (anchor : σ → ℤ) : PhysicalEpochStack base → Prop
  | .zero _ => True
  | .succ frame _ => frame.modulus = M ∧ frame.anchor = anchor

def ScheduledAt (A C : ℕ) (b : ℝ) (depth : ℕ) :
    {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → Prop
  | _, base, .zero _ =>
    base.recordBudget ≤ physicalEpochBudget A C b depth ∧
    (base.incomingBudget + 2) ^ A ≤ base.recordBudget
  | _, base, .succ frame tail =>
    base.recordBudget ≤ physicalEpochBudget A C b depth ∧
    (base.incomingBudget + 2) ^ A ≤ base.recordBudget ∧
    frame.work ≤ (physicalEpochBudget A C b depth + 2) ^ C ∧
    (frame.period : ℝ) ≤ Real.exp ((physicalEpochBudget A C b depth + 2) ^ C) ∧
    frame.freezePower ≤ C ∧ frame.eventPower ≤ C ∧ ScheduledAt A C b (depth + 1) tail

end Erdos3.PhysicalEpochStack

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

theorem filteredRealPolynomialSection_rationalGrid [Fintype ι] [Fintype κ]
    [DecidableEq κ] (S : M →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (l : ℕ)
    (g : (G.realification.adaptedPolynomialFiltration w).Group)
    (hg : G.PolynomialRationalGrid c w l g) :
    F.PolynomialRationalGrid b w
      (matrixDenominator (LinearMap.toMatrix c b S) * l)
      (F.filteredRealPolynomialSection G w S hS g) := by
  rw [F.polynomialRationalGrid_iff_coefficients]
  intro α
  have hc := (G.polynomialRationalGrid_iff_coefficients c w l g).mp hg α
  have ho := realified_linear_coordinate_grid c b S l _ hc
  change (b.baseChange ℝ).equivFun (coefficients
    (map ((S.baseChange ℝ).restrictScalars ℚ)
      (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M))) α) ∈ _
  simpa only [coefficients_map, LinearMap.restrictScalars_apply] using ho

end Erdos3.NilpotentLieFiltration

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

theorem exists_weighted_common_refiltered_orbit_factors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι J Ω L : Type*} [Fintype σ] [Fintype ι] [Fintype J] [Fintype Ω]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (eta : J → L →ₗ[ℚ] ℚ) {p : ℝ}, 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ i j k, rationalLogHeight (b.repr ⁅b i, b j⁆ k) ≤ p) →
      ∀ side : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ C) ≤ side i) →
      ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      ∀ g : Ω → (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ a ∈ H, ∀ j, F.ControlledSymbolFactorization b w hF (eta j) side
        (F.realPolynomialSymbolHom b w hF (fun _ => 1) (g a)) p) →
      let q := (p + 2) ^ C + (((p + 2) ^ 2 + 2) ^ 63 + 1) + p + 1
      ∃ (W : LieSubalgebra ℚ F.AssociatedGraded)
        (v : Fin (Fintype.card ι) → F.AssociatedGraded) (m : ℕ) (H' : Finset Ω),
        H' ⊆ H ∧ 0 < outer.mass H' ∧
        Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis b w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((F.associatedGradedBasis b w hF).repr (v i) k) ≤ q) ∧
        (∀ j x, x ∈ F.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp q ∧
        ∀ a ∈ H', F.HasCommonRefilteredOrbitFactors b w hF side q m W (g a) := by
  obtain ⟨C, hC, hcommon⟩ := exists_common_refiltered_factorization s
  refine ⟨C, hC, ?_⟩
  intro σ ι J Ω L _ _ _ _ _ _ F b w hF eta p hp hι hσ hJ hstructure
    side hside outer H hH g hfactor
  classical
  let q := (p + 2) ^ C + (((p + 2) ^ 2 + 2) ^ 63 + 1) + p + 1
  have hpC : 0 ≤ (p + 2) ^ C := by positivity
  have hpheight : 0 ≤ ((p + 2) ^ 2 + 2) ^ 63 := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hcq : (p + 2) ^ C ≤ q := by dsimp [q]; linarith
  have hvq : ((p + 2) ^ 2 + 2) ^ 63 + 1 ≤ q := by dsimp [q]; linarith
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  have hHne : H.Nonempty := by
    by_contra hn
    have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hH
  obtain ⟨a₀, ha₀⟩ := hHne
  let pick (a : Ω) := if a ∈ H then a else a₀
  have hpick (a) : pick a ∈ H := by
    dsimp only [pick]
    split_ifs with ha
    · exact ha
    · exact ha₀
  choose W v m e middle r hv hW hheight hfreq hm hmp hprod hmid he hr he0 hr0 hmiddle0 hanchor
    using fun a => hcommon F b w hF eta p hp hι hσ hJ hstructure side hside
      (g (pick a)) (hfactor (pick a) (hpick a))
  obtain ⟨a₁, _, H', hsub, _, hsame, hmass⟩ :=
    exists_weighted_common_fast_subalgebra_and_denominator
      (F.associatedGradedBasis b w hF) outer H hH W m (Fintype.card ι) hq
      (hι.trans hpq) (hι.trans hpq)
      (fun a _ => ⟨v a, hv a, fun i k => (hheight a i k).trans hvq⟩)
      (fun a _ => ⟨hm a, (hmp a).trans (Real.exp_le_exp.mpr hcq)⟩)
  refine ⟨W a₁, v a₁, m a₁, H', hsub,
    (mul_pos (Real.exp_pos _) hH).trans_le hmass, hmass, hv a₁, hW a₁,
    fun i k => (hheight a₁ i k).trans hvq, hfreq a₁, hm a₁,
    (hmp a₁).trans (Real.exp_le_exp.mpr hcq), ?_⟩
  intro a ha
  have hpa : pick a = a := if_pos (hsub ha)
  have hout : F.HasCommonRefilteredOrbitFactors b w hF side q (m a) (W a) (g (pick a)) := by
    refine ⟨e a, middle a, r a, hprod a, hmid a, ?_, hr a, he0 a, hr0 a, hmiddle0 a⟩
    exact F.polynomialSlowBound_mono b (fun _ => 1) side hsidepos
      (Real.exp_le_exp.mpr hcq) (e a) (he a)
  simpa only [hpa, (hsame a ha).1, (hsame a ha).2] using hout

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledRefilteredRecoveredExpansion
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def RefilteredProductExpansionSpec (p : ℝ) (q r : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp cost ∧
    ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
      Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
      Q'.GeometryComplexityLE cost ∧
        ∃ Λ : Subgroup Z₀.filtration.Group, Λ ≤ Z₀.lattice ∧
          (Λ.subgroupOf Z₀.lattice).Characteristic ∧ (Λ.subgroupOf Z₀.lattice).Normal ∧
          (Λ.subgroupOf Z₀.lattice).FiniteIndex ∧ (Λ.relIndex Z₀.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Z₀.basis Λ)
            (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid l),
            let V := Z₀.withLattice Λ l hl hin hout
            V.GeometryComplexityLE cost ∧
            letI := V.metricSpace
            let w := fun _ : Unit => 1
            ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ K : ℝ},
                0 < ρ → 0 ≤ K →
                (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
                (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
                (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                (∀ i x y, 0 < A i x → 0 < A i y →
                  dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                ∀ (S : ZMod N → (D a).Niltest w),
                  (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                  (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                    (∀ j, realifyFunctional (freq j a) z.coord = 0) →
                    ∀ x, (S h).observable (z • x) = (S h).observable x) →
                  ∀ (g : ZMod N → ∀ i, (D i).filtration.realification.PolynomialOrbit w),
                    (∀ h, g h a = (S h).orbit) →
                    ∀ (slow middle rat : ZMod N → ((pi D).filtration.realification.adaptedPolynomialFiltration w).Group)
                      (κ : ZMod N → (pi D).RealGroup),
                      (∀ h, κ h ∈ (pi D).realLattice) →
                      (∀ h, slow h * middle h * rat h * (pi D).filtration.realification.adaptedConstantGroupHom w (κ h) =
                        ⟨⟨(NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).log,
                          (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).property⟩⟩) →
                      (∀ h, (pi D).filtration.PolynomialSlowBound (pi D).basis w
                        (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                      (∀ h, (pi D).filtration.PolynomialRationalGrid (pi D).basis w q (rat h)) →
                      (∀ h α, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
                          (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight w α)) →
                      (∀ h, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0) →
                      (∀ i j h x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                        0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                        dist (V.cyclicOrbitPoint
                          (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                            (fun i : I₀ => g h i.val)) N (fun _ : Unit => x))
                          (V.cyclicOrbitPoint
                            (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                              (fun i : I₀ => g h i.val)) N (fun _ : Unit => y)) ≤ K * ρ) →
                      ∃ U : I → J → ZMod N → Q'.Niltest w,
                        (∀ i j h, (U i j h).UnitIntervalValued) ∧
                        (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                        (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                          ∀ x, (U i j h).eval x = 0) ∧
                        ∃ err : ZMod N → ZMod N → ℝ,
                          (∀ h x, ((S h).evalCyclic N (fun _ => x)).re =
                            (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                          ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansionSpec
namespace OAI

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  (B : PositiveShiftBasis.{u} s N q a J) {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  (D : ∀ j, RationalFilteredNilmanifold (L j) s (d j))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))
  (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
  (R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1))
  (anchor : ZMod N) (H : Finset (ZMod N)) (p : ℝ)

structure CommonFactorization where
  weight : ∀ i, Fin (B.anchoredDimension d e i) → ℕ
  adapted : ∀ i k, (B.anchoredFactors D E i).filtration.layer k =
    Submodule.span ℚ ((B.anchoredFactors D E i).basis '' {j | k ≤ weight i j})
  subalgebra : LieSubalgebra ℚ (pi (B.anchoredFactors D E)).filtration.AssociatedGraded
  spanning : Fin (Fintype.card (Σ i, Fin (B.anchoredDimension d e i))) →
    (pi (B.anchoredFactors D E)).filtration.AssociatedGraded
  span_eq : Submodule.span ℚ (Set.range spanning) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule
    ((pi (B.anchoredFactors D E)).filtration.associatedGradedBasis (pi (B.anchoredFactors D E)).basis
      (productBasisWeight weight) (pi_layer_span (B.anchoredFactors D E) weight adapted))
    (productBasisWeight weight) subalgebra.toSubmodule
  height : ∀ i k, rationalLogHeight
    (((pi (B.anchoredFactors D E)).filtration.associatedGradedBasis (pi (B.anchoredFactors D E)).basis
      (productBasisWeight weight) (pi_layer_span (B.anchoredFactors D E) weight adapted)).repr (spanning i) k) ≤ p
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p
  shifts : Finset (ZMod N)
  shifts_sub : shifts ⊆ H
  shifts_nonempty : shifts.Nonempty
  shifts_large : Real.exp (-p) * N ≤ (shifts.card : ℝ)
  factors : ∀ h ∈ shifts, HasFixedProductOrbitFactors (B.anchoredFactors D E) none
    (fun i => (anchoredOptionReferenceData (B.test h) (B.test anchor) A (R h) i).orbit)
    (B.frequency h) (fun _ : Unit => (N : ℝ)) p denominator subalgebra
  frequency : ({h // h ∈ shifts} × Fin B.count) → ∀ i, B.anchoredLieSpace L M i →ₗ[ℚ] ℚ
  frequency_zero : ∀ j x,
    x ∈ (pi (B.anchoredFactors D E)).filtration.realGradedRefiltrationLayer subalgebra s →
      realifyFunctional (piFrequency (frequency j)) x = 0
  invariant : ∀ h ∈ shifts, ∀ z : B.model.RealGroup,
    z ∈ B.model.filtration.realification.subgroup s →
    (∀ j, realifyFunctional (frequency j none) z.coord = 0) → ∀ x,
      (B.test h).observable (z • x) = (B.test h).observable x

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

variable {s N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
  {B : PositiveShiftBasis.{u} s N q a J} {L M : Fin B.count → Type u}
  [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
  [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
  [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
  [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
  {D : ∀ j, RationalFilteredNilmanifold (L j) s (d j)}
  {E : ∀ j, RationalFilteredNilmanifold (M j) s (e j)}
  {A : ∀ j, (D j).Niltest (fun _ : Unit => 1)}
  {R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1)}
  {anchor : ZMod N} {H : Finset (ZMod N)} {p : ℝ}

def CommonFactorization.FactorFamily
    (F : B.CommonFactorization D E A R anchor H p) : Prop :=
    let T := B.anchoredFactors D E
    let g (h : ZMod N) : ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
      fun i => (anchoredOptionReferenceData (D := T) (B.test h) (B.test anchor) A (R h) i).orbit
    ∃ (κ : ZMod N → (pi T).RealGroup)
      (slow middle rat : ZMod N → ((pi T).filtration.realification.adaptedPolynomialFiltration
        (fun _ : Unit => 1)).Group),
      (∀ h ∈ F.shifts, κ h ∈ (pi T).realLattice) ∧
      (∀ h ∈ F.shifts, slow h * middle h * rat h *
        (pi T).filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) (κ h) =
          ⟨⟨(piRealOrbit (fun i => (T i).filtration)
            (g h)).log,
            (piRealOrbit (fun i => (T i).filtration)
            (g h)).property⟩⟩) ∧
      (∀ h ∈ F.shifts, (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
        (fun _ => (N : ℝ)) (Real.exp p) (slow h)) ∧
      (∀ h ∈ F.shifts, (pi T).filtration.PolynomialRationalGrid (pi T).basis (fun _ : Unit => 1)
        F.denominator (rat h)) ∧
      (∀ h ∈ F.shifts, coefficients
        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))) 0 = 0) ∧
      (∀ h ∈ F.shifts, ∀ α, coefficients
        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, B.anchoredLieSpace L M i))) α ∈
          (pi T).filtration.realGradedRefiltrationLayer F.subalgebra (Finsupp.weight (fun _ : Unit => 1) α))

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

def CommonRefilteredExpansionSpec (s r C : ℕ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q a J)
      {L M : Fin B.count → Type}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
      [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
      (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1) (e j))
      (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
      (R : ZMod N → ∀ j, (E j).Niltest (fun _ : Unit => 1))
      (anchor : ZMod N) (H : Finset (ZMod N)) {p : ℝ}
      (F : B.CommonFactorization D E A R anchor H p),
      2 ≤ p → q ≤ p →
      (∀ j, (D j).GeometryComplexityLE p) → (∀ j, (E j).GeometryComplexityLE p) →
      let T := B.anchoredFactors D E
      let t := productExpansionBudget p
      ∃ U : RationalFilteredNilmanifold ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra)
          (s + 1) (finrank ℚ ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra)),
        U.filtration = (pi T).filtration.gradedRefiltration F.subalgebra ∧
        U.lattice = (pi T).lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := ((pi T).filtration.gradedRefiltration F.subalgebra).lowerCentralSeries_eq_bot)
            ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra).incl) ∧
        U.GeometryComplexityLE ((t + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ ((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra) ∧
          ∃ Q : RationalFilteredNilmanifold
              (((pi T).filtration.gradedRefiltrationSubalgebra F.subalgebra) ⧸
                U.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = U.filtration.quotientTop ∧
            Q.lattice = U.lattice.map
              (U.filtration.quotientStepHom (U.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((t + C) ^ C) ∧
            (nativeRefilteredTarget T none F.subalgebra U Q).GeometryComplexityLE ((t + C) ^ C) ∧
            ∃ cost : ℝ, 0 ≤ cost ∧ cost ≤ (t + C) ^ C ∧
              RefilteredProductExpansionSpec T none F.subalgebra U Q t F.denominator r cost

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem structure_height {p : ℝ} (hp : 0 ≤ p) (i j k : Fin 1) :
    rationalLogHeight (lieStructureConstants (RationalTorus.basis 1) i j k) ≤ p := by
  simpa [lieStructureConstants, RationalTorus.lie_eq_zero, rationalLogHeight] using hp

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem formal_mark_realEval
    {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ)
    (g : F.realification.PolynomialOrbit w) (marked : G.realification.PolynomialOrbit w)
    (hm : map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log)
    (x : σ → ℝ) :
    realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ (F.realification.polynomialOrbitRealEval w x g) =
      G.realification.polynomialOrbitRealEval w x marked := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom φ (eval₂ x g.log) = eval₂ x marked.log
  rw [← hm]
  exact (eval₂_map (realificationLieHom φ).toLinearMap x g.log).symm

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ ι κ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nE nF : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nE)
    (hE : E.filtration = D.filtration.gradedRefiltration W)

variable (EF : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hEF : EF.filtration = Fmark.filtration.gradedRefiltration (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

include hφ

attribute [local irreducible] NilpotentLieFiltration.associatedGradedMap
  NilpotentLieFiltration.gradedRefiltrationMap
  includedRefilteredOrbit externalCandidateOrbit

theorem refiltered_mark_realification_commutes (z : E.RealGroup) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl z) =
    realificationMap (hnil := EF.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot)
      (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := EF.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) z) := by
  have hc : φ.toLinearMap.comp (D.filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap =
      (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl.toLinearMap.comp ((D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)).toLinearMap := by
    ext x
    exact (D.filtration.gradedRefiltrationMap_apply Fmark.filtration φ hφ W x).symm
  have he := congrArg (fun g => g.baseChange ℝ) hc
  apply NilpotentLieBCHGroup.ext
  change φ.toLinearMap.baseChange ℝ
      ((D.filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap.baseChange ℝ z.coord) =
    (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl.toLinearMap.baseChange ℝ
      (((D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)).toLinearMap.baseChange ℝ z.coord)
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using
    congrArg (fun g => g z.coord) he

end Erdos3.RationalFilteredNilmanifold

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

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom polynomialOrbitCoordinates

theorem polynomialOrbitRealChart_polynomialCoordinates
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) :
    F.realification.polynomialOrbitCoordinates v
      (F.polynomialOrbitRealChart w v β hβ g) =
    F.weightedAdaptedRealChartHom w v β hβ
      (F.realification.polynomialOrbitCoordinates w g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [F.realification.polynomialOrbitCoordinates_log, F.polynomialOrbitRealChart_log,
    F.weightedAdaptedRealChartHom_coord, F.realification.polynomialOrbitCoordinates_log]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialPatchWeightedChartNiltest
namespace OAI

section

namespace Erdos3.PolynomialPatch

open scoped NNReal TensorProduct

variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
  [Fintype (PolynomialShearIndex A.weight)]
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

noncomputable def shearNiltest (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : σ => 1) where
  orbit := A.shearOrbit
  observable z := (A.shearObservable z : ℂ)
  normBound := 1
  lipBound := A.shearObservableLipBound M
  norm_le z := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, NNReal.coe_one] using A.abs_shearObservable_le_one z
  lipschitz := by
    let : MetricSpace ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) :=
      (polynomialShearNilmanifold A.weight s A.weight_le).metricSpace
    change LipschitzWith (A.shearObservableLipBound M)
      (fun z : (polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
        polynomialShearRealLattice s A.weight_le => (A.shearObservable z : ℂ))
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp (A.shearObservable_lipschitz M hA)

theorem shearNiltest_unitInterval (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    (A.shearNiltest M hA).UnitIntervalValued := by
  intro z
  exact ⟨rfl, A.shearObservable_mem_Icc z⟩

theorem shearNiltest_complexity (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) {p : ℝ}
    (hgeometry : (polynomialShearNilmanifold A.weight s A.weight_le).GeometryComplexityLE p)
    (hbound : Real.log (3 + (A.shearObservableLipBound M : ℝ)) ≤ p) :
    (A.shearNiltest M hA).ComplexityLE p := by
  exact ⟨hgeometry, by simpa only [shearNiltest, NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num] using hbound⟩

end Erdos3.PolynomialPatch

end

section

namespace Erdos3.PolynomialSlots

variable {X Y : Type*} {d s : ℕ} {w : Fin d → ℕ}

theorem shearObservable_eval_lift (B : PolynomialSlots X d w) (A : PolynomialSlots Y d w)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
    (Φ : PatchKernel d) (t : Y → ℝ) :
    let P : PolynomialPatch X s d := ⟨w, hpos, hs, hw, B, Φ⟩
    P.shearObservable (QuotientGroup.mk (A.shearGroupLift s hs t)) =
      (B.shearTransformedSlots hw (A.loweringAt t)).patchValue Φ := by
  intro P
  change polynomialShearOrbitSum w s hs P.shearKernel (A.shearGroupLift s hs t) = _
  rw [P.shearOrbitSum_eq_patchValue]
  simp only [P, shearGroupLift, MulEquiv.apply_symm_apply, inv_inv]

theorem shearObservable_eval_orbit [Fintype (PolynomialShearIndex w)]
    (B : PolynomialSlots X d w) (A : PolynomialSlots Y d w)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
    (Φ : PatchKernel d) (t : Y → ℝ) :
    let P : PolynomialPatch X s d := ⟨w, hpos, hs, hw, B, Φ⟩
    P.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration w s hs).realification.polynomialOrbitRealEval
        (fun _ : Y => 1) t (A.shearPolynomialOrbit s hs))) =
      (B.shearTransformedSlots hw (A.loweringAt t)).patchValue Φ := by
  rw [A.shearPolynomialOrbit_realEval]
  exact shearObservable_eval_lift B A hw hpos hs Φ t

end Erdos3.PolynomialSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.VaryingRankFixedPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialPatch

def castRank {X : Type*} {s d e : ℕ} (P : PolynomialPatch X s d) (h : d = e) :
    PolynomialPatch X s e := h ▸ P

theorem castRank_value {X : Type*} {s d e : ℕ} (P : PolynomialPatch X s d)
    (h : d = e) (t : X → ℝ) : (P.castRank h).value t = P.value t := by
  subst e
  rfl

theorem castRank_kernel_lip {X : Type*} {s d e : ℕ} (P : PolynomialPatch X s d)
    (h : d = e) : (P.castRank h).kernel.lip = P.kernel.lip := by
  subst e
  rfl

def formAtWeight {X : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
    (w : Fin d → ℕ) (h : P.weight = w) : PolynomialSlots X d w := h ▸ P.form

theorem formAtWeight_value {X : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
    (w : Fin d → ℕ) (h : P.weight = w) (t : X → ℝ) :
    ((P.formAtWeight w h).slots t).patchValue P.kernel = P.value t := by
  subst w
  rfl

def rankWeightCode {X : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
    (D : ℕ) (hd : d ≤ D) : Fin (D + 1) × (Fin D → Fin (s + 1)) :=
  (⟨d, Nat.lt_succ_of_le hd⟩, fun i =>
    if hi : i.val < d then ⟨P.weight ⟨i.val, hi⟩, Nat.lt_succ_of_le (P.weight_le _)⟩ else 0)

theorem rankWeightCode_eq {X : Type*} {s d e D : ℕ}
    (P : PolynomialPatch X s d) (Q : PolynomialPatch X s e)
    (hd : d ≤ D) (he : e ≤ D)
    (hc : P.rankWeightCode D hd = Q.rankWeightCode D he) :
    ∃ h : d = e, (P.castRank h).weight = Q.weight := by
  have hde : d = e := congrArg (fun c => c.1.val) hc
  subst e
  refine ⟨rfl, ?_⟩
  funext i
  have h := congrArg (fun c => (c.2 ⟨i.val, i.isLt.trans_le hd⟩).val) hc
  simpa only [rankWeightCode, dif_pos i.isLt, castRank] using h

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

open Module Submodule

noncomputable def poly (q : ℕ) (X : Type*) (j : Fin q) :
    VectorPolynomial X ℝ (J q j → ℝ) := 0

end Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformPhysicalVisitBounds
namespace OAI

section

namespace Erdos3

universe u v

namespace PhysicalEpochComparison

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def Controlled (c : PhysicalEpochComparison base m a J gap) : Prop :=
  (a : ℝ) ≤ Real.exp base.recordBudget ∧
  ∀ i, 2 * Real.exp (-base.recordBudget) * (base.sides i : ℝ) ≤ (c.sides i : ℝ)

end PhysicalEpochComparison

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalStabilityParameters
namespace OAI

section

namespace Erdos3.PhysicalEpochStack

open scoped BigOperators

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound s : ℕ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

def periods : {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} → PhysicalEpochStack base → List ℕ
  | _, _, .zero _ => []
  | _, _, .succ frame tail => frame.period :: periods tail

end Erdos3.PhysicalEpochStack

end

section

namespace Erdos3

universe u v

namespace PhysicalEpochStack

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}

inductive RecordEvent (m J : ℕ) : {s : ℕ} → {base : PhysicalEpochSource.{u, v} σ s bound} →
    PhysicalEpochStack base → Prop
  | head {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base) (tail : PhysicalEpochStack frame.child)
      (state : PhysicalEpochRecords base)
      (record : ∃ r, state.records = r :: frame.state.records)
      (moduli : ∀ r ∈ state.records, r.modulus ∣ m * J)
      (drop : state.dimension < frame.state.dimension) : RecordEvent m J (.succ frame tail)
  | tail {s : ℕ} {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base) {oldTail : PhysicalEpochStack frame.child}
      (event : RecordEvent m J oldTail) : RecordEvent m J (.succ frame oldTail)

end PhysicalEpochStack

open PhysicalEpochStack

end Erdos3

end

section

namespace Erdos3

open PhysicalEpochStack

universe u v

structure PhysicalStabilityParameters (limit : ℕ) where
  C : ℕ
  A : ℕ
  Kf : ℕ
  K : ℕ
  C_ge_two : 2 ≤ C
  A_pos : 1 ≤ A
  Kf_ge_two : 2 ≤ Kf
  K_ge_two : 2 ≤ K
  growth : ∀ b : ℝ, 0 ≤ b → physicalEpochBudget A C b limit ≤ (b + 2) ^ K
  frames : ∀ t : ℕ, t ≤ limit → PhysicalFrameConstructionBound.{u, v} t C
  event :
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
      (b : ℝ) (depth : ℕ) (selected : σ → ℤ)
      {base : PhysicalEpochSource.{u, v} σ s bound}
      (stack : PhysicalEpochStack base) (c : PhysicalEpochComparison base m a J gap),
    0 ≤ b → depth + s ≤ limit → ScheduledAt A C b depth stack → AlignedAt m selected stack →
    c.Controlled → (∀ i, c.anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    (m * a * stack.periods.prod).Coprime J →
    (∀ i, ((m * J : ℕ) : ℝ) * Real.exp
      (5 * physicalEpochBudget A C b (depth + s) +
        2 * (physicalEpochBudget A C b (depth + s) + 2) ^ Kf + 16) ≤ (base.sides i : ℝ)) →
    ∀ anchor : σ → ℤ,
    (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
    (∀ i, anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    ∃ next : PhysicalEpochStack base,
      Event stack next ∧ AlignedAt (m * J) anchor next ∧ ScheduledAt A C b depth next

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedLayerFreezing
namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open _root_.MvPolynomial

variable {σ τ : Type*} {s D E h : ℕ} {A : PolynomialPatch σ s (D + E)}

noncomputable def reparam (L : A.LowestLayerModel h)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) :
    (A.reparam f hf).LowestLayerModel h where
  matrix := L.matrix
  strict := L.strict
  origin i := aeval f (L.origin i)
  degree i := weightedSupportLE_aeval (fun _ : σ => 1) (fun _ : τ => 1) f hf (L.degree i)
  weights := L.weights
  form_eq t := by
    change ((A.form.reparam f hf).slots t).takePrefix = _
    rw [PolynomialSlots.reparam_slots, L.form_eq]
    simp only [MvPolynomial.comp_aeval_apply]

noncomputable def onAffineLine (L : A.LowestLayerModel h) (a q : σ → ℝ) :
    (A.onAffineLine a q).LowestLayerModel h :=
  L.reparam (PolynomialPatch.affineLineParameters a q) (PolynomialPatch.affineLineParameters_degree a q)

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

def PatchKernel.zeroWithLip (d : ℕ) (L : ℝ≥0) : PatchKernel d where
  value _ := 0
  nonneg _ := le_rfl
  le_one _ := zero_le_one
  support _ h := (h rfl).elim
  lip := L
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_self]
    exact mul_nonneg L.coe_nonneg (dist_nonneg (x := x) (y := y))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchWeightDescent
namespace OAI

section

namespace Erdos3
open scoped Classical

@[simp] theorem relativePatchDistinctWeights_castRank {X : Type*} {s d e : ℕ}
    (A : PolynomialPatch X s d) (h : d = e) :
    relativePatchDistinctWeights (A.castRank h) = relativePatchDistinctWeights A := by
  subst e
  rfl

@[simp] theorem relativePatchDistinctWeights_coordinateFiber {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ} (A : PolynomialPatch X s d)
    (keep : X → Prop) (fixed : {i // ¬keep i} → ℤ) :
    relativePatchDistinctWeights (A.coordinateFiber keep fixed) = relativePatchDistinctWeights A := rfl

@[simp] theorem relativePatchComplexity_coordinateFiber {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ} (A : PolynomialPatch X s d)
    (keep : X → Prop) (fixed : {i // ¬keep i} → ℤ) :
    relativePatchComplexity (A.coordinateFiber keep fixed) = relativePatchComplexity A := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualOrdinaryPointwiseSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ γ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
  (w : σ → ℕ)

noncomputable def gradedImagePointwiseSpanningFamily (v : γ → F.AssociatedGraded) :
    SymbolBasisIndex w ν × γ → G.PolynomialSymbol w :=
  G.pointwiseSymbolSpanningFamily c ν hG w (F.gradedImageSpanningFamily G φ hφ v)

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedImagePointwiseSpanningFamily_span [Fintype (SymbolBasisIndex w ν)]
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v)) =
      (G.symbolPointwiseSubalgebra c ν hG w
        (W.map (F.associatedGradedMap G φ hφ))).toSubmodule := by
  exact G.pointwiseSymbolSpanningFamily_span c ν hG w
    (W.map (F.associatedGradedMap G φ hφ))
    (F.associatedGradedMap_image_graded G e ω hF c ν hG φ hφ W hW)
    (F.gradedImageSpanningFamily G φ hφ v)
    (F.gradedImageSpanningFamily_span G φ hφ W v hv)

theorem gradedImagePointwiseSpanningFamily_height [Fintype ι]
    (v : γ → F.AssociatedGraded) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight
      ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) :
    ∀ z i, RationalHeightLE ((G.polynomialSymbolBasis c ν hG w).repr
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v z) i)
        ⌈Real.exp ((p + 2) ^ 4)⌉₊ := by
  exact G.pointwiseSymbolSpanningFamily_height c ν hG w
    (F.gradedImageSpanningFamily G φ hφ v) (one_le_ceil_exp _)
    (fun a j => rationalHeightLE_ceil_exp
      (F.gradedImageSpanningFamily_logHeight G φ hφ e ω hF c ν hG v hp hι hvH hφH a j))

theorem gradedImagePointwiseSpanningFamily_controlled
    [Fintype σ] [Fintype ι] [Fintype κ] [Fintype γ]
    [Fintype (SymbolBasisIndex w ν)]
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hw : ∀ i, 0 < w i) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight
      ((F.associatedGradedBasis e ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (e i)) j) ≤ p) :
    Submodule.span ℚ (Set.range
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v)) =
        (G.symbolPointwiseSubalgebra c ν hG w
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule ∧
    BasisGradedSubmodule (G.associatedGradedBasis c ν hG) ν
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    (∀ z i, RationalHeightLE ((G.polynomialSymbolBasis c ν hG w).repr
      (F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG w v z) i)
        ⌈Real.exp ((p + 2) ^ 4)⌉₊) ∧
    (Fintype.card (SymbolBasisIndex w ν × γ) : ℝ) ≤ pointwiseFastSectionInput t p ∧
    1 ≤ ⌈Real.exp ((p + 2) ^ 4)⌉₊ ∧
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  exact ⟨F.gradedImagePointwiseSpanningFamily_span G φ hφ c ν hG w e ω hF W v hW hv,
    F.associatedGradedMap_image_graded G e ω hF c ν hG φ hφ W hW,
    F.gradedImagePointwiseSpanningFamily_height G φ hφ c ν hG w e ω hF v hp hι hvH hφH,
    G.pointwiseSpanningIndex_card_le c ν hG w hw hp hκ hγ hσ,
    one_le_ceil_exp _, gradedImagePointwiseSpanning_heightBound hp⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ γ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype γ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (c : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))

theorem ordinaryGradedImagePointwiseSpanning_controlled
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : γ → F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hγ : (Fintype.card γ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hvH : ∀ a i, rationalLogHeight
      ((F.associatedGradedBasis b ω hF).repr (v a) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p) :
    let vg := F.gradedImagePointwiseSpanningFamily G φ hφ c ν hG (fun _ : σ => 1) v
    Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule ∧
    BasisGradedSubmodule (G.associatedGradedBasis c ν hG) ν
      (W.map (F.associatedGradedMap G φ hφ)).toSubmodule ∧
    (∀ z i, RationalHeightLE ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr
      (vg z) i) ⌈Real.exp ((p + 2) ^ 4)⌉₊) ∧
    (Nat.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ ordinaryImagePointwiseBudget s t p ∧
    (Nat.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ ordinaryImagePointwiseBudget s t p ∧
    (Nat.card (SymbolBasisIndex (fun _ : σ => 1) ν × γ) : ℝ) ≤ ordinaryImagePointwiseBudget s t p ∧
    1 ≤ ⌈Real.exp ((p + 2) ^ 4)⌉₊ ∧
    (⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp (ordinaryImagePointwiseBudget s t p) := by
  let : Fintype (SymbolBasisIndex (fun _ : σ => 1) ω) :=
    F.ordinarySymbolBasisFintype b ω hF
  let : Fintype (SymbolBasisIndex (fun _ : σ => 1) ν) :=
    G.ordinarySymbolBasisFintype c ν hG
  obtain ⟨hspan, hgraded, hheight, hcount, hH, hHexp⟩ :=
    F.gradedImagePointwiseSpanningFamily_controlled G φ hφ c ν hG (fun _ : σ => 1)
      b ω hF W v hW hv (fun _ => Nat.zero_lt_one) hp hι hκ hγ hσ hvH hφH
  refine ⟨hspan, hgraded, hheight, ?_, ?_, ?_, hH, ?_⟩
  · have hsource := F.symbolBasisIndex_card_le_spanning_budget b ω hF
      (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) hp hι hσ
    simpa only [Nat.card_eq_fintype_card] using
      (hsource.trans (symbolCount_le_sectionInput s hp)).trans
        (ordinaryImagePointwiseBudget_source s t hp)
  · have htarget := G.symbolBasisIndex_card_le_spanning_budget c ν hG
      (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) hp hκ hσ
    simpa only [Nat.card_eq_fintype_card] using
      (htarget.trans (symbolCount_le_sectionInput t hp)).trans
        (ordinaryImagePointwiseBudget_target s t hp)
  · simpa only [Nat.card_eq_fintype_card] using
      hcount.trans (ordinaryImagePointwiseBudget_target s t hp)
  · exact hHexp.trans (Real.exp_le_exp.mpr (ordinaryImagePointwiseBudget_height s t hp))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledMarkedPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_prescribed_real_polynomial_lift
    {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧ l ∣ m ∧
      ∀ (x : F.RealPolynomialSymbolGroup w)
        (q : (G.realification.adaptedPolynomialFiltration w).Group),
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ x.coord =
        (G.realPolynomialSymbolHom c τ hG w q).coord →
      ∃ z : (F.realification.adaptedPolynomialFiltration w).Group,
        F.realPolynomialSymbolHom b ω hF w z = x ∧
        F.realPolynomialGroupMap G φ hφ w z = q ∧
        (∀ (a : ℕ) (T : σ → ℝ), (∀ i, 0 < T i) →
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) x →
          CoefficientBound (c.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) q.coord.val →
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ (a + 12))) z.coord.val) ∧
        (F.SymbolRationalGrid b ω hF w l x → CoefficientGrid (c.baseChange ℝ) l q.coord.val →
          CoefficientGrid (b.baseChange ℝ) m z.coord.val) := by
  classical
  obtain ⟨S, hS, hSlayer, hheight⟩ := F.exists_bounded_filtered_section G b ω hF c τ hG
    φ.toLinearMap hsurj hH hentries
  have hφm : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact hentries i j
  have hSm : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j)
      (rationalKernelHeight (Fintype.card κ) H) := by
    intro i j
    simpa only [LinearMap.toMatrix_apply] using hheight i j
  let m := matrixDenominator (LinearMap.toMatrix c b S) *
    matrixDenominator (LinearMap.toMatrix b c φ.toLinearMap) * l
  obtain ⟨hm, hlm, _⟩ := sectionCorrectedPolynomial_denominator_bounds b c φ.toLinearMap S hφm hSm hl
  refine ⟨m, hm, filtered_section_pair_denominator_le_exp
    (LinearMap.toMatrix b c φ.toLinearMap) (LinearMap.toMatrix c b S) l hp hι hκ hHp hφm hSm hlp,
    hlm, ?_⟩
  intro x q hcompat
  obtain ⟨z, hz, hsymbol, hmarked⟩ := F.sectionCorrectedPolynomial_prescribed_symbol G φ hφ
    b ω hF c τ hG w S hS hSlayer x.coord q.coord hcompat
  refine ⟨⟨z⟩, NilpotentLieBCHGroup.ext hsymbol, NilpotentLieBCHGroup.ext hmarked, ?_, ?_⟩
  · intro a T hT hx hq
    change CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ (a + 12))) z.val
    rw [hz]
    have hx' : CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ a))
        (F.realSymbolRepresentative b ω hF w x.coord) :=
      F.realSymbolRepresentative_slow_coefficients b ω hF w T hT (Real.exp_nonneg _) x hx
    have hout := sectionCorrectedPolynomial_coefficientBound b c φ.toLinearMap S hφm hSm
      (F.realSymbolRepresentative b ω hF w x.coord) q.coord.val T hT
      (Real.exp_nonneg _) (Real.exp_nonneg _) hx' hq
    exact hout.mono _ T hT
      (filtered_section_coefficient_loss_le_exp (Fintype.card ι) (Fintype.card κ) H a hp hι hκ hHp)
  · intro hx hq
    change CoefficientGrid (b.baseChange ℝ) m z.val
    rw [hz]
    have hx' : CoefficientGrid (b.baseChange ℝ) l
        (F.realSymbolRepresentative b ω hF w x.coord) := by
      obtain ⟨v, hv⟩ := F.realSymbolRepresentative_rational_coefficients b ω hF w l x hx
      intro α
      exact ⟨fun i => v (α, i), funext (fun i => congrFun hv (α, i))⟩
    exact sectionCorrectedPolynomial_coefficientGrid b c φ.toLinearMap S
      (F.realSymbolRepresentative b ω hF w x.coord) q.coord.val hl hx' hq

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_marked_polynomial_factorization
    {σ ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧ l ∣ m ∧
      ∀ (a : ℕ) (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
        (E P R : F.RealPolynomialSymbolGroup w),
      E * P * R = F.realPolynomialSymbolHom b ω hF w g →
      ∀ EF RF : (G.realification.adaptedPolynomialFiltration w).Group,
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ E.coord =
        (G.realPolynomialSymbolHom c τ hG w EF).coord →
      (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ R.coord =
        (G.realPolynomialSymbolHom c τ hG w RF).coord →
      F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
      CoefficientBound (c.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) EF.coord.val →
      F.SymbolRationalGrid b ω hF w l R →
      CoefficientGrid (c.baseChange ℝ) l RF.coord.val →
      ∃ e middle r : (F.realification.adaptedPolynomialFiltration w).Group,
        e * middle * r = g ∧
        F.realPolynomialSymbolHom b ω hF w e = E ∧
        F.realPolynomialSymbolHom b ω hF w middle = P ∧
        F.realPolynomialSymbolHom b ω hF w r = R ∧
        F.realPolynomialGroupMap G φ hφ w e = EF ∧
        F.realPolynomialGroupMap G φ hφ w r = RF ∧
        F.realPolynomialGroupMap G φ hφ w middle =
          EF⁻¹ * F.realPolynomialGroupMap G φ hφ w g * RF⁻¹ ∧
        CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + 2) ^ (a + 12))) e.coord.val ∧
        CoefficientGrid (b.baseChange ℝ) m r.coord.val := by
  obtain ⟨m, hm, hmp, hlm, hlift⟩ := F.exists_controlled_prescribed_real_polynomial_lift
    G φ hφ b ω hF c τ hG w hsurj hH hl hentries hp hι hκ hHp hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro a T hT g E P R hprod EF RF hE hR hEslow hEFbound hRgrid hRFgrid
  obtain ⟨e, he, heF, hebound, _⟩ := hlift E EF hE
  obtain ⟨r, hr, hrF, _, hrgrid⟩ := hlift R RF hR
  refine ⟨e, e⁻¹ * g * r⁻¹, r, by group, he, ?_, hr, heF, hrF, ?_,
    hebound a T hT hEslow hEFbound, hrgrid hRgrid hRFgrid⟩
  · rw [map_mul, map_mul, map_inv, map_inv, he, hr, ← hprod]
    group
  · rw [map_mul, map_mul, map_inv, map_inv, heF, hrF]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseCanonicalTopology
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open PolynomialTranslationLie
open scoped TensorProduct

theorem canonicalT2Space (s : ℕ) :
    letI := canonicalTopology s
    T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
  realification_moduleTopology_t2 (nilmanifold s).basis

theorem withCanonicalTopology {P : Prop}
    (h : ∀ [∀ r, TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight r)]
      [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight r)]
      [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight r)]
      [∀ r, T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight r)], P) : P := by
  let (r : ℕ) := canonicalTopology r
  let (r : ℕ) := canonicalTopologicalAddGroup r
  let (r : ℕ) := canonicalContinuousSMul r
  let (r : ℕ) := canonicalT2Space r
  exact h

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPatchShearFiberCandidateScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal TensorProduct

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
  [Fintype (PolynomialShearIndex P.weight)]

theorem shearObservable_local_realEval (A : PolynomialSlots Y d P.weight) (u : Y → ℝ) :
    P.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration P.weight s P.weight_le).realification.polynomialOrbitRealEval
        (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) =
      (P.form.shearTransformedSlots P.weight_mono (A.loweringAt u)).patchValue P.kernel := by
  exact PolynomialSlots.shearObservable_eval_orbit P.form A P.weight_mono
    P.weight_pos P.weight_le P.kernel u

theorem shearObservable_local_integerEval (A : PolynomialSlots Y d P.weight) (u : Y → ℤ) :
    P.shearObservable (QuotientGroup.mk
      ((polynomialShearNilmanifold P.weight s P.weight_le).filtration.realification.polynomialOrbitEval
        (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) =
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u i : ℝ)))).patchValue P.kernel := by
  change P.shearObservable (QuotientGroup.mk
    ((polynomialShearFiltration P.weight s P.weight_le).realification.polynomialOrbitEval
      (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) = _
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
  exact P.shearObservable_local_realEval A _

theorem fullSliceLaw_shearObservable_score [Fintype Y] [DecidableEq Y]
    (A : PolynomialSlots Y d P.weight) {N : Y → ℕ} {q : ℕ}
    (S : ResidueBoxSlice N q) (hq : 0 < q) (hlen : ∀ i, 0 < S.length i)
    (f : (Y → ℤ) → ℝ) (lam : ℝ) :
    (S.fullSliceLaw hlen).mean (fun u => (f u.val - lam) *
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u.val i : ℝ)))).patchValue P.kernel) =
      (𝔼 u ∈ S.integerPoints, ((f u - lam : ℝ) : ℂ) *
        (P.shearObservable (QuotientGroup.mk
          ((polynomialShearNilmanifold P.weight s P.weight_le).filtration.realification.polynomialOrbitEval
            (fun _ : Y => 1) u (A.shearPolynomialOrbit s P.weight_le))) : ℂ)).re := by
  rw [S.fullSliceLaw_mean hlen, S.expect_integerPoints hq, Complex.re_expect]
  apply Finset.expect_congr rfl
  intro u _
  rw [P.shearObservable_local_integerEval]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedKernelRationalGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

theorem exists_marked_kernel_rational_grid_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (b : Basis ι ℚ L) (c : Basis κ ℚ M) (ω : ι → ℕ)
      (_hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
        (l : ℕ), 0 < l →
      (by classical exact
        ((matrixDenominator (LinearMap.toMatrix c b S) * l : ℕ) : ℝ)) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (R : (F.realification.adaptedPolynomialFiltration w).Group)
          (RF : (G.realification.adaptedPolynomialFiltration w).Group),
          F.PolynomialRationalGrid b w l R → G.PolynomialRationalGrid c w l RF →
          F.PolynomialRationalGrid b w m
            ((F.filteredRealPolynomialSection G w S hS RF)⁻¹ * R) := by
  classical
  obtain ⟨C, hC, hprod⟩ := exists_polynomial_rational_product_bound s 2
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ t F G b c ω hlayers w hw H p hH hp hι hσ hHp hb S hS l hl hlp
  let q := matrixDenominator (LinearMap.toMatrix c b S) * l
  have hq : 0 < q := Nat.mul_pos (matrixDenominator_pos _) hl
  have hlq : l ∣ q := dvd_mul_left _ _
  obtain ⟨m, hm, hmp, hqm, hmul⟩ :=
    hprod F b ω hlayers w hw H p hH hp hι hσ hHp hb q hq hlp
  refine ⟨m, hm, hmp, hlq.trans hqm, ?_⟩
  intro R RF hR hRF
  have hs := F.filteredRealPolynomialSection_rationalGrid G b c w S hS l RF hRF
  have hi := F.polynomialRationalGrid_inv b w q _ hs
  have hr := F.polynomialRationalGrid_of_dvd b w hl hlq R hR
  have hout := hmul [(F.filteredRealPolynomialSection G w S hS RF)⁻¹, R]
    (by simp) (by intro r hr'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr';
                  rcases hr' with rfl | rfl; exact hi; exact hr)
  simpa only [List.prod_cons, List.prod_nil, mul_one] using hout

end Erdos3.NilpotentLieFiltration

end

end OAI
end


