-- Prove2me | Definitions.Def_OAIE3v2B151
-- name    : OAIE3v2B151
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:01:06.96701+00:00
-- url     : https://prove2.me/theorems/0f46d0be-e420-46ce-990d-7b58f1813b47
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 153 of 311
-- statement:
--   Definitions bundle 153 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B140`, `OAIE3v2B141` of this split.
--
--   Modules: `Estimates/AdaptedAnchoredComparison.lean`, `Estimates/AntisymmetricPartitionApproximation.lean`, `Estimates/BiasedNativeTerminal.lean`, `Estimates/CommonPivotQuotientTop.lean`, `Estimates/CommonPositivePartitionRefinement.lean`, `Estimates/ControlledComparisonModel.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/HomogeneousQuotientSymbolLiftBounds.lean`, `Estimates/NativeCrossFactorization.lean`, `Estimates/NativeMarkedDiagramOrbitLift.lean`, `Estimates/NativeOptionOriginalOrbit.lean`, `Estimates/NativeSampleModelFamily.lean`, `Estimates/OptionComplementCover.lean`, `Estimates/RealifiedTopQuotient.lean`, `Estimates/SampledNativeModel.lean`, `Estimates/SourceUnitCover.lean`, `Estimates/StepOneSymbolLinearPart.lean`, `Estimates/StrongRefiltrationReconstruction.lean`, `Estimates/TerminalControlledFactorization.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Estimates/UniformFrozenDescent.lean`, `Estimates/WeightedTwistedTranslationLipschitz.lean`, `Geometry/GradedTopCoordinates.lean`, `Geometry/MixedCoordinateTransfer.lean`, `Geometry/SquareRecoveryCoordinates.lean`, `Lattices/FixedAffineResidueDescent.lean`, `Linear/BiasedChosenBasisStepDrop.lean`, `Linear/ExternalFamilyPrecenterProjectionData.lean`, `Linear/NativeDilationPairProjections.lean`, `Linear/RealGradedFastCoefficientKernel.lean`, `Linear/ShiftFailurePositiveBasis.lean`, `Linear/SplitCoverProjection.lean`, `Linear/StepOneGradedKernel.lean`, `Nilpotent/LocalNiltestFixedNativePartners.lean`, `Nilpotent/NativeMultidegreeNiltest.lean`, `Nilpotent/WeightedTranslationTwistedNiltest.lean`, `Polynomial/AntisymmetricBoxPolynomial.lean`, `Polynomial/GradedPolynomialSymbolInverse.lean`, `Polynomial/NativeDegreeRankFamily.lean`, `Polynomial/NativePolynomialOrbitConstruction.lean`, `Polynomial/PrescribedFastPolynomialFactorization.lean`, `Polynomial/RefilteredPolynomialProjection.lean`, `Probability/PositiveDensityNormalization.lean`, `Sampling/MarkedKernelProjectionScoreRestoration.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B140
import Definitions.Def_OAIE3v2B141

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTwistedTranslationLipschitz
namespace OAI

section

namespace Erdos3

namespace PolynomialTranslationLie

open _root_.MvPolynomial NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem twistedBufferedTranslationTerm_lipschitz (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (β : Fin m → ℤ) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (twistedBufferedTranslationTermLip w d Ψ A K)
      (fun g => twistedBufferedTranslationTerm M Ψ D₀ T (bchRealTranslationHom w d hwd g) β) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let C := translationDisplacementNN w d
  let B := bufferedTranslationTermLip w d Ψ A
  let ρ := bchRealTranslationHom w d hwd
  have hC : 0 < (C : ℝ) := weightedTranslationDisplacementConstant_pos _ _ _
  apply lipschitzWith_of_complex_unit_near _ C (B + K * C)
  · intro g
    exact twistedBufferedTranslationTerm_norm_le_one M Ψ D₀ T hT (ρ g) β
  · intro x y hnear
    let z := x * y⁻¹
    have hz : z * y = x := by dsimp [z]; group
    have hdist : dist 1 z = dist x y := by
      have hh := (rightMetricSpace_isometry_mul_right
        ((weightedOrderedBasis w d hw).baseChange ℝ) y⁻¹).dist_eq y x
      simpa only [z, mul_inv_cancel, dist_comm y x] using hh
    have hnearz : dist 1 z ≤ 1 / (C : ℝ) := by
      rw [hdist, le_div_iff₀ hC]
      simpa only [mul_comm] using hnear.le
    have hbounds := bchRealTranslation_bounds_near_one w d hw hd hwd z
    simp only [Fintype.card_fin] at hbounds
    have hb := (hbounds hnearz).1
    change ∀ i, |(ρ z).base i| ≤ (C : ℝ) * dist 1 z at hb
    rw [hdist] at hb
    let rx := fun i => (ρ x).base i - (β i : ℝ)
    let ry := fun i => (ρ y).base i - (β i : ℝ)
    have hres : dist rx ry ≤ (C : ℝ) * dist x y := by
      apply (dist_pi_le_iff (mul_nonneg C.coe_nonneg dist_nonneg)).mpr
      intro i
      have hbase : (ρ x).base i = (ρ z).base i + (ρ y).base i := by
        rw [← hz, map_mul]
        rfl
      dsimp [rx, ry]
      rw [Real.dist_eq, hbase]
      rw [show (ρ z).base i + (ρ y).base i - (β i : ℝ) -
        ((ρ y).base i - (β i : ℝ)) = (ρ z).base i by ring]
      exact hb i
    have hmult : ‖T rx (fun i => (β i : ZMod M)) - T ry (fun i => (β i : ZMod M))‖ ≤
        (K : ℝ) * ((C : ℝ) * dist x y) := by
      simpa only [dist_eq_norm] using
        ((hLip (fun i => (β i : ZMod M))).dist_le_mul rx ry).trans
          (mul_le_mul_of_nonneg_left hres K.coe_nonneg)
    have hphase : ‖bufferedTranslationTerm Ψ D₀ (ρ x) β -
        bufferedTranslationTerm Ψ D₀ (ρ y) β‖ ≤ (B : ℝ) * dist x y := by
      simpa only [dist_eq_norm] using
        (bufferedTranslationTerm_lipschitz w d hw hd hwd Ψ D₀ A hdegree hD β).dist_le_mul x y
    have hbx : ‖bufferedTranslationTerm Ψ D₀ (ρ x) β‖ ≤ 1 := by
      simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
      exact Ψ.le_one _
    have hmul := complex_mul_sub_mul_le_unit
      (T rx (fun i => (β i : ZMod M))) (bufferedTranslationTerm Ψ D₀ (ρ x) β)
      (T ry (fun i => (β i : ZMod M))) (bufferedTranslationTerm Ψ D₀ (ρ y) β)
      hbx (hT _ _)
    apply hmul.trans
    apply (add_le_add hmult hphase).trans_eq
    simp only [NNReal.coe_add, NNReal.coe_mul]
    ring

theorem twistedBufferedTranslationPhase_lipschitz (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r)) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (2 * twistedBufferedTranslationTermLip w d Ψ A K)
      (fun g => twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd g)) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  exact separated_complex_tsum_lipschitz
    (fun β g => twistedBufferedTranslationTerm M Ψ D₀ T (bchRealTranslationHom w d hwd g) β)
    (fun β => twistedBufferedTranslationTerm_lipschitz w d hw hd hwd M Ψ D₀ A K
      hdegree hD T hT hLip β)
    (fun g β γ => twistedBufferedTranslationTerm_unique M Ψ D₀ T
      (bchRealTranslationHom w d hwd g) β γ)

end PolynomialTranslationLie

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedPolynomialRealValueHom (t : σ → ℝ) :
    (F.realification.adaptedPolynomialFiltration w).Group →* F.realification.Group :=
  (F.realification.polynomialOrbitRealEval w t).comp (F.realification.adaptedBCHToOrbit w)

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefilteredPolynomialProjection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

include hφ in
theorem realificationLieHom_mem_layer (j : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ F.realification.layer j) :
    realificationLieHom φ x ∈ G.realification.layer j :=
  baseChange_mem_of_mapsTo (F.layer j) (G.layer j) φ.toLinearMap (hφ j) hx

noncomputable def realPolynomialGroupMap :
    (F.realification.adaptedPolynomialFiltration w).Group →*
      (G.realification.adaptedPolynomialFiltration w).Group :=
  mapOfSteps (hL := (F.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := (G.realification.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ)) (F.realificationLieHom_mem_layer G φ hφ) w)

theorem realPolynomialGroupMap_log
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    ((F.realPolynomialGroupMap G φ hφ w g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) =
      VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
        (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

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

noncomputable def realificationTopQuotientHom :
    ((ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1))) :=
  lieQuotientDescend (F.realification.layerIdeal (s + 1))
    (realLieHomToRat (realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1)))))
    (fun x hx => (realification_mkQ_eq_zero_iff (F.layer (s + 1)) x).mpr hx)

@[simp] theorem realificationTopQuotientHom_mk (x : ℝ ⊗[ℚ] L) :
    F.realificationTopQuotientHom (lieQuotientMap (F.realification.layerIdeal (s + 1)) x) =
      realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) x := rfl

theorem realificationTopQuotientHom_bijective :
    Function.Bijective F.realificationTopQuotientHom := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := lieQuotientMap_surjective (F.realification.layerIdeal (s + 1)) x
    obtain ⟨b, rfl⟩ := lieQuotientMap_surjective (F.realification.layerIdeal (s + 1)) y
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (lieQuotientMap_eq_zero _ _).mpr
    apply (realification_mkQ_eq_zero_iff (F.layer (s + 1)) (a - b)).mp
    change realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy
  · intro y
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ
      (lieQuotientMap_surjective (F.layerIdeal (s + 1))) y
    exact ⟨lieQuotientMap (F.realification.layerIdeal (s + 1)) x, hx⟩

noncomputable def realificationTopQuotientEquiv :
    ((ℝ ⊗[ℚ] L) ⧸ F.realification.layerIdeal (s + 1)) ≃ₗ⁅ℚ⁆
      (ℝ ⊗[ℚ] (L ⧸ F.layerIdeal (s + 1))) :=
  LieEquiv.ofBijective F.realificationTopQuotientHom F.realificationTopQuotientHom_bijective

@[simp] theorem realificationTopQuotientEquiv_mk (x : ℝ ⊗[ℚ] L) :
    F.realificationTopQuotientEquiv (lieQuotientMap (F.realification.layerIdeal (s + 1)) x) =
      realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1))) x := rfl

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

theorem gradedRefiltrationLayer_map_mem (U : LieSubalgebra ℚ F.AssociatedGraded)
    (j : ℕ) (x : L) (hx : x ∈ F.gradedRefiltrationLayer U j) :
    φ x ∈ G.gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) j := by
  obtain ⟨hxF, hxU⟩ := (F.mem_gradedRefiltrationLayer U j x).mp hx
  apply (G.mem_gradedRefiltrationLayer _ j (φ x)).mpr
  exact ⟨hφ j x hxF, F.associatedGradedPieceMap j ⟨x, hxF⟩, hxU,
    F.associatedGradedMap_piece G φ hφ j ⟨x, hxF⟩⟩

noncomputable def gradedRefiltrationMap (U : LieSubalgebra ℚ F.AssociatedGraded) :
    F.gradedRefiltrationSubalgebra U →ₗ⁅ℚ⁆
      G.gradedRefiltrationSubalgebra (U.map (F.associatedGradedMap G φ hφ)) where
  toLinearMap :=
    { toFun x := ⟨φ x, F.gradedRefiltrationLayer_map_mem G φ hφ U 1 x x.property⟩
      map_add' x y := Subtype.ext (map_add φ (x : L) (y : L))
      map_smul' a x := Subtype.ext (map_smul φ a (x : L)) }
  map_lie' {x y} := Subtype.ext (LieHom.map_lie φ x y)

@[simp] theorem gradedRefiltrationMap_apply (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.gradedRefiltrationSubalgebra U) :
    (F.gradedRefiltrationMap G φ hφ U x : M) = φ x := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonPivotQuotientTop
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

section Product

variable {L W : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing W] [LieAlgebra ℚ W] {s : ℕ}

def prod (F : NilpotentLieFiltration L s) (P : NilpotentLieFiltration W s) :
    NilpotentLieFiltration (L × W) s where
  layer j := (F.layer j).prod (P.layer j)
  antitone := by
    intro i j hij x hx
    exact ⟨F.antitone hij hx.1, P.antitone hij hx.2⟩
  one_eq_top := by rw [F.one_eq_top, P.one_eq_top, Submodule.prod_top]
  lie_mem := by
    intro i j x y hx hy
    exact ⟨F.lie_mem hx.1 hy.1, P.lie_mem hx.2 hy.2⟩
  terminal := by rw [F.terminal, P.terminal, Submodule.prod_bot]

@[simp] theorem prod_layer (F : NilpotentLieFiltration L s)
    (P : NilpotentLieFiltration W s) (j : ℕ) :
    (F.prod P).layer j = (F.layer j).prod (P.layer j) := rfl

@[simp] theorem mem_prod_layer (F : NilpotentLieFiltration L s)
    (P : NilpotentLieFiltration W s) (j : ℕ) (x : L × W) :
    x ∈ (F.prod P).layer j ↔ x.1 ∈ F.layer j ∧ x.2 ∈ P.layer j := Iff.rfl

end Product

variable {L Y W J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] [LieRing W] [LieAlgebra ℚ W] {s : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

noncomputable def pivotQuotientFiltration :
    NilpotentLieFiltration (L ⧸ F.pivotAnnihilatorIdeal π eta js) s :=
  F.quotientLie (F.pivotAnnihilatorIdeal π eta js) (by rw [F.terminal]; exact bot_le)

@[simp] theorem pivotQuotientFiltration_layer (j : ℕ) :
    (F.pivotQuotientFiltration π eta js).layer j =
      (F.layer j).map (lieQuotientMap (F.pivotAnnihilatorIdeal π eta js)).toLinearMap := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationTwistedNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

theorem weightedTranslationTwistedObservable_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space) :
    ‖weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T g‖ ≤ 1 :=
  twistedBufferedTranslationQuotientPhase_norm_le_one M Ψ D₀ T hT _

variable [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedTranslationTwistedObservable_lipschitz
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r)) :
    letI := (weightedTranslationResidueNilmanifold w d hw hwd M hM).metricSpace
    LipschitzWith (2 * twistedBufferedTranslationTermLip w d Ψ A K)
      (weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T) := by
  let e := (weightedOrderedBasis w d hw).baseChange ℝ
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) := e.finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace_isIsometricSMul
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  exact rightCosetMetricSpace_lipschitz_lift
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice_closed_discrete.1
    (weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T)
    (twistedBufferedTranslationPhase_lipschitz w d hw hd hwd M Ψ D₀ A K hdegree hD T hT hLip)

noncomputable def weightedTranslationTwistedNiltest {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest ω where
  orbit := q
  observable := weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T
  normBound := 1
  lipBound := 2 * twistedBufferedTranslationTermLip w d Ψ A K
  norm_le := weightedTranslationTwistedObservable_norm_le_one w d hw hwd M hM Ψ D₀ T hT
  lipschitz := weightedTranslationTwistedObservable_lipschitz
    w d hw hwd M hM hd Ψ D₀ A K hdegree hD T hT hLip

@[simp] theorem weightedTranslationTwistedNiltest_eval {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℤ) :
    (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD T hT hLip q).eval t =
      twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω t q)) := rfl

@[simp] theorem weightedTranslationTwistedNiltest_evalReal {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℝ) :
    (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD T hT hLip q).evalReal t =
      twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval ω t q)) := rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeSampleCorrelation {σ X : Type*} (w : σ → ℕ)
    (degree : ℕ) (p : ℝ) (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  complexity : test.ComplexityLE p
  correlation : Real.exp (-p) ≤ ‖𝔼 x ∈ S, f x * star (test.eval (sample x))‖

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct Pointwise BigOperators

structure NativeSampleModel {σ X : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (f : X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest w
  norm : test.normBound ≤ 1
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = test.eval (sample x)

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

theorem NativeSampleModel.norm_le (F : NativeSampleModel w degree p sample f) (x : X) :
    ‖f x‖ ≤ 1 := by
  rw [F.eval]
  exact (F.test.norm_eval_le _).trans F.norm

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {σ X : Type*} {w : σ → ℕ} {degree : ℕ} {p : ℝ}
  {sample : X → σ → ℤ} {f : X → ℂ}

structure VerticalExpansion (native : NativeSampleModel w degree p sample f)
    (q rho : ℝ) where
  I : Type
  [finite : Fintype I]
  frequency : I → native.L →ₗ[ℚ] ℚ
  component : I → native.model.Niltest w
  card_le : (Fintype.card I : ℝ) ≤ Real.exp (verticalDecompositionBudget q)
  height_le : ∀ i j, rationalLogHeight (frequency i (native.model.basis j)) ≤
    verticalDecompositionBudget q
  orbit_eq : ∀ i, (component i).orbit = native.test.orbit
  norm_eq : ∀ i, (component i).normBound = native.test.normBound
  lip_eq : ∀ i, (component i).lipBound = native.test.lipBound
  vertical : ∀ i (z : native.model.RealGroup),
    z ∈ native.model.filtration.realification.subgroup degree → ∀ x,
      (component i).observable (z • x) =
        character ((realifyFunctional (frequency i) z.coord : ℝ) : CircleFourier.Circle) *
          (component i).observable x
  integral : ∀ i, (∃ x, (component i).observable x ≠ 0) →
    ∀ z : native.model.RealGroup,
      z ∈ native.model.filtration.realification.subgroup degree →
      z ∈ native.model.realLattice → ∃ n : ℤ, realifyFunctional (frequency i) z.coord = n
  preserves_character : ∀ (z : native.model.RealGroup) (c : ℂ),
    (∀ x, native.test.observable (z • x) = c * native.test.observable x) →
      ∀ i x, (component i).observable (z • x) = c * (component i).observable x
  observable_error : ∀ x,
    ‖(∑ i, (component i).observable x) - native.test.observable x‖ ≤ rho

attribute [instance] VerticalExpansion.finite

end Erdos3.NativeSampleModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalNiltestFixedNativePartners
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def withOrbit (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) : D.Niltest v where
  orbit := g
  observable := T.observable
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le := T.norm_le
  lipschitz := T.lipschitz

theorem withOrbit_eval (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) (x : τ → ℤ) :
    (T.withOrbit g).eval x = T.observable
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval v x g)) := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def constantGroupOrbit (g : F.Group) : F.PolynomialOrbit w :=
  polynomialOrbitOfLog (monomial (R := ℚ) 0 g.coord)
    ((F.mem_adaptedSubmodule w _).mp
      (F.monomial_mem_adaptedSubmodule w 0 (by
        simp only [map_zero]
        exact F.antitone (Nat.zero_le 1) (by simp [F.one_eq_top]))))

@[simp] theorem polynomialOrbitEval_constantGroupOrbit (g : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval w x (F.constantGroupOrbit w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp [polynomialOrbitEval_coord, constantGroupOrbit, eval_monomial]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def withLeftTranslatedOrbit (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) : D.Niltest v :=
  T.withOrbit (D.filtration.realification.constantGroupOrbit v g * orbit)

@[simp] theorem withLeftTranslatedOrbit_observable (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) :
    (T.withLeftTranslatedOrbit g orbit).observable = T.observable := rfl

@[simp] theorem withLeftTranslatedOrbit_complexity (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) (p : ℝ) :
    (T.withLeftTranslatedOrbit g orbit).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

@[simp] theorem withLeftTranslatedOrbit_eval (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) (x : τ → ℤ) :
    (T.withLeftTranslatedOrbit g orbit).eval x = T.observable
      (g • QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval v x orbit)) := by
  rw [withLeftTranslatedOrbit, withOrbit_eval, map_mul,
    NilpotentLieFiltration.polynomialOrbitEval_constantGroupOrbit]
  rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

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

noncomputable def kernelProjection (T : D.Niltest w)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s) : D.Niltest w := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  exact T.averageCircles
    (fun i => D.centralRationalCircle (b i).val (hK (b i).property))
    (List.finRange (finrank ℚ K))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3
open Module CircleFourier
open scoped TensorProduct BigOperators Classical

structure ExternalFamilyPrecenterProjectionData
    {L σ X : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
    (T : X → D.Niltest w) (p q : ℝ) where
  Freq : Type
  instFintype : Fintype Freq
  eta : Freq → L →ₗ[ℚ] ℚ
  U : Freq → X → D.Niltest w
  card_bound : (@Fintype.card Freq instFintype : ℝ) ≤ Real.exp q
  eta_height : ∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ q
  U_bounds : ∀ j x, (U j x).ComplexityLE q ∧
    (U j x).orbit = (T x).orbit ∧ (U j x).normBound = (T x).normBound ∧
    (U j x).lipBound = (T x).lipBound
  vertical : ∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
    (U j a).observable (z • x) =
      character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
        (U j a).observable x
  contractive : ∀ j a b (ε : ℝ),
    (∀ x, ‖(T a).observable x - (T b).observable x‖ ≤ ε) →
    ∀ x, ‖(U j a).observable x - (U j b).observable x‖ ≤ ε
  select : ∀ {Ω G : Type} [Fintype Ω] [Fintype G],
    ∀ (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s),
    ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
      (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
      (path : Ω → G → D.Space) (weight : Ω → G → ℂ),
    (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
    (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
      (fun x => weight a x * (T (physical a x)).observable (path a x))).re) →
    ∃ (code : Fin (finrank ℚ P) → Option Freq) (S : X → D.Niltest w)
      (retained : Finset Ω),
      (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE q ∧
        (S x).orbit = (T x).orbit) ∧
      (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
        ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
      (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
        ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
      retained ⊆ productive ∧
      outer.mass productive * Real.exp (-q) ≤ outer.mass retained ∧
      ∀ a ∈ retained,
        (∀ i j, code i = some j → Real.exp (-q) <
          ‖(localLaw a).complexMean (fun x =>
            weight a x * (U j (physical a x)).observable (path a x))‖) ∧
        Real.exp (-q) ≤ ((localLaw a).complexMean
          (fun x => weight a x * (S (physical a x)).observable (path a x))).re

attribute [instance] ExternalFamilyPrecenterProjectionData.instFintype

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MarkedKernelProjectionScoreRestoration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

@[simp] theorem polynomialOrbitRealEval_constantGroupOrbit
    (w : σ → ℕ) (g : F.realification.Group) (x : σ → ℝ) :
    F.realification.polynomialOrbitRealEval w x
      (F.realification.constantGroupOrbit w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp only [polynomialOrbitRealEval_coord, constantGroupOrbit, polynomialOrbitOfLog_log,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)

noncomputable def topQuotientMarkedMap :
    (L ⧸ D.filtration.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (M ⧸ E.filtration.layerIdeal (s + 1)) :=
  lieQuotientProjection (D.filtration.layerIdeal (s + 1))
    (E.filtration.layerIdeal (s + 1)) φ (hφ (s + 1))

variable (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

include hQ hQF in
theorem topQuotientMarkedMap_mem_layer (j : ℕ)
    (x : L ⧸ D.filtration.layerIdeal (s + 1)) (hx : x ∈ Q.filtration.layer j) :
    D.topQuotientMarkedMap E φ hφ x ∈ QF.filtration.layer j := by
  rw [hQ] at hx
  rw [hQF]
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨φ z, hφ j z hz, rfl⟩

noncomputable def topQuotientMarkedOrbit (q : Q.filtration.realification.PolynomialOrbit w) :
    QF.filtration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (map (realLieHomToRat (realificationLieHom (D.topQuotientMarkedMap E φ hφ))).toLinearMap q.log)
    (Q.filtration.realification.adapted_map QF.filtration.realification _
      (Q.filtration.realificationLieHom_mem_layer QF.filtration
        (D.topQuotientMarkedMap E φ hφ)
        (D.topQuotientMarkedMap_mem_layer E φ hφ Q hQ QF hQF)) w q.adapted)

@[simp] theorem topQuotientMarkedOrbit_log (q : Q.filtration.realification.PolynomialOrbit w) :
    (D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q).log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (E.filtration.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap q.log := rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeVectorCorrelation {I : Type*} (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : I → ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  complexity : test.ComplexityLE p
  coordinate : I
  correlation : Real.exp (-p) ≤
    ‖𝔼 x, f coordinate x * star (test.evalCyclic N (fun _ => x))‖

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionComplementCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (E : RationalFilteredNilmanifold L s d)

noncomputable def singletonProductSpace (y : E.Space) :
    (pi (fun _ : Unit => E)).Space :=
  (productSpaceEquiv (fun _ : Unit => E)).symm (fun _ => y)

@[simp] theorem productSpaceEquiv_singletonProductSpace (y : E.Space) (i : Unit) :
    productSpaceEquiv (fun _ : Unit => E) (E.singletonProductSpace y) i = y := by
  simp only [singletonProductSpace, Equiv.apply_symm_apply]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SplitCoverProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D E : RationalFilteredNilmanifold L s d)

noncomputable def sublatticeProjection (h : E.lattice ≤ D.lattice) : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice (MonoidHom.id _) (Subgroup.map_mono h)

@[simp] theorem sublatticeProjection_mk (h : E.lattice ≤ D.lattice) (x : E.RealGroup) :
    sublatticeProjection D E h (QuotientGroup.mk x) = QuotientGroup.mk x := rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure UnitVerticalObservable (D : RationalFilteredNilmanifold L s d)
    (T : Subgroup D.RealGroup) (I : Type*) [Fintype I] (p : ℝ) where
  observable : I → D.Space → ℂ
  unit : ∀ x, ∑ i, ‖observable i x‖ ^ 2 = 1
  norm : ∀ i x, ‖observable i x‖ ≤ 1
  lipBound : ℝ≥0
  lip_bound : (lipBound : ℝ) ≤ Real.exp p
  lipschitz : letI := D.metricSpace; ∀ i, LipschitzWith lipBound (observable i)
  frequency : L →ₗ[ℚ] ℚ
  height : ∀ i, rationalLogHeight (frequency (D.basis i)) ≤ p
  vertical : ∀ i z, z ∈ T → ∀ x, observable i (z • x) =
    CircleFourier.character ((realifyFunctional frequency z.coord : ℝ) : CircleFourier.Circle) *
      observable i x
  integral : ∀ z : D.RealGroup, z ∈ T → z ∈ D.realLattice →
    ∃ n : ℤ, realifyFunctional frequency z.coord = n

namespace UnitVerticalObservable

variable {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p q : ℝ}

noncomputable def mono (V : D.UnitVerticalObservable T I p) (hpq : p ≤ q) :
    D.UnitVerticalObservable T I q :=
  { V with
    lip_bound := V.lip_bound.trans (Real.exp_le_exp.mpr hpq)
    height := fun i => (V.height i).trans hpq }

end UnitVerticalObservable

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeMultidegreeNilcharacter {σ : Type*} [Fintype σ] (bound : σ → ℕ) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L (∑ i, bound i) dim
  multi : model.MultidegreeStructure bound
  complexity : multi.ComplexityLE p
  orbit : multi.filtration.realification.PolynomialOrbit
  outputDim : ℕ
  output_pos : 0 < outputDim
  output_bound : (outputDim : ℝ) ≤ Real.exp p
  vertical : model.UnitVerticalObservable (multi.realSubgroup bound) (Fin outputDim) p

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

namespace NativeMultidegreeNilcharacter

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def mono (hpq : p ≤ q) : NativeMultidegreeNilcharacter bound q :=
  { W with
    complexity := W.complexity.mono W.multi hpq
    output_bound := W.output_bound.trans (Real.exp_le_exp.mpr hpq)
    vertical := W.vertical.mono hpq }

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreeRankFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeDegreeRankFamily (s r : ℕ) (A : Type*) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L s dim
  rank : model.DegreeRankStructure r
  complexity : rank.ComplexityLE p
  orbit : A → model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)
  normalized : ∀ a, model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (orbit a) = 1
  outputDim : ℕ
  output_pos : 0 < outputDim
  output_bound : (outputDim : ℝ) ≤ Real.exp p
  vertical : model.UnitVerticalObservable (rank.realSubgroup s r) (Fin outputDim) p

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

end Erdos3

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

noncomputable def optionOriginalSpaceProjection : (optionProduct D₀ D).Space → D₀.Space :=
  productProjection (optionFactors D₀ D) none

@[simp] theorem optionOriginalSpaceProjection_mk (z : (optionProduct D₀ D).RealGroup) :
    optionOriginalSpaceProjection D₀ D (QuotientGroup.mk z) =
      QuotientGroup.mk (productProjectionHom (optionFactors D₀ D) none z) := rfl

@[simp] theorem optionOriginalSpaceProjection_piRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w)
    (x : σ → ℤ) :
    optionOriginalSpaceProjection D₀ D
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x
        (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g))) =
      QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w x (g none)) :=
  congrArg (fun z : D₀.RealGroup => (QuotientGroup.mk z : D₀.Space))
    (piRealOrbit_eval (fun i => (optionFactors D₀ D i).filtration) g x none)

noncomputable def optionOriginalObservable {P : Type*} (observable : P → D₀.Space → ℂ) :
    P → (optionProduct D₀ D).Space → ℂ :=
  fun a z => observable a (optionOriginalSpaceProjection D₀ D z)

@[simp] theorem optionOriginalObservable_apply {P : Type*}
    (observable : P → D₀.Space → ℂ) (a : P) (z : (optionProduct D₀ D).Space) :
    optionOriginalObservable D₀ D observable a z =
      observable a (optionOriginalSpaceProjection D₀ D z) := rfl

@[simp] theorem optionOriginalObservable_piRealOrbit {P σ : Type*} {w : σ → ℕ}
    (observable : P → D₀.Space → ℂ)
    (g : ∀ i, (optionFactors D₀ D i).filtration.realification.PolynomialOrbit w)
    (a : P) (x : σ → ℤ) :
    optionOriginalObservable D₀ D observable a
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x
        (piRealOrbit (fun i => (optionFactors D₀ D i).filtration) g))) =
      observable a (QuotientGroup.mk
        (D₀.filtration.realification.polynomialOrbitEval w x (g none))) := by
  rw [optionOriginalObservable_apply, optionOriginalSpaceProjection_piRealOrbit]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem optionOriginalProjection_layers (k : ℕ)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i)
    (hx : x ∈ (optionProduct D₀ D).filtration.layer k) :
    liePiEval (R := ℚ) none x ∈ D₀.filtration.layer k :=
  (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k x).mp hx none

noncomputable def optionOriginalOrbit {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) :
    D₀.filtration.realification.PolynomialOrbit w :=
  (D₀.filtration.realification.polynomialOrbitCoordinates w).symm
    ((optionProduct D₀ D).filtration.realPolynomialGroupMap D₀.filtration
      (liePiEval none) (optionOriginalProjection_layers D₀ D) w
      ((optionProduct D₀ D).filtration.realification.polynomialOrbitCoordinates w g))

attribute [local irreducible] realPolynomialGroupMap

@[simp] theorem optionOriginalOrbit_log {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) :
    (optionOriginalOrbit D₀ D g).log =
      VectorPolynomial.map ((realificationLieHom (liePiEval (R := ℚ)
        (M := optionLieSpace L₀ L) none)).toLinearMap.restrictScalars ℚ) g.log := by
  unfold optionOriginalOrbit
  rw [polynomialOrbitCoordinates_symm_log]
  exact (optionProduct D₀ D).filtration.realPolynomialGroupMap_log D₀.filtration
    (liePiEval none) (optionOriginalProjection_layers D₀ D) w
    ((optionProduct D₀ D).filtration.realification.polynomialOrbitCoordinates w g)

@[simp] theorem optionOriginalOrbit_eval {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D₀.filtration.realification.polynomialOrbitEval w x (optionOriginalOrbit D₀ D g) =
      productProjectionHom (optionFactors D₀ D) none
        ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ)) (optionOriginalOrbit D₀ D g).log =
    realificationLieHom (liePiEval none) (VectorPolynomial.eval (fun i => (x i : ℚ)) g.log)
  rw [optionOriginalOrbit_log]
  exact VectorPolynomial.eval_map _ _ _

@[simp] theorem optionOriginalOrbit_value {σ : Type*} {w : σ → ℕ}
    (g : (optionProduct D₀ D).filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    optionOriginalSpaceProjection D₀ D
      (QuotientGroup.mk ((optionProduct D₀ D).filtration.realification.polynomialOrbitEval w x g)) =
    QuotientGroup.mk (D₀.filtration.realification.polynomialOrbitEval w x
      (optionOriginalOrbit D₀ D g)) :=
  congrArg (fun z : D₀.RealGroup => (QuotientGroup.mk z : D₀.Space))
    (optionOriginalOrbit_eval D₀ D g x).symm

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledComparisonModel
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

@[simp] theorem pairToPi_one (x : L × L) : pairToPi x 1 = x.2 := rfl

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

def dilationPairToPi (q : ℚ) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ (Fin 2 → L) :=
  pairToPi.comp (F.dilationPairSubalgebra q).incl

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrescribedFastPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realPolynomialSymbolQuotientLinear :
    F.realification.PolynomialSymbol w →ₗ[ℚ] F.RealPolynomialSymbol w :=
  (F.realification.shiftedAdaptedIdeal w).toSubmodule.liftQ
    (F.realPolynomialSymbolMap b ω hlayers w).toLinearMap (by
      intro p hp
      apply (F.realPolynomialSymbolMap_eq_zero_iff b ω hlayers w p).mpr
      exact (F.realification.polynomialSymbolMap_eq_zero_iff w p).mpr hp)

@[simp] theorem realPolynomialSymbolQuotientLinear_map
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolQuotientLinear b ω hlayers w
      (F.realification.polynomialSymbolMap w p) = F.realPolynomialSymbolMap b ω hlayers w p := rfl

noncomputable def realPolynomialSymbolQuotientHom :
    F.realification.PolynomialSymbol w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w where
  toLinearMap := F.realPolynomialSymbolQuotientLinear b ω hlayers w
  map_lie' {x y} := by
    obtain ⟨p, rfl⟩ := F.realification.polynomialSymbolMap_surjective w x
    obtain ⟨q, rfl⟩ := F.realification.polynomialSymbolMap_surjective w y
    change F.realPolynomialSymbolQuotientLinear b ω hlayers w
      ⁅F.realification.polynomialSymbolMap w p, F.realification.polynomialSymbolMap w q⁆ = _
    rw [← LieHom.map_lie, F.realPolynomialSymbolQuotientLinear_map]
    exact (F.realPolynomialSymbolMap b ω hlayers w).map_lie p q

theorem realPolynomialSymbolQuotientHom_bijective :
    Function.Bijective (F.realPolynomialSymbolQuotientHom b ω hlayers w) := by
  constructor
  · intro x y hxy
    obtain ⟨p, rfl⟩ := F.realification.polynomialSymbolMap_surjective w x
    obtain ⟨q, rfl⟩ := F.realification.polynomialSymbolMap_surjective w y
    apply (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hlayers w p q).mp
    exact hxy
  · intro x
    obtain ⟨p, hp⟩ := F.realPolynomialSymbolMap_surjective b ω hlayers w x
    exact ⟨F.realification.polynomialSymbolMap w p, hp⟩

noncomputable def realPolynomialSymbolQuotientEquiv :
    F.realification.PolynomialSymbol w ≃ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieEquiv.ofBijective (F.realPolynomialSymbolQuotientHom b ω hlayers w)
    (F.realPolynomialSymbolQuotientHom_bijective b ω hlayers w)

@[simp] theorem realPolynomialSymbolQuotientEquiv_map
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolQuotientEquiv b ω hlayers w
      (F.realification.polynomialSymbolMap w p) = F.realPolynomialSymbolMap b ω hlayers w p := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativePolynomialOrbitConstruction
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

structure NativePolynomialOrbitFactors {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (eta : L →ₗ[ℚ] ℚ) (A : σ → ℝ) (p : ℝ) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  adapted : ∀ k, D.filtration.layer k = Submodule.span ℚ (basis '' {i | k ≤ weight i})
  basis_height : ∀ i j, rationalLogHeight (D.basis.repr (basis i) j) ≤ p
  subalgebra : LieSubalgebra ℚ D.filtration.AssociatedGraded
  generator : Fin (finrank ℚ L) → D.filtration.AssociatedGraded
  spanning : Submodule.span ℚ (Set.range generator) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule (D.filtration.associatedGradedBasis basis weight adapted)
    weight subalgebra.toSubmodule
  generator_height : ∀ i j, rationalLogHeight
    ((D.filtration.associatedGradedBasis basis weight adapted).repr (generator i) j) ≤ p
  kills_top : ∀ z ∈ D.filtration.realGradedRefiltrationLayer subalgebra s,
    realifyFunctional eta z = 0
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p
  latticeConstant : D.RealGroup
  latticeConstant_mem : latticeConstant ∈ D.realLattice
  slow : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group
  middle : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group
  rational : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group
  product : slow * middle * rational *
    D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) latticeConstant = g
  slow_bound : ∀ α i, |(basis.baseChange ℝ).repr
    (coefficients (slow.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
      Real.exp p / monomialScale A α
  rational_grid : (fun z : (σ →₀ ℕ) × Fin (finrank ℚ L) => (basis.baseChange ℝ).repr
    (coefficients (rational.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈
      realDenominatorGrid denominator
  middle_zero : coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
  rational_zero : coefficients (rational.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
  middle_coefficients : ∀ α, coefficients
    (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      D.filtration.realGradedRefiltrationLayer subalgebra (Finsupp.weight (fun _ => 1) α)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFrozenDescent
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

noncomputable def topQuotientModel (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold (L ⧸ F.layerIdeal (s + 1)) s
      (Fintype.card {i : Fin d // ¬ s + 1 ≤ w i}) :=
  F.coordinateQuotientModel b w hlayers (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hlayers (s + 1)) Γ N hN hin hout

@[simp] theorem topQuotientModel_filtration (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).filtration = F.quotientTop := rfl

@[simp] theorem topQuotientModel_lattice (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    (F.topQuotientModel b w hlayers Γ N hN hin hout).lattice =
      Γ.map (F.quotientStepHom (F.layerIdeal (s + 1)) le_rfl) := rfl

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

structure PositiveCyclicModel (degree N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℝ) where
  L : Type u
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  positive : test.UnitIntervalValued
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = (test.evalCyclic N (fun _ => x)).re

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeDilationPairProjections
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairProjection (q : ℚ) (j : Fin 2) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ L :=
  (liePiEval j).comp (F.dilationPairToPi q)

@[simp] theorem dilationPairProjection_zero (q : ℚ) :
    F.dilationPairProjection q 0 = F.dilationPairFirst q := rfl

@[simp] theorem dilationPairProjection_one (q : ℚ) :
    F.dilationPairProjection q 1 = F.dilationPairSecond q := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeMultidegreeNiltest
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {σ τ : Type*} [Fintype σ] {bound : σ → ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

noncomputable def component (i : Fin W.outputDim) : W.model.Niltest (fun _ : σ => 1) where
  orbit := W.multi.orbitToOrdinary W.orbit
  observable := W.vertical.observable i
  normBound := 1
  lipBound := W.vertical.lipBound
  norm_le := W.vertical.norm i
  lipschitz := W.vertical.lipschitz i

theorem component_complexity (i : Fin W.outputDim) : (W.component i).ComplexityLE (p + 4) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  refine ⟨W.complexity.1.mono W.model (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + (W.vertical.lipBound : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp p := by linarith [W.vertical.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def boxComponent (out : Fin W.outputDim) (a b : Fin 4) :
    W.model.Niltest (fun _ : Fin 4 => 1) :=
  (W.component out).linearPullbackHom
    ![{ toFun := fun n => n a, map_zero' := rfl, map_add' := fun _ _ => rfl },
      { toFun := fun n => n b, map_zero' := rfl, map_add' := fun _ _ => rfl }]

noncomputable def antisymmetricBoxFactors (i j : Fin W.outputDim) :
    Fin 8 → W.model.Niltest (fun _ : Fin 4 => 1) :=
  ![(W.boxComponent i 0 2).conjugate, W.boxComponent j 2 0,
    W.boxComponent i 1 2, (W.boxComponent j 2 1).conjugate,
    W.boxComponent i 0 3, (W.boxComponent j 3 0).conjugate,
    (W.boxComponent i 1 3).conjugate, W.boxComponent j 3 1]

noncomputable def antisymmetricBoxFrequencies : Fin 8 → (W.L →ₗ[ℚ] ℚ) :=
  ![-W.vertical.frequency, W.vertical.frequency, W.vertical.frequency, -W.vertical.frequency,
    W.vertical.frequency, -W.vertical.frequency, -W.vertical.frequency, W.vertical.frequency]

theorem antisymmetricBoxFactors_complexity (i j : Fin W.outputDim) (k : Fin 8) :
    (W.antisymmetricBoxFactors i j k).ComplexityLE (p + 8) := by
  have hi := (W.component_complexity i).mono (by linarith : p + 4 ≤ p + 8)
  have hj := (W.component_complexity j).mono (by linarith : p + 4 ≤ p + 8)
  fin_cases k
  · exact hi
  · exact hj
  · exact hi
  · exact hj
  · exact hi
  · exact hj
  · exact hi
  · exact hj

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

noncomputable def antisymmetricBoxNiltest (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    (pi (fun _ : Fin 8 => W.model)).Niltest (fun _ : Fin 4 => 1) :=
  piNiltest (fun _ : Fin 8 => W.model) (W.antisymmetricBoxFactors i j)
    (by linarith) (by simpa using hp) (W.antisymmetricBoxFactors_complexity i j)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AntisymmetricBoxPolynomial
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p q : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def antisymmetricBoxPolynomial (i j : Fin W.outputDim) :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun _ : Fin 8 => W.model.filtration)
    (fun k => (W.antisymmetricBoxFactors i j k).orbit)
  ⟨⟨o.log, o.property⟩⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPartitionApproximation
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeAntisymmetricOrbitFactors {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ) (q : ℝ) where
  leftIndex : Fin W.outputDim
  rightIndex : Fin W.outputDim
  basis : Basis (Fin (finrank ℚ (Fin 8 → W.L))) ℚ (Fin 8 → W.L)
  weight : Fin (finrank ℚ (Fin 8 → W.L)) → ℕ
  adapted : ∀ k, (pi (fun _ : Fin 8 => W.model)).filtration.layer k =
    Submodule.span ℚ (basis '' {i | k ≤ weight i})
  basis_height : ∀ i j,
    rationalLogHeight ((pi (fun _ : Fin 8 => W.model)).basis.repr (basis i) j) ≤ q
  subalgebra : LieSubalgebra ℚ (pi (fun _ : Fin 8 => W.model)).filtration.AssociatedGraded
  generator : Fin (finrank ℚ (Fin 8 → W.L)) →
    (pi (fun _ : Fin 8 => W.model)).filtration.AssociatedGraded
  spanning : Submodule.span ℚ (Set.range generator) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule
    ((pi (fun _ : Fin 8 => W.model)).filtration.associatedGradedBasis basis weight adapted)
    weight subalgebra.toSubmodule
  generator_height : ∀ i j, rationalLogHeight
    (((pi (fun _ : Fin 8 => W.model)).filtration.associatedGradedBasis basis weight adapted).repr
      (generator i) j) ≤ q
  kills_top : ∀ z ∈ (pi (fun _ : Fin 8 => W.model)).filtration.realGradedRefiltrationLayer
      subalgebra (∑ k, mixedCorrelationDegree 1 k),
    realifyFunctional (piFrequency W.antisymmetricBoxFrequencies) z = 0
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp q
  latticeConstant : (pi (fun _ : Fin 8 => W.model)).RealGroup
  latticeConstant_mem : latticeConstant ∈ (pi (fun _ : Fin 8 => W.model)).realLattice
  slow :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group
  middle :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group
  rational :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group
  product : slow * middle * rational *
    (pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedConstantGroupHom
      (fun _ : Fin 4 => 1) latticeConstant = W.antisymmetricBoxPolynomial leftIndex rightIndex
  slow_bound : ∀ α i, |(basis.baseChange ℝ).repr
    (coefficients (slow.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) α) i| ≤
      Real.exp q / monomialScale (fun _ : Fin 4 => (N : ℝ)) α
  rational_grid : (fun z : ((Fin 4) →₀ ℕ) × Fin (finrank ℚ (Fin 8 → W.L)) =>
    (basis.baseChange ℝ).repr
      (coefficients (rational.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) z.1) z.2) ∈
        realDenominatorGrid denominator
  middle_zero : coefficients
    (middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) 0 = 0
  rational_zero : coefficients
    (rational.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) 0 = 0
  middle_coefficients : ∀ α, coefficients
    (middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) α ∈
      (pi (fun _ : Fin 8 => W.model)).filtration.realGradedRefiltrationLayer subalgebra
        (Finsupp.weight (fun _ => 1) α)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeAntisymmetricFrozenDescent {p : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N : ℕ}
    (V : NativeAntisymmetricOrbitFactors W N p) (q : ℝ) where
  nonnegative : 0 ≤ p
  [productTopology : TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [productTopologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [productContinuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [productHausdorff : T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  outerBudget : ℝ
  outer_nonnegative : 0 ≤ outerBudget
  outer_bound : outerBudget ≤ q
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp outerBudget
  rational_values : ∀ x : Fin 4 → ℤ,
    ((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).equivFun
      ((pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
        (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.rational).coord ∈
      realDenominatorGrid denominator
  slow_values : ∀ x : Fin 4 → ℤ, (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → ∀ i,
    |((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).repr
      ((pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
        (fun _ : Fin 4 => 1) (fun j => (x j : ℝ)) V.slow).coord i| ≤ Real.exp outerBudget
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L 1 dim
  model_complexity : model.GeometryComplexityLE q
  orbit : model.filtration.realification.PolynomialOrbit (fun _ : Fin 4 => 1)
  descend : ∀ a r : (pi (fun _ : Fin 8 => W.model)).RealGroup,
    (∀ i, |((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).repr a.coord i| ≤
      Real.exp outerBudget) →
    ((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).equivFun r.coord ∈
      realDenominatorGrid denominator →
    ∃ S : model.Niltest (fun _ : Fin 4 => 1), S.orbit = orbit ∧
      S.normBound = (W.antisymmetricBoxNiltest nonnegative V.leftIndex V.rightIndex).normBound ∧
      S.ComplexityLE q ∧ ∀ x : Fin 4 → ℤ,
        S.eval x = (W.antisymmetricBoxNiltest nonnegative V.leftIndex V.rightIndex).observable
          (QuotientGroup.mk (a *
            (pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
              (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.middle * r))

attribute [local instance] NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquareRecoveryCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

@[simp] theorem productProjectionHom_pi_symm (g : ∀ i, (D i).RealGroup) (i : ι) :
    productProjectionHom D i ((realBCHPiEquiv (fun j => (D j).filtration)).symm g) = g i :=
  congrFun ((realBCHPiEquiv (fun j => (D j).filtration)).apply_symm_apply g) i

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShiftFailurePositiveBasis
namespace OAI

section

universe u

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

structure PositiveShiftBasis (degree N : ℕ) [NeZero N] (p : ℝ)
    (a J : ZMod N → ℝ) where
  L : Type u
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  geometry : model.GeometryComplexityLE p
  count : ℕ
  count_le_dim : count ≤ dim
  shifts : Finset (ZMod N)
  shifts_nonempty : shifts.Nonempty
  shifts_large : Real.exp (-p) * N ≤ (shifts.card : ℝ)
  frequency : ZMod N → Fin count → L →ₗ[ℚ] ℚ
  mode : ZMod N → Fin count → model.Niltest (fun _ : Unit => 1)
  test : ZMod N → model.Niltest (fun _ : Unit => 1)
  frequency_height : ∀ h ∈ shifts, ∀ j i, rationalLogHeight (frequency h j (model.basis i)) ≤ p
  mode_complexity : ∀ h ∈ shifts, ∀ j, (mode h j).ComplexityLE p
  mode_orbit : ∀ h ∈ shifts, ∀ j, (mode h j).orbit = (test h).orbit
  mode_norm : ∀ h ∈ shifts, ∀ j, (mode h j).normBound ≤ 1
  mode_vertical : ∀ h ∈ shifts, ∀ j z, z ∈ model.filtration.realification.subgroup degree → ∀ x,
    (mode h j).observable (z • x) = character
      ((realifyFunctional (frequency h j) z.coord : ℝ) : CircleFourier.Circle) * (mode h j).observable x
  mode_bias : ∀ h ∈ shifts, ∀ j, Real.exp (-p) <
    ‖𝔼 n, (mode h j).evalCyclic N (fun _ => n) * (a n : ℂ) * (J (n + h) : ℂ)‖
  independent : ∀ h ∈ shifts,
    LinearIndependent ℚ (fun j => (frequency h j).comp (model.filtration.layer degree).subtype)
  test_positive : ∀ h ∈ shifts, (test h).UnitIntervalValued
  test_complexity : ∀ h ∈ shifts, (test h).ComplexityLE p
  test_invariant : ∀ h ∈ shifts, ∀ z : model.RealGroup,
    z ∈ model.filtration.realification.subgroup degree →
    (∀ j, realifyFunctional (frequency h j) z.coord = 0) → ∀ x,
      (test h).observable (z • x) = (test h).observable x
  test_violation : ∀ h ∈ shifts, Real.exp (-p) <
    𝔼 n, a n * J (n + h) * ((test h).evalCyclic N (fun _ => n)).re

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSampleModelFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeSampleModelFamily {ι σ X : Type*} (w : σ → ℕ) (degree : ℕ) (p : ℝ)
    (sample : X → σ → ℤ) (g : ι → X → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : ι → model.Niltest w
  norm : ∀ i, (test i).normBound ≤ 1
  complexity : ∀ i, (test i).ComplexityLE p
  eval : ∀ i x, g i x = (test i).eval (sample x)

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff
  NativeSampleModelFamily.lie NativeSampleModelFamily.algebra
  NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd
  NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareGradedSndMap :
    F.squareFiltration.quotientTop.AssociatedGraded →ₗ⁅ℚ⁆ F.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTop.associatedGradedMap F.quotientTop
    F.reducedSquareSnd F.reducedSquareSnd_mem

noncomputable def fastGradedDiagonal
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    LieSubalgebra ℚ F.quotientTop.AssociatedGraded :=
  W.map F.reducedSquareGradedSndMap

noncomputable def fullFastGradedDiagonal
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    LieSubalgebra ℚ F.AssociatedGraded :=
  (F.fastGradedDiagonal W).comap F.quotientTopGradedMap

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

noncomputable def reducedSquareGradedDifference :
    F.squareFiltration.quotientTop.AssociatedGraded →ₗ[ℚ] F.AssociatedGraded :=
  (bW).constr ℚ (fun a => Sum.elim (fun _ : ι => (0 : F.AssociatedGraded))
    (fun i : {i // 2 ≤ ω i} => F.associatedGradedBasis e ω hF i.val) a.val)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepOneSymbolLinearPart
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L)

variable (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def stepOneGradedEquiv : L ≃ₗ⁅ℚ⁆ F.AssociatedGraded :=
  { b.repr.trans (F.associatedGradedBasis b ω hlayers).repr.symm with
  map_lie' {x y} := by
    rw [F.stepOne_lie_eq_zero, F.associatedGradedFiltration.stepOne_lie_eq_zero]
    exact map_zero (b.repr.trans (F.associatedGradedBasis b ω hlayers).repr.symm) }

@[simp] theorem stepOneGradedEquiv_coordinate (x : L) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.stepOneGradedEquiv b ω hlayers x) i =
      b.repr x i := by
  change (F.associatedGradedBasis b ω hlayers).repr
    ((F.associatedGradedBasis b ω hlayers).repr.symm (b.repr x)) i = _
  rw [LinearEquiv.apply_symm_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.StepOneGradedKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L 1) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def stepOneGradedFrequency (η : L →ₗ[ℚ] ℚ) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  η.comp (F.stepOneGradedEquiv b ω hlayers).symm.toLinearEquiv.toLinearMap

@[simp] theorem stepOneGradedFrequency_equiv (η : L →ₗ[ℚ] ℚ) (x : L) :
    F.stepOneGradedFrequency b ω hlayers η (F.stepOneGradedEquiv b ω hlayers x) = η x := by
  change η ((F.stepOneGradedEquiv b ω hlayers).symm (F.stepOneGradedEquiv b ω hlayers x)) = _
  rw [LieEquiv.symm_apply_apply]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealGradedFastCoefficientKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def fastGradedRelativeKernel
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    Submodule ℚ F.squareFiltration.quotientTop.AssociatedGraded :=
  W.toSubmodule ⊓ F.reducedSquareGradedSndMap.ker.toSubmodule

noncomputable def fullFastGradedRelative
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    Submodule ℚ F.AssociatedGraded :=
  (F.fastGradedRelativeKernel W).map (F.reducedSquareGradedDifference e ω hF)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GradedTopCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)

noncomputable def quotientTopGradedSection : F.quotientTop.AssociatedGraded →ₗ[ℚ] F.AssociatedGraded :=
  (bQ).constr ℚ (fun i => F.associatedGradedBasis e ω hF i.val)

@[simp] theorem quotientTopGradedSection_basis (i : QuotientTopBasisIndex s ω) :
    F.quotientTopGradedSection e ω hF ((bQ) i) = F.associatedGradedBasis e ω hF i.val :=
  Basis.constr_basis _ _ _ i

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

noncomputable def realSymbolOfGradedPolynomial
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) : F.RealPolynomialSymbol w :=
  ((F.polynomialSymbolBasis e ω hF w).baseChange ℝ).repr.symm
    (supportedCoordinates ((F.associatedGradedBasis e ω hF).baseChange ℝ)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2} P)

noncomputable def realGradedSymbolPolynomialHom :
    F.RealPolynomialSymbolGroup w →*
      PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
  NilpotentLieBCHGroup.map (F.realGradedSymbolPolynomial e ω hF w)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TerminalControlledFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "bG" => F.associatedGradedBasis e ω hF
local notation "SG" => F.RealPolynomialSymbolGroup (fun _ : σ => 1)

def SymbolTerminalFactorization (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (T : σ → ℝ) (original : SG) (p : ℝ) : Prop :=
  ∃ Z : LieSubalgebra ℚ F.AssociatedGraded, BasisGradedSubmodule bG ω Z.toSubmodule ∧
    (∀ x ∈ Z, η (basisGradeProjection bG ω (s + 1) x) = 0) ∧
    ∃ bZ : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
      (∀ i j, (((bG).repr (bZ i : F.AssociatedGraded) j).num.natAbs : ℝ) ≤ Real.exp p ∧
        (((bG).repr (bZ i : F.AssociatedGraded) j).den : ℝ) ≤ Real.exp p) ∧
      ∃ A P B : SG, A * P * B = original ∧
        A.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) (F.fullFastGradedDiagonal W)) ∧
        B.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) (F.fullFastGradedDiagonal W)) ∧
        P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) Z) ∧
        F.SymbolSlowBound e ω hF (fun _ : σ => 1) T (Real.exp p) A ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ F.SymbolRationalGrid e ω hF (fun _ : σ => 1) m B

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedNativeTerminal
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def BiasedNativeTerminalSpec (s C : ℕ) : Prop :=
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
        ∃ (l : ℕ) (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
          (A B R : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
          0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ A * B * R = g ∧
          D.filtration.RealAdaptedCoefficientBound e ω hF (fun _ => 1)
            (fun i => (lengths i : ℝ)) (Real.exp ((p + C) ^ C)) A.coord ∧
          D.filtration.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) l R.coord ∧
          D.filtration.SymbolTerminalFactorization e ω hF W (D.filtration.gradedFrequency e ω hF η)
            (fun i => (lengths i : ℝ))
            (D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
              (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) B)) ((p + C) ^ C)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BiasedChosenBasisStepDrop
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def BiasedChosenBasisStepDropSpec (s C : ℕ) : Prop :=
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
        D.filtration.ControlledSymbolFactorization e ω hF η (fun i => (lengths i : ℝ))
          (D.filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
            (D.filtration.realAdaptedPolynomialGroupHom (fun _ => 1) g)) ((p + C) ^ C)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

namespace NilpotentLieFiltration

noncomputable def scalarAffineOrbitHom {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ) :
    F.PolynomialOrbit (fun _ : σ => 1) →* F.PolynomialOrbit (fun _ : σ => 1) :=
  F.polynomialOrbitSubstitute (scalarAffinePolynomial r h) (scalarAffinePolynomial_support r h)

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedAnchoredComparison
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

noncomputable def AnchoredChildResidueComparison {σ K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing K] [LieAlgebra ℚ K] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (cost η δ : ℝ) (lo : σ → ℤ) (N : σ → ℕ) (M P : ℕ) (u v : σ → ℤ) (J : σ → ℕ) : Prop :=
  let Q := Nat.lcm M (M * P)
  ∃ (lo' : σ → ℤ) (N' : σ → ℕ) (w z : σ → ℤ) (U : V.Niltest (fun _ : σ => 1)),
    (∀ i, lo i ≤ lo' i ∧ lo' i + N' i ≤ lo i + N i) ∧
    (∀ i, 0 < N' i) ∧
    (∀ i, δ * (N i : ℝ) / 8 ≤ (N' i : ℝ) ∧ (N' i : ℝ) ≤ δ * (N i : ℝ) / 2) ∧
    (∀ i, lo' i ≤ w i ∧ w i < lo' i + N' i) ∧
    (∀ i, lo' i ≤ z i ∧ z i < lo' i + N' i) ∧
    (∀ i, w i ≡ u i [ZMOD (M : ℤ)]) ∧
    (∀ i, z i ≡ v i [ZMOD (M * J i : ℕ)]) ∧
    (∀ i, z i ≡ w i [ZMOD (Q : ℤ)]) ∧
    Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun _ => (Q : ℤ)) w) ∧
    Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun i => (Q * J i : ℕ)) z) ∧
    U.orbit = V.filtration.realification.scalarAffineOrbitHom (Q / M : ℕ)
      (fun i => (commonStrideIndex u M w i : ℚ)) child ∧
    U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
    η ≤ ‖residuePairMean U.eval lo' N' Q w z J false - residuePairMean U.eval lo' N' Q w z J true‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ R S V W : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

noncomputable def weightedHomogeneousPart (w : σ → ℕ) (d : ℕ) :
    VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R V :=
  (MvPolynomial.weightedHomogeneousComponent w d).rTensor V

end Erdos3.VectorPolynomial

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

noncomputable def selectedJointReference :
    FiniteProbabilityWeights (A × rectangularWeightIndices 0 W 1) :=
  (FiniteProbabilityWeights.uniformFinset A hA).prod (selectedResidueFiniteLaw modulus T W hW hZ)

end Erdos3

end

end OAI
end


