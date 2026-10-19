-- Prove2me | Definitions.Def_OAIE3v2B228
-- name    : OAIE3v2B228
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:26:01.182464+00:00
-- url     : https://prove2.me/theorems/50ae9c3f-b094-4ebd-b1e8-bccfa511a73f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 233 of 311
-- statement:
--   Definitions bundle 233 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B206`, `OAIE3v2B207`, `OAIE3v2B208`, `OAIE3v2B211` of this split.
--
--   Modules: `Dynamics/CommonRefilteredGlobalMarkedFamilyReset.lean`, `Dynamics/TranslationMajorDetectedPotentialData.lean`, `Estimates/CommonRefilteredFactorsNestedFreeze.lean`, `Estimates/DetectedTranslationMajorBase.lean`, `Estimates/LowTaggedRationalLiftRewrite.lean`, `Estimates/RealSymbolGradedCoefficientBound.lean`, `Geometry/CertifiedFullChartDecompositionSource.lean`, `Geometry/CommonRefilteredFactorsSymbolTransport.lean`, `Geometry/GlobalMarkedNativeChartResetConditions.lean`, `Geometry/InhomogeneousFullChartLift.lean`, `Geometry/SymbolCoordinateFreezeBounds.lean`, `Lattices/LowTaggedAffineCoordinates.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/FullChartPolynomialLiftControl.lean`, `Polynomial/LowTaggedPolynomialCoordinates.lean`, `Polynomial/MajorPhaseDetectedDecomposition.lean`, `Polynomial/MajorPhaseVectorDecomposition.lean`, `Polynomial/PolynomialCoordinateFreezeBounds.lean`, `Probability/AllocatedRecoveredChartMass.lean`, `Sampling/ForecastPreparedScaleBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B207
import Definitions.Def_OAIE3v2B208
import Definitions.Def_OAIE3v2B211

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

variable {X : Type*}

theorem normalizedTwistFrequencyPolynomial_low_eval (cover d : ℕ)
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (u : X → ℝ) :
    MvPolynomial.eval u
        (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly) =
      (∑ i : Fin (Fintype.card (LowTaggedIndex J d)),
        (lowTaggedFrequency J d a i : ℝ) *
          MvPolynomial.eval u (lowTaggedPolynomial J d poly i)) / (cover : ℝ) := by
  classical
  rw [normalizedTwistFrequencyPolynomial_eval]
  calc
    _ = (∑ i : Σ j, J j, if i.1.val + 1 ≤ d then
        (a i : ℝ) * eval u (poly i.1) i.2 else 0) / (cover : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.1.val + 1 ≤ d <;>
        simp only [truncateTaggedFrequency, hi, ite_true, ite_false,
          Int.cast_zero, zero_mul, zero_div, mul_div_assoc]
    _ = _ := by
      rw [lowTagged_sum]
      simp only [lowTaggedFrequency, lowTaggedPolynomial_eval]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowTaggedRationalLiftRewrite
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

theorem normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist
    (M d : ℕ) (hM : 0 < M) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (β : Fin (Fintype.card (LowTaggedIndex J d)) → ℤ) :
    (Real.fourierChar (MvPolynomial.eval u
      (normalizedTwistFrequencyPolynomial M (truncateTaggedFrequency d a) poly)) : ℂ) =
      rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c
        (fun i => MvPolynomial.eval u (lowTaggedPolynomial J d poly i) - c i - (β i : ℝ))
        (fun i => (β i : ZMod M)) := by
  rw [normalizedTwistFrequencyPolynomial_low_eval J]
  symm
  simpa only [sub_add_cancel] using
    rationalLiftCharacterTwist_residual M hM (lowTaggedFrequency J d a) c
      (fun i => MvPolynomial.eval u (lowTaggedPolynomial J d poly i) - c i) β

theorem normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist_affine
    (M d : ℕ) (hM : 0 < M) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (start : X → ℤ) (q : ℤ) (v : X → ℤ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (β : Fin (Fintype.card (LowTaggedIndex J d)) → ℤ) :
    (Real.fourierChar (MvPolynomial.eval (fun x => ((start x + q * v x : ℤ) : ℝ))
      (normalizedTwistFrequencyPolynomial M (truncateTaggedFrequency d a) poly)) : ℂ) =
      rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c
        (fun i => MvPolynomial.eval (fun x => ((start x + q * v x : ℤ) : ℝ))
          (lowTaggedPolynomial J d poly i) - c i - (β i : ℝ))
        (fun i => (β i : ZMod M)) :=
  normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist J M d hM a poly
    (fun x => ((start x + q * v x : ℤ) : ℝ)) c β

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotentialData
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_translationMajorDetectedPotentialData (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ B L ι : Type} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (w : B → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
      {e : ℕ} (D : RationalFilteredNilmanifold L d e),
      let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      ∀ (orbit : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : σ => 1))
        (partner : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (η : weightedSubalgebra w d →ₗ[ℚ] ℚ),
        η (centralRationalElement w d hd 1) = 1 →
      ∀ (T : σ → ℝ) (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
        (Fintype.card B : ℝ) ≤ p →
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ p) →
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) T
          (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
            D orbit partner b ω hLayers) p →
      ∃ (l : ℕ) (E P R : N.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : ι → N.filtration.AssociatedGraded)
        (U : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial B ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
        E * P * R = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          D orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1) T (Real.exp p) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l R ∧
        (∀ t : σ → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : σ => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : σ => 1))
              P.coord)) ∈ realificationLieSubalgebra U) ∧
        U = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ p) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : σ => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ U, ∀ z ∈ U.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤
          Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + (p + 2)^4 + 1 + C)^C) := by
  obtain ⟨C, hC, hpotential⟩ := exists_associatedGraded_controlled_potential d hd
  refine ⟨C, hC, ?_⟩
  intro σ B L ι _ _ _ _ w hw hwd _ M hM e D N orbit partner b ω hLayers η hη
    T p hp hι hB hb hfactor
  obtain ⟨l, E, P, R, W, v, hl, hlp, hprod, hE, hR, hv, hW, hheight, hkill, hP⟩ := hfactor
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
  have hφ : ∀ j, ∀ x ∈ N.filtration.layer j, φ x ∈ (weightedFiltration w d hwd).layer j :=
    pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
  let U := W.map (weightedTranslationGradedProjection N.filtration w d hw hwd φ hφ)
  have hentries (i : ι) (j : WeightedBasisIndex w d) :
      rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p := by
    have h := productProjection_coordinate_logHeight
      (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (b i) (hb i) true (weightedIndexOrder w d j)
    change rationalLogHeight ((weightedOrderedBasis w d hw).repr (φ (b i))
      (weightedIndexOrder w d j)) ≤ p at h
    have he := weightedOrderedBasis_repr w d hw (φ (b i)) (weightedIndexOrder w d j)
    have he' : (weightedOrderedBasis w d hw).repr (φ (b i)) (weightedIndexOrder w d j) =
        (weightedBasis w d hw).repr (φ (b i)) j :=
      he.trans (congrArg ((weightedBasis w d hw).repr (φ (b i)))
        ((weightedIndexOrder w d).symm_apply_apply j))
    exact he' ▸ h
  have hkill' : ∀ x ∈ W,
      basisGradeProjection (N.filtration.associatedGradedBasis b ω hLayers) ω d x = x →
      N.filtration.gradedFrequency b ω hLayers (η.comp φ.toLinearMap) x = 0 := by
    simpa only [pairFrequency_zero_comp] using hkill
  obtain ⟨V, q, hV, hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hpotential N.filtration b ω hLayers w hw hwd φ hφ W hW v hv p hp hι hB
      hentries hheight η hη hkill'
  refine ⟨l, E, P, R, W, v, U, V, q, hl, hlp, hprod, hE, hR, ?_, rfl, hv, hW, hheight, hP, hV, hderiv,
    hq, hqp, hgrid, hmass, hcoeff⟩
  intro t
  have hm := N.filtration.projected_realSymbolRepresentative_mem_homogeneous_image
    (weightedFiltration w d hwd) b ω hLayers
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ (fun _ : σ => 1) W P.coord hP t
  convert hm using 1
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DetectedTranslationMajorBase
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

theorem residuePairProjectedGenerators_data
    {B L ι : Type} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e) :
    let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    ∀ (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
      (hN : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
      {n : ℕ} (v : Fin n → N.filtration.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
      ∀ {p : ℝ}, 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ p) →
      (∀ j i, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p) →
      let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
      let hφ := pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      let U := W.map (weightedTranslationGradedProjection N.filtration w d hw hwd φ hφ)
      let g := detectedTranslationProjectedGenerators N.filtration w d hw hwd φ hφ v
      let C := detectedTranslationProjectedBaseMatrix N.filtration w d hw hwd φ hφ v
      Submodule.span ℚ (Set.range g) = U.toSubmodule ∧
      Submodule.span ℚ (Set.range (fun j i => C i j)) =
        U.toSubmodule.map (baseLinear.comp (weightedSubalgebra w d).subtype) ∧
      (∀ j i, rationalLogHeight ((weightedBasis w d hw).repr (g j) i) ≤ (p + 2)^4) ∧
      (∀ i j, rationalLogHeight (C i j) ≤ (p + 2)^4) ∧
      ∀ j a, rationalLogHeight ((g j).val.polynomial.coeff a) ≤ (p + 2)^4 := by
  intro N b ω hN W n v hv p hp hι hb hcoords φ hφ U g C
  have hentries (i : ι) (j : WeightedBasisIndex w d) :
      rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p := by
    have h := productProjection_coordinate_logHeight
      (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (b i) (hb i) true (weightedIndexOrder w d j)
    change rationalLogHeight ((weightedOrderedBasis w d hw).repr (φ (b i))
      (weightedIndexOrder w d j)) ≤ p at h
    have he := weightedOrderedBasis_repr w d hw (φ (b i)) (weightedIndexOrder w d j)
    have he' : (weightedOrderedBasis w d hw).repr (φ (b i)) (weightedIndexOrder w d j) =
        (weightedBasis w d hw).repr (φ (b i)) j :=
      he.trans (congrArg ((weightedBasis w d hw).repr (φ (b i)))
        ((weightedIndexOrder w d).symm_apply_apply j))
    exact he' ▸ h
  exact ⟨detectedTranslationProjectedGenerators_span N.filtration w d hw hwd φ hφ W v hv,
    detectedTranslationProjectedBaseMatrix_span N.filtration w d hw hwd φ hφ W v hv,
    detectedTranslationProjectedGenerators_coordinate_logHeight N.filtration w d hw hwd φ hφ
      b ω hN hp hι hentries v hcoords,
    detectedTranslationProjectedBaseMatrix_logHeight N.filtration w d hw hwd φ hφ
      b ω hN hp hι hentries v hcoords,
    detectedTranslationProjectedGenerators_polynomial_logHeight N.filtration w d hw hwd φ hφ
      b ω hN hp hι hentries v hcoords⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LowTaggedAffineCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

theorem lowTaggedPolynomial_residueAffine (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (q : ℕ) (r : X → ℤ)
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedPolynomial J d (fun j => residueAffine q r (poly j)) i =
      residueAffinePolynomial q r (lowTaggedPolynomial J d poly i) := by
  apply MvPolynomial.funext
  intro x
  rw [lowTaggedPolynomial_eval, eval_residueAffine,
    residueAffinePolynomial_eval_real, lowTaggedPolynomial_eval]

theorem lowTaggedPolynomial_centered_residueAffine_homogeneousComponent (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (q : ℕ) (r : X → ℤ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    homogeneousComponent (lowTaggedWeight J d i)
        (residueAffinePolynomial q r (lowTaggedPolynomial J d poly i - C (c i))) =
      homogeneousComponent (lowTaggedWeight J d i)
        (lowTaggedPolynomial J d (fun j => residueAffine q r (poly j)) i) := by
  rw [lowTaggedPolynomial_residueAffine]
  have hc : homogeneousComponent (lowTaggedWeight J d i) (C (c i) : MvPolynomial X ℝ) = 0 := by
    apply homogeneousComponent_eq_zero
    simpa using lowTaggedWeight_pos J d i
  simp only [residueAffinePolynomial, map_sub, eval₂Hom_C, hc, sub_zero]

theorem lowTaggedTopPolynomial_centered_residueAffine (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (q : ℕ) (r : X → ℤ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :
    ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
        (fun i => homogeneousComponent (lowTaggedWeight J d i)
          (residueAffinePolynomial q r (lowTaggedPolynomial J d poly i - C (c i)))) =
      lowTaggedTopPolynomial J d (fun j => residueAffine q r (poly j)) := by
  unfold lowTaggedTopPolynomial
  congr 1
  funext i
  exact lowTaggedPolynomial_centered_residueAffine_homogeneousComponent J d poly q r c i

end Erdos3.VectorPolynomial

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

variable {η V : Type*} [Fintype η] [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
variable (N : X → ℕ) (B : ℝ) (eV : Basis η ℝ V)
variable (p : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ V)

theorem majorPhaseVectorDetectedConclusion_of_coordinates
    (hp : ∀ α, Finsupp.weight (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) α ≠ d →
      coefficients p α = 0)
    (hscalar : ∀ i, MajorPhaseDetectedConclusion (L := L) J d U poly c
      (coordinate (eV.coord i).toAddMonoidHom p) N B) :
    MajorPhaseVectorDetectedConclusion (L := L) J d U poly c N B eV p := by
  classical
  simp only [MajorPhaseDetectedConclusion] at hscalar
  choose fast g S Q q hdim hspan hgrade hheight hbase hretain hmass hcoeff
    hq hqB hgrid hden hS hQ hvalue using hscalar
  let slow := ofCoordinates (R := ℚ) eV S
  let rat := ofCoordinates (R := ℚ) eV (fun i => MvPolynomial.map (algebraMap ℚ ℝ) (Q i))
  refine ⟨fast, g, slow, rat, ∏ i, q i,
    (fun i => ⟨hdim i, hspan i, hgrade i, hheight i⟩), hbase, hretain, ?_, ?_,
    majorPhaseCoordinateDenominator_pos q hq,
    majorPhaseCoordinateDenominator_le_exp q B hqB, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [slow, coordinate_ofCoordinates] using hmass i
  · intro i α
    have h := congrArg (fun polynomial : MvPolynomial _ _ => polynomial.coeff α)
      (coordinate_ofCoordinates (R := ℚ) eV S i)
    rw [coeff_coordinate] at h
    exact h ▸ hcoeff i α
  · intro i
    dsimp only [rat]
    rw [coordinate_ofCoordinates]
    exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr
      (majorPhaseCoordinateDenominator_grid q Q hgrid i)
  · intro i
    simpa only [slow, coordinate_ofCoordinates] using hS i
  · intro i
    dsimp only [rat]
    rw [coordinate_ofCoordinates]
    intro α hα
    apply hQ i
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    apply MvPolynomial.mem_support_iff.mp hα
    change (Q i).coeff α = 0 at hz
    change (MvPolynomial.map (algebraMap ℚ ℝ) (Q i)).coeff α = 0
    rw [MvPolynomial.coeff_map, hz, map_zero]
  · intro u z hz
    rw [eval₂_normalizedRealPolynomialChart]
    apply eV.equivFun.injective
    funext i
    change eV.coord i (eval₂ (Sum.elim u z) p) = eV.coord i (_ + _)
    rw [map_add, coordinate_eval₂, coordinate_eval₂, coordinate_eval₂]
    simp only [slow, rat, coordinate_ofCoordinates, MvPolynomial.eval_map]
    have hhom : (coordinate (eV.coord i).toAddMonoidHom p).IsWeightedHomogeneous
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d := by
      intro α hα
      by_contra hweight
      apply hα
      rw [coeff_coordinate, hp α hweight, map_zero]
    simpa only [weightedHomogeneousComponent_eq_self hhom] using hvalue i u z (hz i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseDetectedDecomposition
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

variable {m : ℕ} {X L : Type} [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
  (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
  (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
  (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
  {D : RationalFilteredNilmanifold L t e} (R : D.Niltest (fun _ : X => 1))
  (start : X → ℤ) (q M : ℕ) (hM : 0 < M) (a : (Σ j, J j) → ℤ)
  (hhigh : ∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0)

include hM hhigh in

theorem majorPhase_affine_integrand (v : X → ℤ) :
    let u := fun i => start i + (q : ℤ) * v i
    let A := fun i => residueAffinePolynomial q start
      (lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))
    let y := fun i => MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β u i : ℝ)
    (Real.fourierChar (MvPolynomial.eval
      (fun i => (start i : ℝ) + (q : ℝ) * v i)
      (normalizedTwistFrequencyPolynomial M a poly)) : ℂ) *
      majorPhaseSample J d poly Ψ c F β R.eval u =
    rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c y
        (fun i => (β u i : ZMod M)) * (Ψ.value y : ℂ) *
      (Real.fourierChar (MvPolynomial.eval
        (Sum.elim (fun i => (v i : ℝ)) (fun i => (β u i : ℝ)))
        (jointResidueAffinePolynomial q start F)) : ℂ) *
      (R.scalarAffinePullback (q : ℚ) (fun i => (start i : ℚ))).eval v := by
  have htrunc : truncateTaggedFrequency d a = a := by
    funext i
    rcases i with ⟨j, i⟩
    by_cases hj : j.val + 1 ≤ d
    · simp only [truncateTaggedFrequency, hj, ite_true]
    · simp only [truncateTaggedFrequency, hj, ite_false,
        hhigh j (Nat.lt_of_not_ge hj) i]
  let u : X → ℤ := fun i => start i + (q : ℤ) * v i
  have hfreq := normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist_affine
    J M d hM a poly start q v c (β u)
  rw [htrunc] at hfreq
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hfreq
  have hR : (R.scalarAffinePullback (q : ℚ) (fun i => (start i : ℚ))).eval v = R.eval u := by
    simpa only [Int.cast_natCast, add_comm] using
      R.scalarAffinePullback_eval_integer (q : ℤ) start v
  have hjoint : MvPolynomial.eval
      (Sum.elim (fun i => (v i : ℝ)) (fun i => (β u i : ℝ)))
      (jointResidueAffinePolynomial q start F) =
      MvPolynomial.eval (fun j => ((Sum.elim u (β u) j : ℤ) : ℝ)) F := by
    rw [jointResidueAffinePolynomial_eval]
    apply congrArg (fun x => MvPolynomial.eval x F)
    funext j
    cases j <;> simp only [Sum.elim_inl, Sum.elim_inr, u,
      Int.cast_add, Int.cast_mul, Int.cast_natCast]
  dsimp only
  simp only [residueAffinePolynomial_eval_real, map_sub, eval_C]
  rw [hfreq, hR, hjoint]
  simp only [majorPhaseSample, u, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartDecompositionSource
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem FullChartControlledFactors.mono
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget budget' : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (hle : budget ≤ budget') :
    FullChartControlledFactors F b ω hF J poly N left right budget' := by
  obtain ⟨q, hq, hqB, Echart, hchart, hslow, hgrid⟩ := h
  refine ⟨q, hq, hqB.trans (Real.exp_le_exp.mpr hle), Echart, hchart, ?_, hgrid⟩
  exact CoefficientBound.mono _ _ (fun _ => zero_lt_one) hslow (Real.exp_le_exp.mpr hle)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullChartPolynomialLiftControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ τ ι V : Type*}

theorem CoefficientBound.realChartSubstitute_sharp [Fintype σ]
    [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V] [IsScalarTower ℚ ℝ V]
    (b : Basis ι ℝ V) (T : τ → ℝ) (hT : ∀ i, 0 < T i)
    (f : σ → MvPolynomial τ ℝ) {A B : ℝ} {s : ℕ} {P : VectorPolynomial σ ℚ V}
    (hP : CoefficientBound b (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) s P)
    (hf : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (f i)) ≤ B) :
    CoefficientBound b T
      (((Fintype.card σ : ℝ) + 1) ^ s * A * B ^ s)
      (Erdos3.VectorPolynomial.realChartSubstitute f P) := by
  intro α i
  let Q := coordinate (b.coord i).toAddMonoidHom P
  have hQdeg : Q.totalDegree ≤ s :=
    (degreeLE_one_iff_basis_totalDegree b s P).mp hdegree i
  have hQcoeff (β) : |Q.coeff β| ≤ A := by
    change |b.repr (coefficients P β) i| ≤ A
    simpa [monomialScale] using hP β i
  have hcard : (Q.support.card : ℝ) ≤ ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast mvPolynomial_support_card_le_totalDegree Q hQdeg
  have hbound := scaled_substitution_coeff_bound T hT f Q hB hf hQcoeff hQdeg α
  have heq := congrArg (fun q : MvPolynomial τ ℝ => q.coeff α)
    (coordinate_realChartSubstitute (b.coord i) f P)
  rw [coeff_coordinate] at heq
  change (b.coord i)
    (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α) = _ at heq
  change |(b.coord i)
    (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α)| ≤ _
  rw [heq]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (monomialScale_pos T hT α).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hA)
    (pow_nonneg (zero_le_one.trans hB) s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem realGradedSymbolPolynomialHom_degreeLE
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (left : F.RealPolynomialSymbolGroup w) :
    DegreeLE w s (F.realGradedSymbolPolynomialHom b ω hF w left).coord := by
  intro α hα
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w left.coord α i (by
    have hi := F.adaptedBasis_weight_le_step b ω hF i
    omega)

attribute [local irreducible] realChartSubstitute

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ : Type*} {ι L : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem coefficientBound_gradedBasisSplitting
    (T : σ → ℝ) (M : ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    CoefficientBound (b.baseChange ℝ) T M
      (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ↔
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M P := by
  unfold CoefficientBound
  simp only [coefficients_map, LinearMap.restrictScalars_apply,
    F.gradedBasisSplitting_real_coordinate]

attribute [local irreducible] realChartSubstitute

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.InhomogeneousFullChartLift
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolOfGradedPolynomial realSymbolHomogeneousPullback gradedPolynomialProjection

theorem coefficients_gradedPolynomialProjection (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) (α : σ →₀ ℕ) :
    coefficients (F.gradedPolynomialProjection b ω hF w P) α =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω
        (Finsupp.weight w α) (coefficients P α) := by
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [basisGradeProjection_repr, gradedPolynomialProjection]
  by_cases hi : Finsupp.weight w α = ω i
  · rw [if_pos hi.symm,
      F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(α, i), hi⟩,
      F.realSymbolOfGradedPolynomial_coordinate]
  · rw [if_neg (Ne.symm hi),
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ α i hi]

theorem gradedPolynomialProjection_mem (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    F.gradedPolynomialProjection b ω hF w P ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w := by
  rw [gradedPolynomialProjection]
  exact F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule b ω hF w _

theorem gradedPolynomialProjection_eq_self (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : P ∈ gradedPolynomialSubmodule
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w) :
    F.gradedPolynomialProjection b ω hF w P = P := by
  rw [gradedPolynomialProjection]
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF w P hP

theorem gradedPolynomialProjection_degreeLE (w u : σ → ℕ) (d : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : DegreeLE u d P) :
    DegreeLE u d (F.gradedPolynomialProjection b ω hF w P) := by
  intro α hα
  rw [F.coefficients_gradedPolynomialProjection, hP α hα, map_zero]

theorem gradedPolynomialProjection_coefficientBound (w : σ → ℕ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M P) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
      (F.gradedPolynomialProjection b ω hF w P) := by
  intro α i
  rw [F.coefficients_gradedPolynomialProjection, basisGradeProjection_repr]
  split_ifs
  · exact hP α i
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realSymbolOfGradedPolynomial_homogeneousChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    F.realSymbolOfGradedPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolHomogeneousPullback b ω hF w v β
        (F.realSymbolOfGradedPolynomial b ω hF w p) := by
  classical
  apply ((F.polynomialSymbolBasis b ω hF v).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfGradedPolynomial_coordinate, realSymbolHomogeneousPullback,
    F.realSymbolOfGradedPolynomial_coordinate]
  rw [coefficients_realChartSubstitute, coefficients_realChartSubstitute]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr_of_eq_on_inter
  · intro γ hγ hγ'
    have hz : coefficients (F.realGradedSymbolPolynomial b ω hF w
        (F.realSymbolOfGradedPolynomial b ω hF w p)) γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · have he := F.realGradedSymbolPolynomial_coordinate b ω hF w
        (F.realSymbolOfGradedPolynomial b ω hF w p) ⟨(γ, z.val.2), h⟩
      rw [hz, map_zero, Finsupp.zero_apply, F.realSymbolOfGradedPolynomial_coordinate] at he
      rw [← he, mul_zero]
    · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _
        (fun he => h (he.symm.trans z.property)), zero_mul]
  · intro γ hγ hγ'
    have hz : coefficients p γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfGradedPolynomial_coordinate, hz, map_zero, Finsupp.zero_apply, mul_zero]
    · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ γ z.val.2 h, mul_zero]
  · intro γ hγ hγ'
    have hz := z.property
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfGradedPolynomial_coordinate]
    · have ha : Finsupp.weight v z.val.1 ≠ Finsupp.weight w γ :=
        fun he => h (he.symm.trans hz)
      rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _ ha]
      simp only [zero_mul]

theorem gradedPolynomialProjection_realChartSubstitute
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    F.gradedPolynomialProjection b ω hF v (realChartSubstitute β P) =
      realChartSubstitute β (F.gradedPolynomialProjection b ω hF w P) := by
  rw [gradedPolynomialProjection, gradedPolynomialProjection,
    F.realSymbolOfGradedPolynomial_homogeneousChart b ω hF w v β hβ]
  exact F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ τ : Type*} {ι L : Type} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] realChartSubstitute realSymbolOfGradedPolynomial
  realGradedSymbolPolynomial realSymbolHomogeneousPullback

omit [Fintype σ] in

theorem exists_inhomogeneous_chart_lift_algebraic
    (w : σ → ℕ) (v : τ → ℕ) (E : F.RealPolynomialSymbolGroup w)
    (f : σ → MvPolynomial σ ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hgraded : P ∈ gradedPolynomialSubmodule
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w)
    (hchart : (F.realGradedSymbolPolynomialHom b ω hF w E).coord =
      realChartSubstitute f P)
    (β δ : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v (w i))
    (htop : ∀ i, MvPolynomial.weightedHomogeneousComponent v (w i) (δ i) =
      MvPolynomial.aeval β (f i)) :
    ∃ e : (F.realification.adaptedPolynomialFiltration v).Group,
      e.coord.val = realChartSubstitute δ (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ∧
      F.realPolynomialSymbolHom b ω hF v e =
        F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ E := by
  let Y : F.RealPolynomialSymbolGroup w := ⟨F.realSymbolOfGradedPolynomial b ω hF w P⟩
  have hY : F.realGradedSymbolPolynomial b ω hF w Y.coord = P :=
    F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF w P hgraded
  let S := (F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ
  have hlog : (F.realPolynomialSymbolLift b ω hF w Y).coord.val =
      VectorPolynomial.map (S.restrictScalars ℚ) P := by
    rw [F.realPolynomialSymbolLift_log, F.realSymbolRepresentative_eq_map, hY]
  let e := F.weightedAdaptedRealChartHom w v δ hδ
    (F.realPolynomialSymbolLift b ω hF w Y)
  have he : e.coord.val = realChartSubstitute δ
      (VectorPolynomial.map (S.restrictScalars ℚ) P) := by
    change realChartSubstitute δ (F.realPolynomialSymbolLift b ω hF w Y).coord.val = _
    rw [hlog]
  refine ⟨e, he, ?_⟩
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart,
      F.realPolynomialSymbolHom_lift]
  apply F.realGradedSymbolPolynomialHom_injective b ω hF v
  apply NilpotentLieBCHGroup.ext
  change F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v _ Y.coord) =
      F.realGradedSymbolPolynomial b ω hF v
        (F.realSymbolHomogeneousPullback b ω hF w v β E.coord)
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v _
      (fun _ => MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _),
      F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ, hY]
  change realChartSubstitute _ P =
      realChartSubstitute β (F.realGradedSymbolPolynomialHom b ω hF w E).coord
  rw [hchart, realChartSubstitute_comp]
  exact congrArg (fun z => realChartSubstitute z P) (funext htop)

theorem polynomialSlowBound_inhomogeneous_chart_lift
    {υ : Type*} (v : τ → ℕ) (u : υ → ℕ)
    (e : (F.realification.adaptedPolynomialFiltration v).Group)
    (δ : σ → MvPolynomial τ ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (he : e.coord.val = realChartSubstitute δ (VectorPolynomial.map
      (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P))
    (γ : τ → MvPolynomial υ ℝ) (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
    (T : υ → ℝ) (hT : ∀ i, 0 < T i) {A B : ℝ} {d : ℕ}
    (hbound : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ)
      (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) d P)
    (hmass : ∀ i, realPolynomialMass
      (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ B) :
    F.PolynomialSlowBound b u T
      (((Fintype.card σ : ℝ) + 1) ^ d * A * B ^ d)
      (F.weightedAdaptedRealChartHom v u γ hγ e) := by
  change CoefficientBound (b.baseChange ℝ) T _ (realChartSubstitute γ e.coord.val)
  rw [he, realChartSubstitute_comp]
  exact CoefficientBound.realChartSubstitute_sharp (b.baseChange ℝ) T hT _
    ((F.coefficientBound_gradedBasisSplitting b ω hF _ _ P).mpr hbound)
    hA hB (hdegree.map _) hmass

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GlobalMarkedNativeChartResetConditions
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartHom
  polynomialOrbitRealChart

variable {m s : ℕ} {X τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s)
  (J : Fin m → Type*) [∀ j, Fintype (J j)]
  (Ktag : ∀ j, Submodule ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)

namespace GlobalMarkedNativeFactors

variable {F J Ktag c}
  {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {W : LieSubalgebra ℚ F.AssociatedGraded}

variable {σ : Type*} {w : σ → ℕ}
  {g : (F.realification.adaptedPolynomialFiltration w).Group}
  {E R : F.RealPolynomialSymbolGroup w}

theorem chart_middle_log
    (A : GlobalMarkedNativeFactors F b ω hF w W g E R)
    (v : τ → ℕ) (γ : σ → MvPolynomial τ ℝ)
    (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i)) :
    VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      ((F.gradedRefiltration W).polynomialOrbitRealChart w v γ hγ A.markedMiddle).log =
      (F.weightedAdaptedRealChartHom w v γ hγ A.middle).coord.val := by
  rw [polynomialOrbitRealChart_log, F.weightedAdaptedRealChartHom_coord, ← A.middle_log]
  exact (realChartSubstitute_map γ
    (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl).toLinearMap A.markedMiddle.log).symm

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute
  realPolynomialSymbolHom polynomialOrbitRealChart

variable {α σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem weightedAdaptedRealChartHom_eq_of_fixed_chart
    (w : α → ℕ) (v : σ → ℕ) (β : α → MvPolynomial α ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
    (γ : α → MvPolynomial σ ℝ) (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
    (hfixed : ∀ t : σ → ℝ,
      (fun i => MvPolynomial.eval (fun j => MvPolynomial.eval t (γ j)) (β i)) =
        (fun i => MvPolynomial.eval t (γ i)))
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.weightedAdaptedRealChartHom w v γ hγ
      (F.weightedAdaptedRealChartHom w w β hβ g) =
      F.weightedAdaptedRealChartHom w v γ hγ g := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  simp only [F.weightedAdaptedRealChartHom_coord]
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro t
  rw [map_sub, eval₂_realChartSubstitute, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute, hfixed t, sub_self]

namespace GlobalMarkedNativeFactors

variable {F} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {w : α → ℕ} {v : σ → ℕ}
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {β : α → MvPolynomial α ℝ}
  {hβ : ∀ i, β i ∈ weightedSupportLE w (w i)}
  {g : (F.realification.adaptedPolynomialFiltration w).Group}
  {E R : F.RealPolynomialSymbolGroup w}
  (A : GlobalMarkedNativeFactors F b ω hF w W
    (F.weightedAdaptedRealChartHom w w β hβ g) E R)
  (γ : α → MvPolynomial σ ℝ) (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
  (hfixed : ∀ t : σ → ℝ,
    (fun i => MvPolynomial.eval (fun j => MvPolynomial.eval t (γ j)) (β i)) =
      (fun i => MvPolynomial.eval t (γ i)))

include hfixed

theorem fixed_chart_residual_eq :
    (F.weightedAdaptedRealChartHom w v γ hγ A.left)⁻¹ *
      F.weightedAdaptedRealChartHom w v γ hγ g *
      (F.weightedAdaptedRealChartHom w v γ hγ A.right)⁻¹ =
        F.weightedAdaptedRealChartHom w v γ hγ A.middle := by
  have hprod : F.weightedAdaptedRealChartHom w v γ hγ A.left *
      F.weightedAdaptedRealChartHom w v γ hγ A.middle *
      F.weightedAdaptedRealChartHom w v γ hγ A.right =
        F.weightedAdaptedRealChartHom w v γ hγ g := by
    rw [← map_mul, ← map_mul, A.product,
      F.weightedAdaptedRealChartHom_eq_of_fixed_chart w v β hβ γ hγ hfixed]
  rw [← hprod]
  group

theorem fixed_chart_native_conditions :
    let residual := (F.weightedAdaptedRealChartHom w v γ hγ A.left)⁻¹ *
      F.weightedAdaptedRealChartHom w v γ hγ g *
      (F.weightedAdaptedRealChartHom w v γ hγ A.right)⁻¹
    (F.realPolynomialSymbolHom b ω hF v residual).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF v W) ∧
    coefficients (residual.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∈
      F.realGradedRefiltrationLayer W 1 := by
  dsimp only
  rw [A.fixed_chart_residual_eq γ hγ hfixed]
  exact F.native_refiltered_symbol_conditions W b ω hF v
    ((F.gradedRefiltration W).polynomialOrbitRealChart w v γ hγ A.markedMiddle)
    (F.weightedAdaptedRealChartHom w v γ hγ A.middle) (A.chart_middle_log v γ hγ)

end GlobalMarkedNativeFactors
end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradedCoefficientBound
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolHomogeneousPullback

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem realGradedSymbolPolynomialHom_homogeneousPullback
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) :
    F.realGradedSymbolPolynomialHom b ω hF v
      (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g) =
      realPolynomialChartSubstitution F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
        β (F.realGradedSymbolPolynomialHom b ω hF w g) := by
  apply NilpotentLieBCHGroup.ext
  exact F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ g.coord

theorem realGradedSymbolPolynomialHom_homogeneousPullback_coord
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) :
    (F.realGradedSymbolPolynomialHom b ω hF v
      (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g)).coord =
      realChartSubstitute β (F.realGradedSymbolPolynomialHom b ω hF w g).coord := by
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback b ω hF w v β hβ,
    realPolynomialChartSubstitution_coord]

theorem realGradedSymbolPolynomialHom_homogeneousPullback_of_chart
    {ν : Type*} (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (g : F.RealPolynomialSymbolGroup w) (chart : ν → MvPolynomial σ ℝ)
    (E : PolynomialGroup ν F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot)
    (hchart : F.realGradedSymbolPolynomialHom b ω hF w g =
      realPolynomialChartSubstitution F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
        chart E) :
    (F.realGradedSymbolPolynomialHom b ω hF v
      (F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ g)).coord =
      realChartSubstitute (fun i => MvPolynomial.aeval β (chart i)) E.coord := by
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback_coord b ω hF w v β hβ,
    hchart, realPolynomialChartSubstitution_coord, realChartSubstitute_comp]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem scalarSymbolPolynomial_component_quotient (w : σ → ℕ)
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (k : ℕ) (g : F.RealPolynomialSymbolGroup w) :
    weightedHomogeneousComponent w k (F.scalarSymbolPolynomial b ω hF w (ℓ.comp U.mkQ) g) =
      coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k g.coord) := by
  rw [scalarSymbolPolynomial, realSymbolGradeQuotientPolynomial,
    F.realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart,
    ← coordinate_weightedHomogeneousPart]
  ext α
  simp only [coeff_coordinate, coefficients_map, LinearMap.toAddMonoidHom_coe,
    LinearMap.restrictScalars_apply]
  exact realifyFunctional_comp ℓ U.mkQ _

theorem realSymbolGradeQuotientPolynomial_homogeneousPullback
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ) (x : F.RealPolynomialSymbol w) :
    F.realSymbolGradeQuotientPolynomial b ω hF v U k
        (F.realSymbolHomogeneousPullback b ω hF w v β x) =
      realChartSubstitute β (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro u
  rw [map_sub, eval₂_realChartSubstitute, F.realSymbolGradeQuotientPolynomial_eval,
    F.realSymbolGradeQuotientPolynomial_eval,
    F.realSymbolGradeEvaluation_homogeneousPullback b ω hF w v β hβ, sub_self]

theorem scalarSymbolPolynomial_component_homogeneousPullback
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (k : ℕ) (Z left right : F.RealPolynomialSymbolGroup w) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ
    weightedHomogeneousComponent v k
        (F.scalarSymbolPolynomial b ω hF v (ℓ.comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) =
      aeval β (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k (left⁻¹ * Z * right⁻¹).coord)) := by
  dsimp only
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul,
    F.scalarSymbolPolynomial_component_quotient,
    F.realSymbolHomogeneousPullbackHom_coord,
    F.realSymbolGradeQuotientPolynomial_homogeneousPullback b ω hF w v β hβ]
  apply MvPolynomial.funext
  intro u
  rw [← coordinate_eval₂, eval₂_realChartSubstitute, coordinate_eval₂]
  exact (MvPolynomial.comp_aeval_apply β (MvPolynomial.aeval u) _).symm

theorem scalarSymbolPolynomial_homogeneousComponent_homogeneousPullback
    (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous (fun _ : τ => 1) (w i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (k : ℕ) (Z left right : F.RealPolynomialSymbolGroup w) :
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1) β hβ
    homogeneousComponent k
        (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) (ℓ.comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) =
      aeval β (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U k (left⁻¹ * Z * right⁻¹).coord)) :=
  F.scalarSymbolPolynomial_component_homogeneousPullback b ω hF w (fun _ : τ => 1)
    β hβ U ℓ k Z left right

theorem realSymbolGradeQuotientPolynomial_functional_homogeneous (w : σ → ℕ)
    (U : Submodule ℚ F.AssociatedGraded)
    (ℓ : (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)) →ₗ[ℝ] ℝ)
    (k : ℕ) (x : F.RealPolynomialSymbol w) :
    (coordinate ℓ.toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF w U k x)).IsWeightedHomogeneous w k := by
  intro α hα
  by_contra hweight
  apply hα
  rw [coeff_coordinate,
    F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF w U k x α hweight, map_zero]

theorem exists_sampledCurrentGrade_lower_phase (w : σ → ℕ)
    (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (U : Submodule ℚ F.AssociatedGraded) (ℓ : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] ℚ)
    (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup w) :
    let topβ := fun i => homogeneousComponent (w i) (β i)
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1) topβ
      (fun i => sampledTopPhase_coordinate_homogeneous (w i) (β i))
    ∃ lower : MvPolynomial τ ℝ, lower.totalDegree ≤ n ∧
      aeval β (coordinate (realifyFunctional ℓ).toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w U (n + 1) (left⁻¹ * Z * right⁻¹).coord)) =
      homogeneousComponent (n + 1)
        (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) (ℓ.comp U.mkQ)
          ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) + lower := by
  dsimp only
  let P := coordinate (realifyFunctional ℓ).toAddMonoidHom
    (F.realSymbolGradeQuotientPolynomial b ω hF w U (n + 1) (left⁻¹ * Z * right⁻¹).coord)
  have hP : P.IsWeightedHomogeneous w (n + 1) :=
    F.realSymbolGradeQuotientPolynomial_functional_homogeneous b ω hF w U
      (realifyFunctional ℓ) (n + 1) _
  refine ⟨aeval β P - aeval (fun i => homogeneousComponent (w i) (β i)) P,
    sampledTopPhase_remainder_totalDegree w β hβ hP, ?_⟩
  rw [F.scalarSymbolPolynomial_homogeneousComponent_homogeneousPullback]
  change aeval β P = aeval (fun i => homogeneousComponent (w i) (β i)) P +
    (aeval β P - aeval (fun i => homogeneousComponent (w i) (β i)) P)
  abel

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SymbolCoordinateFreezeBounds
namespace OAI

section

namespace Erdos3
open Module
open scoped Classical

namespace VectorPolynomial

variable {I ι V : Type*} [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem coordinate_coeff_realChartSubstitute_freeze_zero
    (keep : I → Prop) (b : Basis ι ℝ V) (P : VectorPolynomial I ℚ V)
    (α : {i // keep i} →₀ ℕ) (i : ι) :
    b.repr (coefficients (realChartSubstitute (frozenCoordinate keep 0) P) α) i =
      b.repr (coefficients P (α.mapDomain Subtype.val)) i := by
  have h := congrArg (fun Q : MvPolynomial {i // keep i} ℝ => Q.coeff α)
    (coordinate_realChartSubstitute_for_grid (frozenCoordinate keep 0) (b.coord i) P)
  rw [coeff_aeval_frozenCoordinate_zero] at h
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Basis.coord_apply] using h

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinateFreezeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

theorem polynomialRationalGrid_integerChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, MvPolynomial.map (Int.castRingHom ℝ) (β i) ∈ weightedSupportLE v (w i))
    (q : ℕ) (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialRationalGrid b w q g) :
    F.PolynomialRationalGrid b v q
      (F.weightedAdaptedRealChartHom w v
        (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)) hβ g) := by
  classical
  obtain ⟨z, hz⟩ := hg
  have hc : CoefficientGrid (b.baseChange ℝ) q g.coord.val := by
    intro α
    exact ⟨fun i => z (α, i), funext (fun i => congrFun hz (α, i))⟩
  have ho : CoefficientGrid (b.baseChange ℝ) q
      (F.weightedAdaptedRealChartHom w v
        (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i)) hβ g).coord.val := by
    rw [F.weightedAdaptedRealChartHom_coord]
    exact CoefficientGrid.realChartSubstitute_integral (b.baseChange ℝ) q g.coord.val hc
      (fun i => MvPolynomial.map (Int.castRingHom ℝ) (β i))
      (fun i => realPolynomialCoefficientGrid_intCast (β i))
  choose a ha using ho
  exact ⟨fun z => a z.1 z.2, funext (fun z => congrFun (ha z.1) z.2)⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

theorem polynomialCoordinateFreezeZeroHom_coordinate (keep : σ → Prop) (b : Basis ι ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (α : {i // keep i} →₀ ℕ) (i : ι) :
    (b.baseChange ℝ).repr
        (coefficients ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
          VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) α) i =
      (b.baseChange ℝ).repr
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
          (α.mapDomain Subtype.val)) i := by
  rw [F.polynomialCoordinateFreezeZeroHom_coord]
  exact coordinate_coeff_realChartSubstitute_freeze_zero keep (b.baseChange ℝ) _ α i

theorem polynomialSlowBound_freeze_zero (keep : σ → Prop) (b : Basis ι ℚ L)
    (T : σ → ℝ) {M : ℝ}
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialSlowBound b (fun _ : σ => 1) T M g) :
    F.PolynomialSlowBound b (fun _ : {i // keep i} => 1)
      (fun i => T i.val) M (F.polynomialCoordinateFreezeZeroHom keep g) := by
  intro α i
  rw [F.polynomialCoordinateFreezeZeroHom_coordinate]
  have hscale : monomialScale T (α.mapDomain Subtype.val) =
      monomialScale (fun i : {i // keep i} => T i.val) α :=
    Finsupp.prod_mapDomain_index_inj Subtype.val_injective
  simpa only [hscale] using hg (α.mapDomain Subtype.val) i

theorem polynomialCoordinateFreezeZeroHom_coeff_zero (keep : σ → Prop) (b : Basis ι ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    coefficients ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
        VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) 0 =
      coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  apply (b.baseChange ℝ).repr.injective
  ext i
  simpa only [Finsupp.mapDomain_zero] using
    F.polynomialCoordinateFreezeZeroHom_coordinate keep b g 0 i

theorem polynomialCoordinateFreezeZeroHom_zero_constant (keep : σ → Prop) (b : Basis ι ℚ L)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0) :
    coefficients ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
        VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
  rw [F.polynomialCoordinateFreezeZeroHom_coeff_zero keep b g, hg]

theorem polynomialRationalGrid_freeze_zero (keep : σ → Prop) (b : Basis ι ℚ L)
    (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialRationalGrid b (fun _ : σ => 1) q g) :
    F.PolynomialRationalGrid b (fun _ : {i // keep i} => 1) q
      (F.polynomialCoordinateFreezeZeroHom keep g) := by
  classical
  have hcast : (fun i => MvPolynomial.map (Int.castRingHom ℝ)
      (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i)) =
      frozenCoordinate keep (0 : {i // ¬keep i} → ℝ) := by
    funext i
    by_cases hi : keep i <;> simp [frozenCoordinate, hi]
  have hsupport : ∀ i, MvPolynomial.map (Int.castRingHom ℝ)
      (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ) i) ∈
        weightedSupportLE (fun _ : {i // keep i} => 1) 1 := by
    intro i
    rw [congrFun hcast i]
    exact frozenCoordinate_support keep 0 i
  simpa only [polynomialCoordinateFreezeZeroHom, hcast] using
    F.polynomialRationalGrid_integerChart b (fun _ : σ => 1)
      (fun _ : {i // keep i} => 1) (frozenCoordinate keep (0 : {i // ¬keep i} → ℤ))
      hsupport q g hg

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonRefilteredGlobalMarkedFamilyReset
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound

theorem HasCommonRefilteredOrbitFactors.of_dvd
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (side : σ → ℝ) (q : ℝ) {l n : ℕ} (hl : 0 < l) (hln : l ∣ n)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF side q n W g := by
  obtain ⟨e, middle, r, hprod, hfast, he, hr, he0, hr0, hmiddle0⟩ := h
  exact ⟨e, middle, r, hprod, hfast, he,
    F.polynomialRationalGrid_of_dvd b (fun _ : σ => 1) hl hln r hr,
    he0, hr0, hmiddle0⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem realPolynomialSymbolHom_frozenChart_independent
    (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (keep : τ → Prop) (fixed fixed' : {i // ¬keep i} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (fun i => freezePolynomial keep fixed (β i))
        (fun i => freezePolynomial_support keep fixed (hβ i)) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (F.weightedAdaptedRealChartHom w (fun _ : {i // keep i} => 1)
        (fun i => freezePolynomial keep fixed' (β i))
        (fun i => freezePolynomial_support keep fixed' (hβ i)) g) := by
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart,
    F.realPolynomialSymbolHom_weightedAdaptedRealChart]
  have htop : (fun i => weightedHomogeneousComponent (fun _ : {i // keep i} => 1) (w i)
      (freezePolynomial keep fixed (β i))) =
      (fun i => weightedHomogeneousComponent (fun _ : {i // keep i} => 1) (w i)
        (freezePolynomial keep fixed' (β i))) := by
    funext i
    exact freezePolynomial_top_independent keep fixed fixed'
      ((mem_weightedSupportLE_one_iff _ _).mp (hβ i))
  congr 1
  congr 1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {σ R : Type*} [CommRing R]

theorem nestedFrozenCoordinate_eq_freeze_reindex
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → R) :
    (fun i => aeval
      (fun j => X ((nestedFrozenVariableEquiv keepLong keepLater hsub).symm j))
      (frozenCoordinate (fun i : {i // keepLong i} => keepLater i.val) fixed i)) =
      nestedFrozenCoordinate keepLong keepLater fixed := by
  funext i
  by_cases hi : keepLater i.val <;>
    simp [frozenCoordinate, nestedFrozenCoordinate, nestedFrozenVariableEquiv, hi]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem HasCommonRefilteredOrbitFactors.freeze
    (keep : σ → Prop) [DecidablePred keep]
    (fixed : {i // ¬keep i} → ℝ) (side : σ → ℝ) (q : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF (fun i : {i // keep i} => side i.val)
      q l W (F.weightedAdaptedRealChartHom (fun _ : σ => 1)
        (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed)
        (frozenCoordinate_support keep fixed) g) := by
  classical
  obtain ⟨left, middle, right, hprod, hmid, hleft, hright, hleft0, hright0, _⟩ := h
  let pull := F.polynomialCoordinateFreezeZeroHom keep
  let actual := F.weightedAdaptedRealChartHom (fun _ : σ => 1)
    (fun _ : {i // keep i} => 1) (frozenCoordinate keep fixed)
    (frozenCoordinate_support keep fixed) g
  let adjusted := (pull left)⁻¹ * actual * (pull right)⁻¹
  let symbol := F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
  have hfiber : symbol actual = symbol (pull g) := by
    symm
    simpa only [symbol, actual, pull, polynomialCoordinateFreezeZeroHom,
      freezePolynomial, aeval_X] using
      F.realPolynomialSymbolHom_frozenChart_independent b ω hF (fun _ : σ => 1)
        (fun i => X i) (fun i => weightedSupportLE_X (R := ℝ) (fun _ : σ => 1) i)
        keep 0 fixed g
  have hcancel : (pull left)⁻¹ * pull g * (pull right)⁻¹ = pull middle := by
    rw [← hprod, map_mul, map_mul]
    group
  have hadjusted : symbol adjusted = symbol (pull middle) := by
    calc
      _ = symbol ((pull left)⁻¹ * pull g * (pull right)⁻¹) := by
        simp only [adjusted, map_mul, map_inv, hfiber]
      _ = _ := congrArg symbol hcancel
  have hactual : pull left * adjusted * pull right = actual := by
    dsimp only [adjusted]
    group
  have he0 := F.polynomialCoordinateFreezeZeroHom_zero_constant keep b left hleft0
  have hr0 := F.polynomialCoordinateFreezeZeroHom_zero_constant keep b right hright0
  refine ⟨pull left, adjusted, pull right, hactual, ?_,
    F.polynomialSlowBound_freeze_zero keep b side left hleft,
    F.polynomialRationalGrid_freeze_zero keep b l right hright, he0, hr0, ?_⟩
  · change ∀ t, VectorPolynomial.eval₂ t (F.realGradedSymbolPolynomial b ω hF
      (fun _ : {i // keep i} => 1) (symbol adjusted).coord) ∈ _
    rw [hadjusted]
    apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : {i // keep i} => 1) W _).mp
    have hsymbol := F.realPolynomialSymbolHom_homogeneousChart b ω hF
      (fun _ : σ => 1) (fun _ : {i // keep i} => 1) (frozenCoordinate keep 0)
      (frozenCoordinate_zero_homogeneous keep) middle (pull middle)
      (F.polynomialCoordinateFreezeZeroHom_coord keep middle)
    change (F.realPolynomialSymbolHom b ω hF (fun _ : {i // keep i} => 1)
      (pull middle)).coord ∈ _
    rw [hsymbol]
    apply F.realSymbolHomogeneousPullback_mem_pointwise b ω hF
    exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : σ => 1) W _).mpr hmid
  · exact F.realification.polynomial_factor_middle_constant
      (fun _ : {i // keep i} => 1) actual (pull left) adjusted (pull right)
      hactual he0 hr0

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] realPolynomialSymbolHom

theorem HasCommonRefilteredOrbitFactors.of_symbol_eq
    (side : σ → ℝ) (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g actual : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g)
    (hsymbol : F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1) actual =
      F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1) g) :
    F.HasCommonRefilteredOrbitFactors b ω hF side q l W actual := by
  obtain ⟨left, middle, right, hprod, hmid, hleft, hright, hleft0, hright0, _⟩ := h
  let adjusted := left⁻¹ * actual * right⁻¹
  let symbol := F.realPolynomialSymbolHom b ω hF (fun _ : σ => 1)
  have hcancel : left⁻¹ * g * right⁻¹ = middle := by
    rw [← hprod]
    group
  have hadjusted : symbol adjusted = symbol middle := by
    calc
      _ = symbol (left⁻¹ * g * right⁻¹) := by
        simp only [adjusted, map_mul, map_inv, show symbol actual = symbol g from hsymbol]
      _ = _ := congrArg symbol hcancel
  have hactual : left * adjusted * right = actual := by
    dsimp only [adjusted]
    group
  refine ⟨left, adjusted, right, hactual, ?_, hleft, hright, hleft0, hright0, ?_⟩
  · change ∀ t, eval₂ t (F.realGradedSymbolPolynomial b ω hF
      (fun _ : σ => 1) (symbol adjusted).coord) ∈ _
    rw [hadjusted]
    exact hmid
  · exact F.realification.polynomial_factor_middle_constant
      (fun _ : σ => 1) actual left adjusted right hactual hleft0 hright0

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorsNestedFreeze
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute
  realPolynomialSymbolHom

theorem polynomialSlowBound_reindex
    (e : τ ≃ σ) (side : σ → ℝ) (M : ℝ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialSlowBound b (fun _ : σ => 1) side M g) :
    F.PolynomialSlowBound b (fun _ : τ => 1) (fun i => side (e i)) M
      (F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : τ => 1)
        (fun i => MvPolynomial.X (e.symm i))
        (fun i => weightedSupportLE_X (fun _ : τ => 1) (e.symm i)) g) := by
  intro α i
  rw [F.weightedAdaptedRealChartHom_coord,
    coefficients_realChartSubstitute_reindex]
  have hscale : monomialScale side (α.mapDomain e) =
      monomialScale (fun i => side (e i)) α :=
    Finsupp.prod_mapDomain_index_inj e.injective
  simpa only [hscale] using hg (α.mapDomain e) i

theorem HasCommonRefilteredOrbitFactors.reindex [Fintype σ] [Fintype τ] [Fintype ι]
    (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (e : τ ≃ σ) (side : σ → ℝ) (q : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF side q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF (fun i => side (e i)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : τ => 1)
        (fun i => MvPolynomial.X (e.symm i))
        (fun i => weightedSupportLE_X (fun _ : τ => 1) (e.symm i)) g) := by
  classical
  obtain ⟨left, middle, right, hprod, hmid, hleft, hright, hleft0, hright0, hmiddle0⟩ := h
  let pull := F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : τ => 1)
    (fun i => MvPolynomial.X (e.symm i))
    (fun i => weightedSupportLE_X (fun _ : τ => 1) (e.symm i))
  have hzero (a : (F.realification.adaptedPolynomialFiltration
      (fun _ : σ => 1)).Group) :
      coefficients ((pull a).coord : VectorPolynomial τ ℚ (ℝ ⊗[ℚ] L)) 0 =
        coefficients (a.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
    dsimp only [pull]
    rw [F.weightedAdaptedRealChartHom_coord, coefficients_realChartSubstitute_reindex]
    simp only [Finsupp.mapDomain_zero]
  refine ⟨pull left, pull middle, pull right, ?_, ?_, ?_, ?_,
    (hzero left).trans hleft0, (hzero right).trans hright0, ?_⟩
  · rw [← map_mul, ← map_mul, hprod]
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : τ => 1) W _).mp
    dsimp only [pull]
    rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart]
    apply F.realSymbolHomogeneousPullback_mem_pointwise b ω hF
    exact (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF
      (fun _ : σ => 1) W _).mpr hmid
  · exact F.polynomialSlowBound_reindex b e side (Real.exp q) left hleft
  · have hgrid := F.polynomialRationalGrid_integerChart b
      (fun _ : σ => 1) (fun _ : τ => 1)
      (fun i => (MvPolynomial.X (e.symm i) : MvPolynomial τ ℤ))
      (fun i => by simpa only [MvPolynomial.map_X] using
        weightedSupportLE_X (R := ℝ) (fun _ : τ => 1) (e.symm i)) l right hright
    simpa only [MvPolynomial.map_X] using hgrid
  · exact (hzero middle).trans (hmiddle0.trans (hzero g).symm)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {σ ι L : Type*} [Fintype σ] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom

theorem HasCommonRefilteredOrbitFactors.nested_freeze
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → ℝ)
    (side : σ → ℝ) (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : {i // keepLong i} => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors b ω hF
      (fun i : {i // keepLong i} => side i.val) q l W g) :
    F.HasCommonRefilteredOrbitFactors b ω hF
      (fun i : {i // keepLater i} => side i.val) q l W
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
        (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater fixed)
        (nestedFrozenCoordinate_support keepLong keepLater fixed) g) := by
  classical
  let localKeep : {i // keepLong i} → Prop := fun i => keepLater i.val
  let β := frozenCoordinate localKeep fixed
  let e := nestedFrozenVariableEquiv keepLong keepLater hsub
  let γ : {i : {i // keepLong i} // localKeep i} → MvPolynomial {i // keepLater i} ℝ :=
    fun i => X (e.symm i)
  have hβ := frozenCoordinate_support localKeep fixed
  have hγ : ∀ i, γ i ∈ weightedSupportLE (fun _ : {i // keepLater i} => 1) 1 :=
    fun i => weightedSupportLE_X (fun _ : {i // keepLater i} => 1) (e.symm i)
  have hf := HasCommonRefilteredOrbitFactors.freeze F b ω hF localKeep fixed
    (fun i : {i // keepLong i} => side i.val) q l W g h
  have hr := HasCommonRefilteredOrbitFactors.reindex F b ω hF e
    (fun i : {i : {i // keepLong i} // localKeep i} => side i.val.val) q l W
    (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
      (fun _ : {i : {i // keepLong i} // localKeep i} => 1) β hβ g) hf
  have hcomp : (fun i => aeval γ (β i)) = nestedFrozenCoordinate keepLong keepLater fixed :=
    nestedFrozenCoordinate_eq_freeze_reindex keepLong keepLater hsub fixed
  have hcompose := F.weightedAdaptedRealChartHom_comp
    (fun _ : {i // keepLong i} => 1)
    (fun _ : {i : {i // keepLong i} // localKeep i} => 1)
    (fun _ : {i // keepLater i} => 1) β γ hβ hγ
    (weightedRealChart_comp_support _ _ _ β γ hβ hγ) g
  rw [← hcompose] at hr
  simpa only [hcomp, e, nestedFrozenVariableEquiv, Equiv.coe_fn_mk] using hr

end Erdos3.NilpotentLieFiltration

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

theorem preparedSampler_axis_card (j : Fin m) :
    Fintype.card (PreparedSamplerContinuous L j) + preparedSamplerTransverse L j =
      Fintype.card (L j).Coord := by
  simpa only [PreparedSamplerContinuous, Fintype.card_fin, preparedSamplerTransverse] using
    (L j).rank_add_orthogonal_finrank

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedRecoveredChartMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {K X : Type*} [Fintype K]

theorem jointIntegerFullChart_normalized_spatial_top
    (J : Fin m → Type*) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (N : X → ℕ) (a : X → ℤ) (v : Option K × X → ℤ)
    (tag : ∀ j, J j → MvPolynomial K ℤ) (x : X) :
    aeval (fun i => homogeneousComponent (fullTaggedVariableWeight J i)
      (integerSampledRealChart (jointIntegerFullChart J a v tag) i))
      (normalizedRealPolynomialChart (fun x => (N x : ℝ))
        (fullTaggedMajorTopCoordinates J poly) (Sum.inl x)) =
      C ((N x : ℝ)⁻¹) * homogeneousComponent 1
        (affineFramePolynomial (fun k z => (jointIntegerFrame (a, v) k z : ℝ)) x) := by
  simp only [normalizedRealPolynomialChart_inl, map_mul, aeval_C, aeval_X]
  change C ((N x : ℝ)⁻¹) * homogeneousComponent 1
    (MvPolynomial.map (Int.castRingHom ℝ)
      (affineFramePolynomial (jointIntegerFrame (a, v)) x)) = _
  rw [affineFramePolynomial_map]
  rfl

variable {G : Type*} [Fintype G] {I J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedRecoveredIntegerFullChart_spatial_top_mass [Fintype X]
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (fun i => homogeneousComponent (fullTaggedVariableWeight J i)
        (integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) i))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ))
          (fullTaggedMajorTopCoordinates J poly) (Sum.inl x)))) ≤ τ / 8 := by
  unfold allocatedRecoveredIntegerFullChart
  rw [jointIntegerFullChart_normalized_spatial_top]
  have hT : ∀ k, 0 ≤ layerSamplerBox B U b S k :=
    fun k => (by norm_num : (0 : ℝ) ≤ 1).trans (layerSamplerBox_one_le B U b S k)
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN x
  have hsum := narrowSpatial_frame_slope_sum
    (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hξ N hN
    (layerSamplerBox B U b S) hT (layerSamplerBox_sum_le_zero_root_budget B U b S) v hv x
  refine (spatialAffineTop_scaled_inv_mul_mass_le
    (fun k z => (jointIntegerFrame (a, v) k z : ℝ))
    (layerSamplerBox B U b S) hT x (N x) hn).trans ?_
  change (N x : ℝ)⁻¹ * (∑ k, |(v (some k, x) : ℝ)| * layerSamplerBox B U b S k) ≤ _
  calc
    _ ≤ (N x : ℝ)⁻¹ * (τ * (N x : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = τ / 8 := by field_simp

end Erdos3.VectorPolynomial

end

end OAI
end


