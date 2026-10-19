-- Prove2me | Definitions.Def_OAIE3v2B131
-- name    : OAIE3v2B131
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:55:41.868976+00:00
-- url     : https://prove2.me/theorems/d9ba2128-9829-4ad9-b088-4872aef5829e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 133 of 311
-- statement:
--   Definitions bundle 133 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B116`, `OAIE3v2B117`, `OAIE3v2B118`, `OAIE3v2B119` of this split.
--
--   Modules: `Estimates/CoefficientRowEvaluation.lean`, `Estimates/ConstantCenterUniformLifts.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/FreeWeightedEvaluationBounds.lean`, `Estimates/FreeWeightedModelBounds.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/PolarizedCoefficientPermutation.lean`, `Estimates/ProductOrbitCongruence.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/RelativePatchAmplification.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/ScalarDominatedSlack.lean`, `Fourier/ProductFrequencyKernel.lean`, `Geometry/StepOneCoordinateMetric.lean`, `Geometry/SupportedQuotientFamilyFaithful.lean`, `Lattices/CenteredAffineCoefficient.lean`, `Lattices/IntegerOrbitTranslation.lean`, `Lattices/LayerSamplingRankAffine.lean`, `Lattices/SourceLatticeCover.lean`, `Lattices/SupportedQuotientLatticeFaithful.lean`, `Linear/FreeWeightedRankGenerators.lean`, `Linear/SquareBasisGeometry.lean`, `Nilpotent/FreeNilpotentSourceBounds.lean`, `Nilpotent/IdealInvariantNiltestBudget.lean`, `Nilpotent/NiltestAffineProjection.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Polynomial/PositivePolynomialLayerBases.lean`, `Polynomial/RealPositivePolynomialEvaluation.lean`, `Polynomial/SchmidtShortDualVector.lean`, `Sampling/SupportedQuotientExactGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B116
import Definitions.Def_OAIE3v2B117
import Definitions.Def_OAIE3v2B118
import Definitions.Def_OAIE3v2B119

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LayerSamplingRankAffine
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem PolynomialRationalApproximation.homogeneous_dilation_pullback {I : Type*}
    (N L : I → ℝ) (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q h : ℕ) (hq : 0 < q) (K : ℝ) (_hK : 1 ≤ K)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (R R' : ℝ) (hden : (q : ℝ) ^ h * R ≤ R') (hslow : K ^ h * R ≤ R')
    (P : MvPolynomial I ℝ) (hP : P.IsHomogeneous h)
    (happrox : PolynomialRationalApproximation L R (C ((q : ℝ) ^ h) * P)) :
    PolynomialRationalApproximation N R' P := by
  classical
  obtain ⟨D, hD, hDR, Q, hQ⟩ := happrox
  have hR : 0 ≤ R := (Nat.cast_nonneg D).trans hDR
  have hqpow : 0 < (q : ℝ) ^ h := pow_pos (by exact_mod_cast hq) h
  have hDreal : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hR' : 0 ≤ R' := (mul_nonneg hqpow.le hR).trans hden
  refine ⟨q ^ h * D, Nat.mul_pos (Nat.pow_pos hq) hD, ?_,
    homogeneousComponent h Q, ?_⟩
  · push_cast
    exact (mul_le_mul_of_nonneg_left hDR hqpow.le).trans hden
  · intro α
    by_cases hα : α.degree = h
    · rw [coeff_homogeneousComponent, if_pos hα]
      have hid : P.coeff α - ((Q.coeff α : ℤ) : ℝ) / (q ^ h * D : ℕ) =
          ((q : ℝ) ^ h * P.coeff α - ((Q.coeff α : ℤ) : ℝ) / D) / (q : ℝ) ^ h := by
        push_cast
        field_simp
      rw [hid, abs_div, abs_of_pos hqpow]
      have hscale := monomialScale_le_const_mul N L (fun i => (hN i).le) (K * q) hNL α
      rw [hα, mul_pow] at hscale
      have hscaleN := monomialScale_pos N hN α
      have hscaleL := monomialScale_pos L hL α
      calc
        _ ≤ (R / monomialScale L α) / (q : ℝ) ^ h :=
          div_le_div_of_nonneg_right (by simpa only [coeff_C_mul] using hQ α) hqpow.le
        _ ≤ K ^ h * R / monomialScale N α := by
          rw [div_div]
          apply (div_le_div_iff₀ (mul_pos hscaleL hqpow) hscaleN).mpr
          calc
            R * monomialScale N α ≤ R * (K ^ h * (q : ℝ) ^ h * monomialScale L α) :=
              mul_le_mul_of_nonneg_left hscale hR
            _ = (K ^ h * R) * (monomialScale L α * (q : ℝ) ^ h) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hslow hscaleN.le
    · rw [hP.coeff_eq_zero hα, coeff_homogeneousComponent, if_neg hα, Int.cast_zero,
        zero_div, sub_zero, abs_zero]
      exact div_nonneg hR' (monomialScale_pos N hN α).le

theorem PolynomialRationalApproximation.affine_pullback {I : Type*}
    (N L : I → ℝ) (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q h : ℕ) (hq : 0 < q) (r : I → ℤ) (K : ℝ) (hK : 1 ≤ K)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (R R' : ℝ) (hden : (q : ℝ) ^ h * R ≤ R') (hslow : K ^ h * R ≤ R')
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ h)
    (happrox : PolynomialRationalApproximation L R
      (homogeneousComponent h (residueAffinePolynomial q r P))) :
    PolynomialRationalApproximation N R' (homogeneousComponent h P) := by
  rw [residueAffinePolynomial_homogeneousComponent q h r P hP] at happrox
  exact happrox.homogeneous_dilation_pullback N L hN hL q h hq K hK hNL R R'
    hden hslow (homogeneousComponent h P) (homogeneousComponent_isHomogeneous _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem HasLayerSamplingRank.residueAffine {I J : Type*} [Fintype J]
    {h : ℕ} {N L : I → ℝ} {Rbig Rsmall : ℝ}
    {W : Submodule ℝ (J → ℝ)} {P : VectorPolynomial I ℝ (J → ℝ)}
    (hrank : HasLayerSamplingRank h N Rbig W P)
    (hP : VectorPolynomial.DegreeLE (fun _ => 1) h P)
    (hN : ∀ i, 0 < N i) (hL : ∀ i, 0 < L i)
    (q : ℕ) (hq : 0 < q) (r : I → ℤ) (K : ℝ)
    (hNL : ∀ i, N i ≤ K * (q : ℝ) * L i)
    (hrow : Rsmall ≤ Rbig)
    (hden : (q : ℝ)^h * Rsmall ≤ Rbig)
    (hslow : K^h * Rsmall ≤ Rbig) :
    HasLayerSamplingRank h L Rsmall W (VectorPolynomial.residueAffine q r P) := by
  intro a ha hw happ
  apply hrank a (fun j => (ha j).trans hrow) hw
  rw [VectorPolynomial.integerRowPolynomial_residueAffine] at happ
  have hcomparison (i : I) : N i ≤ max 1 K * (q : ℝ) * L i := by
    apply (hNL i).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 K) (Nat.cast_nonneg q)) (hL i).le
  have hslow' : (max 1 K)^h * Rsmall ≤ Rbig := by
    by_cases hK : K ≤ 1
    · simpa only [max_eq_left hK, one_pow, one_mul] using hrow
    · simpa only [max_eq_right (le_of_not_ge hK)] using hslow
  exact happ.affine_pullback N L hN hL q h hq r (max 1 K) (le_max_left _ _)
    hcomparison Rsmall Rbig hden hslow' (VectorPolynomial.integerRowPolynomial a P)
    (VectorPolynomial.integerRowPolynomial_totalDegree_le a hP)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientRowPolynomial_affine_eval {V : Type*}
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (frame : Option K → V → ℝ) (j : Fin m) (i : J j) (x : K → ℝ) :
    MvPolynomial.eval x (coefficientRowPolynomial U (affineSampleCoefficientArray U p hm frame) j i) =
      eval (fun v => frame none v + ∑ k, frame (some k) v * x k) (p j) i := by
  rw [coefficientRowPolynomial_eval]
  simp_rw [affineSampleCoefficientArray_val]
  rw [boundedArrayPolynomial_reconstruct _
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree frame) (p j) (hp j)),
    eval_substitute]
  simp only [affineParameterSubstitution_eval]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CenteredAffineCoefficient
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K V : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j)

noncomputable def centeredAffineCoefficientTorus (center : ∀ j, U j) (frame : Option K → V → ℝ) :
    CoefficientTorus (K := K) U :=
  QuotientAddGroup.mk' (coefficientIntegerLattice U) (centeredAffineCoefficientArray U p hm center frame)

theorem coefficientRowPolynomial_centered_affine_eval
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (center : ∀ j, U j) (frame : Option K → V → ℝ) (j : Fin m) (i : J j) (x : K → ℝ) :
    MvPolynomial.eval x
        (coefficientRowPolynomial U (centeredAffineCoefficientArray U p hm center frame) j i) =
      eval (fun v => frame none v + ∑ k, frame (some k) v * x k) (p j) i - (center j).val i := by
  rw [centeredAffineCoefficientArray, coefficientRowPolynomial_sub, map_sub,
    coefficientRowPolynomial_constant, MvPolynomial.eval_C,
    coefficientRowPolynomial_affine_eval U p hp hm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem uniform_base_reweight_test_le {B Ω X : Type*}
    [Fintype B] [Nonempty B] [Fintype Ω] [Fintype X] [Nonempty X]
    (q : FiniteProbabilityWeights Ω) (D : B × Ω → ℝ) (hD : ∀ z, 0 ≤ D z)
    (hZ : 0 < ((uniform B).prod q).mean D)
    (F : B × Ω → X) (hF : ∀ z, Function.Injective (fun b => F (b, z)))
    (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    {M ε a : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hlower : a ≤ ((uniform B).prod q).mean D)
    (hlocal : ∀ b, q.mean (fun z => D (b, z) * φ (F (b, z))) ≤
      M * q.mean (fun z => φ (F (b, z))) + ε) :
    (((uniform B).prod q).reweightPositive D hD hZ).mean (fun z => φ (F z)) ≤
      ((M * ((Fintype.card X : ℝ) / Fintype.card B)) * (uniform X).mean φ + ε) / a := by
  have href : ((uniform B).prod q).mean (fun z => φ (F z)) ≤
      ((Fintype.card X : ℝ) / Fintype.card B) * (uniform X).mean φ := by
    rw [mean_prod, mean_comm]
    exact (q.mean_mono (fun z => uniform_injective_mean_le _ (hF z) φ hφ)).trans_eq
      (q.mean_const _)
  have hraw : ((uniform B).prod q).mean (fun z => D z * φ (F z)) ≤
      M * ((uniform B).prod q).mean (fun z => φ (F z)) + ε := by
    rw [mean_prod, mean_prod]
    exact ((uniform B).mean_mono hlocal).trans_eq (by rw [mean_add, mean_const_mul, mean_const])
  have hnorm := ((uniform B).prod q).reweightPositive_test_le D hD hZ
    (fun z => φ (F z)) (fun z => hφ (F z)) ha hlower hraw
  apply hnorm.trans
  apply div_le_div_of_nonneg_right _ ha.le
  calc
    _ ≤ M * (((Fintype.card X : ℝ) / Fintype.card B) * (uniform X).mean φ) + ε := by
      gcongr
    _ = _ := by ring

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realAdditiveTripleProjection_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) {n : ℕ}
    {g : (F.additiveTripleFiltration i hi c hc).realification.Group}
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup n) :
    F.realAdditiveTripleProjection i hi c hc j g ∈ F.realification.ordinary.subgroup n := by
  have hm := (F.realifiedAdditiveTripleEquiv_mem_layer i hi c hc n g.coord).mp hg
  obtain ⟨h₀, h₁, h₂⟩ := F.realification.additiveTripleProjections_mem i hi c hc hm
  change (F.realAdditiveTripleProjection i hi c hc j g).coord ∈ F.realification.ordinary.layer n
  rw [F.realAdditiveTripleProjection_coord]
  fin_cases j
  · exact h₀
  · exact h₁
  · exact h₂

theorem realAdditiveTriple_top_group_relation (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (htop : F.realification.weightedLayer c s = ⊥)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup s) :
    F.realAdditiveTripleProjection i hi c hc 0 g =
      F.realAdditiveTripleProjection i hi c hc 1 g *
        F.realAdditiveTripleProjection i hi c hc 2 g := by
  let q : (F.realification.additiveTripleFiltration i hi c hc).Group :=
    ⟨F.realifiedAdditiveTripleEquiv i hi c hc g.coord⟩
  have hq : q ∈ (F.realification.additiveTripleFiltration i hi c hc).subgroup s :=
    (F.realifiedAdditiveTripleEquiv_mem_layer i hi c hc s g.coord).mp hg
  have he (j : Fin 3) : F.realAdditiveTripleProjection i hi c hc j g =
      (NilpotentLieBCHGroup.map (F.realification.additiveTripleProjection i hi c hc j) q :
        F.realification.Group) := by
    apply NilpotentLieBCHGroup.ext
    exact F.realAdditiveTripleProjection_coord i hi c hc j g
  rw [he 0, he 1, he 2]
  exact F.realification.additiveTriple_top_group_relation i hi c hc htop q hq

theorem realAdditiveTriple_top_phase {A : Type*} [Add A]
    (i : σ) (hi : bound i ≤ 1) (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (htop : F.realification.weightedLayer c s = ⊥) (χ : F.realification.Group → A)
    (hχ : ∀ z w, z ∈ F.realification.ordinary.subgroup s →
      w ∈ F.realification.ordinary.subgroup s → χ (z * w) = χ z + χ w)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group)
    (hg : g ∈ (F.additiveTripleFiltration i hi c hc).realification.subgroup s) :
    χ (F.realAdditiveTripleProjection i hi c hc 0 g) =
      χ (F.realAdditiveTripleProjection i hi c hc 1 g) +
        χ (F.realAdditiveTripleProjection i hi c hc 2 g) := by
  rw [F.realAdditiveTriple_top_group_relation i hi c hc htop g hg]
  exact hχ _ _ (F.realAdditiveTripleProjection_mem i hi c hc 1 hg)
    (F.realAdditiveTripleProjection_mem i hi c hc 2 hg)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

namespace Niltest

variable {D} {w : σ → ℕ}

theorem eval_budget {T : D.Niltest w} {p : ℝ} (hp : T.ComplexityLE p) (x : σ → ℤ) :
    ‖T.eval x‖ ≤ Real.exp p := by
  have h := observable_budget hp
  have hn := T.norm_eval_le x
  have hl := T.lipBound.coe_nonneg
  linarith

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

theorem raisedLayerBasis_of_lt (i : Fin (t + 1)) (hi : i.val < s + 1) :
    D.raisedLayerBasis hst i = D.layerBasis ⟨i.val, hi⟩ := by
  simp [raisedLayerBasis, hi]
  rfl

theorem raiseStep_geometry {p : ℝ} (hD : D.GeometryComplexityLE p) :
    (D.raiseStep hst).GeometryComplexityLE p := by
  refine ⟨hD.1, hD.2.1, hD.2.2.1, ?_⟩
  intro i j k
  by_cases hi : i.val < s + 1
  · change rationalLogHeight (D.basis.repr (D.raisedLayerBasis hst i j) k) ≤ p
    rw [D.raisedLayerBasis_of_lt hst i hi]
    exact hD.2.2.2 ⟨i.val, hi⟩ j k
  · have hbot : D.filtration.layer (i.val + 1) = ⊥ :=
      D.filtration.layer_eq_bot_above_step (by omega)
    have hrank : Module.finrank ℚ ((D.filtration.raiseStep hst).layer (i.val + 1)) = 0 := by
      rw [NilpotentLieFiltration.raiseStep_layer, hbot]
      simp
    have hj := j.isLt
    change j.val < Module.finrank ℚ ((D.filtration.raiseStep hst).layer (i.val + 1)) at hj
    rw [hrank] at hj
    omega

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem constantMultidegreeOrbit_eval (a : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval x (F.constantMultidegreeOrbit a) = a := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ)) (monomial 0 a.coord) = a.coord
  rw [eval_monomial, Finsupp.prod_zero_index, one_smul]

noncomputable def normalizeMultidegreeOrbit (p : F.PolynomialOrbit) (a b : F.Group) :
    F.PolynomialOrbit := F.constantMultidegreeOrbit a⁻¹ * p * F.constantMultidegreeOrbit b⁻¹

theorem normalizeMultidegreeOrbit_eval (p : F.PolynomialOrbit) (a b : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval x (F.normalizeMultidegreeOrbit p a b) =
      a⁻¹ * F.polynomialOrbitEval x p * b⁻¹ := by
  simp only [normalizeMultidegreeOrbit, map_mul, F.constantMultidegreeOrbit_eval]

theorem normalizeMultidegreeOrbit_zero (p : F.PolynomialOrbit) (a b : F.Group)
    (h : F.polynomialOrbitEval 0 p = a * b) :
    F.polynomialOrbitEval 0 (F.normalizeMultidegreeOrbit p a b) = 1 := by
  rw [F.normalizeMultidegreeOrbit_eval, h]
  simp

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def rationalDilationOrbit (r : ℚ) (p : F.PolynomialOrbit) : F.PolynomialOrbit :=
  F.polynomialOrbitOfLog (weightedDilation (fun _ : σ => 1) r (p.log F))
    (F.adapted_rationalDilation r _ (p.adapted F))

theorem rationalDilationOrbit_eval (r : ℚ) (p : F.PolynomialOrbit) (x : σ → ℤ) :
    (F.polynomialOrbitEval x (F.rationalDilationOrbit r p)).coord =
      eval (fun i => r * (x i : ℚ)) (p.log F) := by
  change eval (fun i => (x i : ℚ)) (weightedDilation (fun _ : σ => 1) r (p.log F)) = _
  rw [eval_weightedDilation]
  simp only [pow_one]

theorem rationalDilationOrbit_rescaled (r : ℚ) (q : ℤ) (hr : r * (q : ℚ) = 1)
    (p : F.PolynomialOrbit) (x : σ → ℤ) :
    F.polynomialOrbitEval (fun i => q * x i) (F.rationalDilationOrbit r p) =
      F.polynomialOrbitEval x p := by
  apply NilpotentLieBCHGroup.ext
  rw [F.rationalDilationOrbit_eval, F.polynomialOrbitEval_coord]
  simp only [Int.cast_mul, ← mul_assoc, hr, one_mul]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_normalizedCoordinateAddition_orbit (i : σ) (hi : bound i ≤ 1)
    (p : F.PolynomialOrbit) (a b : F.Group) (hp0 : F.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        (((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ x g).coord : L × L × L) =
          ((a⁻¹ * F.polynomialOrbitEval
              (Function.update (fun j => x (some j)) i (x (some i) + x none)) p * b⁻¹).coord,
           (a⁻¹ * F.polynomialOrbitEval (fun j => x (some j)) p * b⁻¹).coord,
           (a⁻¹ * F.polynomialOrbitEval (Function.update (fun j => x (some j)) i (x none)) p * b⁻¹).coord) := by
  obtain ⟨g, hg0, hg⟩ := F.exists_coordinateAddition_orbit i hi (F.normalizeMultidegreeOrbit p a b)
    (F.normalizeMultidegreeOrbit_zero p a b hp0)
  exact ⟨g, hg0, fun x => by simpa only [F.normalizeMultidegreeOrbit_eval] using hg x⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_normalized_dilationPair_orbit (q : ℤ) (p : F.PolynomialOrbit)
    (a b : F.Group) (hp0 : F.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.dilationPairMultidegree (q : ℚ)).PolynomialOrbit,
      (F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval x g).coord : L × L) =
          ((a⁻¹ * F.polynomialOrbitEval (fun i => q * x i) p * b⁻¹).coord,
            (a⁻¹ * F.polynomialOrbitEval x p * b⁻¹).coord) := by
  obtain ⟨g, hg0, hg⟩ := F.exists_integer_dilationPair_orbit q (F.normalizeMultidegreeOrbit p a b)
    (F.normalizeMultidegreeOrbit_zero p a b hp0)
  exact ⟨g, hg0, fun x => by simpa only [F.normalizeMultidegreeOrbit_eval] using hg x⟩

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace RationalFilteredNilmanifold.MultidegreeStructure

theorem realSubgroup_top {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
    (M : D.MultidegreeStructure bound) :
    M.realSubgroup bound = D.filtration.realification.subgroup (∑ i, bound i) := by
  ext x
  change x.coord ∈ (M.filtration.layer bound).baseChange ℝ ↔
    x.coord ∈ (D.filtration.layer (∑ i, bound i)).baseChange ℝ
  rw [← M.ordinary, M.filtration.ordinary_top_eq]

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem replicatedLiePermute_top (e : ReplicatedPermutation bound)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
    (hx : x ∈ F.squarefreeMultidegreeLayer (fun j : ReplicatedIndex bound => j.1) (fun _ => 1)) :
    F.replicatedLiePermute e x = x :=
  F.squarefreeBlockPermute_eq_self_top _ _ _ x hx

theorem replicatedLiePermute_ordinary_top (e : ReplicatedPermutation bound)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))
    (hx : x ∈ (F.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).layer
      (Fintype.card (ReplicatedIndex bound))) : F.replicatedLiePermute e x = x := by
  have htop := (F.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)).ordinary_top_eq
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at htop
  change (F.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).layer
    (Fintype.card (ReplicatedIndex bound)) =
      F.squarefreeMultidegreeLayer (fun j : ReplicatedIndex bound => j.1) (fun _ => 1) at htop
  apply F.replicatedLiePermute_top e x
  rw [← htop]
  exact hx

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

theorem exists_bounded_sorted_adapted_basis_logHeight {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hv : ∀ i j k, rationalLogHeight (e.repr (v i j : L) k) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ s + 1) ∧ IsCentralLieBasis b ∧
      (∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (e i) j) ≤ (p + 3) ^ 5) ∧
      ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := hp.trans (le_add_of_nonneg_right zero_le_one)
  have hd1 : (Fintype.card ι : ℝ) ≤ p + 1 := hd.trans (le_add_of_nonneg_right zero_le_one)
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis e] using hd1
  obtain ⟨b, w, hw, hbound, hcentral, hb, hlayer⟩ :=
    F.exists_bounded_sorted_adapted_basis e v hspan
      (fun i j k => rationalHeightLE_ceil_exp (hv i j k))
  have hinverse := inverse_basis_entries_height e b hH hb
  have hstructure := basis_change_structure_height e b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
  refine ⟨b, w, hw, hbound, hcentral, hlayer,
    fun j i => rationalLogHeight_le_of_height (hb j i) hHp, ?_, ?_⟩
  · intro i j
    apply rationalLogHeight_le_of_height (hinverse i j)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalSolveHeight_le_budget (Fintype.card (Fin (finrank ℚ L))) H hp1 hr hHp
  · intro i j k
    apply rationalLogHeight_le_of_height (hstructure i j k)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalLieStructureHeight_inverse_budget (Fintype.card ι)
        (Fintype.card (Fin (finrank ℚ L))) H hp1 hd1 hr hHp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem rational_functional_value_logHeight {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) (eta : V →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (heta : ∀ i, rationalLogHeight (eta (b i)) ≤ p)
    (x : V) (hx : ∀ i, rationalLogHeight (b.repr x i) ≤ p) :
    rationalLogHeight (eta x) ≤ (p + 2) ^ 4 := by
  classical
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hterms (i) : RationalHeightLE (b.repr x i * eta (b i)) (H * H) :=
    (rationalHeightLE_ceil_exp (hx i)).mul (rationalHeightLE_ceil_exp (heta i))
  have hHH : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp (p + 1) := by gcongr
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  have he : eta x = ∑ i, b.repr x i * eta (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [he]
  apply rationalLogHeight_le_of_height (rationalHeightLE_sum _ hterms)
  exact rational_sum_cost_le_exp (Fintype.card ι) (H * H) hp 2 1 hHH
    (by simpa only [pow_one] using hι.trans (show p ≤ p + 2 by linarith))

end Erdos3

end

section

namespace Erdos3

open Module

theorem linearMap_coordinate_logHeight
    {V W ι κ : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [Fintype ι]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (T : V →ₗ[ℚ] W)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hT : ∀ i j, rationalLogHeight (f.repr (T (e i)) j) ≤ p)
    (x : V) (hx : ∀ i, rationalLogHeight (e.repr x i) ≤ p) (j : κ) :
    rationalLogHeight (f.repr (T x) j) ≤ (p + 2) ^ 4 := by
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hHH : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp (p + 1) :=
        mul_le_mul hH hH (Nat.cast_nonneg H) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  have hraw := linearMap_coordinate_height e f T
    (fun i j => rationalHeightLE_ceil_exp (hT i j)) x
    (fun i => rationalHeightLE_ceil_exp (hx i)) j
  apply rationalLogHeight_le_of_height hraw
  exact rational_sum_cost_le_exp (Fintype.card ι) (H * H) hp 2 1 hHH
    (by simpa only [pow_one] using hn.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def RelativePatchAbsoluteRule (s n₀ : ℕ) (p a Λ : ℝ) (d₀ : ℕ) : Prop :=
  ∀ (N : Fin n₀ → ℕ),
    (∀ i, (N i).Prime) → Function.Injective N →
    (∀ i j, N i ≤ 2 ^ (n₀ + 1) * N j) →
    (∀ i, Real.exp p ≤ (N i : ℝ)) →
    ∀ (f : (Fin n₀ → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a ≤ (𝔼 x ∈ integerBox N, f x) →
      RelativePatchSliceConclusion s N f Λ d₀ p

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def LowDensityRelativeAbsoluteRule (s n₀ : ℕ) (p H : ℝ) (D : ℕ) (x : ℝ) : Prop :=
  ∀ a : ℝ, Real.exp (-p) ≤ a → LowDensityThreshold H a →
    RelativePatchAbsoluteRule s n₀ x a (H * a) D

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantCenterUniformLifts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {X Y R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_subtractConstant (c : V) (p : VectorPolynomial X R V) (d : X →₀ ℕ) :
    coefficients (subtractConstant c p) d = coefficients p d - if d = 0 then c else 0 := by
  classical
  simp [subtractConstant, Finsupp.single_apply, eq_comm]

theorem substitute_subtractConstant (f : X → MvPolynomial Y R) (c : V)
    (p : VectorPolynomial X R V) :
    substitute f (subtractConstant c p) = subtractConstant c (substitute f p) := by
  simp [subtractConstant, monomial]

theorem coefficients_subtractConstant_mem (U : Submodule R V) (c : U)
    (p : VectorPolynomial X R V) (hp : ∀ d, coefficients p d ∈ U) (d : X →₀ ℕ) :
    coefficients (subtractConstant c.val p) d ∈ U := by
  classical
  rw [coefficients_subtractConstant]
  split_ifs
  · exact U.sub_mem (hp d) c.property
  · simpa using hp d

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

theorem affineSampleCoefficientArray_subtractConstant {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (c : ∀ j, U j) (frame : Option K → X → ℝ) :
    affineSampleCoefficientArray U (fun j => subtractConstant (c j).val (p j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)) frame =
      centeredAffineCoefficientArray U p hm c frame := by
  funext s
  apply Subtype.ext
  simp only [centeredAffineCoefficientArray, Pi.sub_apply, Submodule.coe_sub,
    affineSampleCoefficientArray_val, substitute_subtractConstant, coefficients_subtractConstant]
  by_cases hs : s.2.val = 0
  · simp [constantCoefficientArray, hs]
  · simp [constantCoefficientArray, hs]

theorem affineSampleCoefficientTorus_subtractConstant {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (c : ∀ j, U j) (frame : Option K → X → ℝ) :
    affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (p j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)) frame =
      centeredAffineCoefficientTorus U p hm c frame := by
  exact congrArg (QuotientAddGroup.mk' (coefficientIntegerLattice U))
    (affineSampleCoefficientArray_subtractConstant U p hm c frame)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ K Ξ : Type*} [LieRing K] [LieAlgebra ℚ K] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
  (D : RationalFilteredNilmanifold K s d) {w : σ → ℕ}

theorem sectionNiltest_unit_interval
    (g : D.filtration.realification.PolynomialOrbit w) (F : D.Space → Ξ → ℝ)
    (hF : ∀ z a, 0 ≤ F z a ∧ F z a ≤ 1) (M : ℝ≥0)
    (hLip : let := D.metricSpace; ∀ a, LipschitzWith M (fun z => F z a)) (a : Option Ξ) :
    (D.sectionNiltest g F hF M hLip a).UnitIntervalValued := by
  intro z
  exact ⟨rfl, frozenRealSection_unit_interval F hF a z⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_group_parameter_cover (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (B : ℝ≥0) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 1 ≤ B →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) → 0 < ε → 1 / ε ≤ Real.exp p →
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ centers : Fin n → A,
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)
          ∀ x : A, ∃ j, dist x (centers j) ≤ ε := by
  obtain ⟨C₀, _, hsize⟩ := exists_bchBoxCover_count_budget s r
  refine ⟨1 + C₀ + 2, by omega, ?_⟩
  intro L _ _ _ _ _ _ d D B p ε hp hD hB hBp hε hεinv
  let H := ⌈Real.exp p⌉₊
  have hh : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  obtain ⟨c, hc⟩ := D.exists_native_coordinateBox_cover hh B hB hε
  have hcount := hsize d H B (p := p + 1) (by linarith) (by linarith [hD.1])
    (ceil_exp_le_exp_add_one hp)
    (hBp.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) r))) hε
    (hεinv.trans (Real.exp_le_exp.mpr (by linarith)))
  have hshift : ((p + 1) + C₀) ^ C₀ ≤ (p + (1 + C₀ + 2 : ℕ)) ^ (1 + C₀ + 2) := by
    simpa only [Nat.cast_one] using shifted_center_power_bound 1 C₀ hp
  exact ⟨_, by positivity, hcount.trans (Real.exp_le_exp.mpr hshift), c, hc⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeNilpotentSourceBounds
namespace OAI

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module

variable {X ι L : Type*} [Fintype X] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s H : ℕ} (e : Basis ι ℚ L) (f : X → L)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

theorem lift_basis_matrix_logHeight
    (b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (hb : ∀ j, b j ∈ treeGenerators X s) {p : ℝ} (hp : 0 ≤ p)
    (hd : (Fintype.card ι : ℝ) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p)
    (hf : ∀ x i, rationalLogHeight (e.repr (f x) i) ≤ p) (i j) :
    rationalLogHeight (LinearMap.toMatrix b e (lift f hnil).toLinearMap i j) ≤
      (p + 3) ^ (6 * s + 2) := by
  have hraw := lift_basis_matrix_height e f hnil b hb
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
    (fun x i => rationalHeightLE_ceil_exp (hf x i)) i j
  apply rationalLogHeight_le_of_height hraw
  have h := lieTreeHeight_le_exp (Fintype.card ι) ⌈Real.exp p⌉₊ s
    (p := p + 1) (by linarith) (by linarith) (ceil_exp_le_exp_add_one hp)
  simpa only [show p + 1 + 2 = p + 3 by ring] using h

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3

open Module

theorem exists_bounded_free_nilpotent_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
      (Fintype.card (BoundedFreeWord X s) : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
        (∀ i, b i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
        (∀ i w, rationalLogHeight (FreeNilpotentLieAlgebra.coordinates X s (b i) w) ≤ (p + C) ^ C) ∧
        ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C := by
  let H := (2 * (s + 1)) ^ s
  let Q : Polynomial ℕ := Polynomial.C (s + 1) * (Polynomial.X + 1) ^ s +
    Polynomial.C H + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 2) ^ 8)
  refine ⟨C, hC, ?_⟩
  intro X _ p hp hX
  let A := ((s : ℝ) + 1) * (p + 1) ^ s
  let T := A + (H : ℝ) + p + 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAT : A ≤ T := by
    exact (le_add_of_nonneg_right (Nat.cast_nonneg H)).trans
      ((le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right (by norm_num)))
  have hT : 0 ≤ T := hA.trans hAT
  have hHT : (H : ℝ) ≤ T := by
    exact (le_add_of_nonneg_left hA).trans
      ((le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right (by norm_num)))
  have hsum : T + (T + 2) ^ 8 ≤ (p + C) ^ C := by
    simpa [Q, T, A, Polynomial.eval₂_pow] using hbudget p hp
  have hTC : T ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (T + 2) ^ 8)).trans hsum
  have hBC : (T + 2) ^ 8 ≤ (p + C) ^ C := (le_add_of_nonneg_left hT).trans hsum
  have hsize : ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s ≤ A :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add hX (le_refl (1 : ℝ))) s) (by positivity)
  have hn : (Fintype.card (BoundedFreeWord X s) : ℝ) ≤ A := by
    calc
      _ ≤ ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s := by
        exact_mod_cast (boundedFreeWord_card_le (X := X) (s := s))
      _ ≤ _ := hsize
  have hd : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ A := by
    calc
      _ ≤ ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s := by
        exact_mod_cast (FreeNilpotentLieAlgebra.finrank_le X s)
      _ ≤ _ := hsize
  have hHexp : (H : ℝ) ≤ Real.exp T := hHT.trans
    ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.add_one_le_exp T))
  obtain ⟨b, hb, hcoord, hstructure⟩ := FreeNilpotentLieAlgebra.exists_bounded_structure_basis X s
  refine ⟨hd.trans (hAT.trans hTC), hn.trans (hAT.trans hTC), b, hb, ?_, ?_⟩
  · intro i w
    exact rationalLogHeight_le_of_height (hcoord i w)
      (hHexp.trans (Real.exp_le_exp.mpr hTC))
  · intro i j k
    have hcost := embedding_coordinate_height_budget
      (Fintype.card (BoundedFreeWord X s)) (finrank ℚ (FreeNilpotentLieAlgebra X s)) H H
      hT (hn.trans hAT) (hd.trans hAT) hHexp hHexp
    exact rationalLogHeight_le_of_height (hstructure i j k)
      (hcost.trans (Real.exp_le_exp.mpr hBC))

end Erdos3

end

section

namespace Erdos3

open Module
attribute [local instance] LieRing.ofAssociativeRing

theorem exists_free_nilpotent_source_basis (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
      ((FreeNilpotentLieAlgebra.treeGenerators X s).card : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
        (∀ i, b i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr x i) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hmodel⟩ := exists_bounded_free_nilpotent_model s
  let H := (2 * (s + 1)) ^ s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a +
    (Polynomial.X + 2) ^ (3 ^ s) + Polynomial.C H + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 2) ^ 8)
  refine ⟨C, hC, ?_⟩
  intro X _ p hp hX
  let B := (p + a) ^ a
  let V := (p + 2) ^ (3 ^ s)
  let T := B + V + (H : ℝ) + 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hBT : B ≤ T := by
    exact (le_add_of_nonneg_right hV).trans
      ((le_add_of_nonneg_right (Nat.cast_nonneg H)).trans (le_add_of_nonneg_right (by norm_num)))
  have hVT : V ≤ T := by
    exact (le_add_of_nonneg_left hB).trans
      ((le_add_of_nonneg_right (Nat.cast_nonneg H)).trans (le_add_of_nonneg_right (by norm_num)))
  have hHT : (H : ℝ) ≤ T :=
    (le_add_of_nonneg_left (add_nonneg hB hV)).trans (le_add_of_nonneg_right (by norm_num))
  have hT : 0 ≤ T := hB.trans hBT
  have hsum : T + (T + 2) ^ 8 ≤ (p + C) ^ C := by
    simpa [Q, T, B, V, Polynomial.eval₂_pow] using hbudget p hp
  have hTC : T ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (T + 2) ^ 8)).trans hsum
  have hPC : (T + 2) ^ 8 ≤ (p + C) ^ C := (le_add_of_nonneg_left hT).trans hsum
  obtain ⟨hd, hn, b, hb, _, hstructure⟩ := hmodel X p hp hX
  have hgen : ((FreeNilpotentLieAlgebra.treeGenerators X s).card : ℝ) ≤ V := by
    calc
      _ ≤ ((Fintype.card X : ℝ) + 2) ^ (3 ^ s) := by
        exact_mod_cast FreeNilpotentLieAlgebra.treeGenerators_card_le X s
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (add_le_add hX (le_refl (2 : ℝ))) _
  have hHexp : (H : ℝ) ≤ Real.exp T := hHT.trans
    ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.add_one_le_exp T))
  refine ⟨hd.trans (hBT.trans hTC), hgen.trans (hVT.trans hTC), b, hb,
    fun i j k => (hstructure i j k).trans (hBT.trans hTC), ?_⟩
  intro x hx i
  have hraw := embedding_basis_coordinate_height b (Pi.basisFun ℚ (BoundedFreeWord X s))
    (FreeNilpotentLieAlgebra.coordinates X s) (FreeNilpotentLieAlgebra.coordinates_injective X s)
    (show 1 ≤ H from one_le_pow₀ (by omega))
    (fun w j => by simpa only [Pi.basisFun_repr] using
      FreeNilpotentLieAlgebra.treeGenerators_coordinate_height X s (b j) (hb j) w)
    x (fun w => by simpa only [Pi.basisFun_repr] using
      FreeNilpotentLieAlgebra.treeGenerators_coordinate_height X s x hx w) i
  have hcost := embedding_coordinate_height_budget
    (Fintype.card (BoundedFreeWord X s)) (finrank ℚ (FreeNilpotentLieAlgebra X s)) H H
    hT (hn.trans hBT) (hd.trans hBT) hHexp hHexp
  apply rationalLogHeight_le_of_height hraw
  simpa only [Fintype.card_fin] using hcost.trans (Real.exp_le_exp.mpr hPC)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedEvaluationBounds
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : X → ℕ) (f : X → L)
  (hf : ∀ x, f x ∈ F.layer (w x))

namespace FreeWeightedNilpotentLieAlgebra

theorem hom_ext {φ ψ : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ L}
    (h : ∀ x, φ (of X s w x) = ψ (of X s w x)) : φ = ψ := by
  have heq : φ.comp (mk X s w) = ψ.comp (mk X s w) := FreeNilpotentLieAlgebra.hom_ext h
  apply LieHom.ext
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective X s w x
  exact LieHom.congr_fun heq a

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedModelBounds
namespace OAI

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

theorem layer_eq_span (hw : ∀ x, 0 < w x) (d : ℕ) :
    (filtration X s w hw).layer d = Submodule.span ℚ (layerGenerators X s w d : Set _) := by
  classical
  change (FreeNilpotentLieAlgebra.weightedLayer X s w d).map (mk X s w).toLinearMap = _
  rw [FreeNilpotentLieAlgebra.weightedLayer_eq_span, Submodule.map_span]
  simp only [layerGenerators, Finset.coe_image]
  rfl

theorem layerGenerators_mem (hw : ∀ x, 0 < w x) (d : ℕ)
    (x : FreeWeightedNilpotentLieAlgebra X s w) (hx : x ∈ layerGenerators X s w d) :
    x ∈ (filtration X s w hw).layer d := by
  rw [layer_eq_span]
  exact Submodule.subset_span hx

noncomputable def layerFamily (hw : ∀ x, 0 < w x) (d : ℕ)
    (x : layerGenerators X s w d) : (filtration X s w hw).layer d :=
  ⟨x.val, layerGenerators_mem X s w hw d x.val x.property⟩

theorem layerFamily_span (hw : ∀ x, 0 < w x) (d : ℕ) :
    Submodule.span ℚ (Set.range (layerFamily X s w hw d)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  have hrange : Set.range (Subtype.val : layerGenerators X s w d →
      FreeWeightedNilpotentLieAlgebra X s w) = (layerGenerators X s w d : Set _) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange]
  exact (layer_eq_span X s w hw d).symm

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_free_weighted_quotient (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (w : X → ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
      ∃ e : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
        (∀ i, e i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
        (∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (e.repr x i) ≤ (p + C) ^ C) ∧
        ∃ d : ℕ, d ≤ finrank ℚ (FreeNilpotentLieAlgebra X s) ∧ (d : ℝ) ≤ (p + C) ^ C ∧
          ∃ b : Basis (Fin d) ℚ (FreeWeightedNilpotentLieAlgebra X s w),
            ∃ D : Matrix (Fin d) (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ,
              ∃ S : Matrix (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) (Fin d) ℚ,
                LinearMap.toMatrix e b (FreeWeightedNilpotentLieAlgebra.mk X s w).toLinearMap = D ∧
                D * S = 1 ∧
                (∀ i j, rationalLogHeight (D i j) ≤ (p + C) ^ C) ∧
                (∀ i j, rationalLogHeight (S i j) ≤ (p + C) ^ C) ∧
                ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hsource⟩ := exists_free_nilpotent_source_basis s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 3) ^ 51)
  refine ⟨C, hC, ?_⟩
  intro X _ w p hp hX
  classical
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsum : B + (B + 3) ^ 51 ≤ (p + C) ^ C := by
    simpa [Q, B, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (B + 3) ^ 51)).trans hsum
  have h51 : (B + 3) ^ 51 ≤ (p + C) ^ C := (le_add_of_nonneg_left hB).trans hsum
  have hsmall (k : ℕ) (hk : k ≤ 51) : (B + 1 + 2) ^ k ≤ (p + C) ^ C := by
    rw [show B + 1 + 2 = B + 3 by ring]
    exact (pow_le_pow_right₀ (by linarith only [hB]) hk).trans h51
  obtain ⟨hdim, hcount, e, he, hstructure, hgen⟩ := hsource X p hp hX
  let T := FreeNilpotentLieAlgebra.weightedLayerGenerators X s w (s + 1)
  let I := FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)
  let v : T → FreeNilpotentLieAlgebra X s := Subtype.val
  have hrange : Set.range v = (T : Set (FreeNilpotentLieAlgebra X s)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule := by
    rw [hrange]
    exact (FreeNilpotentLieAlgebra.weightedLayer_eq_span X s w (s + 1)).symm
  have hcountT : (Fintype.card T : ℝ) ≤ B := by
    have hsub := Finset.card_le_card (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w (s + 1))
    exact (Nat.cast_le.mpr (by simpa only [T, Fintype.card_coe] using hsub)).trans hcount
  obtain ⟨d, hd, b, D, S, hmatrix, hDS, hD, hS, hbracket⟩ :=
    exists_lie_quotient_basis_exp_height e I v hspan (one_le_ceil_exp B)
      (fun i j => rationalHeightLE_ceil_exp (hgen j.val
        (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w (s + 1) j.property) i))
      (fun i j k => rationalHeightLE_ceil_exp (hstructure i j k))
      (show 0 ≤ B + 1 by linarith only [hB])
      (by simpa only [Fintype.card_fin] using hdim.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
      (hcountT.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
      (ceil_exp_le_exp_add_one hB)
  have hd' : d ≤ finrank ℚ (FreeNilpotentLieAlgebra X s) := by simpa only [Fintype.card_fin] using hd
  refine ⟨hdim.trans hBC, e, he, fun x hx i => (hgen x hx i).trans hBC,
    d, hd', (Nat.cast_le.mpr hd').trans (hdim.trans hBC), b, D, S, hmatrix, hDS, ?_, ?_, ?_⟩
  · intro i j
    exact ((rationalLogHeight_le_iff _ _).mpr (hD i j)).trans (hsmall 7 (by omega))
  · intro i j
    exact ((rationalLogHeight_le_iff _ _).mpr (hS i j)).trans (hsmall 45 (by omega))
  · intro i j k
    exact ((rationalLogHeight_le_iff _ _).mpr (hbracket i j k)).trans (hsmall 51 (by omega))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem squarePairMap_injective : Function.Injective F.squarePairMap := by
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrFun h true) (congrFun h false)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem eval_affinePullback [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) :
    (T.affinePullback A b).eval x = T.eval (integerAffineMap A b x) :=
  T.eval_substitute (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)
    x (integerAffineMap A b x) (integerAffinePolynomial_eval A b x)

theorem eval_linearPullbackHom [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) (x : τ → ℤ) :
    (T.linearPullbackHom f).eval x = T.eval (fun i => f i x) := by
  classical
  change (T.affinePullback (fun i j => f i (Pi.single j 1)) 0).eval x = _
  rw [eval_affinePullback]
  congr 1
  funext i
  simpa only [integerAffineMap, Pi.zero_apply, zero_add] using (integerLinearForm_eq_sum (f i) x).symm

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FreeWeightedRankGenerators
namespace OAI

section

namespace Erdos3.FreeWeightedNilpotentLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s : ℕ) (w : X → ℕ)

theorem rankAlphabetVector_mem (hw : ∀ x, 0 < w x) (a : RankAlphabet X s w) :
    rankAlphabetVector X s w a ∈ (filtration X s w hw).layer (rankAlphabetWeight X s w a) :=
  layerGenerators_mem X s w hw _ a.2.val a.2.property

theorem rankAlphabet_spans_layer (hw : ∀ x, 0 < w x) (d : ℕ) (hd : 0 < d) :
    (filtration X s w hw).layer d ≤ Submodule.span ℚ
      (rankAlphabetVector X s w '' {a | rankAlphabetWeight X s w a = d}) := by
  by_cases hds : d ≤ s + 1
  · let j : Fin (s + 1) := ⟨d - 1, by omega⟩
    have hj : j.val + 1 = d := by dsimp only [j]; omega
    rw [layer_eq_span]
    apply Submodule.span_mono
    intro x hx
    have hx' : x ∈ layerGenerators X s w (j.val + 1) := by simpa only [hj, Finset.mem_coe] using hx
    exact ⟨⟨j, ⟨x, hx'⟩⟩, hj, rfl⟩
  · have hbot : (filtration X s w hw).layer d = ⊥ := by
      apply bot_unique
      exact ((filtration X s w hw).antitone (by omega : s + 1 ≤ d)).trans
        (filtration X s w hw).terminal.le
    rw [hbot]
    exact bot_le

theorem topRankGenerators_span (hw : ∀ x, 0 < w x) (k : ℕ) :
    Submodule.span ℚ (topRankGenerators X s w k : Set _) = (filtration X s w hw).rankLayer s k := by
  rw [(filtration X s w hw).rankLayer_eq_weighted_tree_span
    (rankAlphabetVector X s w) (rankAlphabetWeight X s w) (rankAlphabetWeight_pos X s w)
    (rankAlphabetVector_mem X s w hw) (rankAlphabet_spans_layer X s w hw)]
  rw [(filtration X s w hw).terminal, bot_sup_eq,
    weightedLieTreeSpan_eq_finite_span _ _ (rankAlphabetWeight_pos X s w)]
  rfl

theorem topRankGenerators_logHeight {ι : Type*} [Fintype ι]
    (e : Basis ι ℚ (FreeWeightedNilpotentLieAlgebra X s w)) {p : ℝ}
    (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p)
    (hgen : ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
      rationalLogHeight (e.repr (mk X s w x) i) ≤ p)
    (k : ℕ) (x : FreeWeightedNilpotentLieAlgebra X s w) (hx : x ∈ topRankGenerators X s w k) (i : ι) :
    rationalLogHeight (e.repr x i) ≤ (p + 3) ^ (6 * s + 2) := by
  classical
  have hv (a : RankAlphabet X s w) (j : ι) :
      rationalLogHeight (e.repr (rankAlphabetVector X s w a) j) ≤ p := by
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp a.2.property
    change rationalLogHeight (e.repr a.2.val j) ≤ p
    rw [← hya]
    exact hgen y (FreeNilpotentLieAlgebra.weightedLayerGenerators_subset X s w _ hy) j
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hraw := finiteLieTrees_coordinate_height e (rankAlphabetVector X s w)
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
    (fun a j => rationalHeightLE_ceil_exp (hv a j)) s a (Finset.mem_filter.mp ha).1 i
  apply rationalLogHeight_le_of_height hraw
  simpa only [show p + 1 + 2 = p + 3 by ring] using
    lieTreeHeight_le_exp (Fintype.card ι) ⌈Real.exp p⌉₊ s
      (hp.trans (le_add_of_nonneg_right zero_le_one))
      (hd.trans (le_add_of_nonneg_right zero_le_one)) (ceil_exp_le_exp_add_one hp)

end Erdos3.FreeWeightedNilpotentLieAlgebra

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SupportedQuotientExactGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

theorem quotientStep_exact_grid_supported (Γ : Subgroup F.Group) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N) :
    bchSubgroupCoordinates (supportedQuotientBasis b I.toSubmodule S hspan)
      (Γ.map (F.quotientStepHom I hI)) = scaledIntegerGrid N := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp hx
    have hgc := (bchSubgroupCoordinates_repr b Γ g).mpr hg
    rw [hgrid] at hgc
    obtain ⟨z, hz⟩ := hgc
    refine ⟨fun i => z i, ?_⟩
    funext i
    have hr := congrArg
      (fun v : (F.quotientLie I hI).Group =>
        (supportedQuotientBasis b I.toSubmodule S hspan).equivFun v.coord i) he
    rw [LinearEquiv.apply_symm_apply] at hr
    change (supportedQuotientBasis b I.toSubmodule S hspan).repr
      (I.toSubmodule.mkQ g.coord) i = x i at hr
    rw [supportedQuotientBasis_repr_mk] at hr
    exact hr.symm.trans (congrFun hz i)
  · exact F.quotientStep_inner_grid_supported b I hI S hspan Γ
      (by rw [hgrid])

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.StepOneCoordinateMetric
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module Manifold NilpotentLieBCHGroup
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  (F : NilpotentLieFiltration L 1) (e : Basis ι ℝ L)

omit [IsScalarTower ℚ ℝ L] in
theorem stepOne_rightTranslate (g : F.Group) (x : ι → ℝ) :
    rightTranslate e g x = x + e.equivFun g.coord := by
  simp only [rightTranslate, basisHomeomorph_apply, F.stepOne_coord_mul, map_add]
  rw [← basisHomeomorph_apply, Homeomorph.apply_symm_apply]

omit [IsScalarTower ℚ ℝ L] in
theorem stepOne_rightVelocity (g : F.Group) :
    rightVelocity e g = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  unfold rightVelocity
  have heq : rightTranslate e g⁻¹ = fun x => x + e.equivFun (g⁻¹).coord :=
    funext (F.stepOne_rightTranslate e g⁻¹)
  rw [heq]
  simp

theorem stepOne_norm_mfderiv_coordinates_le (g : F.Group) :
    letI := basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
    letI := rightRiemannianBundle (hnil := F.lowerCentralSeries_eq_bot) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖tangentModelVector (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v)‖ ≤ ‖v‖ := by
  let := basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
  let := rightRiemannianBundle (hnil := F.lowerCentralSeries_eq_bot) e
  intro v
  calc
    _ = ‖tangentModelVector v‖ := congrArg (fun w => ‖tangentModelVector w‖)
      (mfderiv_basisHomeomorph_coordinates e g v)
    _ ≤ coordinateL2Norm v := norm_le_coordinateL2Norm _
    _ = ‖v‖ := by
      rw [norm_tangent_eq_coordinateL2Norm, F.stepOne_rightVelocity]
      rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}
  (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound)

noncomputable def piRealOrbit (g : ∀ i, (F i).realification.PolynomialOrbit) :
    (pi F).realification.PolynomialOrbit :=
  (pi F).realification.polynomialOrbitOfLog
    (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ)
      ((g i).log (F i).realification)) (by
      intro a
      simp only [map_sum, Finsupp.finsetSum_apply, VectorPolynomial.coefficients_map]
      apply Submodule.sum_mem
      intro i _
      exact realProductSingle_mem_layer F i _ ((g i).adapted (F i).realification a))

theorem piRealOrbit_eval (g : ∀ i, (F i).realification.PolynomialOrbit) (x : σ → ℤ) (i : ι) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (pi F).ordinary.lowerCentralSeries_eq_bot)
      (hM := (F i).ordinary.lowerCentralSeries_eq_bot) (liePiEval i)
      ((pi F).realification.polynomialOrbitEval x (piRealOrbit F g)) =
        (F i).realification.polynomialOrbitEval x (g i) := by
  classical
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieBCHGroup.realificationMap_coord, polynomialOrbitEval_coord,
    piRealOrbit, polynomialOrbitOfLog, PolynomialOrbit.log, map_sum, VectorPolynomial.eval_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

theorem piRealOrbit_coefficient (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (α : σ →₀ ℕ) (i : ι) :
    realificationLieHom (liePiEval i) (coefficients (piRealOrbit F p).log α) =
      coefficients (p i).log α := by
  classical
  simp only [piRealOrbit, polynomialOrbitOfLog_log, map_sum,
    Finsupp.finsetSum_apply, coefficients_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ProductFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem piFrequency_single (eta : ∀ i, L i →ₗ[ℚ] ℚ) (i : ι) (x : L i) :
    letI := Classical.decEq ι
    piFrequency eta (Pi.single i x) = eta i x := by
  classical
  rw [piFrequency_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SourceLatticeCover
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix

namespace RationalFilteredNilmanifold

theorem exists_native_source_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {s t d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup D.filtration.Group,
        Λ ≤ D.lattice ∧ (Λ.subgroupOf D.lattice).Characteristic ∧
        (Λ.subgroupOf D.lattice).Normal ∧ (Λ.subgroupOf D.lattice).FiniteIndex ∧
        (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          (D.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
          Λ ≤ E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 2 * R ^ 2 + (R + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d e D E φ p hp hD hE hφ
  classical
  let A := LinearMap.toMatrix D.basis E.basis φ.toLinearMap
  have hAb : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply matrixDenominator_le_exp_power A hp 1
      (by simpa only [Fintype.card_fin] using hE.1)
      (by simpa only [Fintype.card_fin] using hD.1)
    intro i j
    have h := ((rationalLogHeight_le_iff _ p).mp (hφ i j)).2
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact h.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  let N₀ := E.grid * matrixDenominator A
  let Λ₀ := E.lattice.comap (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ)
  have hN₀ : 0 < N₀ := Nat.mul_pos E.grid_pos (matrixDenominator_pos A)
  have hgrid : scaledIntegerGrid N₀ ⊆ bchSubgroupCoordinates D.basis Λ₀ := by
    rw [bchSubgroupCoordinates_comap_ofSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot) D.basis E.basis φ E.lattice]
    intro x hx
    exact E.inner_grid (matrix_mulVec_fine_grid A E.grid hx)
  let r := p + (p + 2) ^ 3
  have hpr : p ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hr : 0 ≤ r := hp.trans hpr
  have hN₀b : (N₀ : ℝ) ≤ Real.exp r := by
    rw [show (N₀ : ℝ) = (E.grid : ℝ) * matrixDenominator A by exact Nat.cast_mul _ _]
    exact (mul_le_mul hE.2.1 hAb (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hNb, hin, hout⟩ :=
    D.filtration.exists_normal_cover_exp_quadratic D.basis D.lattice Λ₀
      D.grid N₀ D.grid_pos hN₀ D.inner_grid D.outer_grid hgrid hr
      (by simpa only [Fintype.card_fin] using hD.1.trans hpr)
      (hD.2.1.trans (Real.exp_le_exp.mpr hpr)) hN₀b
  have htotal : r + 2 * r ^ 2 + (r + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by nlinarith [sq_nonneg r, sq_nonneg (r + 2)]
  have hiC : 2 * r ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 2)]
  have hgC : (r + 2) ^ 2 ≤ (p + C) ^ C := by nlinarith [sq_nonneg r]
  exact ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hiC),
    N, hN, hin, hout,
    D.withLattice_geometry Λ N hN hin hout hD (hpr.trans hrC)
      (hNb.trans (Real.exp_le_exp.mpr hgC)), htarget⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SupportedQuotientLatticeFaithful
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t u : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

include hspan in
theorem realQuotientStep_integral_coordinates (Γ : Subgroup F.Group) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : F.realification.Group)
    (hg : F.realQuotientStepHom I hI g ∈
      (Γ.map (F.quotientStepHom I hI)).map realificationHom) :
    ∃ z : {i // i ∉ S} → ℤ, ∀ i : {i // i ∉ S},
      (b.baseChange ℝ).repr g.coord i = (N : ℝ) * (z i : ℝ) := by
  let bq : Basis {i // i ∉ S} ℚ (L ⧸ I) := supportedQuotientBasis b I.toSubmodule S hspan
  have hq : bchSubgroupCoordinates bq (Γ.map (F.quotientStepHom I hI)) = scaledIntegerGrid N :=
    F.quotientStep_exact_grid_supported b I hI S hspan Γ N hgrid
  obtain ⟨z, hz⟩ := (mem_realification_integral_lattice_iff (L := L ⧸ I)
    (hnil := (F.quotientLie I hI).lowerCentralSeries_eq_bot) bq
    (Γ.map (F.quotientStepHom I hI)) N hq (F.realQuotientStepHom I hI g)).mp hg
  refine ⟨z, fun i => ?_⟩
  have hi := hz i
  change ((supportedQuotientBasis b I.toSubmodule S hspan).baseChange ℝ).repr
    (I.toSubmodule.mkQ.baseChange ℝ g.coord) i = _ at hi
  rwa [realSupportedQuotientBasis_repr_mk] at hi

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedQuotientFamilyFaithful
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {α ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)

theorem realQuotientFamily_lattice_detect
    (I : α → LieIdeal ℚ L) (hI : ∀ a, F.layer (t + 1) ≤ (I a).toSubmodule)
    (S : α → Set ι) (hspan : ∀ a, (I a).toSubmodule = Submodule.span ℚ (b '' S a))
    (hcover : ∀ i, ∃ a, i ∉ S a)
    (Γ : Subgroup F.Group) (N : ℕ) (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : F.realification.Group)
    (hg : ∀ a, F.realQuotientStepHom (I a) (hI a) g ∈
      (Γ.map (F.quotientStepHom (I a) (hI a))).map realificationHom) :
    g ∈ Γ.map realificationHom := by
  classical
  have hcoords (a : α) := F.realQuotientStep_integral_coordinates b (I a) (hI a)
    (S a) (hspan a) Γ N hgrid g (hg a)
  choose z hz using hcoords
  choose a ha using hcover
  apply (mem_realification_integral_lattice_iff b Γ N hgrid g).mpr
  exact ⟨fun i => z (a i) ⟨i, ha i⟩, fun i => hz (a i) ⟨i, ha i⟩⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPositivePolynomialEvaluation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialEvaluation : F.positivePolynomialAlgebra →ₗ⁅ℚ⁆ L :=
  (evalLie (fun _ : σ => (1 : ℚ))).comp F.positivePolynomialAlgebra.incl

theorem positivePolynomialEvaluation_apply (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialEvaluation p = eval (fun _ : σ => (1 : ℚ)) p.val := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialComponent (a : σ →₀ ℕ) :
    F.positivePolynomialAlgebra →ₗ[ℚ] F.positivePolynomialAlgebra where
  toFun p := ⟨monomial a (coefficients p.val a),
    F.monomial_mem_adaptedSubmodule a (p.property.1 a), by
      classical
      by_cases ha : a = 0
      · subst a
        simp only [coefficients_monomial, Finsupp.single_eq_same, F.positivePolynomial_constant]
      · simp [ha]⟩
  map_add' p q := by
    apply Subtype.ext
    change monomial a (coefficients (p.val + q.val) a) =
      monomial a (coefficients p.val a) + monomial a (coefficients q.val a)
    simp [monomial, TensorProduct.tmul_add]
  map_smul' c p := by
    apply Subtype.ext
    change monomial a (coefficients (c • p.val) a) = c • monomial a (coefficients p.val a)
    simp [monomial]

theorem sum_positivePolynomialComponent (p : F.positivePolynomialAlgebra) :
    ∑ a ∈ (coefficients p.val).support, F.positivePolynomialComponent a p = p := by
  classical
  apply Subtype.ext
  change F.positivePolynomialAlgebra.incl
    (∑ a ∈ (coefficients p.val).support, F.positivePolynomialComponent a p) = p.val
  rw [map_sum]
  exact sum_monomial_coefficients p.val

theorem positivePolynomialEvaluation_component (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialEvaluation (F.positivePolynomialComponent a p) = coefficients p.val a := by
  change eval (fun _ : σ => (1 : ℚ)) (monomial a (coefficients p.val a)) = _
  simp [eval_monomial, Finsupp.prod]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialDegreeLayer (n : ℕ) :
    Submodule ℚ F.positivePolynomialAlgebra :=
  (coefficientSupport {a : σ →₀ ℕ | n ≤ ∑ i, a i}).comap
    F.positivePolynomialAlgebra.incl.toLinearMap

theorem positivePolynomialDegreeLayer_antitone : Antitone F.positivePolynomialDegreeLayer := by
  intro n m hnm p hp a ha
  exact hp a (fun hm => ha (hnm.trans hm))

theorem positivePolynomialDegreeLayer_one : F.positivePolynomialDegreeLayer 1 = ⊤ := by
  classical
  apply top_unique
  intro p _ a ha
  change ¬1 ≤ ∑ i, a i at ha
  have hs : (∑ i, a i) = 0 := by omega
  have hz : a = 0 := by
    ext i
    have hi : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    simpa only [hs, Nat.le_zero_eq, Finsupp.zero_apply] using hi
  subst a
  exact p.property.2

theorem positivePolynomialDegreeLayer_lie {n m : ℕ} {p q : F.positivePolynomialAlgebra}
    (hp : p ∈ F.positivePolynomialDegreeLayer n) (hq : q ∈ F.positivePolynomialDegreeLayer m) :
    ⁅p, q⁆ ∈ F.positivePolynomialDegreeLayer (n + m) := by
  change ⁅p.val, q.val⁆ ∈ coefficientSupport _
  apply coefficientSupport_lie (S := {a : σ →₀ ℕ | n ≤ ∑ i, a i})
    (T := {a : σ →₀ ℕ | m ≤ ∑ i, a i}) _ hp hq
  intro a ha b hb
  change n + m ≤ ∑ i, (a + b) i
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib] using add_le_add ha hb

theorem positivePolynomialDegreeLayer_terminal :
    F.positivePolynomialDegreeLayer ((∑ i, bound i) + 1) = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply coefficients.injective
  ext a
  change coefficients p.val a = 0
  by_cases ha : (fun i => a i) ≤ bound
  · apply hp a
    have hsum : (∑ i, a i) ≤ ∑ i, bound i := Finset.sum_le_sum (fun i _ => ha i)
    change ¬(∑ i, bound i) + 1 ≤ ∑ i, a i
    omega
  · simpa only [F.terminal _ ha, Submodule.mem_bot] using p.property.1 a

noncomputable def positivePolynomialDegreeFiltration :
    NilpotentLieFiltration F.positivePolynomialAlgebra (∑ i, bound i) where
  layer := F.positivePolynomialDegreeLayer
  antitone := F.positivePolynomialDegreeLayer_antitone
  one_eq_top := F.positivePolynomialDegreeLayer_one
  lie_mem := F.positivePolynomialDegreeLayer_lie
  terminal := F.positivePolynomialDegreeLayer_terminal

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ}

variable (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialCoordinates :
    F.positivePolynomialAlgebra →ₗ[ℚ] (BoxedDegreeIndex bound → L) where
  toFun p a := coefficients p.val (boxedDegreeMonomial a)
  map_add' p q := by ext a; simp
  map_smul' c p := by ext a; simp

theorem positivePolynomialCoordinates_injective : Function.Injective F.positivePolynomialCoordinates := by
  classical
  intro p q hpq
  apply Subtype.ext
  apply coefficients.injective
  ext a
  by_cases ha : (fun i => a i) ≤ bound
  · let b : BoxedDegreeIndex bound := fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩
    have hb : boxedDegreeMonomial b = a := by ext i; simp [b]
    have h := congrFun hpq b
    change coefficients p.val (boxedDegreeMonomial b) = coefficients q.val (boxedDegreeMonomial b) at h
    simpa only [hb] using h
  · have hp : coefficients p.val a = 0 := by
      simpa only [F.terminal _ ha, Submodule.mem_bot] using p.property.1 a
    have hq : coefficients q.val a = 0 := by
      simpa only [F.terminal _ ha, Submodule.mem_bot] using q.property.1 a
    rw [hp, hq]

instance positivePolynomialFiniteDimensional [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ F.positivePolynomialAlgebra :=
  FiniteDimensional.of_injective F.positivePolynomialCoordinates F.positivePolynomialCoordinates_injective

theorem positivePolynomial_finrank_le [FiniteDimensional ℚ L] :
    finrank ℚ F.positivePolynomialAlgebra ≤ (∏ i, (bound i + 1)) * finrank ℚ L := by
  classical
  calc
    _ ≤ finrank ℚ (BoxedDegreeIndex bound → L) :=
      LinearMap.finrank_le_finrank_of_injective F.positivePolynomialCoordinates_injective
    _ = ∑ _ : BoxedDegreeIndex bound, finrank ℚ L := Module.finrank_pi_fintype ℚ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_pi, Fintype.card_fin, Nat.cast_id]

theorem positivePolynomial_finrank_le_total [FiniteDimensional ℚ L] :
    finrank ℚ F.positivePolynomialAlgebra ≤ 2 ^ (∑ i, bound i) * finrank ℚ L := by
  classical
  have h : (∏ i, (bound i + 1)) ≤ 2 ^ (∑ i, bound i) := by
    calc
      _ ≤ ∏ i, 2 ^ bound i := Finset.prod_le_prod' (fun i _ => Nat.succ_le_of_lt (Nat.lt_two_pow_self))
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum]
  exact F.positivePolynomial_finrank_le.trans (Nat.mul_le_mul_right _ h)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realPositivePolynomialMap :
    (ℝ ⊗[ℚ] F.positivePolynomialAlgebra) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  VectorPolynomial.realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) F.positivePolynomialAlgebra.incl)

theorem realPositivePolynomialMap_coefficient_tmul
    (r : ℝ) (p : F.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    coefficients (F.realPositivePolynomialMap (r ⊗ₜ[ℚ] p)) a = r ⊗ₜ[ℚ] coefficients p.val a := by
  change coefficients (VectorPolynomial.realificationLieEquiv (r ⊗ₜ[ℚ] p.val)) a = _
  exact coefficients_realificationLieEquiv_tmul r p.val a

theorem realPositivePolynomialMap_adapted (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realification.Adapted (F.realPositivePolynomialMap x) := by
  intro a
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    rw [F.realPositivePolynomialMap_coefficient_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (p.property.1 a)
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact Submodule.add_mem _ hx hy

theorem realPositivePolynomialMap_constant (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    coefficients (F.realPositivePolynomialMap x) 0 = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    rw [F.realPositivePolynomialMap_coefficient_tmul, p.property.2, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]

noncomputable def realPositivePolynomialTensor :
    (ℝ ⊗[ℚ] F.positivePolynomialAlgebra) →ₗ⁅ℚ⁆ F.realification.positivePolynomialAlgebra where
  toLinearMap := F.realPositivePolynomialMap.toLinearMap.codRestrict
    F.realification.positivePolynomialAlgebra.toSubmodule
    (fun x => ⟨F.realPositivePolynomialMap_adapted x, F.realPositivePolynomialMap_constant x⟩)
  map_lie' {x y} := by
    apply Subtype.ext
    exact F.realPositivePolynomialMap.map_lie x y

theorem realPositivePolynomialTensor_injective : Function.Injective F.realPositivePolynomialTensor := by
  intro x y h
  apply realification_subtype_injective F.positivePolynomialAlgebra.toSubmodule
  apply VectorPolynomial.realificationLieEquiv.injective
  exact congrArg Subtype.val h

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialMultidegreeLayer (a : σ → ℕ) :
    Submodule ℚ F.positivePolynomialAlgebra :=
  (coefficientSupport {b : σ →₀ ℕ | a ≤ fun i => b i}).comap
    F.positivePolynomialAlgebra.incl.toLinearMap

theorem positivePolynomialMultidegreeLayer_antitone :
    Antitone F.positivePolynomialMultidegreeLayer := by
  intro a b hab p hp c hc
  exact hp c (fun hbc => hc (hab.trans hbc))

theorem positivePolynomialMultidegreeLayer_zero : F.positivePolynomialMultidegreeLayer 0 = ⊤ := by
  apply top_unique
  intro p _ a ha
  exact False.elim (ha (fun i => Nat.zero_le (a i)))

theorem positivePolynomialMultidegreeLayer_lie {a b : σ → ℕ} {p q : F.positivePolynomialAlgebra}
    (hp : p ∈ F.positivePolynomialMultidegreeLayer a)
    (hq : q ∈ F.positivePolynomialMultidegreeLayer b) :
    ⁅p, q⁆ ∈ F.positivePolynomialMultidegreeLayer (a + b) := by
  change ⁅p.val, q.val⁆ ∈ coefficientSupport _
  apply coefficientSupport_lie (S := {c : σ →₀ ℕ | a ≤ fun i => c i})
    (T := {c : σ →₀ ℕ | b ≤ fun i => c i}) _ hp hq
  intro c hc d hd i
  exact add_le_add (hc i) (hd i)

theorem positivePolynomialMultidegreeLayer_terminal (a : σ → ℕ) (ha : ¬a ≤ bound) :
    F.positivePolynomialMultidegreeLayer a = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply coefficients.injective
  ext b
  change coefficients p.val b = 0
  by_cases hab : a ≤ fun i => b i
  · have hb : ¬(fun i => b i) ≤ bound := fun hb => ha (hab.trans hb)
    simpa only [F.terminal _ hb, Submodule.mem_bot] using p.property.1 b
  · exact hp b hab

theorem positivePolynomialComponent_mem_layer (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialComponent a p ∈ F.positivePolynomialMultidegreeLayer (fun i => a i) := by
  change monomial a (coefficients p.val a) ∈
    coefficientSupport {b : σ →₀ ℕ | (fun i => a i) ≤ fun i => b i}
  apply monomial_mem_coefficientSupport
  exact fun i => le_rfl

theorem positivePolynomialDegreeLayer_eq (n : ℕ) :
    F.positivePolynomialDegreeLayer n =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), F.positivePolynomialMultidegreeLayer a := by
  classical
  apply le_antisymm
  · intro p hp
    rw [← F.sum_positivePolynomialComponent p]
    apply Submodule.sum_mem
    intro a ha
    have hn : n ≤ ∑ i, a i := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp ha) (hp a hn)
    have hle : F.positivePolynomialMultidegreeLayer (fun i => a i) ≤
        ⨆ (b : σ → ℕ) (_hb : n ≤ ∑ i, b i), F.positivePolynomialMultidegreeLayer b :=
      le_iSup_of_le (fun i => a i) (le_iSup_of_le hn le_rfl)
    exact hle (F.positivePolynomialComponent_mem_layer a p)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha p hp b hb
    apply hp b
    intro hab
    exact hb (ha.trans (Finset.sum_le_sum (fun i _ => hab i)))

noncomputable def positivePolynomialMultidegree :
    MultidegreeLieFiltration σ F.positivePolynomialAlgebra (∑ i, bound i) bound where
  ordinary := F.positivePolynomialDegreeFiltration
  layer := F.positivePolynomialMultidegreeLayer
  antitone := F.positivePolynomialMultidegreeLayer_antitone
  zero_eq_top := F.positivePolynomialMultidegreeLayer_zero
  lie_mem := F.positivePolynomialMultidegreeLayer_lie
  terminal := F.positivePolynomialMultidegreeLayer_terminal
  degree_eq := F.positivePolynomialDegreeLayer_eq

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem positivePolynomialComponent_eq_zero (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialComponent a p = 0 ↔ coefficients p.val a = 0 := by
  constructor
  · intro h
    have he := congrArg (fun q : F.positivePolynomialAlgebra => coefficients q.val a) h
    change coefficients (monomial a (coefficients p.val a)) a =
      coefficients (0 : VectorPolynomial σ ℚ L) a at he
    simpa only [coefficients_monomial,
      Finsupp.single_eq_same, map_zero, Finsupp.zero_apply] using he
  · intro h
    apply Subtype.ext
    change monomial a (coefficients p.val a) = 0
    simp [h, monomial]

noncomputable def positivePolynomialDiagonal (p : F.positivePolynomialAlgebra) :
    VectorPolynomial σ ℚ F.positivePolynomialAlgebra :=
  (coefficients p.val).sum (fun a _ => monomial a (F.positivePolynomialComponent a p))

theorem positivePolynomialDiagonal_coefficient (p : F.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    coefficients (F.positivePolynomialDiagonal p) a = F.positivePolynomialComponent a p := by
  classical
  by_cases ha : a ∈ (coefficients p.val).support
  · simp [positivePolynomialDiagonal, Finsupp.sum, Finsupp.single_apply, ha]
  · have hz : F.positivePolynomialComponent a p = 0 :=
      (F.positivePolynomialComponent_eq_zero a p).mpr (Finsupp.notMem_support_iff.mp ha)
    simp [positivePolynomialDiagonal, Finsupp.sum, Finsupp.single_apply, ha, hz]

theorem positivePolynomialDiagonal_adapted (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialMultidegree.Adapted (F.positivePolynomialDiagonal p) := by
  intro a
  rw [F.positivePolynomialDiagonal_coefficient]
  exact F.positivePolynomialComponent_mem_layer a p

theorem positivePolynomialDiagonal_constant (p : F.positivePolynomialAlgebra) :
    coefficients (F.positivePolynomialDiagonal p) 0 = 0 := by
  rw [F.positivePolynomialDiagonal_coefficient, F.positivePolynomialComponent_eq_zero]
  exact p.property.2

theorem positivePolynomialDiagonal_projection (p : F.positivePolynomialAlgebra) :
    VectorPolynomial.map F.positivePolynomialEvaluation.toLinearMap
      (F.positivePolynomialDiagonal p) = p.val := by
  apply coefficients.injective
  ext a
  rw [coefficients_map, F.positivePolynomialDiagonal_coefficient]
  exact F.positivePolynomialEvaluation_component a p

theorem positivePolynomialDiagonal_eval (p : F.positivePolynomialAlgebra) (x : σ → ℚ) :
    F.positivePolynomialEvaluation (eval x (F.positivePolynomialDiagonal p)) = eval x p.val := by
  change F.positivePolynomialEvaluation.toLinearMap (eval x (F.positivePolynomialDiagonal p)) = _
  rw [← eval_map, F.positivePolynomialDiagonal_projection]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem positivePolynomial_support_of_layers (S : Set (σ →₀ ℕ))
    (hS : ∀ a, a ≠ 0 → a ∉ S → F.layer (fun i => a i) = ⊥)
    (p : F.positivePolynomialAlgebra) : p.val ∈ coefficientSupport S := by
  intro a ha
  by_cases hz : a = 0
  · subst a
    exact p.property.2
  · simpa only [hS a hz ha, Submodule.mem_bot] using p.property.1 a

theorem positivePolynomialLayer_le_outsideDownset
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (a : σ →₀ ℕ) (ha : a ∉ J) :
    F.positivePolynomialMultidegreeLayer (fun i => a i) ≤
      (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule := by
  intro p hp
  apply (mem_restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ p).mpr
  intro b hb
  apply hp b
  intro hab
  exact ha (hJ hab hb)

noncomputable def positivePolynomialDownsetQuotient
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) :=
  F.positivePolynomialMultidegree.quotientMultidegree
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ)

theorem positivePolynomialDownsetQuotient_terminal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (a : σ →₀ ℕ) (ha : a ∉ J) :
    (F.positivePolynomialDownsetQuotient J hJ).layer (fun i => a i) = ⊥ :=
  F.positivePolynomialMultidegree.quotientMultidegree_layer_eq_bot _ _
    (F.positivePolynomialLayer_le_outsideDownset J hJ a ha)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_positivePolynomial_orbit (g : F.PolynomialOrbit)
    (hg : F.polynomialOrbitEval 0 g = 1) :
    ∃ h : F.positivePolynomialMultidegree.PolynomialOrbit,
      F.positivePolynomialMultidegree.polynomialOrbitEval 0 h = 1 ∧
      ∀ x, NilpotentLieBCHGroup.mapOfSteps F.positivePolynomialEvaluation
          (F.positivePolynomialMultidegree.polynomialOrbitEval x h) =
        F.polynomialOrbitEval x g := by
  have hzero : coefficients (PolynomialOrbit.log F g) 0 = 0 := by
    have hcoord := congrArg NilpotentLieBCHGroup.coord hg
    change eval (fun i => ((0 : σ → ℤ) i : ℚ)) (PolynomialOrbit.log F g) = 0 at hcoord
    simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using hcoord
  let p : F.positivePolynomialAlgebra := ⟨PolynomialOrbit.log F g, PolynomialOrbit.adapted F g, hzero⟩
  let h := F.positivePolynomialMultidegree.polynomialOrbitOfLog
    (F.positivePolynomialDiagonal p) (F.positivePolynomialDiagonal_adapted p)
  refine ⟨h, ?_, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    change eval (fun i => ((0 : σ → ℤ) i : ℚ)) (F.positivePolynomialDiagonal p) = 0
    simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using
      F.positivePolynomialDiagonal_constant p
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact F.positivePolynomialDiagonal_eval p (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realPositivePolynomialEvaluation_commute (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realification.positivePolynomialEvaluation (F.realPositivePolynomialTensor x) =
      realificationLieHom F.positivePolynomialEvaluation x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    change eval (fun _ : σ => (1 : ℚ))
      (VectorPolynomial.realificationLieEquiv (r ⊗ₜ[ℚ] p.val)) =
        r ⊗ₜ[ℚ] eval (fun _ : σ => (1 : ℚ)) p.val
    exact eval_realificationLieEquiv_tmul r p.val _
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositivePolynomialLayerBases
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positiveCoefficientLayer (a : BoxedDegreeIndex bound) : Submodule ℚ L := by
  classical
  exact if boxedDegreeMonomial a = 0 then ⊥ else F.layer (fun i => (a i).val)

theorem mem_positiveCoefficientLayer (a : BoxedDegreeIndex bound) (x : L) :
    x ∈ F.positiveCoefficientLayer a ↔
      x ∈ F.layer (fun i => (a i).val) ∧ (boxedDegreeMonomial a = 0 → x = 0) := by
  classical
  by_cases ha : boxedDegreeMonomial a = 0
  · have hzero : (fun i => (a i).val) = 0 := by
      funext i
      have h := congrArg (fun b : σ →₀ ℕ => b i) ha
      simpa only [boxedDegreeMonomial_apply, Finsupp.zero_apply, Pi.zero_apply] using h
    simp [positiveCoefficientLayer, ha, hzero, F.zero_eq_top]
  · simp [positiveCoefficientLayer, ha]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

theorem pairDifferenceFunctional_eq_piFrequency {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (η : L →ₗ[ℚ] ℚ) :
    pairDifferenceFunctional η = piFrequency (fun i : Fin 2 => if i = 0 then η else -η) := by
  ext x
  simp [piFrequency_apply, Fin.sum_univ_two, pairDifferenceFunctional_apply, sub_eq_add_neg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerOrbitTranslation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

@[simp] theorem integerOrbitPoint_translate
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (c n : ℤ) :
    D.integerOrbitPoint (g.translate (fun _ => Nat.zero_lt_one) (fun _ => c)) n =
      D.integerOrbitPoint g (n + c) := by
  unfold integerOrbitPoint
  rw [NilpotentLieFiltration.polynomialOrbitEval_translate]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

def LeadingWeylBound (k B K : ℕ) : Prop :=
  ∀ (P : Polynomial ℝ), P.natDegree ≤ k → ∀ N : ℕ, 0 < N → K ≤ N →
    (N : ℝ) / B ≤ ‖polynomialExponentialSum P N‖ →
    ∃ q : ℕ, 0 < q ∧ q ≤ K ∧ ∃ p : ℤ,
      |(q : ℝ) * P.coeff k - p| ≤ (K : ℝ) / (N : ℝ) ^ k

end Erdos3

end

end OAI
end


