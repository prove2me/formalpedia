-- Prove2me | Definitions.Def_OAIE3v2B102
-- name    : OAIE3v2B102
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:01.140657+00:00
-- url     : https://prove2.me/theorems/9a840265-010e-456e-a568-15efafce5db0
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 104 of 311
-- statement:
--   Definitions bundle 104 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B073`, `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B089`, `OAIE3v2B090` of this split.
--
--   Modules: `Estimates/BoundedCoefficientExpansion.lean`, `Estimates/BoundedHomogeneousFactorization.lean`, `Estimates/FreeWeightedLayerBounds.lean`, `Estimates/HomogenizedModeFactorization.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/OneSiteCoefficientFactorization.lean`, `Estimates/PinnedSectionMeans.lean`, `Estimates/RealSymbolRepresentativeSplitting.lean`, `Estimates/SquareGradedRelative.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Estimates/VectorAlgebraicMajorDecomposition.lean`, `Estimates/VectorHomogenization.lean`, `FixedDensity/GeneratorCells.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/LayeredFourierCharacter.lean`, `Fourier/ProductFrequencyKernel.lean`, `Fourier/SectionRetainedFourier.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/AffineCoveredSiteValues.lean`, `Lattices/RetainedAffineCommonCover.lean`, `Linear/BooleanJetMatrixFactor.lean`, `Linear/DualIdealSteps.lean`, `Linear/TopSubspaceAdaptedBasis.lean`, `Nilpotent/BCHChartCutoffSmooth.lean`, `Nilpotent/BCHConjugationLinear.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Nilpotent/BCHUniformQuotientCharts.lean`, `Nilpotent/FreeNilpotentLieAlgebra.lean`, `Nilpotent/FreeWeightedNilpotentLieAlgebra.lean`, `Polynomial/AdaptedBinomialFactorization.lean`, `Polynomial/AdaptedPolynomialSubstitution.lean`, `Polynomial/BoundedArrayPolynomial.lean`, `Polynomial/PolynomialShearFactorialIntegrality.lean`, `Polynomial/PolynomialTranslationActionCompatibility.lean`, `Polynomial/RaisedDegreeRank.lean`, `Polynomial/RankPolynomialFactorization.lean`, `Polynomial/RealPolynomialChartSubstitution.lean`, `Polynomial/ShiftedPolynomialBasis.lean`, `Polynomial/ShiftedPolynomialIdeals.lean`, `Polynomial/TranslationPhasePointBounds.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Polynomial/TranslationTopDegree.lean`, `Polynomial/VectorPolynomialAffineDegree.lean`, `Probability/ObservedProductDensity.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B073
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B089
import Definitions.Def_OAIE3v2B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
namespace OAI


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem polynomialOrbitSubstitute_eval {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (p : F.PolynomialOrbit w) (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (f i) = (y i : ℚ)) :
    F.polynomialOrbitEval v x (F.polynomialOrbitSubstitute f hf p) = F.polynomialOrbitEval w y p := by
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun j => (x j : ℚ)) (VectorPolynomial.substitute f p.log) = _
  rw [VectorPolynomial.eval_substitute]
  simp only [hxy]
  rfl

end Erdos3.NilpotentLieFiltration

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorHomogenization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

theorem eval_homogenize {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (p : VectorPolynomial I R W) (x : I → R) :
    eval (fun i : Option I => i.elim 1 x) (homogenize h p) = eval x p := by
  have he := congrArg (eval x) (dehomogenize_homogenize h p)
  rw [eval_substitute] at he
  convert he using 1
  apply congrArg (fun y => eval y (homogenize h p))
  funext i
  cases i <;> simp [dehomogenizingSubstitution]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realLieSubgroup (K : LieSubalgebra ℝ L) : Subgroup (NilpotentLieBCHGroup L s hnil) :=
  subgroup (realLieSubalgebraOverRat K)

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped NNReal Topology

theorem lieBCH_right_coordinates_sub_bound {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H s : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (x y z : L) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx : ∀ i, |e.repr x i| ≤ B) (hy : ∀ i, |e.repr y i| ≤ B)
    (hz : ∀ i, |e.repr z i| ≤ B) (hxy : ∀ i, |e.repr x i - e.repr y i| ≤ δ) (k : ι) :
    |e.repr (lieBCH s x z) k - e.repr (lieBCH s y z) k| ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  classical
  let P := bchCoordinatePolynomial c s k
  let v : Fin 2 × ι → ℝ := fun i => e.repr (![x, z] i.1) i.2
  let w : Fin 2 × ι → ℝ := fun i => e.repr (![y, z] i.1) i.2
  have hdegree : P.totalDegree ≤ s := bchCoordinatePolynomial_totalDegree c s k
  have hv (i : Fin 2 × ι) : |v i| ≤ B := by
    rcases i with ⟨j, i⟩
    fin_cases j
    · exact hx i
    · exact hz i
  have hw (i : Fin 2 × ι) : |w i| ≤ B := by
    rcases i with ⟨j, i⟩
    fin_cases j
    · exact hy i
    · exact hz i
  have hvw (i : Fin 2 × ι) : |v i - w i| ≤ δ := by
    rcases i with ⟨j, i⟩
    fin_cases j
    · exact hxy i
    · simpa [v, w] using hδ
  have hcoeff (m) : |((P.coeff m : ℚ) : ℝ)| ≤ bchCoordinateHeight s (Fintype.card ι) H :=
    (bchCoordinatePolynomial_height c hc s k m).abs_real_le
  have h := abs_aeval_sub_aeval_box_bound P v w (Nat.cast_nonneg _) hB hδ hcoeff hv hw hvw hdegree
  have hevalv : aeval v P = e.repr (lieBCH s x z) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x z k
  have hevalw : aeval w P = e.repr (lieBCH s y z) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s y z k
  rw [hevalv, hevalw] at h
  have hcard := polynomial_support_card_le P hdegree
  apply h.trans
  dsimp only [bchBoxCoordinateBound]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hcard

namespace NilpotentLieBCHGroup

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem lipschitzOn_rightTranslate_box (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    LipschitzOnWith ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
      bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
      (rightTranslate e g) {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  change ∀ i, |v i| ≤ B at hv
  change ∀ i, |w i| ≤ B at hw
  apply (dist_pi_le_iff (mul_nonneg
    (bchBoxCoordinateBound_nonneg _ _ _ (by linarith : 0 ≤ B)) dist_nonneg)).mpr
  intro k
  rw [Real.dist_eq]
  change |e.equivFun (lieBCH s (e.equivFun.symm v) g.coord) k -
    e.equivFun (lieBCH s (e.equivFun.symm w) g.coord) k| ≤ _
  simp only [Basis.equivFun_apply]
  apply lieBCH_right_coordinates_sub_bound e c hstructure hc _ _ _ hB dist_nonneg
  · simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hv
  · simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hw
  · exact hg
  · intro i
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply, Real.dist_eq] using
      dist_le_pi_dist v w i

theorem norm_fderiv_rightTranslate_zero_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    ‖fderiv ℝ (rightTranslate e g) 0‖ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B := by
  apply norm_fderiv_le_of_lipschitzOn ℝ ?_ (lipschitzOn_rightTranslate_box e c hstructure hc g B hB hg)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ι → ℝ) (by linarith : 0 < B))
  intro v hv i
  have hi := norm_le_pi_norm v i
  rw [Metric.mem_ball, dist_zero_right] at hv
  exact (show |v i| ≤ ‖v‖ by simpa only [Real.norm_eq_abs] using hi).trans hv.le

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualIdealSteps
namespace OAI


namespace Erdos3.NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
  (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

include hT in
theorem dualLinearLift_logDerivative (z : DualGroup hL)
    (hz : dualTangentLinear z.coord ∈ I) :
    T (dualLogDerivative z) =
      dualLogDerivative (hnil := hM) (⟨dualLinearLift B T z.coord⟩ : DualGroup hM) := by
  have hc : -dualConstantLie (dualBaseLinear z.coord) ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (-dualConstantLie (dualBaseLinear z.coord)) ∈ I
    rw [map_neg, dualTangentLinear_constant, neg_zero]
    exact I.zero_mem
  have hh := dualLinearLift_lieBCH I B T hT s hz hc
  have ht := congrArg dualTangentLinear hh
  rw [dualLinearLift_tangent, map_neg, dualLinearLift_constant] at ht
  change T (dualLogDerivative z) =
    dualTangentLinear (lieBCH s (dualLinearLift B T z.coord)
      (-dualConstantLie (dualBaseLinear (dualLinearLift B T z.coord))))
  rw [dualLinearLift_base]
  exact ht

include hT in
theorem dualLinearLift_logDerivative_eq (z : DualGroup hL)
    (hz : dualTangentLinear z.coord ∈ I) (z' : DualGroup hM)
    (he : dualLinearLift B T z.coord = z'.coord) :
    T (dualLogDerivative z) = dualLogDerivative (hnil := hM) z' := by
  have hg : (⟨dualLinearLift B T z.coord⟩ : DualGroup hM) = z' := NilpotentLieBCHGroup.ext he
  exact (dualLinearLift_logDerivative hM I B T hT z hz).trans
    (congrArg (dualLogDerivative (hnil := hM)) hg)

end Erdos3.NilpotentLieBCHGroup


namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_mem_of_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (z : DualGroup hnil)
    (hb : dualBaseLinear z.coord ∈ U) (ht : dualTangentLinear z.coord ∈ V) :
    dualLogDerivative z ∈ V := by
  let S := dualInvariantSubalgebra U V hUV
  have hz : z.coord ∈ S := ⟨hb, ht⟩
  have hc : dualConstantLie (dualBaseLinear z.coord) ∈ S := by
    change dualBaseLinear (dualConstantLie (dualBaseLinear z.coord)) ∈ U ∧
      dualTangentLinear (dualConstantLie (dualBaseLinear z.coord)) ∈ V
    simpa only [dualBaseLinear_constant, dualTangentLinear_constant] using And.intro hb V.zero_mem
  exact (lieBCH_mem S s hz (S.neg_mem hc)).2

end NilpotentLieBCHGroup
end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_lie [Fintype σ] (h : σ → ℚ) (p q : VectorPolynomial σ ℚ L) :
    directionalDerivative h ⁅p, q⁆ =
      ⁅directionalDerivative h p, q⁆ + ⁅p, directionalDerivative h q⁆ := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    pderiv_lie, smul_add, Finset.sum_add_distrib,
    sum_lie (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    lie_sum (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    smul_lie (R := ℚ) (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L),
    lie_smul (R := ℚ) (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L)]

theorem directionalDerivative_direction_add [Fintype σ]
    (h k : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative (h + k) p = directionalDerivative h p + directionalDerivative k p := by
  simp only [directionalDerivative, Pi.add_apply, add_smul, Finset.sum_add_distrib,
    LinearMap.add_apply]

theorem directionalDerivative_direction_smul [Fintype σ]
    (r : ℚ) (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative (r • h) p = r • directionalDerivative h p := by
  simp only [directionalDerivative, Pi.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, LinearMap.smul_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorAlgebraicMajorDecomposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R T : Type*} [CommRing R] [CommRing T]

theorem polynomialTranslate_eval_ring (h : B → R) (P : MvPolynomial B R) (b : B → R) :
    eval b (polynomialTranslate h P) = eval (fun i => b i + h i) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, polynomialTranslate_X, map_add, eval_X, eval_C]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationActionCompatibility
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
variable {σ R : Type*} [CommRing R]

namespace PolynomialTranslationGroupOver

theorem action_inverse_X_inl_eval (g : PolynomialTranslationGroupOver R σ)
    (β : σ → R) (y : R) (i : σ) :
    eval (Sum.elim β (fun _ : Unit => y))
      ((actionMonoidHom g).symm (X (Sum.inl i))) = β i - g.base i := by
  have he : (actionMonoidHom g).symm = actionMonoidHom g⁻¹ := (map_inv actionMonoidHom g).symm
  rw [he]
  change eval _ (actionHom g⁻¹ (X (Sum.inl i))) = _
  rw [actionHom_X_inl]
  simp [sub_eq_add_neg]

theorem action_inverse_X_inr_eval (g : PolynomialTranslationGroupOver R σ)
    (β : σ → R) (y : R) :
    eval (Sum.elim β (fun _ : Unit => y))
      ((actionMonoidHom g).symm (X (Sum.inr ()))) = y - eval β g.polynomial := by
  have he : (actionMonoidHom g).symm = actionMonoidHom g⁻¹ := (map_inv actionMonoidHom g).symm
  rw [he]
  change eval _ (actionHom g⁻¹ (X (Sum.inr ()))) = _
  rw [actionHom_X_inr]
  simp only [base_inv,polynomial_inv,map_neg,polynomialTranslate_comp_ring,
    neg_add_cancel,polynomialTranslate_zero_ring]
  simp [MvPolynomial.eval_rename,sub_eq_add_neg]

end PolynomialTranslationGroupOver
end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem integerCoefficientPolynomials_translate (b : σ → ℚ)
    (hb : ∀ i, ∃ z : ℤ, b i = (z : ℚ))
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    polynomialTranslate b P ∈ integerCoefficientPolynomials σ := by
  apply integerPolynomialHom_preserves (polynomialTranslate b) _ hP
  intro i
  rw [polynomialTranslate_X]
  exact (integerCoefficientPolynomials σ).add_mem
    (integerCoefficientPolynomials_X i)
    ((integerCoefficientPolynomials_C_iff (b i)).mpr (hb i))

theorem integerCoefficientPolynomials_translate_iff (b : σ → ℚ)
    (hb : ∀ i, ∃ z : ℤ, b i = (z : ℚ)) (P : MvPolynomial σ ℚ) :
    polynomialTranslate b P ∈ integerCoefficientPolynomials σ ↔
      P ∈ integerCoefficientPolynomials σ := by
  constructor
  · intro hP
    have hneg : ∀ i, ∃ z : ℤ, (-b) i = (z : ℚ) := by
      intro i
      obtain ⟨z, hz⟩ := hb i
      exact ⟨-z, by simp [hz]⟩
    have h := integerCoefficientPolynomials_translate (-b) hneg hP
    simpa only [polynomialTranslate_comp_ring, neg_add_cancel,
      polynomialTranslate_zero_ring] using h
  · exact integerCoefficientPolynomials_translate b hb

end Erdos3


namespace Erdos3.PolynomialTranslationGroupOver

open _root_.MvPolynomial
variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem map_actionHom (φ : R →+* S) (g : PolynomialTranslationGroupOver R σ)
    (P : MvPolynomial (σ ⊕ Unit) R) :
    MvPolynomial.map φ (actionHom g P) =
      actionHom (PolynomialTranslationGroupOver.map φ g) (MvPolynomial.map φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP =>
      simp only [map_mul,hP,MvPolynomial.map_X]
      congr 1
      cases i with
      | inl i => simp
      | inr u =>
          simp only [actionHom_X_inr,map_add,map_X,MvPolynomial.map_rename,
            polynomialTranslate_map_ring,map_polynomial]
          rfl

theorem rationalEquiv_action (g : PolynomialTranslationGroup σ) :
    actionMonoidHom (rationalEquiv g) = PolynomialTranslationGroup.actionMonoidHom g := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  cases i <;> rfl

end Erdos3.PolynomialTranslationGroupOver

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {B U : Type*}

theorem translationPhaseArgument_mul (D₀ : MvPolynomial B ℝ)
    (g γ : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) :
    translationPhaseArgument D₀ (g * γ) (β + γ.base) =
      translationPhaseArgument D₀ g β + eval (β + γ.base) γ.polynomial := by
  simp only [translationPhaseArgument, PolynomialTranslationGroupOver.polynomial_mul,
    PolynomialTranslationGroupOver.base_mul, map_add, polynomialTranslate_eval_ring]
  have h₁ : (fun i => (β + γ.base) i + (-γ.base) i) = β := by ext i; simp
  have h₂ : β + γ.base - (g.base + γ.base) = β - g.base := by abel
  rw [h₁, h₂]
  ring

theorem translationPhaseArgument_integer_character
    (χ : AddChar ℝ ℂ) (hχ : ∀ z : ℤ, χ (z : ℝ) = 1)
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B)
    (z β : B → ℤ) (Q : MvPolynomial B ℤ) :
    χ (translationPhaseArgument D₀
      (g * ⟨fun i => (z i : ℝ), MvPolynomial.map (Int.castRingHom ℝ) Q⟩)
      (fun i => ((β i + z i : ℤ) : ℝ))) =
        χ (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) := by
  have hβ : (fun i => ((β i + z i : ℤ) : ℝ)) =
      (fun i => (β i : ℝ)) + (fun i => (z i : ℝ)) := by ext i; simp
  rw [hβ, translationPhaseArgument_mul, χ.map_add_eq_mul]
  have hQ : eval ((fun i => (β i : ℝ)) + (fun i => (z i : ℝ)))
      (MvPolynomial.map (Int.castRingHom ℝ) Q) = (eval (β + z) Q : ℝ) := by
    change eval (fun i => (β i : ℝ) + (z i : ℝ)) _ = _
    simpa only [Pi.add_apply, Int.cast_add] using eval_integer_polynomial_real Q (β + z)
  rw [hQ, hχ, mul_one]

theorem translationPhaseArgument_fourier_integer
    (D₀ : MvPolynomial B ℝ) (g : PolynomialTranslationGroupOver ℝ B)
    (z β : B → ℤ) (Q : MvPolynomial B ℤ) :
    (Real.fourierChar (translationPhaseArgument D₀
      (g * ⟨fun i => (z i : ℝ), MvPolynomial.map (Int.castRingHom ℝ) Q⟩)
      (fun i => ((β i + z i : ℤ) : ℝ))) : ℂ) =
        (Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ))) : ℂ) := by
  apply translationPhaseArgument_integer_character
    (Circle.coeHom.compAddChar Real.fourierChar) ?_
  intro z
  change (Circle.exp (2 * Real.pi * (z : ℝ)) : ℂ) = 1
  rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
  simp

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {B : Type*}

theorem translationPhaseArgument_left_increment
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) :
    translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β =
      eval (β - g.base) z.polynomial +
        (eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀) := by
  simp only [translationPhaseArgument, PolynomialTranslationGroupOver.polynomial_mul,
    PolynomialTranslationGroupOver.base_mul, map_add, polynomialTranslate_eval_ring]
  have h₁ : (fun i => β i + (-g.base) i) = β - g.base := by ext i; simp [sub_eq_add_neg]
  have h₂ : β - (z.base + g.base) = β - g.base - z.base := by abel
  rw [h₁, h₂]
  ring

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationTopDegree
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {X R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_translate_mem (U : Submodule R V) (a : X → R)
    (p : VectorPolynomial X R V) (hp : ∀ d, coefficients p d ∈ U) (d : X →₀ ℕ) :
    coefficients (translate a p) d ∈ U := by
  rw [coefficients_translate]
  exact Submodule.sum_mem U (fun b _ => U.smul_mem _ (hp b))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem norm_mfderiv_mapReal_le {C : ℝ}
    (hA : ∀ w, coordinateL2Norm (basisCoordinateMap e f φ.toLinearMap w) ≤ C * coordinateL2Norm w)
    (g : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    letI := rightRiemannianBundle (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hM) f
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hM := hM) φ) g v‖ ≤ C * ‖v‖ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  intro v
  have hv := mfderiv_mapReal_coordinates (hM := hM) e f φ g v
  have hc := congrArg (fun T : (ι → ℝ) →L[ℝ] (κ → ℝ) => T v)
    (rightVelocity_mapReal (hM := hM) e f φ g)
  have hvel := (congrArg (fun w : κ → ℝ => rightVelocity f (mapReal (hM := hM) φ g) w) hv).trans hc
  calc
    ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hM := hM) φ) g v‖ =
        coordinateL2Norm (rightVelocity f (mapReal (hM := hM) φ g)
          (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hM := hM) φ) g v)) :=
      norm_tangent_eq_coordinateL2Norm f _ _
    _ = coordinateL2Norm (basisCoordinateMap e f φ.toLinearMap (rightVelocity e g v)) :=
      congrArg coordinateL2Norm hvel
    _ ≤ C * coordinateL2Norm (rightVelocity e g v) := hA _
    _ = C * ‖v‖ := congrArg (C * ·) (norm_tangent_eq_coordinateL2Norm e g v).symm

theorem lipschitz_mapReal_of_coordinate_bound {C : ℝ≥0} (hC : 0 < C)
    (hA : ∀ w, coordinateL2Norm (basisCoordinateMap e f φ.toLinearMap w) ≤ C * coordinateL2Norm w) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith C (mapReal (hnil := hnil) (hM := hM) φ) := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  apply riemannianEDist_le_mul_of_mfderiv_bound hC (contMDiff_mapReal e f φ 1)
  intro g v
  have h := ENNReal.ofReal_le_ofReal (norm_mfderiv_mapReal_le (hM := hM) e f φ hA g v)
  simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ofReal_norm,
    ENNReal.ofReal_coe_nnreal] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem coordinate_norm_le_rightVelocity (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) (v : ι → ℝ) :
    ‖v‖ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * coordinateL2Norm (rightVelocity e g v) := by
  have h := congrArg (fun A : (ι → ℝ) →L[ℝ] (ι → ℝ) => A v)
    (rightTranslate_fderiv_zero_rightVelocity e g)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  calc
    ‖v‖ = ‖fderiv ℝ (rightTranslate e g) 0 (rightVelocity e g v)‖ := congrArg norm h.symm
    _ ≤ ‖fderiv ℝ (rightTranslate e g) 0‖ * ‖rightVelocity e g v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * coordinateL2Norm (rightVelocity e g v) :=
      mul_le_mul (norm_fderiv_rightTranslate_zero_le e c hstructure hc g B hB hg)
        (norm_le_coordinateL2Norm _) (norm_nonneg _) (bchBoxCoordinateBound_nonneg _ _ _ (by linarith))

theorem norm_mfderiv_basisHomeomorph_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖tangentModelVector (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v)‖ ≤
        bchBoxCoordinateBound s (Fintype.card ι) H B * ‖v‖ := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  intro v
  have hcoords : tangentModelVector
      (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v) = tangentModelVector v :=
    mfderiv_basisHomeomorph_coordinates e g v
  apply (congrArg norm hcoords).le.trans
  exact (coordinate_norm_le_rightVelocity e c hstructure hc g B hB hg v).trans_eq
    (congrArg (bchBoxCoordinateBound s (Fintype.card ι) H B * ·)
      (norm_tangent_eq_coordinateL2Norm e g v).symm)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

theorem bchLogMetricConstant_pos (s d H : ℕ) (B : ℝ≥0) : 0 < bchLogMetricConstant s d H B := by
  change 0 < bchBoxCoordinateBound s d H B + 1
  have := bchBoxCoordinateBound_nonneg s d H B.coe_nonneg
  linarith

namespace NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem edist_coordinates_le_of_near_one (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H B
    (C : ℝ≥0∞) * edist 1 g < B →
      edist (basisHomeomorph (hnil := hnil) e 1) (basisHomeomorph e g) ≤ C * edist 1 g := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H B
  dsimp only
  intro hnear
  apply coordinate_edist_le_of_riemannianEDist_lt (bchLogMetricConstant_pos s (Fintype.card ι) H B)
    (contMDiff_basisHomeomorph e 1) 1 g ?_ hnear
  intro z hz v
  have hznorm : ‖basisHomeomorph e z‖ ≤ B := by
    simpa only [Metric.mem_closedBall, basisHomeomorph_apply, coord_one, map_zero,
      dist_zero_right] using hz
  have hzbox (i) : |e.repr z.coord i| ≤ B := by
    have hi := (norm_le_pi_norm (basisHomeomorph e z) i).trans hznorm
    simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs] using hi
  have hv := norm_mfderiv_basisHomeomorph_le e c hstructure hc z B hB hzbox v
  have hAC : bchBoxCoordinateBound s (Fintype.card ι) H B ≤ (C : ℝ) := by
    change bchBoxCoordinateBound s (Fintype.card ι) H B ≤ bchBoxCoordinateBound s (Fintype.card ι) H B + 1
    linarith
  have hv' := hv.trans (mul_le_mul_of_nonneg_right hAC (norm_nonneg v))
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ofReal_norm, ENNReal.ofReal_coe_nnreal] using
    ENNReal.ofReal_le_ofReal hv'

theorem norm_coordinates_le_of_near_one (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H B
    (C : ℝ) * dist 1 g < B → ‖basisHomeomorph e g‖ ≤ C * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H B
  dsimp only
  intro hnear
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB
  have hnearE : (C : ℝ≥0∞) * edist 1 g < B := by
    have h : ENNReal.ofReal ((C : ℝ) * dist 1 g) < ENNReal.ofReal (B : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff hBpos).mpr hnear
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h
    simpa only [edist_dist] using h
  have h := edist_coordinates_le_of_near_one e c hstructure hc B hB g hnearE
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top 1 g)) h
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    basisHomeomorph_apply, coord_one, map_zero, dist_zero_left,
    ENNReal.toReal_ofReal (norm_nonneg _)] using hr

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem lipschitz_mapReal_of_entry_bound (B : ℝ≥0)
    (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B)
      (mapReal (hnil := hnil) (hM := hM) φ) := by
  apply lipschitz_mapReal_of_coordinate_bound e f φ (coordinateLipschitzBound_pos _ _ _)
  intro w
  exact basisCoordinateMap_L2_bound e f φ.toLinearMap B B.coe_nonneg hφ w

variable (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
  (hΛ : IsClosed (Λ : Set (NilpotentLieBCHGroup M t hM)))
  (hmap : Γ ≤ Λ.comap (mapReal φ))

theorem lipschitz_quotient_mapReal_of_entry_bound (B : ℝ≥0)
    (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) :
    letI := quotientMetricSpace e Γ hΓ
    letI := quotientMetricSpace f Λ hΛ
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B)
      (cosetMap Γ Λ (mapReal φ) hmap) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let : FiniteDimensional ℝ M := f.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hM) f
  exact lipschitz_cosetMap Γ Λ hΓ hΛ (mapReal φ) hmap
    (lipschitz_mapReal_of_entry_bound e f φ B hφ)

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)

variable (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (Λ : Subgroup (NilpotentLieBCHGroup M t hM)) (hφ : Γ ≤ Λ.comap (mapOfSteps φ))

theorem lipschitz_realificationMap_quotient (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (H : ℕ) (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := realificationQuotientMetricSpace e Γ l hl hΓ
    letI := realificationQuotientMetricSpace f Λ m hm hΛ
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H)
      (cosetMap (Γ.map realificationHom) (Λ.map realificationHom)
        (realificationMap (hnil := hnil) (hM := hM) φ)
        (realificationMap_subgroup φ Γ Λ hφ)) := by
  apply lipschitz_quotient_mapReal_of_entry_bound (e.baseChange ℝ) (f.baseChange ℝ)
    (realificationLieHom φ) (Γ.map realificationHom) (Λ.map realificationHom)
    (realification_subgroup_closed_discrete e Γ l hl hΓ).1
    (realification_subgroup_closed_discrete f Λ m hm hΛ).1
    (realificationMap_subgroup φ Γ Λ hφ) H
  intro k i
  rw [realificationLieHom_basis]
  exact (hH k i).abs_real_le

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3

open Module

namespace NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realBCHLine_zero (v : L) : realBCHLine (hnil := hnil) v 0 = 1 := by
  apply ext
  exact zero_smul ℝ v

theorem realBCHLine_one (v : L) : realBCHLine (hnil := hnil) v 1 = ⟨v⟩ := by
  apply ext
  exact one_smul ℝ v

theorem realBCHLine_add (v : L) (r t : ℝ) :
    realBCHLine (hnil := hnil) v (r + t) = realBCHLine v r * realBCHLine v t := by
  apply ext
  change (r + t) • v = lieBCH s (r • v) (t • v)
  rw [lieBCH_eq_add_of_lie_eq_zero hnil (by simp [smul_lie, lie_smul]), add_smul]

theorem realBCHLine_commute (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (r : ℝ) (g : NilpotentLieBCHGroup L s hnil) : Commute (realBCHLine v r) g := by
  apply commute_of_lie_eq_zero
  change ⁅r • v, g.coord⁆ = 0
  rw [smul_lie, hv, smul_zero]

variable [IsScalarTower ℚ ℝ L] {ι : Type*} [Fintype ι] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]

theorem realBCHLine_dist_one_le (e : Basis ι ℝ L) (v : L) (r : ℝ) :
    letI := rightMetricSpace (hnil := hnil) e
    dist (realBCHLine (hnil := hnil) v r) 1 ≤ |r| * coordinateL2Norm (e.equivFun v) := by
  let := rightMetricSpace (hnil := hnil) e
  rw [dist_comm]
  apply (dist_one_le_coordinateL2Norm e (realBCHLine v r)).trans_eq
  change coordinateL2Norm (e.equivFun (r • v)) = _
  rw [map_smul, coordinateL2Norm_smul]

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearFactorialIntegrality
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearLog_apply (e : WeightedLoweringAut w R) (P : MvPolynomial σ R) :
    (polynomialShearLog e).val P = polynomialShearLogValue e P := rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem polynomialShear_factorial_log_integral (s : ℕ) (hw : ∀ i, w i ≤ s)
    (e : WeightedLoweringAut w ℚ) (he : e ∈ integerWeightedLoweringSubgroup w) (i : σ) :
    (s.factorial : ℚ) • (polynomialShearLog e).val (X i) ∈ integerCoefficientPolynomials σ := by
  rw [polynomialShearLog_apply, polynomialShearLogValue_eq_sum _
    (weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)), Finset.smul_sum]
  apply (integerCoefficientPolynomials σ).sum_mem
  intro k hk
  rw [smul_smul]
  exact integerCoefficientPolynomials_rat_smul
    (factorial_log_scalar_integer s k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    (integerWeightedLowering_difference_pow e he (integerCoefficientPolynomials_X i) k)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

omit [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L] in
theorem centralBCHFlow_period (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    realBCHLine (hnil := hnil) v 1 • x = x := by
  apply central_smul_eq_self_of_mem Γ
  · simpa only [realBCHLine_one] using hperiod
  · exact realBCHLine_commute v hv 1

theorem centralBCHFlow_isometry (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0) (r : ℝ) :
    letI := quotientMetricSpace e Γ hΓ
    Isometry (fun x : NilpotentLieBCHGroup L s hnil ⧸ Γ => realBCHLine (hnil := hnil) v r • x) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact isometry_quotient_central_smul Γ hΓ (realBCHLine (hnil := hnil) v r) (realBCHLine_commute v hv r)

theorem centralBCHFlow_displacement (v : L) (r : ℝ) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    dist (realBCHLine (hnil := hnil) v r • x) x ≤ coordinateL2Norm (e.equivFun v) * |r| := by
  let := rightMetricSpace (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  have h := (quotientMetricSpace_lipschitz_orbit e Γ hΓ x).dist_le_mul (realBCHLine (hnil := hnil) v r) 1
  have hbound := realBCHLine_dist_one_le (hnil := hnil) e v r
  simp only [one_smul, NNReal.coe_one, one_mul] at h
  exact h.trans (hbound.trans_eq (mul_comm _ _))

noncomputable def centralBCHCircleAction (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    CircleFourier.IsometricCircleAction (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let := quotientMetricSpace e Γ hΓ
  exact CircleFourier.isometricCircleActionOfFlow (fun r x => realBCHLine (hnil := hnil) v r • x)
    (fun x => by rw [realBCHLine_zero, one_smul])
    (fun r t x => by rw [realBCHLine_add, mul_smul])
    (centralBCHFlow_period Γ v hv hperiod)
    (centralBCHFlow_isometry e Γ hΓ v hv)
    ⟨coordinateL2Norm (e.equivFun v), coordinateL2Norm_nonneg _⟩
    (centralBCHFlow_displacement e Γ hΓ v)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedBinomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedBCHToOrbit (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* F.PolynomialOrbit w :=
  (NilpotentLieBCHGroup.map (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := VectorPolynomial.lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot)
    (F.adaptedLieSubalgebra w).incl).codRestrict _ (fun g => g.coord.property)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialAffineDegree
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

theorem degreeLE_finset_sum {I A R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (weight : I → ℕ) (h : ℕ) (s : Finset A) (p : A → VectorPolynomial I R W)
    (hp : ∀ a ∈ s, DegreeLE weight h (p a)) : DegreeLE weight h (∑ a ∈ s, p a) := by
  intro d hd
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun a ha => hp a ha d hd)

theorem degreeLE_tmul_totalDegree {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (P : MvPolynomial I R) (w : W) {h : ℕ} (hP : P.totalDegree ≤ h) :
    DegreeLE (1 : I → ℕ) h (P ⊗ₜ[R] w) := by
  intro d hd
  have hsum : h < ∑ i ∈ d.support, d i := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_def, smul_eq_mul, mul_one] using hd
  rw [coefficients_tmul, MvPolynomial.coeff_eq_zero_of_totalDegree_lt (hP.trans_lt hsum), zero_smul]

theorem degreeLE_substitute_affine {I K R W : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] {h : ℕ}
    (f : I → MvPolynomial K R) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : VectorPolynomial I R W) (hp : DegreeLE (1 : I → ℕ) h p) :
    DegreeLE (1 : K → ℕ) h (substitute f p) := by
  classical
  rw [← sum_monomial_coefficients p, Finsupp.sum, map_sum]
  apply degreeLE_finset_sum
  intro d hd
  rw [monomial, substitute_tmul]
  apply degreeLE_tmul_totalDegree
  have hb : d.sum (fun _ n => n) ≤ h := by
    simpa only [Finsupp.weight_apply, Pi.one_def, smul_eq_mul, mul_one] using
      (degreeLE_iff (1 : I → ℕ) h p).mp hp d hd
  simpa only [Nat.mul_one] using aeval_polynomial_totalDegree_le (MvPolynomial.monomial d (1 : R)) f
    ((MvPolynomial.totalDegree_monomial_le d 1).trans hb) hf

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogenizedModeFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem homogeneous_degreeLE {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {h : ℕ} {p : VectorPolynomial I R W} (hp : Homogeneous h p) : DegreeLE (1 : I → ℕ) h p := by
  apply (degreeLE_iff _ _ _).mpr
  intro d hd
  have he := homogeneous_support_degree hp hd
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using he.le

theorem dehomogenize_degreeLE {I R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {h : ℕ} {p : VectorPolynomial (Option I) R W} (hp : Homogeneous h p) :
    DegreeLE (1 : I → ℕ) h (substitute dehomogenizingSubstitution p) := by
  classical
  apply degreeLE_substitute_affine _ _ p (homogeneous_degreeLE hp)
  intro i
  cases i with
  | none => simp [dehomogenizingSubstitution]
  | some i =>
    change (MvPolynomial.monomial (Finsupp.single i 1) (1 : R)).totalDegree ≤ 1
    simpa using MvPolynomial.totalDegree_monomial_le (Finsupp.single i 1) (1 : R)

theorem siteEvaluation_homogenize {I S R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (site : S → I → R) (h : ℕ) (p : VectorPolynomial I R W) :
    siteEvaluation (fun s (i : Option I) => i.elim 1 (site s)) (homogenize h p) = siteEvaluation site p := by
  funext s
  exact eval_homogenize h p (site s)

theorem siteEvaluation_dehomogenize {I S R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (site : S → I → R) (p : VectorPolynomial (Option I) R W) :
    siteEvaluation site (substitute dehomogenizingSubstitution p) =
      siteEvaluation (fun s (i : Option I) => i.elim 1 (site s)) p := by
  funext s
  change eval (site s) (substitute dehomogenizingSubstitution p) = _
  rw [eval_substitute]
  apply congrArg (fun x => eval x p)
  funext i
  cases i <;> simp [dehomogenizingSubstitution]

theorem homogeneous_site_factorization_iff {I S R W : Type*}
    [CommRing R] [AddCommGroup W] [Module R W]
    (h : ℕ) (site : S → I → R) (Λ : VectorPolynomial I R W →ₗ[R] R)
    (M : (S → W) →ₗ[R] R) :
    (∀ p, Homogeneous h p → Λ (substitute dehomogenizingSubstitution p) =
      M (siteEvaluation (fun s (i : Option I) => i.elim 1 (site s)) p)) ↔
    (∀ p, DegreeLE (1 : I → ℕ) h p → Λ p = M (siteEvaluation site p)) := by
  constructor
  · intro hf p hp
    have he := hf (homogenize h p) (homogenize_homogeneous h p hp)
    rwa [dehomogenize_homogenize, siteEvaluation_homogenize] at he
  · intro hf p hp
    have he := hf (substitute dehomogenizingSubstitution p) (dehomogenize_degreeLE hp)
    rwa [siteEvaluation_dehomogenize] at he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineModeLift {K W : Type*} [AddCommGroup W] [Module ℝ W]
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) : VectorPolynomial (Option K) ℝ W →ₗ[ℝ] ℝ :=
  Λ.comp (substitute dehomogenizingSubstitution)

theorem affineModeLift_substitute {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (b : Option K → I → ℝ) :
    affineModeLift Λ (substitute (fun j => rowPolynomial (fun k => b k j)) p) =
      Λ (substitute (affineParameterSubstitution b) p) := by
  rw [affineModeLift, LinearMap.comp_apply, substitute_comp]
  simp only [dehomogenize_rowPolynomial]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem affineModeLift_comp_map {K V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) :
    affineModeLift (L.comp (map f)) = (affineModeLift L).comp (map f) := by
  apply LinearMap.ext
  intro q
  simp only [affineModeLift, LinearMap.comp_apply, map_substitute]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LayeredFourierCharacter
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

noncomputable def layeredCoefficientCharacter {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) : ℂ :=
  character (((∑ j, L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j))) : ℝ) :
    CircleFourier.Circle)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedCoefficientExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem degreeLE_monomial_of_degree_le {K W : Type*} [AddCommGroup W] [Module ℝ W]
    {d : K →₀ ℕ} {h : ℕ} (hd : d.degree ≤ h) (w : W) :
    DegreeLE (1 : K → ℕ) h (monomial (R := ℝ) d w) := by
  classical
  intro e he
  rw [coefficients_monomial]
  by_cases hed : e = d
  · subst e
    have hh : h < d.degree := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using he
    exact False.elim ((not_lt_of_ge hd) hh)
  · simp [Ne.symm hed]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem sum_bounded_monomial_coefficients {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ}
    (p : VectorPolynomial K ℝ W) (hp : DegreeLE (1 : K → ℕ) h p) :
    (∑ d : BoundedCoefficientExponent K h, monomial d.val (coefficients p d.val)) = p := by
  apply coefficients.injective
  ext e
  simp only [map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  by_cases he : e.degree ≤ h
  · rw [Finset.sum_eq_single (⟨e, he⟩ : BoundedCoefficientExponent K h)]
    · simp
    · intro d _ hd
      have hde : d.val ≠ e := fun h => hd (Subtype.ext h)
      simp [hde]
    · simp
  · have hz : coefficients p e = 0 := hp e (by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using lt_of_not_ge he)
    rw [hz]
    apply Finset.sum_eq_zero
    intro d _
    have hde : d.val ≠ e := fun h => he (h ▸ d.property)
    simp [hde]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedArrayPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def boundedArrayPolynomial {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W) :
    VectorPolynomial K ℝ W := ∑ d, monomial d.val (x d)

theorem boundedArrayPolynomial_degreeLE {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W) :
    DegreeLE (1 : K → ℕ) h (boundedArrayPolynomial h x) := by
  intro e he
  rw [boundedArrayPolynomial, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro d _
  exact degreeLE_monomial_of_degree_le d.property (x d) e he

theorem boundedArrayPolynomial_reconstruct {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ} (p : VectorPolynomial K ℝ W)
    (hp : DegreeLE (1 : K → ℕ) h p) :
    boundedArrayPolynomial h (fun d => coefficients p d.val) = p :=
  sum_bounded_monomial_coefficients p hp

theorem coefficientFunctional_boundedArrayPolynomial {K J : Type*} [Fintype K] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (frequency : (K →₀ ℕ) → J → ℝ)
    (x : BoundedCoefficientExponent K h → U) :
    coefficientFunctional frequency (map U.subtype (boundedArrayPolynomial h x)) =
      subspaceArrayFunctional U (fun d a => frequency d.val a) x := by
  simp only [boundedArrayPolynomial, map_sum, map_monomial, coefficientFunctional_monomial]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem siteEvaluation_boundedArrayPolynomial {K S W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (site : S → K → ℤ)
    (x : BoundedCoefficientExponent K h → W) :
    siteEvaluation (fun s k => (site s k : ℝ)) (boundedArrayPolynomial h x) =
      matrixModuleAction (fun s d => (boundedSiteMatrix h site s d : ℝ)) x := by
  funext s
  change eval (fun k => (site s k : ℝ)) (boundedArrayPolynomial h x) =
    ∑ d : BoundedCoefficientExponent K h, (boundedSiteMatrix h site s d : ℝ) • x d
  simp only [boundedArrayPolynomial, map_sum, eval_monomial,
    boundedSiteMatrix, Finsupp.prod, Int.cast_prod, Int.cast_pow]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedHomogeneousFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem homogeneous_factorization_to_bounded_site {K S J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (site : S → K → ℝ)
    (frequency : (K →₀ ℕ) → J → ℝ) (M : (S → U) →ₗ[ℝ] ℝ)
    (hf : ∀ p : VectorPolynomial (Option K) ℝ U, Homogeneous h p →
      affineModeLift (coefficientFunctional frequency) (map U.subtype p) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) p)) :
    ∀ p : VectorPolynomial K ℝ U, DegreeLE (1 : K → ℕ) h p →
      coefficientFunctional frequency (map U.subtype p) = M (siteEvaluation site p) := by
  let L := (coefficientFunctional frequency).comp (map U.subtype)
  have hlift : ∀ p, Homogeneous h p → affineModeLift L p =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) p) := by
    simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply] using hf
  exact (homogeneous_site_factorization_iff h site L M).mp hlift

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareLattice (Γ : Subgroup F.Group) : Subgroup F.squareFiltration.Group :=
  Γ.comap F.squareFstHom ⊓ Γ.comap F.squareSndHom

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialIdeals
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem adaptedConstant_mem_shiftedPolynomialIdeal (k : ℕ) {x : L} (hx : x ∈ F.layer k) :
    F.adaptedConstant w x ∈ F.shiftedPolynomialIdeal w k := by
  apply F.monomial_mem_shiftedAdaptedSubmodule
  simpa only [map_zero, Nat.zero_add] using hx

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def normalizedShiftLog (s : ℕ) (h : σ → ℚ) (a b : L)
    (p : VectorPolynomial σ ℚ L) : VectorPolynomial σ ℚ L :=
  lieBCH s (monomial 0 a) (lieBCH s (translate h p) (monomial 0 b))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

theorem adaptedBasis_weight_le_step (i : ι) : ω i ≤ s := by
  by_contra hi
  have hb : b i ∈ F.layer (s + 1) := by
    rw [hlayers]
    exact Submodule.subset_span ⟨i, (show s + 1 ≤ ω i by omega), rfl⟩
  rw [F.terminal, Submodule.mem_bot] at hb
  exact b.ne_zero i hb

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

abbrev AdaptedBasisIndex {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}

section Dimension

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) (s : ℕ)
  (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω

theorem adaptedBasisIndex_degree_le (z : AdaptedBasisIndex w ω) :
    z.val.1.sum (fun _ n => n) ≤ s := by
  apply le_trans ?_ (z.property.trans (hω z.val.2))
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right _ (hw i))

noncomputable def adaptedBasisCode (z : AdaptedBasisIndex w ω) :
    (Σ n : Fin (s + 1), Fin n.val → σ) × ι :=
  (⟨⟨z.val.1.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le (adaptedBasisIndex_degree_le w ω s hw hω z)⟩,
    z.val.1.toMultiset.toList.get⟩, z.val.2)

theorem adaptedBasisCode_injective : Function.Injective (adaptedBasisCode w ω s hw hω) := by
  classical
  intro z u h
  have hi := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => t.2) h
  change z.val.2 = u.val.2 at hi
  have hl := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => List.ofFn t.1.2) h
  change List.ofFn z.val.1.toMultiset.toList.get = List.ofFn u.val.1.toMultiset.toList.get at hl
  rw [List.ofFn_get, List.ofFn_get] at hl
  have hm := congrArg (fun t : List σ => (t : Multiset σ)) hl
  rw [Multiset.coe_toList, Multiset.coe_toList] at hm
  apply Subtype.ext
  apply Prod.ext _ hi
  ext i
  have hh := congrArg (fun t : Multiset σ => t.count i) hm
  simpa only [Finsupp.count_toMultiset] using hh

variable [Fintype σ] [Fintype ι]

theorem adaptedBasisIndex_finite : Finite (AdaptedBasisIndex w ω) :=
  Finite.of_injective (adaptedBasisCode w ω s hw hω) (adaptedBasisCode_injective w ω s hw hω)

@[instance_reducible] noncomputable def adaptedBasisIndexFintype : Fintype (AdaptedBasisIndex w ω) := by
  let : Finite (AdaptedBasisIndex w ω) := adaptedBasisIndex_finite w ω s hw hω
  exact Fintype.ofFinite _

end Dimension
end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareGradedRelative
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def associatedGradedFiltration : NilpotentLieFiltration F.AssociatedGraded s :=
  F.polynomialSymbolFiltration (fun _ : Unit => 1)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedPieceMap_coordinate (j : ℕ) (v : F.layer j) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.associatedGradedPieceMap j v) i =
      if j = ω i then b.repr (v : L) i else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedPieceMap_apply,
    F.polynomialSymbolBasis_repr_map]
  simp only [F.gradedMonomialLinear_coe, coefficients_monomial]
  by_cases h : j = ω i
  · simp [h]
  · have h' : unitMonomial j ≠ unitMonomial (ω i) := fun he => h (unitMonomial_injective he)
    simp [h, h']

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module

def SymbolRationalGrid {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (l : ℕ) (g : F.RealPolynomialSymbolGroup w) : Prop :=
  (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z)
    ∈ realDenominatorGrid l

end NilpotentLieFiltration
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
  (w : σ → ℕ)

include hlayers

theorem realSymbolOfPolynomial_eq_zero_iff
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w p = 0 ↔
      ∀ α, coefficients (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
        F.realification.layer (Finsupp.weight w α + 1) := by
  constructor
  · intro hp α
    apply (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mpr
    intro i hi
    by_cases he : Finsupp.weight w α = ω i
    · have hc := F.realSymbolOfPolynomial_coordinate b ω hlayers w p ⟨(α, i), he⟩
      rw [hp, map_zero, Finsupp.zero_apply] at hc
      exact hc.symm
    · exact (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
        (p.property α) i (by omega)
  · intro hp
    apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
    ext z
    rw [map_zero, Finsupp.zero_apply, F.realSymbolOfPolynomial_coordinate]
    exact (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mp
      (hp z.val.1) z.val.2 (by have hz := z.property; omega)

theorem realSymbolOfPolynomial_eq_iff_symbolMap_eq
    (p q : F.realification.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w p = F.realSymbolOfPolynomial b ω hlayers w q ↔
      F.realification.polynomialSymbolMap w p = F.realification.polynomialSymbolMap w q := by
  rw [← sub_eq_zero, ← map_sub]
  change F.realSymbolOfPolynomial b ω hlayers w
    ((p - q : F.realification.adaptedLieSubalgebra w) : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = 0 ↔ _
  rw [F.realSymbolOfPolynomial_eq_zero_iff b ω hlayers w (p - q),
    F.realification.polynomialSymbolMap_eq_iff]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeNilpotentLieAlgebra
namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

namespace FreeNilpotentLieAlgebra

noncomputable def mk : FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ FreeNilpotentLieAlgebra X s :=
  lieQuotientMap (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s)

theorem mk_surjective : Function.Surjective (mk X s) :=
  lieQuotientMap_surjective _

noncomputable def of (x : X) : FreeNilpotentLieAlgebra X s := mk X s (FreeLieAlgebra.of ℚ x)

variable {X s} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

@[simp] theorem lift_of (f : X → L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (x : X) :
    lift f hnil (of X s x) = f x := FreeLieAlgebra.lift_of_apply _ _

end FreeNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedLayerBounds
namespace OAI

section

namespace Erdos3.FreeNilpotentLieAlgebra

variable (X : Type*) (s : ℕ)

theorem mk_lieTreeEval (a : FreeMagma X) :
    mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a) = lieTreeEval (of X s) a :=
  map_lieTreeEval (mk X s) (FreeLieAlgebra.of ℚ) a

noncomputable def weightedLayer (w : X → ℕ) (d : ℕ) : Submodule ℚ (FreeNilpotentLieAlgebra X s) :=
  weightedLieUpperSpan (of X s) w d

theorem weightedLayer_antitone (w : X → ℕ) : Antitone (weightedLayer X s w) :=
  weightedLieUpperSpan_antitone (of X s) w

theorem weightedLayer_lie_mem (w : X → ℕ) {d e : ℕ} {x y : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ weightedLayer X s w d) (hy : y ∈ weightedLayer X s w e) :
    ⁅x, y⁆ ∈ weightedLayer X s w (d + e) :=
  weightedLieUpperSpan_lie_mem (of X s) w hx hy

theorem weightedLayer_eq_top (w : X → ℕ) (d : ℕ) (hd : ∀ a : FreeMagma X, d ≤ lieTreeWeight w a) :
    weightedLayer X s w d = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨p, rfl⟩ := mk_surjective X s x
  apply freeLie_linear_induction (fun p => mk X s p ∈ weightedLayer X s w d)
  · simpa only [map_zero] using (weightedLayer X s w d).zero_mem
  · intro p q hp hq
    rw [map_add]
    exact (weightedLayer X s w d).add_mem hp hq
  · intro c p hp
    rw [map_smul]
    exact (weightedLayer X s w d).smul_mem c hp
  · intro a
    rw [mk_lieTreeEval]
    exact Submodule.subset_span ⟨a, hd a, rfl⟩

theorem weightedLayer_zero (w : X → ℕ) : weightedLayer X s w 0 = ⊤ :=
  weightedLayer_eq_top X s w 0 (fun _ => Nat.zero_le _)

theorem weightedLayer_one (w : X → ℕ) (hw : ∀ i, 0 < w i) : weightedLayer X s w 1 = ⊤ :=
  weightedLayer_eq_top X s w 1 (fun a => a.length_pos.trans_le (lieTree_length_le_weight w hw a))

noncomputable def weightedLayerIdeal (w : X → ℕ) (d : ℕ) : LieIdeal ℚ (FreeNilpotentLieAlgebra X s) :=
  { weightedLayer X s w d with
    lie_mem := by
      intro x y hy
      have hx : x ∈ weightedLayer X s w 0 := by rw [weightedLayer_zero]; exact Submodule.mem_top
      change ⁅x, y⁆ ∈ weightedLayer X s w d
      simpa only [Nat.zero_add] using weightedLayer_lie_mem X s w hx hy }

end Erdos3.FreeNilpotentLieAlgebra

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineSampleCoefficientArray {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (b : Option K → I → ℝ) : CoefficientArray (K := K) U :=
  fun s => coefficients (substitute (affineParameterSubstitution b)
    (restrictCoefficients (U s.1) (p s.1) (hm s.1))) s.2.val

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneSiteCoefficientFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem coefficientArray_factor_of_bounded_site {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hf : ∀ j, ∃ Mj : (S → U j) →ₗ[ℝ] ℝ,
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
          Mj (siteEvaluation (fun _ : S => fun k => (t k : ℝ)) p)) :
    ∃ M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ,
      coefficientArrayFunctional U frequency = M.comp (coefficientEvaluationArray U t) := by
  choose Mj hMj using hf
  let A (j : Fin m) : CoefficientArray (K := Empty) U →ₗ[ℝ] (S → U j) :=
    LinearMap.pi (fun _ => LinearMap.proj (⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩ :
      CoefficientSlot Empty m))
  let M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ := ∑ j, (Mj j).comp (A j)
  refine ⟨M, ?_⟩
  apply LinearMap.ext
  intro x
  have hj (j : Fin m) :
      subspaceArrayFunctional (U j) (fun d a => (frequency j d.val a : ℝ)) (fun d => x ⟨j, d⟩) =
        Mj j (A j (coefficientEvaluationArray U t x)) := by
    let v : BoundedCoefficientExponent K (j.val + 1) → U j := fun d => x ⟨j, d⟩
    have he := hMj j (boundedArrayPolynomial (j.val + 1) v)
      (boundedArrayPolynomial_degreeLE (j.val + 1) v)
    rw [coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial] at he
    exact he
  calc
    _ = ∑ j : Fin m, subspaceArrayFunctional (U j)
        (fun d a => (frequency j d.val a : ℝ)) (fun d => x ⟨j, d⟩) := by
      change (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a) = _
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ j, Mj j (A j (coefficientEvaluationArray U t x)) := Finset.sum_congr rfl (fun j _ => hj j)
    _ = _ := by simp only [M, LinearMap.comp_apply, LinearMap.sum_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productConditionalMean (S : Finset I)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (FiniteProbabilityWeights.pi μ).mean (fun y => f (productCoordinateMix S x y))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

variable [Fintype ι] [∀ i, Fintype (X i)]

noncomputable def mass (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (c : ProductCylinder X) : ℝ :=
  productConditionalMean μ c.1 f (c.assignment base)

end ProductCylinder

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace FaceRegularityState

noncomputable def booleanCutCorrelation
    (S : FaceRegularityState Ω) (f : Ω → ℝ)
    (A : BooleanCutTest Ω) : ℝ :=
  mean fun x => S.residual f x * A.eval x

end FaceRegularityState

end Erdos3.FixedDensity

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

noncomputable def piFrequency (eta : ∀ i, L i →ₗ[ℚ] ℚ) : (∀ i, L i) →ₗ[ℚ] ℚ :=
  ∑ i, (eta i).comp (liePiEval i).toLinearMap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

def affineCubeModeFactors {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : Prop :=
  ∀ j, ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
    ∀ P, Homogeneous (j.val + 1) P →
      affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
        (map (U j).subtype P) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem affineCubeModeFactors_bounded {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hf : affineCubeModeFactors U root difference frequency) (j : Fin m) :
    ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
          M (VectorPolynomial.siteEvaluation (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p) := by
  obtain ⟨M, hM⟩ := hf j
  refine ⟨M, homogeneous_factorization_to_bounded_site (U j) (j.val + 1)
    (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ))
    (fun d a => (frequency j d a : ℝ)) M ?_⟩
  have hsite : (fun s (k : Option K) => k.elim (1 : ℝ)
      (fun t => ((affineSite root difference s (some t) : ℤ) : ℝ))) =
      (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) := by
    funext s k
    cases k <;> simp [affineSite, Int.cast_sum]
  simpa only [hsite] using hM

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoveredSiteValues
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

noncomputable def affineCoveredSiteSample {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (x : Option K → I → ℝ) :
    ∀ j, SubspaceArrayTorus (Finset (Fin q)) (U j) := fun j =>
  QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
    ((D : ℝ)⁻¹ • VectorPolynomial.siteEvaluation
      (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ))
      (substitute (affineParameterSubstitution x) (restrictCoefficients (U j) (p j) (hm j))))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem affine_site_substitution_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (p : VectorPolynomial I ℝ W) (x : Option K → I → ℝ) :
    VectorPolynomial.siteEvaluation
      (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ))
      (substitute (affineParameterSubstitution x) p) =
      fun s => eval (integerSiteValue (affineSite root difference s) x) p := by
  funext s
  change eval _ (substitute _ p) = _
  rw [eval_substitute]
  apply congrArg (fun t : I → ℝ => eval t p)
  funext i
  rw [affineParameterSubstitution_eval]
  simp [integerSiteValue, Fintype.sum_option, affineSite, Finset.sum_apply,
    zsmul_eq_mul, mul_comm]

theorem affineCoveredSiteSample_eq_values {I K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (x : Option K → I → ℝ) (j : Fin m) :
    affineCoveredSiteSample U root difference D p hm x j =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j))
        ((D : ℝ)⁻¹ • fun s => eval (integerSiteValue (affineSite root difference s) x)
          (restrictCoefficients (U j) (p j) (hm j))) := by
  unfold affineCoveredSiteSample
  rw [affine_site_substitution_eval]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SectionRetainedFourier
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

noncomputable def affineCubeFourierProjection {I K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (c : F → ℂ) (b : Option K → I → ℝ) : ℂ :=
  ∑ a, if affineCubeModeFactors U root difference (frequency a) then
    c a * layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b else 0

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TopSubspaceAdaptedBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}

def topSubspaceIdeal (F : NilpotentLieFiltration L s) (K : Submodule ℚ L)
    (hK : K ≤ F.layer s) : LieIdeal ℚ L :=
  { K with
    lie_mem := by
      intro x y hy
      rw [← lie_skew, F.top_layer_central (hK hy) x, neg_zero]
      exact K.zero_mem }

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeWeightedNilpotentLieAlgebra
namespace OAI

section

namespace Erdos3

def FreeWeightedNilpotentLieAlgebra (X : Type*) (s : ℕ) (w : X → ℕ) :=
  FreeNilpotentLieAlgebra X s ⧸ FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)

namespace FreeWeightedNilpotentLieAlgebra

variable (X : Type*) (s : ℕ) (w : X → ℕ)

noncomputable instance instLieRing : LieRing (FreeWeightedNilpotentLieAlgebra X s w) :=
  inferInstanceAs (LieRing (FreeNilpotentLieAlgebra X s ⧸
    FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)))

noncomputable instance instLieAlgebra : LieAlgebra ℚ (FreeWeightedNilpotentLieAlgebra X s w) :=
  inferInstanceAs (LieAlgebra ℚ (FreeNilpotentLieAlgebra X s ⧸
    FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1)))

noncomputable def mk : FreeNilpotentLieAlgebra X s →ₗ⁅ℚ⁆ FreeWeightedNilpotentLieAlgebra X s w :=
  lieQuotientMap (FreeNilpotentLieAlgebra.weightedLayerIdeal X s w (s + 1))

theorem mk_surjective : Function.Surjective (mk X s w) := lieQuotientMap_surjective _

theorem mk_eq_zero (x : FreeNilpotentLieAlgebra X s) :
    mk X s w x = 0 ↔ x ∈ FreeNilpotentLieAlgebra.weightedLayer X s w (s + 1) :=
  lieQuotientMap_eq_zero _ x

noncomputable def of (x : X) : FreeWeightedNilpotentLieAlgebra X s w :=
  mk X s w (FreeNilpotentLieAlgebra.of X s x)

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RaisedDegreeRank
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def realLayer (d i : ℕ) : LieIdeal ℝ (ℝ ⊗[ℚ] L) :=
  (F.layerIdeal d i).baseChange ℝ

theorem realLayer_lex_antitone {d e i j : ℕ} (h : d < e ∨ d = e ∧ i ≤ j) :
    F.realLayer e j ≤ F.realLayer d i := Submodule.baseChange_mono ℝ (F.lex_antitone h)

theorem realLayer_congr {d e i j : ℕ} (h : F.layer d i = F.layer e j) :
    F.realLayer d i = F.realLayer e j :=
  le_antisymm (Submodule.baseChange_mono ℝ h.le) (Submodule.baseChange_mono ℝ h.ge)

theorem realLayer_rank_zero_eq_one (d : ℕ) : F.realLayer d 0 = F.realLayer d 1 :=
  F.realLayer_congr (F.rank_zero_eq_one d)

theorem realLayer_overshoot (d i : ℕ) (h : d < i) : F.realLayer d i = F.realLayer (d + 1) 0 :=
  F.realLayer_congr (F.overshoot d i h)

theorem realLayer_terminal : F.realLayer s (r + 1) = ⊥ := by
  have h : F.layerIdeal s (r + 1) = ⊥ := by
    ext x
    change x ∈ F.layer s (r + 1) ↔ x ∈ (⊥ : Submodule ℚ L)
    rw [F.terminal]
  simp only [realLayer, h, LieSubmodule.baseChange_bot]

theorem lie_realLayer_le (d e i j : ℕ) :
    ⁅F.realLayer d i, F.realLayer e j⁆ ≤ F.realLayer (d + e) (i + j) := by
  have h : ⁅F.layerIdeal d i, F.layerIdeal e j⁆ ≤ F.layerIdeal (d + e) (i + j) := by
    rw [LieSubmodule.lie_le_iff]
    exact fun x hx y hy => F.lie_mem hx hy
  rw [realLayer, realLayer, ← LieSubmodule.lie_baseChange]
  exact Submodule.baseChange_mono ℝ h

theorem realLayer_lie_mem {d e i j : ℕ} {x y : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realLayer d i) (hy : y ∈ F.realLayer e j) :
    ⁅x, y⁆ ∈ F.realLayer (d + e) (i + j) :=
  F.lie_realLayer_le d e i j (LieSubmodule.lie_mem_lie hx hy)

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhasePointBounds
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {B : Type*} [Fintype B]

theorem translationPhaseArgument_left_increment_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    |translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β| ≤
      (1 + realPolynomialMass D₀ * Fintype.card B * d) * ε := by
  rw [translationPhaseArgument_left_increment]
  have hdiff (i : B) : |(β - g.base - z.base) i - (β - g.base) i| ≤ ε := by
    change |β i - g.base i - z.base i - (β i - g.base i)| ≤ ε
    rw [show β i - g.base i - z.base i - (β i - g.base i) = -z.base i by ring,
      abs_neg]
    exact hbase i
  have hD : |eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀| ≤
      realPolynomialMass D₀ * Fintype.card B * d * ε := by
    have h := abs_aeval_sub_aeval_mass_box_bound D₀
      (β - g.base - z.base) (β - g.base) (B := 1)
      le_rfl hε hnew hres hdiff hdegree
    simpa only [MvPolynomial.aeval_eq_eval, one_pow, mul_one] using h
  calc
    _ ≤ |eval (β - g.base) z.polynomial| +
      |eval (β - g.base - z.base) D₀ - eval (β - g.base) D₀| := abs_add_le _ _
    _ ≤ ε + realPolynomialMass D₀ * Fintype.card B * d * ε := add_le_add hp hD
    _ = _ := by ring

theorem translationPhaseArgument_left_increment_point_mass_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    |translationPhaseArgument D₀ (z * g) β - translationPhaseArgument D₀ g β| ≤
      (1 + M * Fintype.card B * d) * ε := by
  apply (translationPhaseArgument_left_increment_point_bound D₀ z g β hε hdegree
    hres hnew hbase hp).trans
  gcongr

theorem translationPhaseCharacter_left_increment_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1)
    (hnew : ∀ i, |β i - g.base i - z.base i| ≤ 1)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    ‖(Real.fourierChar (translationPhaseArgument D₀ (z * g) β) : ℂ) -
      (Real.fourierChar (translationPhaseArgument D₀ g β) : ℂ)‖ ≤
      (2 * Real.pi) * (1 + M * Fintype.card B * d) * ε := by
  have hphase := translationPhaseArgument_left_increment_point_mass_bound D₀ z g β
    hε hdegree hD hres hnew hbase hp
  exact (real_fourierChar_norm_sub_le _ _).trans
    ((mul_le_mul_of_nonneg_left hphase (by positivity)).trans_eq (by ring))

omit [Fintype B] in

theorem translation_residual_unit_boxes_of_quarter
    (z g : PolynomialTranslationGroupOver ℝ B) (β : B → ℝ) {ε : ℝ}
    (hε : ε ≤ 1 / 4) (hres : ∀ i, |β i - g.base i| ≤ 1 / 4)
    (hbase : ∀ i, |z.base i| ≤ ε) :
    (∀ i, |β i - g.base i| ≤ 1) ∧
      ∀ i, |β i - g.base i - z.base i| ≤ 1 := by
  constructor
  · intro i
    exact (hres i).trans (by norm_num)
  · intro i
    apply (abs_sub _ _).trans
    have hr := hres i
    have hz := hbase i
    linarith

theorem translationPhaseCharacter_left_increment_quarter_point_bound
    (D₀ : MvPolynomial B ℝ) (z g : PolynomialTranslationGroupOver ℝ B)
    (β : B → ℝ) {d : ℕ} {ε M : ℝ} (hε : 0 ≤ ε) (hεquarter : ε ≤ 1 / 4)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hres : ∀ i, |β i - g.base i| ≤ 1 / 4)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (hp : |eval (β - g.base) z.polynomial| ≤ ε) :
    ‖(Real.fourierChar (translationPhaseArgument D₀ (z * g) β) : ℂ) -
      (Real.fourierChar (translationPhaseArgument D₀ g β) : ℂ)‖ ≤
      (2 * Real.pi) * (1 + M * Fintype.card B * d) * ε := by
  obtain ⟨hres', hnew⟩ := translation_residual_unit_boxes_of_quarter z g β hεquarter hres hbase
  exact translationPhaseCharacter_left_increment_point_bound D₀ z g β
    hε hdegree hD hres' hnew hbase hp

end Erdos3

end

end OAI
end


