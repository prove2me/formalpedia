-- Prove2me | Definitions.Def_OAIE3v2B241
-- name    : OAIE3v2B241
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:53:33.304748+00:00
-- url     : https://prove2.me/theorems/ced65c63-208e-40bf-9a6c-c352ad6ebccb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 246 of 311
-- statement:
--   Definitions bundle 246 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B301`, `OAIE3v2B223`, `OAIE3v2B225`, `OAIE3v2B226`, `OAIE3v2B227` of this split.
--
--   Modules: `Estimates/AntisymmetricPairVerticalModel.lean`, `Estimates/CommonCoefficientFourAnnihilators.lean`, `Estimates/MixedPairFrozenEquivalence.lean`, `Estimates/MixedPreciseSampledExchange.lean`, `Estimates/NativeMixedReflectionBridge.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/SharedFreeFrozenComparison.lean`, `Estimates/SharedFreeRoundingThreshold.lean`, `Estimates/VectorSubspaceCorrectionRepresentatives.lean`, `Geometry/AntisymmetricPairCoordinateTest.lean`, `Geometry/CertifiedFullChartBudgetedTreeBounds.lean`, `Geometry/CertifiedFullChartForwardEarlyTree.lean`, `Geometry/FullTaggedChartCoefficientRange.lean`, `Geometry/MissingCoordinateErrorAbsorption.lean`, `Geometry/MixedAntisymmetricBox.lean`, `Geometry/TerminalChartSlowEvaluation.lean`, `Lattices/ActualFixedSpatialGoodPrimeDeletion.lean`, `Linear/SharedFreeComparisonBasis.lean`, `Nilpotent/MissingCoordinateNiltestApproximation.lean`, `Nilpotent/NativeMixedPairNiltest.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/FullChartPolynomialLiftControl.lean`, `Polynomial/MixedPairPolynomial.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B301
import Definitions.Def_OAIE3v2B223
import Definitions.Def_OAIE3v2B225
import Definitions.Def_OAIE3v2B226
import Definitions.Def_OAIE3v2B227

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.MissingCoordinateNiltestApproximation
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial RationalFilteredNilmanifold
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators NNReal

theorem exists_missing_coordinate_niltest_approximation (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin (s + 1) => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (c : Fin m → ℂ) (F : Fin (s + 1) → Fin m → (Fin (s + 1) → ℤ) → ℂ),
          (∀ j, ‖c j‖ ≤ 2) ∧ (∀ i j x, ‖F i j x‖ ≤ 1) ∧
          (∀ i j x y, (∀ k, k ≠ i → x k = y k) → F i j x = F i j y) ∧
          ∀ x, ‖T.eval x - ∑ j, c j * ∏ i, F i j x‖ ≤ epsilon := by
  obtain ⟨B, _, hsplit⟩ := exists_multidegree_downset_splitting s ((s + 1) * s) a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C (s + 1) + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let q := p + (s + 1 : ℕ)
  have hpq : p ≤ q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hq : 0 ≤ q := hp.trans hpq
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  let M := D.totalDegreeMultidegree (Fin (s + 1)) hT.1
  let J := missingCoordinateDownset s
  have hJ : ∀ i, IsLowerSet (J i) := missingCoordinateDownset_lower s
  let K := fun i => M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J i) (hJ i)
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] K i) := fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] K i) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] K i) :=
    fun i => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J i) (hJ i) q)
  have hM : M.ComplexityLE q := (D.totalDegreeMultidegree_complexity (Fin (s + 1)) hT.1).mono M hpq
  have hfamily : (Fintype.card (Fin (s + 1)) : ℝ) ≤ q + 2 := by
    simp only [Fintype.card_fin]
    dsimp [q]
    linarith only [hp]
  have hcover : ∀ b, b ≠ 0 → (∀ i, b ∉ J i) → M.filtration.layer (fun k => b k) = ⊥ :=
    fun b _ hb => missingCoordinateDownset_terminal D.filtration b hb
  have hscaleq : 1 / epsilon ≤ Real.exp ((q + 2) ^ a) :=
    hscale.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith only [hpq]) a))
  obtain ⟨r, _, _, b, hb, hstable, hE, _, h, _, n, hn, _, hcount, U,
    hUnorm, _, _, hUorbit, happrox⟩ :=
    hsplit (I := Unit) (α := Fin (s + 1)) M J hJ q (by simp) hM hfamily hcover
      (D.filtration.realTotalDegreeOrbit T.orbit) epsilon hepsilon hscaleq
      (by simpa using Real.one_le_exp hq)
  let V := fun i => M.positivePolynomialDownsetModelMultidegree (J i) (hJ i) r b hb hstable
  have hzero (i : Fin (s + 1)) (v : Fin (s + 1) → ℕ)
      (hv : ¬v ≤ missingCoordinateBound s i) : (V i).filtration.layer v = ⊥ := by
    let c : Fin (s + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm v
    exact M.filtration.positivePolynomialDownsetQuotient_terminal (J i) (hJ i) c hv
  let V' := fun i => (V i).restrictBound (missingCoordinateBound s i)
    (missingCoordinateBound_le s i) (hzero i)
  have hindependent (i : Fin (s + 1)) (j : Fin (n i)) (x y : Fin (s + 1) → ℤ)
      (hxy : ∀ k, k ≠ i → x k = y k) : (U i j).eval x = (U i j).eval y := by
    let g : (V i).filtration.realification.PolynomialOrbit :=
      M.filtration.positivePolynomialDownsetOrbit (J i) (hJ i) h
    let g' := (V i).filtration.restrictBoundRealOrbit (missingCoordinateBound s i) (hzero i) g
    exact (V' i).niltest_eval_eq_of_zero_coordinate i (by simp [missingCoordinateBound])
      (U i j) g' (hUorbit i j) x y hxy
  have hlip : (T.lipBound : ℝ) ≤ Real.exp q := by
    have hobs := T.observable_budget hT
    have hnonneg := T.normBound.coe_nonneg
    exact (by linarith only [hobs, hnonneg] : (T.lipBound : ℝ) ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr hpq)
  have hub : ∀ x, ‖T.observable x‖ ≤ 1 := fun x =>
    (T.norm_le x).trans (show (T.normBound : ℝ) ≤ 1 from hnorm)
  obtain ⟨coeff, hcoeff, _, herr⟩ := happrox (fun _ : Unit => T.observable) T.lipBound hlip
    (fun _ => T.lipschitz) (fun _ => hub)
  have hscalar := scalar_error_le_of_vector_error (I := Unit) (J := ∀ i, Fin (n i))
    (S := (Fin (s + 1) → ℤ)) (epsilon := epsilon)
    (fun _ : Unit => fun x => T.observable (QuotientGroup.mk
      (M.filtration.realification.polynomialOrbitEval x (D.filtration.realTotalDegreeOrbit T.orbit))))
    (fun j x => ∏ i, (U i (j i)).eval x) coeff herr ()
  let W := ∀ i, Fin (n i)
  let : Nonempty W := ⟨fun i => ⟨0, hn i⟩⟩
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  refine ⟨Fintype.card W, Fintype.card_pos, hcount.trans (Real.exp_le_exp.mpr hcost),
    (fun j => coeff (e j) ()), (fun i j x => (U i (e j i)).eval x),
    (fun j => hcoeff (e j) ()), ?_, ?_, ?_⟩
  · intro i j x
    exact ((U i (e j i)).norm_eval_le x).trans (by rw [hUnorm]; rfl)
  · intro i j x y hxy
    exact hindependent i (e j i) x y hxy
  · intro x
    have hval : T.observable (QuotientGroup.mk
        (M.filtration.realification.polynomialOrbitEval x
          (D.filtration.realTotalDegreeOrbit T.orbit))) = T.eval x := by
      exact congrArg (fun z => T.observable (QuotientGroup.mk z))
        (D.filtration.realTotalDegreeOrbit_eval T.orbit x)
    have hs := hscalar x
    rw [hval] at hs
    have hsum := e.sum_comp (fun j => coeff j () * ∏ i, (U i (j i)).eval x)
    rw [hsum]
    simpa only [mul_comm] using hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MissingCoordinateErrorAbsorption
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_absorb_missing_coordinate_error (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin (s + 1) => 1)), T.ComplexityLE p →
      ∀ {G X : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset X), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → X → Fin (s + 1) → ℤ) (f : G → X → ℂ),
      (∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 x ∈ S h, f h x * star (T.eval (sample h x))‖) →
      ∃ A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ,
        (∀ i x, ‖A i x‖ ≤ 1) ∧
        (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 x ∈ S h, f h x * ∏ i, A i (sample h x)‖ := by
  obtain ⟨a, _, hsplit⟩ := exists_missing_coordinate_niltest_approximation s 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * X + (X + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT G Ω H hH S hS sample f hf hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let U := T.expNormalize p
  let epsilon := Real.exp (-(2 * p + 1))
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 2 * p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hp, hcost]
  have hscale : 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [sq_nonneg p, hp]
  obtain ⟨m, _, hm, c, V, hc, hV, hindependent, happ⟩ :=
    hsplit U (T.expNormalize_complexity hT) (T.expNormalize_norm hT)
      epsilon (Real.exp_pos _) hscale
  have hepsilon : epsilon ≤ Real.exp (-(2 * p)) / 2 := by
    simpa only [epsilon, show -(2 * p + 1) = -(2 * p) - 1 by ring] using
      exp_sub_one_le_half_exp (-(2 * p))
  have hsmall : Real.exp (-(2 * p + q + 2)) ≤ Real.exp (-(2 * p)) / (2 * Real.exp q * 2) := by
    calc
      _ = Real.exp (-(2 * p + q) - 1 - 1) := by congr 1; ring
      _ ≤ Real.exp (-(2 * p + q) - 1) / 2 := exp_sub_one_le_half_exp _
      _ ≤ (Real.exp (-(2 * p + q)) / 2) / 2 :=
        div_le_div_of_nonneg_right (exp_sub_one_le_half_exp _) (by norm_num)
      _ = _ := by rw [show -(2 * p + q) = -(2 * p) - q by ring, Real.exp_sub]; ring
  let R (h : G) (_ : Unit) (j : Fin m) : Prop :=
    Real.exp (-(2 * p + q + 2)) ≤
      ‖𝔼 x ∈ S h, f h x * star (∏ i, V i j (sample h x))‖
  have hchoice : ∀ h ∈ H, ∀ u, ∃ j, R h u j := by
    intro h hh _
    have hmean : (𝔼 x ∈ S h, f h x * star (U.eval (sample h x))) =
        (Real.exp (-p) : ℂ) * (𝔼 x ∈ S h, f h x * star (T.eval (sample h x))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [U, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
        star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    have hnorm : Real.exp (-(2 * p)) ≤ ‖finiteCorrelation (S h) (f h)
        (fun x => U.eval (sample h x))‖ := by
      unfold finiteCorrelation
      rw [hmean, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      calc
        _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr h hh) (Real.exp_nonneg _)
    obtain ⟨j, hj⟩ := exists_correlating_weighted_summand (hS h hh) (f h)
      (fun x => U.eval (sample h x)) (fun j x => ∏ i, V i j (sample h x)) c
      (Real.exp_pos (-(2 * p))) (Real.exp_pos q) (by norm_num : (0 : ℝ) < 2)
      (by simpa only [Fintype.card_fin] using hm) hc (hf h hh)
      (fun x _ => by rw [norm_sub_rev]; exact (happ (sample h x)).trans hepsilon) hnorm
    exact ⟨j, hsmall.trans hj⟩
  obtain ⟨j, H', hsub, hH', hdense, hfixed⟩ := exists_large_fixed_choices H hH R hchoice
    (by simpa only [Fintype.card_fin] using hm)
  refine ⟨(fun i x => star (V i (j ()) x)), ?_, ?_, H', hsub, hH', ?_, ?_⟩
  · intro i x
    simpa only [norm_star] using hV i (j ()) x
  · intro i x y hxy
    exact congrArg star (hindependent i (j ()) x y hxy)
  · have hdense' : Real.exp (-q) * (H.card : ℝ) ≤ (H'.card : ℝ) := by
      simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hdense
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense'
  · intro h hh
    simpa only [star_prod] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hfixed h hh ())

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

namespace NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_coefficientFour_generators (hs : 2 ≤ s) (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) :
    ∃ v : Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim)) → (Fin 4 → W.L),
      Submodule.span ℚ (Set.range v) = D.coefficientFourSpace d ∧
      ∀ a j, rationalLogHeight (W.fourRankBasis.repr (v a) j) ≤ coefficientFourHeightBudget P := by
  classical
  obtain ⟨v, hv, hvH⟩ := (mem_heightBoundedSubspaces W.fourRankBasis _ _ _).mp
    (D.spaces_mem_candidates hP d)
  let K := W.rank.filtration.layer d.val 2
  let e := W.rank.basis d ⟨2, by omega⟩
  let φ : (Fin 4 → K) →ₗ[ℚ] (Fin 4 → W.L) :=
    LinearMap.pi (fun k => K.subtype.comp (LinearMap.proj k))
  let u : (Σ _ : Fin 4, Fin (finrank ℚ K)) → (Fin 4 → W.L) :=
    φ ∘ Pi.basis (fun _ : Fin 4 => e)
  have hu : Submodule.span ℚ (Set.range u) = Submodule.pi Set.univ (fun _ : Fin 4 => K) := by
    rw [show u = φ ∘ Pi.basis (fun _ : Fin 4 => e) from rfl, Set.range_comp,
      ← Submodule.map_span, (Pi.basis (fun _ : Fin 4 => e)).span_eq, Submodule.map_top]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Submodule.mem_pi.mpr (fun k _ => (y k).property)
    · intro hx
      exact ⟨fun k => ⟨x k, (Submodule.mem_pi.mp hx) k (Set.mem_univ k)⟩, rfl⟩
  let Q := P + refiltrationCoordinateBudget P + 1
  have hcost := refiltrationCoordinateBudget_nonneg hP
  have hQ : 0 ≤ Q := by dsimp only [Q]; linarith
  have hPQ : P ≤ Q := by dsimp only [Q]; linarith
  have hvQ (a) (j) : rationalLogHeight (W.fourRankBasis.repr (v a) j) ≤ Q := by
    have h := rationalLogHeight_le_of_height (hvH a j) (ceil_exp_le_exp_add_one hcost)
    exact h.trans (by dsimp only [Q]; linarith)
  have huQ (a) (j) : rationalLogHeight (W.fourRankBasis.repr (u a) j) ≤ Q := by
    rw [NativeDegreeRankFamily.fourRankBasis, Pi.basis_repr]
    change rationalLogHeight (W.model.basis.repr
      ((Pi.basis (fun _ : Fin 4 => e) a j.1 : K) : W.L) j.2) ≤ Q
    rw [Pi.basis_apply]
    by_cases hja : j.1 = a.1
    · rw [hja, Pi.single_eq_same]
      exact ((W.complexity.mono W.rank hbP).2 d ⟨2, by omega⟩ a.2 j.2).trans hPQ
    · rw [Pi.single_eq_of_ne hja]
      simpa [rationalLogHeight] using hQ
  have hspan : Submodule.span ℚ (Set.range (Sum.elim v u)) = D.coefficientFourSpace d := by
    rw [span_range_sumElim, hv, hu, D.coefficientFourSpace_eq_sup]
  obtain ⟨z, hz, hzH⟩ := exists_bounded_submodule_ambient_spanning W.fourRankBasis
    (D.coefficientFourSpace d) (Sum.elim v u) hspan (one_le_ceil_exp Q)
    (fun a j => rationalHeightLE_ceil_exp (by
      cases a with
      | inl a => exact hvQ a j
      | inr a => exact huQ a j))
  refine ⟨z, hz, fun a j => ?_⟩
  have h := rationalLogHeight_le_of_height (hzH a j) (ceil_exp_le_exp_add_one hQ)
  simpa only [Q, coefficientFourHeightBudget, add_assoc, one_add_one_eq_two] using h

theorem exists_coefficientFour_basis (hs : 2 ≤ s) (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) :
    ∃ e : Basis (Fin (finrank ℚ (D.coefficientFourSpace d))) ℚ (D.coefficientFourSpace d),
      ∀ a j, rationalLogHeight (W.fourRankBasis.repr (e a : Fin 4 → W.L) j) ≤
        coefficientFourHeightBudget P := by
  classical
  let : FiniteDimensional ℚ (Fin 4 → W.L) := W.fourRankBasis.finiteDimensional_of_finite
  obtain ⟨v, hv, hvH⟩ := D.exists_coefficientFour_generators hs hP hbP d
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hv] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro a j
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz a
  rw [← hk]
  exact hvH k j

end NativeRankRelation.CommonData
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_correlation_refined_basis (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (d : Fin s) :
    ∃ a : Basis (Fin (finrank ℚ (fourRefinedRelation (D.coefficientFreeSpan d)
        (D.dependentFreeSpan d) (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)))) ℚ
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)),
      ∀ j i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => E.basis)).repr
        (a j : Fin 4 → D.CoefficientFreeLieAlgebra) i) ≤
          fourRefinementBasisBudget (Q + coefficientFourHeightBudget P') := by
  obtain ⟨c, hc⟩ := D.exists_coefficientFreeSpan_basis E.basis F (by omega) d
  obtain ⟨b, hb⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  obtain ⟨k, hk⟩ := D'.exists_coefficientFour_basis hs hP' hQP' ⟨d.val + 1, by omega⟩
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hB := coefficientFourHeightBudget_nonneg hP'
  have hQA : Q ≤ Q + coefficientFourHeightBudget P' := le_add_of_nonneg_right hB
  have hBA : coefficientFourHeightBudget P' ≤ Q + coefficientFourHeightBudget P' :=
    le_add_of_nonneg_left hQ
  apply exists_fourRefinedRelation_basis_logHeight E.basis _ _
    (D.dependentFreeSpan_le_coefficientFreeSpan d) _ c b k (add_nonneg hQ hB)
    (by simpa only [Fintype.card_fin] using hT.1.1.trans hQA)
    (fun a i => (hc a i).trans hQA) (fun a i => (hb a i).trans hQA)
  exact fun a i => (hk a i).trans hBA

theorem exists_correlation_refined_annihilator (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (d : Fin s) :
    ∃ m : ℕ, m ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
      ∃ ℓ : (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin m → ℚ),
        Function.Surjective ℓ ∧ LinearMap.ker ℓ =
          fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
        (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ
          (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
            fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
        (∀ x ∈ D.dependentFreeSpan d, ℓ (fourDiagonalMap (R := ℚ) x) = 0) ∧
        (∀ z ∈ fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩),
          ℓ (fourDiagonalMap (R := ℚ) (z 0)) +
            ℓ (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0
              (z 0 + z 1 - z 2 - z 3)) = 0) ∧
        fourPetalSpace (D.dependentFreeSpan d)
          (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)) =
          D.dependentFreeSpan d ⊓ LinearMap.ker
            (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) := by
  obtain ⟨c, hc⟩ := D.exists_coefficientFreeSpan_basis E.basis F (by omega) d
  obtain ⟨b, hb⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  obtain ⟨k, hk⟩ := D'.exists_coefficientFour_basis hs hP' hQP' ⟨d.val + 1, by omega⟩
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hB := coefficientFourHeightBudget_nonneg hP'
  have hQA : Q ≤ Q + coefficientFourHeightBudget P' := le_add_of_nonneg_right hB
  have hBA : coefficientFourHeightBudget P' ≤ Q + coefficientFourHeightBudget P' :=
    le_add_of_nonneg_left hQ
  simpa only [Fintype.card_fin] using
    exists_fourRefinedRelation_annihilator E.basis _ _
      (D.dependentFreeSpan_le_coefficientFreeSpan d) _ c b k (add_nonneg hQ hB)
      (by simpa only [Fintype.card_fin] using hT.1.1.trans hQA)
      (fun a i => (hc a i).trans hQA) (fun a i => (hb a i).trans hQA)
      (fun a i => (hk a i).trans hBA)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

noncomputable def pairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.antisymmetricPairModels).Niltest (fun _ : Fin 2 => 1) :=
  piNiltest V.antisymmetricPairModels (V.pairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
    (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
    (V.pairComparisonTests_complexity a b)

theorem pairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.pairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (antisymmetricPairBudget p q)) :=
  piNiltest_complexity V.antisymmetricPairModels (V.pairComparisonTests a b) _ _ _

theorem pairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairComparisonNiltest a b).observable x =
      star (W.vertical.observable a (productProjection V.antisymmetricPairModels (some 0) x)) *
        W.vertical.observable b (productProjection V.antisymmetricPairModels (some 1) x) := by
  change (∏ k, (V.pairComparisonTests a b k).observable
    (productProjection V.antisymmetricPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (star (W.vertical.observable a
    (productProjection V.antisymmetricPairModels (some 0) x)) *
      W.vertical.observable b (productProjection V.antisymmetricPairModels (some 1) x)) = _
  exact one_mul _

theorem pairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l)) (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.antisymmetricPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.pairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.antisymmetricPairModels (V.pairComparisonTests a b)
    V.antisymmetricPairFrequencies _ _ _ (V.pairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ k, mixedCorrelationDegree 1 k)) (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairComparisonNiltest a b).observable (z • x) =
      (V.pairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ k, mixedCorrelationDegree 1 k) :=
    (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.pairComparisonNiltest_vertical a b z htop, R.kills_top z.coord hz]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AntisymmetricPairCoordinateTest
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pairCoordinateNiltest_observable (k : Fin 2) (out : Fin W.outputDim)
    (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairCoordinateNiltest k out).observable x =
      W.vertical.observable out (productProjection V.antisymmetricPairModels (some k) x) := by
  change (∏ l, (V.pairCoordinateTests k out l).observable
    (productProjection V.antisymmetricPairModels l x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * (W.vertical.observable out
      (productProjection V.antisymmetricPairModels (some 0) x) * 1) = _
    simp only [one_mul, mul_one]
    rfl
  · change 1 * (1 * W.vertical.observable out
      (productProjection V.antisymmetricPairModels (some 1) x)) = _
    simp only [one_mul]
    rfl

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPairVerticalModel
namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pairFrozenVector_error (k : Fin 2) (out : Fin W.outputDim) (x y : Fin 2 → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) : (pi V.antisymmetricPairModels).Space) =
      QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi V.antisymmetricPairModels).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi V.antisymmetricPairModels).basis.baseChange ℝ)
    ‖W.eval out (correlationInput (x k) (x k.rev)) -
        R.pairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (antisymmetricPairBudget p q)) *
        dist (R.slowValue x) (R.slowValue y) := by
  let D := pi V.antisymmetricPairModels
  let T := V.pairCoordinateNiltest k out
  let b := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin 2 => 1) (fun i => (x i : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq T.observable (R.slowValue x) b
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left T.observable T.lipschitz
    (R.slowValue x) (R.slowValue y) b (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (T.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (antisymmetricPairBudget p q)) := by
    have h := T.observable_budget (V.pairCoordinateNiltest_complexity k out)
    linarith [T.normBound.coe_nonneg]
  have hraw : ‖R.pairFrozenVector k (R.slowValue x) (R.rationalValue x) out x -
      R.pairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (antisymmetricPairBudget p q)) *
        dist (R.slowValue x) (R.slowValue y) := by
    simpa only [T, V.pairCoordinateNiltest_observable, pairFrozenVector, frozenMiddleValue, b] using
      hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)
  simpa only [← R.pairFrozenVector_diagonal k out x] using hraw

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

theorem select_pair_local_partition {b c : ℝ}
    (hlocal : R.HasPairLocalApproximation b) (hred : R.HasPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin 2 → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin 2 → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence 1 c
            (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.pairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ (k : Fin 2) (out : Fin W.outputDim),
            (𝔼 x : Fin 2 → ZMod N,
              ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
                ∑ j, (A j x : ℂ) * R.pairAnchoredVector
                  (fun i => ((y j i).val : ℤ)) k out (fun i => ((x i).val : ℤ))‖) ≤
              Real.exp b * ρ + 4 * B.card / N := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin 2 → ZMod N) (i : Fin 2) => ((x i).val : ℤ)
  have hv (x : Fin 2 → ZMod N) (i : Fin 2) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin 2 → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.pairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro k out
  let F := fun x : Fin 2 → ZMod N => W.eval out (correlationInput (v x k) (v x k.rev))
  let G := fun j (x : Fin 2 → ZMod N) => R.pairAnchoredVector (v (y j)) k out (v x)
  let E := coordinateExceptional (ι := Fin 2) B
  have hpoint (j : I) (x : Fin 2 → ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖F x - G j x‖ ≤ Real.exp b * ρ := by
    have hx' := (not_mem_coordinateExceptional B x).mp hx
    obtain ⟨hy', hAy⟩ := hy j x hx' hAx
    obtain ⟨hres, hnear⟩ := hcells j x (y j) hx' hy' hAx hAy
    exact hmodel (v (y j)) (hv (y j)) k out (v x) ρ hρ (hv x) hres
      (by simpa only [v, Int.cast_natCast] using hnear)
  have hcap (x : Fin 2 → ZMod N) : ‖F x - ∑ j, (A j x : ℂ) * G j x‖ ≤ 2 := by
    apply norm_sub_positive_sum_le (fun j => A j x) (fun j => G j x) (F x) 2
      (fun j => hA j x) (hsum x)
    intro j _
    exact (norm_sub_le _ _).trans (by
      have hF : ‖F x‖ ≤ 1 := W.norm_eval out _
      have hG : ‖G j x‖ ≤ 1 := R.pairAnchoredVector_norm _ _ _ _
      linarith)
  have hgood (x : Fin 2 → ZMod N) (hx : x ∉ E) :
      ‖F x - ∑ j, (A j x : ℂ) * G j x‖ ≤ Real.exp b * ρ :=
    norm_sub_positive_sum_le (fun j => A j x) (fun j => G j x) (F x) (Real.exp b * ρ)
      (fun j => hA j x) (hsum x) (fun j => hpoint j x hx)
  have herr := expect_abs_le_of_exceptional_set E
    (fun x => ‖F x - ∑ j, (A j x : ℂ) * G j x‖) (mul_nonneg (Real.exp_nonneg b) hρ)
    (fun x => by simpa only [abs_of_nonneg (norm_nonneg _)] using hcap x)
    (fun x hx => by simpa only [abs_of_nonneg (norm_nonneg _)] using hgood x hx)
  have hdensity : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * (B.card : ℝ) / N := by
    simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat] using
      coordinateExceptional_density_le (ι := Fin 2) B
  have herr' : (𝔼 x : Fin 2 → ZMod N, ‖F x - ∑ j, (A j x : ℂ) * G j x‖) ≤
      Real.exp b * ρ + 2 * ((E.card : ℝ) / Fintype.card (Fin 2 → ZMod N)) := by
    simpa only [abs_of_nonneg (norm_nonneg _), mul_div_assoc] using herr
  apply herr'.trans
  calc
    _ ≤ Real.exp b * ρ + 2 * (2 * (B.card : ℝ) / N) := by gcongr
    _ = _ := by ring

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem pairCoordinate_common_vertical (k : Fin 2) (out : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ l, mixedCorrelationDegree 1 l))
    (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairCoordinateNiltest k out).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency
          (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) : ℝ) : CircleFourier.Circle) *
        (V.pairCoordinateNiltest k out).observable x := by
  have htop := (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer_le
    R.subalgebra _ hz
  have heq := R.pair_top_agreement z.coord hz
  rw [V.pairCoordinateNiltest_observable, productProjection_smul]
  have hv := W.pairComponent_vertical out k k.rev
    (productProjectionHom V.antisymmetricPairModels (some k) z)
    (productProjectionHom_mem_layer V.antisymmetricPairModels (some k) _ z htop)
    (productProjection V.antisymmetricPairModels (some k) x)
  change W.vertical.observable out _ = _ at hv
  refine hv.trans ?_
  change CircleFourier.character
      ((realifyFunctional W.vertical.frequency
        (realificationLieHom (V.antisymmetricPairProjection k) z.coord) : ℝ) : CircleFourier.Circle) *
      W.vertical.observable out _ = _
  have hphase : realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection k) z.coord) =
    realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) := by
    fin_cases k
    · rfl
    · exact heq.symm
  rw [hphase]
  exact congrArg (fun w : ℂ => CircleFourier.character
    ((realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) : ℝ) : CircleFourier.Circle) * w)
      (V.pairCoordinateNiltest_observable k out x).symm

theorem pairCoordinate_comparison_invariant (k l : Fin 2) (i j : Fin W.outputDim)
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.antisymmetricPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ l, mixedCorrelationDegree 1 l))
    (x y : (pi V.antisymmetricPairModels).Space) :
    (V.pairCoordinateNiltest k i).observable (z • x) *
      star ((V.pairCoordinateNiltest l j).observable (z • y)) =
    (V.pairCoordinateNiltest k i).observable x * star ((V.pairCoordinateNiltest l j).observable y) := by
  let c := CircleFourier.character
    ((realifyFunctional W.vertical.frequency
      (realificationLieHom (V.antisymmetricPairProjection 0) z.coord) : ℝ) : CircleFourier.Circle)
  have hc : c * star c = 1 := by
    dsimp only [c]
    rw [← CircleFourier.character_neg, ← CircleFourier.character_add,
      add_neg_cancel, CircleFourier.character_zero]
  rw [R.pairCoordinate_common_vertical k i z hz x,
    R.pairCoordinate_common_vertical l j z hz y, star_mul]
  change (c * _) * (_ * star c) = _
  calc
    _ = (c * star c) * ((V.pairCoordinateNiltest k i).observable x *
      star ((V.pairCoordinateNiltest l j).observable y)) := by ring
    _ = _ := by rw [hc, one_mul]

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_separated_family_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ {J K : Type*} [Fintype J] [Fintype K]
        {chi : J → (Fin (s + 1) → ℤ) → ℂ} {eta : K → (Fin (s + 1) → ℤ) → ℂ},
      NativeIntegerVectorEquivalence s p chi eta →
      (∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) →
      ∀ {G Ω : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset Ω), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → Ω → Fin (s + 1) → ℤ) (f : G → Ω → ℂ),
      (∀ h ∈ H, ∀ u ∈ S h, ‖f h u‖ ≤ 1) →
      ∀ (j : J) (A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
      (∀ i x, ‖A i x‖ ≤ 1) →
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → A i x = A i y) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 u ∈ S h, f h u * star (chi j (sample h u)) * ∏ i, A i (sample h u)‖) →
      ∃ (k : K) (B : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
        (∀ i x, ‖B i x‖ ≤ 1) ∧
        (∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 u ∈ S h, f h u * star (eta k (sample h u)) * ∏ i, B i (sample h u)‖ := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_missing_coordinate_error s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * X + (3 * X + 2 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p hp J K _ _ chi eta E hunit G Ω H hH S hS sample f hf j A hA hAind hcorr
  classical
  let P := Σ k : K, Fin (E.selectedExpansion j k).count
  let rel (h : G) (_ : Unit) (c : P) : Prop :=
    Real.exp (-(p + 2 * p)) ≤ ‖𝔼 u ∈ S h,
      (f h u * ∏ i, A i (sample h u)) * star (eta c.1 (sample h u)) *
        star (((E.selectedExpansion j c.1).test c.2).eval (sample h u))‖
  have hchoice : ∀ h ∈ H, ∀ u, ∃ c, rel h u c := by
    intro h hh _
    obtain ⟨k, l, hl⟩ := E.transfer_sample_correlation (S h) (sample h) j
      (fun u => f h u * ∏ i, A i (sample h u)) (fun u _ => hunit (sample h u)) (by
        simpa only [mul_right_comm] using hcorr h hh)
    exact ⟨⟨k, l⟩, hl⟩
  have hcount : (Fintype.card P : ℝ) ≤ Real.exp (2 * p) := by
    change (Fintype.card (Σ k : K, Fin (E.selectedExpansion j k).count) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _k : K, Real.exp p := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [Fintype.card_fin] using (E.selectedExpansion j k).count_bound
      _ = (Fintype.card K : ℝ) * Real.exp p := by simp
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul_of_nonneg_right E.right_dimension (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, two_mul]
  obtain ⟨c, H₁, hsub₁, hH₁, hsize₁, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice hcount
  have hsize₁' : Real.exp (-(2 * p)) * (H.card : ℝ) ≤ (H₁.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize₁
  let T := (E.selectedExpansion j (c ()).1).test (c ()).2
  let r := 3 * p + 2
  let t := (r + a) ^ a
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have h3pr : p + 2 * p ≤ r := by dsimp only [r]; linarith
  have htotal : 2 * p + t ≤ (p + C) ^ C := by
    simpa [X, r, t, Polynomial.eval₂_pow] using hbudget p hp
  have htc : t ≤ (p + C) ^ C := by linarith
  have heta (x : Fin (s + 1) → ℤ) : ‖eta (c ()).1 x‖ ≤ 1 := by
    have hle : ‖eta (c ()).1 x‖ ^ 2 ≤ ∑ k, ‖eta k x‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖eta k x‖) (Finset.mem_univ _)
    rw [hunit] at hle
    nlinarith only [hle, norm_nonneg (eta (c ()).1 x)]
  let F (h : G) (u : Ω) := f h u * star (eta (c ()).1 (sample h u)) * ∏ i, A i (sample h u)
  have hF : ∀ h ∈ H₁, ∀ u ∈ S h, ‖F h u‖ ≤ 1 := by
    intro h hh u hu
    dsimp only [F]
    rw [norm_mul, norm_mul, norm_star, norm_prod]
    exact (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      ((mul_le_of_le_one_left (norm_nonneg _) (hf h (hsub₁ hh) u hu)).trans (heta _))).trans
      (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hA i _))
  have hFcorr : ∀ h ∈ H₁, Real.exp (-r) ≤
      ‖𝔼 u ∈ S h, F h u * star (T.eval (sample h u))‖ := by
    intro h hh
    have ht := hfixed h hh ()
    dsimp only [rel] at ht
    simpa only [F, T, mul_right_comm] using
      (Real.exp_le_exp.mpr (neg_le_neg h3pr)).trans ht
  obtain ⟨D, hD, hDind, H₂, hsub₂, hH₂, hsize₂, hfinal⟩ := habsorb T
    (((E.selectedExpansion j (c ()).1).complexity (c ()).2).mono hpr)
    H₁ hH₁ S (fun h hh => hS h (hsub₁ hh)) sample F hF hFcorr
  refine ⟨(c ()).1, (fun i x => A i x * D i x), ?_, ?_, H₂, hsub₂.trans hsub₁, hH₂, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hD i x)
  · intro i x y hxy
    change A i x * D i x = A i y * D i y
    rw [hAind i x y hxy, hDind i x y hxy]
  · calc
      _ ≤ Real.exp (-(2 * p + t)) * (H.card : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (Nat.cast_nonneg _)
      _ = Real.exp (-t) * (Real.exp (-(2 * p)) * (H.card : ℝ)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-t) * (H₁.card : ℝ) :=
        mul_le_mul_of_nonneg_left hsize₁' (Real.exp_nonneg _)
      _ ≤ _ := hsize₂
  · intro h hh
    simpa only [F, Finset.prod_mul_distrib, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg htc)).trans (hfinal h hh)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_antisymmetric_family (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (c : ℤ) (i j : Fin W.outputDim),
      ∀ {G Ω : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset Ω), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → Ω → Fin (n + 2) → ℤ) (f : G → Ω → ℂ),
      (∀ h ∈ H, ∀ u ∈ S h, ‖f h u‖ ≤ 1) →
      ∀ (A : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
      (∀ k x, ‖A k x‖ ≤ 1) →
      (∀ k x y, (∀ l, l ≠ k → x l = y l) → A k x = A k y) →
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 u ∈ S h,
        f h u * star (W.mixedReflectionSource c (i, j) (sample h u)) * ∏ k, A k (sample h u)‖) →
      ∃ (i' j' : Fin W.outputDim) (B : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
        (∀ k x, ‖B k x‖ ≤ 1) ∧
        (∀ k x y, (∀ l, l ≠ k → x l = y l) → B k x = B k y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 u ∈ S h, f h u * W.mixedAntisymmetric i' j' (sample h u) * ∏ k, B k (sample h u)‖ := by
  obtain ⟨a, _, hreflect⟩ := exists_mixed_reflected_pair_equivalence n
  obtain ⟨b, _, htransfer⟩ := exists_separated_family_correlation (n + 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Q + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W c i j G Ω H hH S hS sample f hf A hA hAind hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have E := hreflect W c
  obtain ⟨k, B, hB, hBind, H', hsub, hH', hsize, hBcorr⟩ := htransfer hr (E.mono hqr)
    (W.mixed_reflection_target_unit c) H hH S hS sample f hf (i, j) A hA hAind
    (fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hcorr h hh))
  obtain ⟨D, hD, hDind, hpoint⟩ := W.exists_mixed_reflection_weights c k B hB hBind
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨k.1.2, k.2.2, D, hD, hDind, H', hsub, hH', ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg _)).trans hsize
  · intro h hh
    have heq : (𝔼 u ∈ S h, f h u * star (W.mixedReflectionTarget c k (sample h u)) *
        ∏ l, B l (sample h u)) =
        𝔼 u ∈ S h, f h u * W.mixedAntisymmetric k.1.2 k.2.2 (sample h u) * ∏ l, D l (sample h u) := by
      apply Finset.expect_congr rfl
      intro u _
      rw [mul_assoc, hpoint, ← mul_assoc]
    rw [← heq]
    exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hBcorr h hh)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators Classical

theorem exists_mixed_sum_antisymmetric_correlation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ (j k : Fin W.outputDim) (B : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
        (∀ j x, ‖B j x‖ ≤ 1) ∧
        (∀ j x y, (∀ l, l ≠ j → x l = y l) → B j x = B j y) ∧
        Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 u : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
            W.mixedAntisymmetric j k
                (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun l => (u l).val))) *
              ∏ l, B l (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun j => (u j).val)))‖ := by
  obtain ⟨b, _, htransfer⟩ := exists_mixed_antisymmetric_family n
  let X : Polynomial ℕ := Polynomial.X
  let R := X + Polynomial.C (2 * 2 ^ (n + 1)) * X + 12
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := 2 * ((2 ^ (n + 1) : ℕ) : ℝ) * p + 10
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  let K (_ : Unit) (h m : ℤ) (u : Fin n → ℤ) := star (W.eval i (mixedSlotInput h m u))
  have hK : ∀ t h m u, ‖K t h m u‖ ≤ 1 := by
    intro t h m u
    simpa only [K, norm_star] using W.norm_eval i (mixedSlotInput h m u)
  obtain ⟨z, carry, D, hD, hDind, hreflect⟩ := exists_cyclic_mixed_reflection n hp K hK
    (fun _ => f) (fun _ => hf) (fun _ => A) (fun _ => hA) (fun _ => hmiss) (by
      simpa only [K, Fintype.expect_const] using hcorr)
  let c : ℤ := z.val + (carry.val : ℤ) * N
  let V := W.mono hpr
  let sample (t : (Fin n → ZMod N) × (ZMod N × ZMod N)) : Fin (n + 2) → ℤ :=
    Fin.cons (t.2.1.val : ℤ) (Fin.cons (t.2.2.val : ℤ) (fun l => (t.1 l).val))
  have hpoint (u : Fin n → ZMod N) (h h' : ZMod N) :
      star (V.mixedReflectionSource c (i, i) (sample (u, (h, h')))) =
        K () h.val (c - h.val - h'.val) (fun l => (u l).val) *
          star (K () h'.val (c - h.val - h'.val) (fun l => (u l).val)) := by
    change star (W.eval i (mixedSlotInput (h.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val)) *
      star (W.eval i (mixedSlotInput (h'.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val)))) =
        star (W.eval i (mixedSlotInput (h.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val))) *
          star (star (W.eval i (mixedSlotInput (h'.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val))))
    simp only [star_mul, star_star]
    exact mul_comm _ _
  have hsource : Real.exp (-r) ≤
      ‖𝔼 t : (Fin n → ZMod N) × (ZMod N × ZMod N),
        star (V.mixedReflectionSource c (i, i) (sample t)) * ∏ l, D () l (sample t)‖ := by
    simp_rw [expect_prod_split, hpoint]
    simpa only [Fintype.univ_unit, Finset.expect_singleton, sample, c] using
      (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans hreflect
  obtain ⟨j, k, B, hB, hBind, H, _, hH, _, hfinal⟩ := htransfer V c i i
    (Finset.univ : Finset Unit) Finset.univ_nonempty
    (fun _ => (Finset.univ : Finset ((Fin n → ZMod N) × (ZMod N × ZMod N))))
    (fun _ _ => Finset.univ_nonempty) (fun _ => sample) (fun _ _ => (1 : ℂ))
    (fun _ _ _ _ => by norm_num) (D ()) (hD ()) (hDind ())
    (fun _ _ => by simpa only [one_mul] using hsource)
  obtain ⟨t, ht⟩ := hH
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    convert hbudget p hp using 1
    simp [X, R, r, q, Polynomial.eval₂_pow, Nat.cast_mul]
    ring
  have hmono (x : Fin (n + 2) → ℤ) :
      V.mixedAntisymmetric j k x = W.mixedAntisymmetric j k x := rfl
  simp_rw [hmono] at hfinal
  refine ⟨j, k, B, hB, hBind, ?_⟩
  simpa only [expect_prod_split, sample, one_mul] using
    (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hfinal t ht)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedAntisymmetricBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace NativeMultidegreeNilcharacter

theorem exists_mixed_sum_antisymmetric_box (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ j k : Fin W.outputDim, Real.exp (-((p + C) ^ C)) ≤
        (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
          W.mixedAntisymmetric j k (fun l => (x l).val))).re := by
  obtain ⟨a, _, hcorr⟩ := exists_mixed_sum_antisymmetric_correlation n
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Polynomial.C (2 ^ (n + 2)) * Q)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hinput
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨j, k, B, hB, hBind, hpositive⟩ := hcorr W f hf i A hA hmiss hinput
  let F (x : Fin (n + 2) → ZMod N) := W.mixedAntisymmetric j k (fun l => (x l).val)
  let U (l : Fin (n + 2)) (x : Fin (n + 2) → ZMod N) := B l (fun l => (x l).val)
  have hvals (h m : ZMod N) (u : Fin n → ZMod N) :
      (fun l => (((Fin.cons h (Fin.cons m u) : Fin (n + 2) → ZMod N) l).val : ℤ)) =
        Fin.cons (h.val : ℤ) (Fin.cons (m.val : ℤ) (fun l => (u l).val)) := by
    funext l
    refine Fin.cases ?_ (fun l => ?_) l
    · rfl
    · refine Fin.cases ?_ (fun l => ?_) l <;> rfl
  have hmean : boxTestCorrelation F U =
      𝔼 u : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        W.mixedAntisymmetric j k (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun l => (u l).val))) *
          ∏ l, B l (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun j => (u j).val))) := by
    rw [boxTestCorrelation, expect_mixed_tuple]
    simp only [F, U, hvals]
  have hU : ∀ l, MissesBoxCoordinate (U l) l := by
    intro l x v
    apply hBind l
    intro m hml
    change (((Function.update x l v) m).val : ℤ) = ((x m).val : ℤ)
    rw [Function.update_of_ne hml]
  have hbox := boxTest_cauchySchwarz (n + 1) F U (fun l x => hB l _) hU
  have hscore : Real.exp (-((2 ^ (n + 2) : ℕ) : ℝ) * ((p + a) ^ a)) ≤
      (boxPhaseMoment (n + 2) F).re := by
    have hpower : Real.exp (-((2 ^ (n + 2) : ℕ) : ℝ) * ((p + a) ^ a)) =
        Real.exp (-((p + a) ^ a)) ^ (2 ^ (n + 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpower]
    apply (pow_le_pow_left₀ (Real.exp_nonneg _) ?_ _).trans hbox
    rwa [hmean]
  have hcost : ((2 ^ (n + 2) : ℕ) : ℝ) * ((p + a) ^ a) ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨j, k, ?_⟩
  exact (Real.exp_le_exp.mpr (by linarith)).trans hscore

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeMixedPairNiltest
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixedPairNiltest_complexity :
    V.mixedPairNiltest.ComplexityLE (productNiltestBudget (mixedPairBudget p q)) :=
  piNiltest_complexity V.mixedPairModels V.mixedPairTests _ _ _

theorem mixedPairNiltest_eval (x : Fin (n + 2) → ℤ) :
    V.mixedPairNiltest.eval x =
      W.mixedAntisymmetric i j x * star (V.test.eval x) := by
  rw [mixedPairNiltest, piNiltest_eval]
  exact V.mixedPairTests_eval x

theorem mixedPairNiltest_vertical (z : (pi V.mixedPairModels).RealGroup)
    (hz : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : (pi V.mixedPairModels).Space) :
    V.mixedPairNiltest.observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.mixedPairFrequencies) z.coord : ℝ) : CircleFourier.Circle) *
          V.mixedPairNiltest.observable x :=
  piNiltest_vertical V.mixedPairModels V.mixedPairTests V.mixedPairFrequencies _ _ _
    V.mixedPairTests_vertical z hz x

theorem mixedPairNiltest_bias :
    Real.exp (-q) ≤ ‖𝔼 x ∈ integerBox (fun _ : Fin (n + 2) => N), V.mixedPairNiltest.eval x‖ := by
  rw [integerBox_expect_eq_zmod]
  simp_rw [V.mixedPairNiltest_eval]
  exact V.correlation

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeComparisonBasis
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_sharedFreeComparisonSpace_basis
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') (d : Fin s) :
    let C := (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)
    let P := fourPetalSpace (D.dependentFreeSpan d)
      (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))
    let K := D.coefficientFreeFiltration.layer (d.val + 1) 2
    ∃ b : Basis (Fin (finrank ℚ (petalComparisonSpace C P K))) ℚ (petalComparisonSpace C P K),
      ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (b a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P' := by
  intro C P K
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  let H := fourRefinementBasisBudget (Q + coefficientFourHeightBudget P')
  let A := Q + H
  have hH : 0 ≤ H := fourRefinementBasisBudget_nonneg
    (add_nonneg hQ (coefficientFourHeightBudget_nonneg hP'))
  have hA : 0 ≤ A := add_nonneg hQ hH
  have hQA : Q ≤ A := le_add_of_nonneg_right hH
  have hHA : H ≤ A := le_add_of_nonneg_left hQ
  obtain ⟨k, hk⟩ := D.exists_correlation_refined_basis E T hbQ hT F V g hg D' hs hP' hQP' d
  obtain ⟨b, hb⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  obtain ⟨c, hc⟩ := exists_firstProjection_basis_logHeight E.basis _ k
    (fun a i => (hk a i).trans hHA)
  obtain ⟨p, hp⟩ := exists_fourPetalSpace_basis_logHeight E.basis _ _ b k hA
    (by simpa only [Fintype.card_fin] using hT.1.1.trans hQA)
    (fun a i => (hb a i).trans hQA) (fun a i => (hk a i).trans hHA)
  have hK : ∃ k : Basis (Fin (finrank ℚ K)) ℚ K,
      ∀ a i, rationalLogHeight (E.basis.repr (k a : D.CoefficientFreeLieAlgebra) i) ≤ Q := by
    exact T.exists_layer_basis_of_eq hT ⟨d.val + 1, by omega⟩ ⟨2, by omega⟩ K
      (congrArg (fun T => T.layer (d.val + 1) 2) hTfil)
  obtain ⟨k₂, hk₂⟩ := hK
  have hpre : 0 ≤ preimageBasisBudget (4 * A) := preimageBasisBudget_nonneg (by positivity)
  have hAL : A ≤ sharedFreeComparisonBasisBudget Q P' := le_add_of_nonneg_right hpre
  have hPL : preimageBasisBudget (4 * A) ≤ sharedFreeComparisonBasisBudget Q P' :=
    le_add_of_nonneg_left hA
  exact exists_petalComparisonSpace_basis_logHeight E.basis C P K c p k₂
    (add_nonneg hA hpre) (fun a i => (hc a i).trans hAL) (fun a i => (hp a i).trans hPL)
    (fun a i => (hk₂ a i).trans (hQA.trans hAL))

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F in
theorem exists_comparisonCoefficientBases
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    ∃ B : ∀ d : Fin s, Basis (Fin (finrank ℚ
        (D.comparisonCoefficientSpace E T hbQ hT V g hg D' d))) ℚ
        (D.comparisonCoefficientSpace E T hbQ hT V g hg D' d),
      ∀ d a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B d a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P' := by
  classical
  choose B hB using fun d => D.exists_sharedFreeComparisonSpace_basis E T hbQ hT F V g hg D'
    hTfil hs hP' hQP' d
  exact ⟨B, hB⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeFrozenComparison
namespace OAI

section

namespace Erdos3.SubspaceFreeLift

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_uniform_lower_pair_model {L I : Type} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure (r + 1))
    (S : Fin s → Submodule ℚ (Fin 2 → L))
    (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
    (hS : ∀ j, S j ≤ (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration.layer (j.val + 1) 0)
    {p : ℝ} (hp : 2 ≤ p) (hT : T.ComplexityLE p)
    (hB : ∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => D.basis)).repr
      (B j a : Fin 2 → L) i) ≤ p)
    (V : D.UnitVerticalObservable (T.realSubgroup s (r + 1)) I p)
    (hzero : ∀ x ∈ (filtration S T.filtration.rank_le_degree).layer s (r + 1),
      pairDifferenceFunctional V.frequency
        (evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS x) = 0) :
    let pM := (p + nativePairModelConstant s) ^ nativePairModelConstant s
    let φ := evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS
    ∃ M : RationalFilteredNilmanifold (Algebra S (r + 1)) s (finrank ℚ (Algebra S (r + 1))),
      ∃ U : M.DegreeRankStructure (r + 1),
        U.filtration = filtration S T.filtration.rank_le_degree ∧ U.ComplexityLE pM ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S (r + 1))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S (r + 1)) :=
           IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 M.basis
         ∃ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1)) (I × I) pM,
           (∀ i x, Z.observable i (QuotientGroup.mk x) =
             V.pairedObservable T i (QuotientGroup.mk (realificationMap
               (hnil := M.filtration.lowerCentralSeries_eq_bot)
               (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ x))) ∧
           M.HasUniformLowerRankUnitFamily U Z.observable (fun _ : Unit => 1)
             (nativeLowerPairModelBudget s p)) := by
  intro pM φ
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fin 2 → L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (Pi.basis (fun _ : Fin 2 => D.basis))
  obtain ⟨M, U, hU, hUc, _, _, _, _, hZ⟩ :=
    (exists_native_pair_model.{0, 0} s).choose_spec.2 L I (r + 1) d D T S B hS p hp hT hB V
  refine ⟨M, U, hU, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hfreq, hobs⟩ := hZ
  refine ⟨Z, hobs, ?_⟩
  have hZzero : ∀ x ∈ U.filtration.layer s (r + 1), Z.frequency x = 0 := by
    intro x hx
    rw [hfreq]
    exact hzero x (by simpa only [hU] using hx)
  exact UnitVerticalObservable.hasUniformLowerRankUnitFamily M U Z (fun _ : Unit => 1)
    ((Nat.cast_nonneg _).trans hUc.1.1) hUc hZzero

end Erdos3.SubspaceFreeLift

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedPairPolynomial
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixedPairNiltest_symbol {ι : Type*}
    (b : Module.Basis ι ℚ V.MixedPairAlgebra) (w : ι → ℕ)
    (hF : ∀ k, (pi V.mixedPairModels).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ w a})) :
    V.mixedPairNiltest.symbol b w hF =
      (pi V.mixedPairModels).filtration.realPolynomialSymbolHom b w hF
        (fun _ : Fin (n + 2) => 1) V.mixedPairPolynomial := rfl

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairFrozenEquivalence
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {n m : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixedOriginalPairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.mixedOriginalPairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) :=
  piNiltest_complexity V.mixedPairModels (V.mixedOriginalPairComparisonTests a b) _ _ _

theorem mixedOriginalPairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.mixedPairModels).Space) :
    (V.mixedOriginalPairComparisonNiltest a b).observable x =
      W.vertical.observable a (productProjection V.mixedPairModels (some 0) x) *
        star (W.vertical.observable b (productProjection V.mixedPairModels (some 1) x)) := by
  change (∏ k, (V.mixedOriginalPairComparisonTests a b k).observable
    (productProjection V.mixedPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (W.vertical.observable a
    (productProjection V.mixedPairModels (some 0) x) *
      star (W.vertical.observable b (productProjection V.mixedPairModels (some 1) x))) = _
  exact one_mul _

end NativeSampleCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPreciseSampledExchange
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem select_mixed_pointwise_partition {b c : ℝ}
    (hlocal : R.HasMixedPairLocalApproximation b) (hred : R.HasMixedPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin (n + 2) → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin (n + 2) → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence (n + 1) c
            (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ a x, (∀ l, x l ∉ B) → 0 < A a x →
            ∀ (k : Fin 2) (out : Fin W.outputDim),
              ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) -
                R.mixedPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
                  (fun l => ((x l).val : ℤ))‖ ≤ Real.exp b * ρ := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin (n + 2) → ZMod N) (i : Fin (n + 2)) => ((x i).val : ℤ)
  have hv (x : Fin (n + 2) → ZMod N) (i : Fin (n + 2)) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin (n + 2) → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.mixedPairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro a x hx hax k out
  obtain ⟨hy', hAy⟩ := hy a x hx hax
  obtain ⟨hres, hnear⟩ := hcells a x (y a) hx hy' hax hAy
  exact hmodel (v (y a)) (hv (y a)) k out (v x) ρ hρ (hv x) hres
    (by simpa only [v, Int.cast_natCast] using hnear)

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {B I U : Type*} [Fintype B] [Fintype I]
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)

include hA

theorem normalizedChartSubspaceCoordinates_eval_mem (x : U → ℝ) :
    (fun b => MvPolynomial.eval x (A b)) ∈ K := by
  let P := ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A
  let Q := restrictCoefficients K P (normalizedChart_coefficients_mem K A hA)
  have heval : (eval (V := K) x Q : B → ℝ) = eval x P :=
    eval_restrictCoefficients K P (normalizedChart_coefficients_mem K A hA) x
  have hcoord : eval x P = fun b => MvPolynomial.eval x (A b) := by
    have h := eval₂_ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A x
    have he : eval₂ x P = eval x P := by
      simpa using (eval₂_algebraMap (S := ℝ) x P)
    rw [he] at h
    simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
      using h
  rw [← hcoord, ← heval]
  exact (eval (V := K) x Q).property

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype B] [Fintype I]

theorem polynomialSubspaceRestriction_normalizedChart
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    polynomialSubspaceRestriction K e
        (aeval (R := ℝ) (normalizedRealPolynomialChart H A) p) =
      aeval (R := ℝ) (normalizedRealPolynomialChart H
        (normalizedChartSubspaceCoordinates K e A hA))
        (polynomialSubspaceRestriction K e p) :=
  normalizedRealPolynomialChart_linear_restriction H A _ _
    (normalizedChartSubspaceCoordinates_reconstruct_C K e A hA) p

theorem normalizedChart_subspace_decomposition
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)
    (p slow rat : MvPolynomial (U ⊕ B) ℝ)
    (h : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) p =
        eval (Sum.elim (fun i => u i / H i)
          (fun i => b i - eval u (A i))) slow + eval (Sum.elim u b) rat) :
    polynomialSubspaceRestriction K e p =
      aeval (R := ℝ) (normalizedRealPolynomialChart H
        (normalizedChartSubspaceCoordinates K e A hA))
        (polynomialSubspaceRestriction K e slow) +
      polynomialSubspaceRestriction K e rat := by
  have he : polynomialSubspaceRestriction K e p =
      polynomialSubspaceRestriction K e
        (aeval (R := ℝ) (normalizedRealPolynomialChart H A) slow + rat) := by
    apply polynomialSubspaceRestriction_eq_of_eval
    intro u b hb
    rw [map_add]
    exact (h u b hb).trans (by
      congr 1
      exact (eval_normalizedRealPolynomialChart_substitution H A u b slow).symm)
  rw [he, map_add, polynomialSubspaceRestriction_normalizedChart]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorSubspaceCorrectionRepresentatives
namespace OAI

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I η α : Type*} [Fintype B] [Fintype I] [Fintype η]

theorem exists_finite_vector_subspace_normalized_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ d, (fun b => (A b).coeff d) ∈ K)
    (P : η → MvPolynomial (U ⊕ B) ℝ)
    (S : Finset ((U ⊕ I) →₀ ℕ)) (bound : ℝ) (hbound : 0 ≤ bound)
    (q : ℕ) (hq : 0 < q)
    (slow rat : α → η → MvPolynomial (U ⊕ B) ℝ) (admissible : α → Prop)
    (hsupport : ∀ a, admissible a → ∀ i,
      (polynomialSubspaceRestriction K e (slow a i)).support ⊆ S ∧
      (polynomialSubspaceRestriction K e (rat a i)).support ⊆ S)
    (hslow : ∀ a, admissible a → ∀ i d,
      |(polynomialSubspaceRestriction K e (slow a i)).coeff d| ≤ bound)
    (hrat : ∀ a, admissible a → ∀ i d,
      ∃ z : ℤ, (polynomialSubspaceRestriction K e (rat a i)).coeff d = (z : ℝ) / q)
    (hidentity : ∀ a, admissible a → ∀ i (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) (P i) =
        eval (Sum.elim (fun j => u j / H j)
          (fun j => b j - eval u (A j))) (slow a i) + eval (Sum.elim u b) (rat a i)) :
    ∃ m : ℕ, m ≤ ((2 * ⌈(q : ℝ) * bound⌉₊ + 3) ^ S.card) ^ Fintype.card η ∧
      ∃ candidate : Fin m → α,
        (∀ j, admissible (candidate j)) ∧
        ∀ a, admissible a → ∃ j, ∀ i,
          polynomialSubspaceRestriction K e (slow (candidate j) i) =
            polynomialSubspaceRestriction K e (slow a i) ∧
          polynomialSubspaceRestriction K e (rat (candidate j) i) =
            polynomialSubspaceRestriction K e (rat a i) := by
  classical
  let restrict : α → η →
      (MvPolynomial (U ⊕ I) ℝ × MvPolynomial (U ⊕ I) ℝ) :=
    fun a i => (polynomialSubspaceRestriction K e (slow a i),
      polynomialSubspaceRestriction K e (rat a i))
  choose n hn c _hc hcover using fun i : η =>
    exists_finite_normalized_real_grid_corrections H hH
      (normalizedChartSubspaceCoordinates K e A hA) S
      (polynomialSubspaceRestriction K e (P i)) bound hbound q hq
  let Index := ∀ i : η, Fin (n i)
  let enum : Index ≃ Fin (Fintype.card Index) := Fintype.equivFin Index
  let family : Fin (Fintype.card Index) → η →
      (MvPolynomial (U ⊕ I) ℝ × MvPolynomial (U ⊕ I) ℝ) :=
    fun j i => c i (enum.symm j i)
  have hcoverage : ∀ a, admissible a → ∃ j, family j = restrict a := by
    intro a ha
    have each (i : η) : ∃ j, c i j = restrict a i := by
      apply hcover i
      refine ⟨(hsupport a ha i).1, (hsupport a ha i).2,
        hslow a ha i, hrat a ha i, ?_⟩
      exact normalizedChart_subspace_decomposition K e H A hA (P i)
        (slow a i) (rat a i) (hidentity a ha i)
    choose indices hi using each
    refine ⟨enum indices, ?_⟩
    funext i
    simpa only [family, Equiv.symm_apply_apply] using hi i
  obtain ⟨m, hm, candidate, hvalid, hcomplete⟩ :=
    exists_finite_fiber_representatives restrict admissible family hcoverage
  refine ⟨m, hm.trans ?_, candidate, hvalid, ?_⟩
  · change Fintype.card (∀ i : η, Fin (n i)) ≤ _
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∏ _i : η, (2 * ⌈(q : ℝ) * bound⌉₊ + 3) ^ S.card :=
        Finset.prod_le_prod' (fun i _ => hn i)
      _ = _ := by simp
  · intro a ha
    obtain ⟨j, hj⟩ := hcomplete a ha
    refine ⟨j, fun i => ?_⟩
    have hi := congrFun hj i
    exact ⟨congrArg Prod.fst hi, congrArg Prod.snd hi⟩

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I η α : Type*} [Fintype U] [Fintype B] [Fintype I] [Fintype η]

theorem exists_finite_primitive_subspace_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ d, (fun b => (A b).coeff d) ∈ K)
    (P : η → MvPolynomial (U ⊕ B) ℝ)
    (s q d : ℕ) (hq : 0 < q) (hd : 0 < d)
    (L M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L)
    (hegrid : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (slow rat : α → η → MvPolynomial (U ⊕ B) ℝ) (admissible : α → Prop)
    (hdegree : ∀ a, admissible a → ∀ i,
      (slow a i).totalDegree ≤ s ∧ (rat a i).totalDegree ≤ s)
    (hcoeff : ∀ a, admissible a → ∀ i ex, |(slow a i).coeff ex| ≤ M)
    (hgrid : ∀ a, admissible a → ∀ i, realPolynomialCoefficientGrid q (rat a i))
    (hidentity : ∀ a, admissible a → ∀ i (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) (P i) =
        eval (Sum.elim (fun j => u j / H j)
          (fun j => b j - eval u (A j))) (slow a i) + eval (Sum.elim u b) (rat a i)) :
    let Rcap := (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
      (max 1 ((Fintype.card I : ℝ) * L)) ^ s
    ∃ m : ℕ,
      m ≤ ((2 * ⌈((q * d ^ s : ℕ) : ℝ) * Rcap⌉₊ + 3) ^
        ((Fintype.card (U ⊕ I) + 1) ^ s)) ^ Fintype.card η ∧
      ∃ candidate : Fin m → α,
        (∀ j, admissible (candidate j)) ∧
        ∀ a, admissible a → ∃ j, ∀ i,
          polynomialSubspaceRestriction K e (slow (candidate j) i) =
            polynomialSubspaceRestriction K e (slow a i) ∧
          polynomialSubspaceRestriction K e (rat (candidate j) i) =
            polynomialSubspaceRestriction K e (rat a i) := by
  classical
  dsimp only
  let Rcap := (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
    (max 1 ((Fintype.card I : ℝ) * L)) ^ s
  have hRcap : 0 ≤ Rcap := mul_nonneg
    (mul_nonneg (pow_nonneg (by positivity) s) hM)
    (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) s)
  obtain ⟨m, hm, candidate, hvalid, hcover⟩ :=
    exists_finite_vector_subspace_normalized_correction_representatives
      K e H hH A hA P (boundedExponentWindow (U ⊕ I) s)
      Rcap hRcap (q * d ^ s) (Nat.mul_pos hq (pow_pos hd s))
      slow rat admissible
      (fun a ha i => ⟨support_subset_boundedExponentWindow _
        ((polynomialSubspaceRestriction_totalDegree_le K e _).trans (hdegree a ha i).1),
        support_subset_boundedExponentWindow _
        ((polynomialSubspaceRestriction_totalDegree_le K e _).trans (hdegree a ha i).2)⟩)
      (fun a ha i ex => polynomialSubspaceRestriction_coeff_le K e (slow a i) hM he
        (hdegree a ha i).1 (hcoeff a ha i) ex)
      (fun a ha i ex => polynomialSubspaceRestriction_coeff_div K e (rat a i)
        q d s hq hd hegrid (hdegree a ha i).2 (hgrid a ha i) ex)
      hidentity
  refine ⟨m, hm.trans ?_, candidate, hvalid, hcover⟩
  apply Nat.pow_le_pow_left
  exact Nat.pow_le_pow_right (by omega)
    (boundedExponentWindow_card_le (U ⊕ I) s)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped BigOperators

variable {U B I η α V : Type*} [Fintype U] [Fintype B] [Fintype I] [Fintype η]
  [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem exists_finite_vector_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K) (basis : Basis η ℝ V)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ ex, (fun b => (A b).coeff ex) ∈ K)
    (P : VectorPolynomial (U ⊕ B) ℚ V)
    (s q d : ℕ) (hq : 0 < q) (hd : 0 < d)
    (L M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L)
    (hegrid : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (slow rat : α → VectorPolynomial (U ⊕ B) ℚ V) (admissible : α → Prop)
    (hdegree : ∀ a, admissible a → ∀ i,
      (coordinate (basis.coord i).toAddMonoidHom (slow a)).totalDegree ≤ s ∧
      (coordinate (basis.coord i).toAddMonoidHom (rat a)).totalDegree ≤ s)
    (hcoeff : ∀ a, admissible a → ∀ i ex, |basis.coord i (coefficients (slow a) ex)| ≤ M)
    (hgrid : ∀ a, admissible a → ∀ ex,
      (fun i => basis.coord i (coefficients (rat a) ex)) ∈ realDenominatorGrid q)
    (hidentity : ∀ a, admissible a → ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval₂ (Sum.elim u b) P =
        eval₂ (Sum.elim u b) (realChartSubstitute (normalizedRealPolynomialChart H A) (slow a)) +
        eval₂ (Sum.elim u b) (rat a)) :
    let Rcap := (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
      (max 1 ((Fintype.card I : ℝ) * L)) ^ s
    ∃ m : ℕ,
      m ≤ ((2 * ⌈((q * d ^ s : ℕ) : ℝ) * Rcap⌉₊ + 3) ^
        ((Fintype.card (U ⊕ I) + 1) ^ s)) ^ Fintype.card η ∧
      ∃ candidate : Fin m → α,
        (∀ j, admissible (candidate j)) ∧
        ∀ a, admissible a → ∃ j, ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
          eval₂ (Sum.elim u b) (slow (candidate j)) = eval₂ (Sum.elim u b) (slow a) ∧
          eval₂ (Sum.elim u b) (rat (candidate j)) = eval₂ (Sum.elim u b) (rat a) ∧
          eval₂ (Sum.elim u b)
              (realChartSubstitute (normalizedRealPolynomialChart H A) (slow (candidate j))) =
            eval₂ (Sum.elim u b)
              (realChartSubstitute (normalizedRealPolynomialChart H A) (slow a)) := by
  let scalar := fun (p : VectorPolynomial (U ⊕ B) ℚ V) i =>
    coordinate (basis.coord i).toAddMonoidHom p
  obtain ⟨m, hm, candidate, hvalid, hcover⟩ :=
    exists_finite_primitive_subspace_correction_representatives K e H hH A hA
      (scalar P) s q d hq hd L M hM he hegrid
      (fun a => scalar (slow a)) (fun a => scalar (rat a)) admissible hdegree
      (fun a ha i ex => by simpa only [scalar, coeff_coordinate,
        LinearMap.toAddMonoidHom_coe] using hcoeff a ha i ex)
      (fun a ha i => coordinate_grid_of_vector_grid basis q (rat a) (hgrid a ha) i)
      (by
        intro a ha i u b hb
        have h := congrArg (basis.coord i) (hidentity a ha u b hb)
        rw [eval₂_normalizedRealPolynomialChart] at h
        simpa only [map_add, coordinate_eval₂] using h)
  refine ⟨m, hm, candidate, hvalid, ?_⟩
  intro a ha
  obtain ⟨j, hj⟩ := hcover a ha
  have heval (t : α → VectorPolynomial (U ⊕ B) ℚ V)
      (ht : ∀ i, polynomialSubspaceRestriction K e (scalar (t (candidate j)) i) =
        polynomialSubspaceRestriction K e (scalar (t a) i))
      (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
      eval₂ (Sum.elim u b) (t (candidate j)) = eval₂ (Sum.elim u b) (t a) := by
    apply basis.repr.injective
    ext i
    change basis.coord i _ = basis.coord i _
    rw [coordinate_eval₂, coordinate_eval₂]
    exact polynomialSubspaceRestriction_eval_eq K e _ _ (ht i) u b hb
  refine ⟨j, ?_⟩
  intro u b hb
  refine ⟨heval slow (fun i => (hj i).1) u b hb,
    heval rat (fun i => (hj i).2) u b hb, ?_⟩
  rw [eval₂_normalizedRealPolynomialChart, eval₂_normalizedRealPolynomialChart]
  exact heval slow (fun i => (hj i).1) _ _
    (K.sub_mem hb (normalizedChartSubspaceCoordinates_eval_mem K A hA u))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullChartPolynomialLiftControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators

variable {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem degreeLE_weightedDegreeTruncate (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) : DegreeLE w d (weightedDegreeTruncate w d p) := by
  intro α hα
  rw [coefficients_weightedDegreeTruncate, if_neg (not_le_of_gt hα)]

theorem degreeLE_one_weightedDegreeTruncate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE (fun _ => 1) d (weightedDegreeTruncate w d p) := by
  intro α hα
  apply degreeLE_weightedDegreeTruncate w d p α
  have h := exponentSum_le_positive_weight w hw α
  have he : Finsupp.weight (fun _ : σ => 1) α = α.sum (fun _ n => n) := by
    simp [Finsupp.weight_apply]
  rw [he] at hα
  exact hα.trans_le h

section Bounds
variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem CoefficientBound.weightedDegreeTruncate (b : Basis ι ℝ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    {p : VectorPolynomial σ ℚ L} (hp : CoefficientBound b T M p)
    (w : σ → ℕ) (d : ℕ) : CoefficientBound b T M (weightedDegreeTruncate w d p) := by
  intro α i
  rw [coefficients_weightedDegreeTruncate]
  split_ifs
  · exact hp α i
  · simp only [map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le
end Bounds

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeQuotientPolynomial realSymbolGradeEvaluation restrictedMajorCorrection

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

theorem exists_full_chart_finite_stage_representatives [Fintype X]
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ))
    (p : ℝ) (blocks a : ℕ) (ha : 254 ≤ a)
    (hcert : RationalTaggedConstraintCertificate J Set.univ K' p blocks)
    (hp : 0 ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p) (hblocks : (blocks : ℝ) ≤ p)
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ Utag j) → point ∈ K')
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) (hq : 0 < q)
    (hqcap : (q : ℝ) ≤ Real.exp ((p + a) ^ a))
    (hbudget : budget ≤ (p + a) ^ a) :
    ∃ count : ℕ, (count : ℝ) ≤
        Real.exp ((p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin count →
        (VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal ×
          VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal),
        (∀ j, FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
          Z left right K₀ Utag poly N budget q K' (candidate j)) ∧
        ∀ pair, FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
          Z left right K₀ Utag poly N budget q K' pair →
          ∃ j, ∀ t ∈ K',
            eval₂ t (candidate j).1 = eval₂ t pair.1 ∧
            eval₂ t (candidate j).2 = eval₂ t pair.2 ∧
            eval₂ t (realChartSubstitute chart (candidate j).1) =
              eval₂ t (realChartSubstitute chart pair.1) := by
  obtain ⟨n, Kbase, e, matrix, d, _, hdim, _, _, _, _, he, _, hd, hdCap, hegrid, hset, hret⟩ :=
    hcert.exists_certified_chart_basis_budget hp hJ hblocks
  let L := Real.exp (((p + 2) ^ 2 + 2) ^ 63)
  let M := Real.exp budget
  let admissible := FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
    Z left right K₀ Utag poly N budget q K'
  have hA := fullTaggedMajorTopCoordinates_coefficients_mem J poly Utag hpoly Kbase
    (hret Utag hretained)
  have hdegree : ∀ pair, admissible pair → ∀ i,
      (coordinate (basis.coord i).toAddMonoidHom pair.1).totalDegree ≤ k ∧
      (coordinate (basis.coord i).toAddMonoidHom pair.2).totalDegree ≤ k := by
    intro pair h i
    unfold admissible FullChartAdmissibleStageCorrection at h
    exact ⟨h.2.2.1 i, h.2.2.2.1 i⟩
  have hcap : ∀ pair, admissible pair → ∀ i ex,
      |basis.coord i (coefficients pair.1 ex)| ≤ M := by
    intro pair h i ex
    unfold admissible FullChartAdmissibleStageCorrection at h
    exact h.2.2.2.2.2.2.2.2.2.1 ex i
  have hgrid : ∀ pair, admissible pair → ∀ ex,
      (fun i => basis.coord i (coefficients pair.2 ex)) ∈ realDenominatorGrid q := by
    intro pair h ex
    unfold admissible FullChartAdmissibleStageCorrection at h
    exact h.2.2.2.2.2.2.2.2.2.2.1 ex
  have hidentity : ∀ pair, admissible pair → ∀ (u : X → ℝ) (v : (Σ j, J j) → ℝ),
      v ∈ Kbase → eval₂ (Sum.elim u v)
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ (Sum.elim u v) (realChartSubstitute chart pair.1) + eval₂ (Sum.elim u v) pair.2 := by
    intro pair h u v hv
    unfold admissible FullChartAdmissibleStageCorrection at h
    have ht : Sum.elim u v ∈ K' := by
      rw [hset]
      exact hv
    with_reducible exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (Sum.elim u v) ht
  obtain ⟨count, hcount, candidate, hvalid, hcover⟩ := exists_finite_vector_correction_representatives
    Kbase e basis (fun i => (N i : ℝ)) (fun i => by exact_mod_cast hN i)
    (fullTaggedMajorTopCoordinates J poly) hA
    (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord)
    k q d hq hd L M (Real.exp_nonneg budget) he hegrid
    Prod.fst Prod.snd admissible hdegree hcap hgrid hidentity
  refine ⟨count, ?_, candidate, hvalid, ?_⟩
  · have hI : (Fintype.card (Σ j, Fin (n j)) : ℝ) ≤ p :=
      (Nat.cast_le.mpr hdim).trans hJ
    have henvelope := certified_basis_envelope hp ha
    have hcountbudget :=
      (Classical.choose_spec (exists_finite_primitive_correction_budget k a)).2
        (Fintype.card X) (Fintype.card (Σ j, J j)) (Fintype.card (Σ j, Fin (n j)))
        (Fintype.card η) q d p L M hp hX hJ hI hη hqcap
        (hdCap.trans henvelope.2) henvelope.1 (Real.exp_nonneg budget)
        (Real.exp_le_exp.mpr hbudget)
    apply (Nat.cast_le.mpr hcount).trans
    simpa only [Fintype.card_sum, fullChartStageCountConstant] using hcountbudget
  · with_reducible
      exact vector_correction_cover_on_set (V := quotientReal) Kbase K' hset Prod.fst Prod.snd
        (fun pair => realChartSubstitute chart pair.1) admissible candidate hcover

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection
  realSymbolGradeQuotientPolynomial CertifiedFullChartFiniteHistory.outer
  FullChartControlledFactors

namespace CertifiedFullChartFiniteHistory
variable {X ι η L : Type} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s m : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}

  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Kinitial : Set (X ⊕ (Σ j, J j) → ℝ)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

theorem terminal_mem_fast
    (history : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift
      Z Kinitial Utag poly N Bphase s)
    (hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast) :
    ∀ t ∈ history.K,
      eval₂ t (F.realGradedSymbolPolynomial b ω hF (fullTaggedVariableWeight J)
        (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.baseChange ℝ := by
  intro t ht
  apply (F.restricted_symbol_grade_terminal b ω hF (fullTaggedVariableWeight J)
    fast hfast _ t).mpr
  with_reducible exact history.invariant_outer t ht

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeQuotientPolynomial realSymbolGradeEvaluation restrictedMajorCorrection
  fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (budget : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "Good" => FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
  Z left right K₀ Utag poly N budget

theorem exists_full_chart_optional_stage_branch
    (q : ℕ) (K' : Set Point) (p : ℝ) (blocks a : ℕ) (ha : 254 ≤ a)
    (hcert : RationalTaggedConstraintCertificate J Set.univ K' p blocks)
    (hp : 0 ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p) (hblocks : (blocks : ℝ) ≤ p)
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ Utag j) → point ∈ K₀)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) (hq : 0 < q)
    (hqcap : (q : ℝ) ≤ Real.exp ((p + a) ^ a)) (hbudget : budget ≤ (p + a) ^ a) :
    ∃ c : ℕ, (c : ℝ) ≤ Real.exp
        ((p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin c → VP × VP, (∀ j, Good q K' (candidate j)) ∧
        ∀ pair, Good q K' pair → ∃ j, ∀ t ∈ K',
          eval₂ t (candidate j).1 = eval₂ t pair.1 ∧
          eval₂ t (candidate j).2 = eval₂ t pair.2 ∧
          eval₂ t (realChartSubstitute chart (candidate j).1) =
            eval₂ t (realChartSubstitute chart pair.1) := by
  by_cases hex : ∃ pair, Good q K' pair
  · obtain ⟨pair, hpair⟩ := hex
    have hret : ∀ point, (∀ j, (fun z => point (Sum.inr ⟨j, z⟩)) ∈ Utag j) →
        point ∈ K' := by
      unfold FullChartAdmissibleStageCorrection at hpair
      rcases hpair with ⟨_, _, _, _, _, _, _, _, hretain, _⟩
      intro point hpoint
      exact hretain point (hretained point hpoint) hpoint
    exact exists_full_chart_finite_stage_representatives F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget q K' p blocks a ha hcert hp hX hJ hη hblocks
      hret hpoly hN hq hqcap hbudget
  · refine ⟨0, by simpa using Real.exp_nonneg _, Fin.elim0, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · intro pair hpair; exact (hex ⟨pair, hpair⟩).elim

theorem exists_full_chart_finite_stage_branches
    {past p : ℝ} {blocks : ℕ}
    (a : ℕ) (ha : 254 ≤ a)
    (hprevious : RationalTaggedConstraintCertificate J Set.univ K₀ past blocks)
    (hp : 0 ≤ p) (hpast : past ≤ p) (hbudget : budget ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (hblocks : ((blocks + Fintype.card η * m : ℕ) : ℝ) ≤ p)
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ Utag j) → point ∈ K₀)
    (hpoly : ∀ j ex, ex ≠ 0 → coefficients (poly j) ex ∈ Utag j)
    (hN : ∀ i, 1 ≤ N i) :
    ∃ count : ℕ, (count : ℝ) ≤ Real.exp
        ((Fintype.card η : ℝ) * budget + (p + 8) ^ 8 +
          (p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin count → (ℕ × Set Point) × (VP × VP),
        (∀ i, Good (candidate i).1.1 (candidate i).1.2 (candidate i).2) ∧
        ∀ q K' pair, Good q K' pair → ∃ i,
          (candidate i).1 = (q, K') ∧ ∀ t ∈ K',
            eval₂ t (candidate i).2.1 = eval₂ t pair.1 ∧
            eval₂ t (candidate i).2.2 = eval₂ t pair.2 ∧
            eval₂ t (realChartSubstitute chart (candidate i).2.1) =
              eval₂ t (realChartSubstitute chart pair.1) := by
  obtain ⟨n, hn, branches, hbranches, hcover⟩ :=
    exists_fullChart_admissible_stage_branches F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget hprevious hp hpast hbudget hm hJ hblocks
  let validLabel := fun (l : ℕ × Set Point) (pair : VP × VP) => Good l.1 l.2 pair
  let relLabel := fun (l : ℕ × Set Point) (pair pair' : VP × VP) => ∀ t ∈ l.2,
    eval₂ t pair.1 = eval₂ t pair'.1 ∧ eval₂ t pair.2 = eval₂ t pair'.2 ∧
    eval₂ t (realChartSubstitute chart pair.1) = eval₂ t (realChartSubstitute chart pair'.1)
  let valid := fun i => validLabel (branches i)
  let rel := fun i => relLabel (branches i)
  have hnum := stage_branch_numeric hp hη hbudget ha
  have hbranch : ∀ i : Fin n, ∃ c : ℕ,
      (c : ℝ) ≤ Real.exp ((p + fullChartStageCountConstant k a) ^ fullChartStageCountConstant k a) ∧
      ∃ candidate : Fin c → VP × VP, (∀ j, valid i (candidate j)) ∧
        ∀ pair, valid i pair → ∃ j, rel i (candidate j) pair := by
    intro i
    dsimp only [valid, rel, validLabel, relLabel]
    exact exists_full_chart_optional_stage_branch F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget (branches i).1 (branches i).2
      p (blocks + Fintype.card η * m) a ha (hbranches i).2.2 hp hX hJ hη hblocks
      hretained hpoly hN (hbranches i).1
      (((Nat.cast_le.mpr (hbranches i).2.1).trans (Nat.floor_le (Real.exp_nonneg _))).trans
        (Real.exp_le_exp.mpr hnum.1)) hnum.2
  obtain ⟨count, hcount, candidate, hvalid, hcomplete⟩ :=
    exists_finite_classified_representatives branches validLabel relLabel
      (fun l pair => hcover l.1 l.2 pair) hbranch
  refine ⟨count, ?_, candidate, hvalid, fun q K' pair => hcomplete (q, K') pair⟩
  exact (hcount.trans (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _))).trans_eq
    (Real.exp_add _ _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartForwardEarlyTree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

theorem stageBranchLog_mono (dim n : ℕ) (cap : ℝ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) : stageBranchLog dim n cap p ≤ stageBranchLog dim n cap q := by
  unfold stageBranchLog
  have hfirst : (p + 8) ^ 8 ≤ (q + 8) ^ 8 := by gcongr
  have hlast : (p + fullChartStageCountConstant (n + 1) 254) ^
      fullChartStageCountConstant (n + 1) 254 ≤
      (q + fullChartStageCountConstant (n + 1) 254) ^
        fullChartStageCountConstant (n + 1) 254 := by gcongr
  exact add_le_add (add_le_add le_rfl hfirst) hlast

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type} (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)

theorem majorPhaseNearestLift_close (u : X → ℤ)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) - c i -
      (majorPhaseNearestLift J k poly c u i : ℝ)| ≤ 1 / 2 :=
  by
    unfold majorPhaseNearestLift
    exact nearestIntegerLift_close
      (fun j => MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly j) - c j) i

noncomputable def majorPhasePlateauSignal
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ) (u : X → ℤ) : ℂ :=
  majorPhaseSample J k poly (majorPhasePlateauKernel _) c P
    (majorPhaseNearestLift J k poly c) (fun _ => 1) u

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local instance retainedReferencePrimeNeZero : ∀ p : path.primes, NeZero p.val :=
  path.primeNeZero

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end


