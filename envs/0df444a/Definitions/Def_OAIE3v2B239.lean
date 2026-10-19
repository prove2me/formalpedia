-- Prove2me | Definitions.Def_OAIE3v2B239
-- name    : OAIE3v2B239
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:12:39.828745+00:00
-- url     : https://prove2.me/theorems/4143817b-dbf5-481d-b639-88f8538a8a24
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 244 of 311
-- statement:
--   Definitions bundle 244 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B220`, `OAIE3v2B221`, `OAIE3v2B222`, `OAIE3v2B223`, `OAIE3v2B224` of this split.
--
--   Modules: `Estimates/BoundedNativeDependentApproximations.lean`, `Estimates/CommonDependentIntegralModel.lean`, `Estimates/CommonDependentWordLayers.lean`, `Estimates/CommonFreeSunflower.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/NativeGlobalErrorSplitting.lean`, `Estimates/NativeMultilinearQuadruples.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/NativeSharedFreeFamily.lean`, `Geometry/CommonNativeCoordinateCorrections.lean`, `Geometry/NativeCoordinateErrorReduction.lean`, `Lattices/NativeRetainedIntegerMultilinearQuadruples.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/CommonRealDependentProjection.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/RankOrbitCoefficientCorrections.lean`, `Nilpotent/CoordinateNiltestSplitting.lean`, `Polynomial/CommonAnchorPolynomialCorrections.lean`, `Polynomial/NativeFreePolynomialLifts.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B220
import Definitions.Def_OAIE3v2B221
import Definitions.Def_OAIE3v2B222
import Definitions.Def_OAIE3v2B223
import Definitions.Def_OAIE3v2B224

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem normalizedLower_norm {b : ℝ} (hpb : p ≤ b) (h x : ZMod N) :
    ‖W.normalizedLower b h x‖ ≤ 1 := by
  by_cases hh : h ∈ W.shifts
  · rw [W.normalizedLower_of_mem b h hh]
    exact (((W.selectedWitness ⟨h, hh⟩).test.expNormalize b).norm_evalCyclic_le N _).trans
      ((W.selectedWitness ⟨h, hh⟩).test.expNormalize_norm
        ((W.selectedWitness ⟨h, hh⟩).complexity.mono hpb))
  · simp only [normalizedLower, dif_neg hh, norm_zero, zero_le_one]

end Erdos3.NativeCorrelationStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeGlobalErrorSplitting
namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem normalizedErrorCorrelator_norm {b : ℝ} (hpb : p ≤ b)
    (hf : ∀ x, ‖f x‖ ≤ 1) (m : ZMod N → ZMod N → ℂ) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (h x : ZMod N) : ‖W.normalizedErrorCorrelator b m h x‖ ≤ 1 := by
  simp only [normalizedErrorCorrelator, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (multiplicativeDerivative_norm_le_one f hf h x)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hm h x)).trans
        (W.normalizedLower_norm hpb h x))

theorem normalizedErrorCorrelator_correlation {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d}
    (T : D.Niltest (fun _ : Fin 2 => 1)) (b : ℝ) (m : ZMod N → ZMod N → ℂ)
    (h : ZMod N) (hh : h ∈ W.shifts)
    (hcorr : Real.exp (-b) ≤ ‖𝔼 x, multiplicativeDerivative f h x * star
      (m h x * (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
        T.eval ![(h.val : ℤ), (x.val : ℤ)])‖) :
    Real.exp (-(3 * b)) ≤ ‖𝔼 x, W.normalizedErrorCorrelator b m h x *
      star ((T.expNormalize b).eval ![(h.val : ℤ), (x.val : ℤ)])‖ := by
  have hc : (Real.exp (-(2 * b)) : ℂ) = (Real.exp (-b) : ℂ) * (Real.exp (-b) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring_nf
  have hmean : (𝔼 x, W.normalizedErrorCorrelator b m h x *
        star ((T.expNormalize b).eval ![(h.val : ℤ), (x.val : ℤ)])) =
      (Real.exp (-(2 * b)) : ℂ) * (𝔼 x, multiplicativeDerivative f h x * star
        (m h x * (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
          T.eval ![(h.val : ℤ), (x.val : ℤ)])) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    rw [normalizedErrorCorrelator, W.normalizedLower_of_mem b h hh]
    simp only [RationalFilteredNilmanifold.Niltest.expNormalize,
      RationalFilteredNilmanifold.Niltest.scaleComplex_eval,
      RationalFilteredNilmanifold.Niltest.scaleComplex_evalCyclic, hc,
      star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ = Real.exp (-(2 * b)) * Real.exp (-b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff
  NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem absorb_split_term {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s r N p f)
    {d : ℕ} {B epsilon : ℝ} {u : (Fin 2 → ℤ) → ℂ}
    (R : NativeTwoVariableSplit s d B epsilon u) (j : Fin R.count)
    (m : ZMod N → ZMod N → ℂ) (weight : ZMod N → ℂ)
    (h : ZMod N) (hmem : h ∈ W.shifts) {b F Q : ℝ}
    (hpb : p ≤ b) (hbQ : b ≤ Q) (hFQ : F ≤ Q)
    (E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) F
      (fun x => (R.test true j).eval ![(h.val : ℤ), x ()]))
    (hfirst : ∀ x : ZMod N, (R.test false j).eval ![(h.val : ℤ), (x.val : ℤ)] = weight x)
    (hcorr : Real.exp (-Q) ≤
      ‖𝔼 x, W.normalizedErrorCorrelator b m h x * star
        ((R.test false j).eval ![(h.val : ℤ), (x.val : ℤ)] *
          (R.test true j).eval ![(h.val : ℤ), (x.val : ℤ)])‖) :
    Nonempty (NativeVectorCorrelation (s - 1) N (productNiltestBudget (3 * Q + 4))
      (fun _ : Unit => fun x => multiplicativeDerivative f h x * star (m h x * weight x))) := by
  let U := (W.selectedWitness ⟨h, hmem⟩).test.expNormalize b
  have hU : U.ComplexityLE b :=
    (W.selectedWitness ⟨h, hmem⟩).test.expNormalize_complexity
      ((W.selectedWitness ⟨h, hmem⟩).complexity.mono hpb)
  let g (_ : Unit) (x : ZMod N) := multiplicativeDerivative f h x * star (m h x * weight x)
  let Z : NativeVectorCorrelation (s - 1) N Q
      (fun z : Unit => fun x => g z x * star ((R.test true j).eval ![(h.val : ℤ), (x.val : ℤ)])) := {
    L := (W.selectedWitness ⟨h, hmem⟩).L
    dim := (W.selectedWitness ⟨h, hmem⟩).dim
    model := (W.selectedWitness ⟨h, hmem⟩).model
    test := U
    complexity := hU.mono hbQ
    coordinate := ()
    correlation := by
      simpa only [g, normalizedErrorCorrelator,
        W.normalizedLower_of_mem b h hmem, hfirst, U, star_mul,
        mul_assoc, mul_left_comm, mul_comm] using hcorr }
  exact ((E.toCyclic N).mono hFQ).absorb_correlation g Z

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff
  NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_split_global_error (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ GlobalErrorSplittingStatement s C := by
  obtain ⟨a, _, hsplit⟩ := exists_totalDegree_niltest_splitting s 2
  obtain ⟨c, _, hfreeze⟩ := NativeTwoVariableSplit.exists_second_expansion_budget s
  obtain ⟨C, hC, hbudget⟩ := exists_global_error_budget a c
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W L _ _ _ _ _ _ d D T b hb hpb hT H hsub hH m hm hf hcorr
  have hb0 : 0 ≤ b := by linarith only [hb]
  let B := (b + a) ^ a
  let F := (B + c) ^ c
  let Q := 3 * b + B + F + 3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hbQ : b ≤ Q := by dsimp [Q]; linarith only [hb0, hB, hF]
  have hFQ : F ≤ Q := by dsimp [Q]; linarith only [hb0, hB]
  have hcQ : 3 * b + B + 1 ≤ Q := by dsimp [Q]; linarith only [hF]
  have hcostB : B ≤ (b + C) ^ C := (hbudget b hb0).1
  have hcost : productNiltestBudget (3 * Q + 4) ≤ (b + C) ^ C := (hbudget b hb0).2
  let epsilon := Real.exp (-(3 * b + 1))
  have hscale : 1 / epsilon ≤ Real.exp ((b + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [hb0, sq_nonneg b]
  have hR : Nonempty (NativeTwoVariableSplit s d B epsilon (T.expNormalize b).eval) :=
    hsplit (T.expNormalize b) (T.expNormalize_complexity hT)
      (T.expNormalize_norm hT) epsilon (Real.exp_pos _) hscale
  obtain ⟨R⟩ := hR
  have hepsilon : epsilon ≤ Real.exp (-(3 * b)) / 2 := by
    simpa only [epsilon, show -(3 * b + 1) = -(3 * b) - 1 by ring] using
      exp_sub_one_le_half_exp (-(3 * b))
  obtain ⟨j, S, hSH, hS, hsize, hterm⟩ := R.exists_fixed_correlating_term H hH
    (fun (h x : ZMod N) => ![(h.val : ℤ), (x.val : ℤ)]) (W.normalizedErrorCorrelator b m)
    (Real.exp_pos _) hepsilon
    (fun h _ x => W.normalizedErrorCorrelator_norm hpb hf m hm h x)
    (fun h hh => W.normalizedErrorCorrelator_correlation T b m h (hsub hh) (hcorr h hh))
  let weight (x : ZMod N) := (R.test false j).eval ![0, (x.val : ℤ)]
  have hweight (x : ZMod N) : ‖weight x‖ ≤ 1 :=
    ((R.test false j).norm_eval_le _).trans
      (show ((R.test false j).normBound : ℝ) ≤ 1 from R.test_norm false j)
  have hfirst (h x : ZMod N) :
      (R.test false j).eval ![(h.val : ℤ), (x.val : ℤ)] = weight x :=
    R.first_eval_eq j _ _ rfl
  have hsmall : Real.exp (-(3 * b + B + 1)) ≤ Real.exp (-(3 * b)) / (2 * Real.exp B) := by
    calc
      _ = Real.exp (-(3 * b + B) - 1) := by congr 1; ring
      _ ≤ Real.exp (-(3 * b + B)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [show -(3 * b + B) = -(3 * b) - B by ring, Real.exp_sub]; ring
  refine ⟨weight, S, hweight, hSH, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcostB))
      (Nat.cast_nonneg H.card)).trans hsize
  · intro h hh
    let hmem : h ∈ W.shifts := hsub (hSH hh)
    have hE : ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) F
        (fun x => (R.test true j).eval ![(h.val : ℤ), x ()]), E.count = 1 :=
      hfreeze R j (h.val : ℤ)
    obtain ⟨E, _⟩ := hE
    have hz := (Real.exp_le_exp.mpr (neg_le_neg hcQ)).trans (hsmall.trans (hterm h hh))
    obtain ⟨V⟩ := W.absorb_split_term R j m weight h hmem hpb hbQ hFQ E (hfirst h) hz
    exact ⟨V.mono hcost⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CoordinateNiltestSplitting
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial RationalFilteredNilmanifold
open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators NNReal

theorem exists_coordinate_niltest_splitting (σ : Type) [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (i : σ) {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : σ => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ a) →
      Nonempty (NativeCoordinateSplit i s d ((p + C) ^ C) epsilon T.eval) := by
  obtain ⟨C, hC, hsplit⟩ := exists_two_downset_splitting s (Fintype.card σ * s) a
  refine ⟨C, hC, ?_⟩
  intro i L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  classical
  let M := D.totalDegreeMultidegree σ hT.1
  let J := coordinateSplitDownset s i
  have hJ : ∀ b, IsLowerSet (J b) := coordinateSplitDownset_lower s i
  let K := fun b => M.filtration.positivePolynomialAlgebra ⧸
    restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra (J b) (hJ b)
  let : ∀ b, TopologicalSpace (ℝ ⊗[ℚ] K b) := fun _ => moduleTopology ℝ _
  let : ∀ b, IsTopologicalAddGroup (ℝ ⊗[ℚ] K b) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ b, T2Space (ℝ ⊗[ℚ] K b) :=
    fun b => realification_moduleTopology_t2 (M.positivePolynomialDownsetFinBasis (J b) (hJ b) p)
  let g := D.filtration.realTotalDegreeOrbit T.orbit
  have hsum : (∑ _ : σ, s) = Fintype.card σ * s := by simp
  have hM : M.ComplexityLE p := D.totalDegreeMultidegree_complexity σ hT.1
  have hcover : ∀ c, c ≠ 0 → c ∉ J false ∪ J true →
      M.filtration.layer (fun j => c j) = ⊥ :=
    fun c _ hc => coordinateSplitDownset_terminal D.filtration i c hc
  obtain ⟨r, _, _, B, hB, hstable, hresult⟩ :=
    hsplit M J hJ p hsum hM hcover g epsilon hepsilon hscale
  obtain ⟨hE, hdim, hterminal, h, _, happrox⟩ := hresult
  have hlip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hb := T.observable_budget hT
    have hn := T.normBound.coe_nonneg
    linarith
  have hub : ∀ x, ‖T.observable x‖ ≤ 1 := fun x =>
    (T.norm_le x).trans (show (T.normBound : ℝ) ≤ 1 from hnorm)
  obtain ⟨N, hN, hNbound, A, B', hAnorm, hBnorm, hA, hB', hAg, hBg, herr⟩ :=
    happrox T.observable T.lipBound hlip T.lipschitz hub
  let E := fun b => M.positivePolynomialDownsetModel (J b) (hJ b) r B hB hstable
  let F := fun b => M.positivePolynomialDownsetModelMultidegree (J b) (hJ b) r B hB hstable
  have hzero (b : Bool) (v : σ → ℕ) (hv : ¬v ≤ coordinateSplitBound s i b) :
      (F b).filtration.layer v = ⊥ := by
    let c : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm v
    exact hterminal b c hv
  let R := fun b => (F b).restrictBound (coordinateSplitBound s i b)
    (coordinateSplitBound_le s i b) (hzero b)
  let tests : ∀ b, Fin N → (E b).Niltest (fun _ : σ => 1) :=
    fun b => match b with
      | false => A
      | true => B'
  refine ⟨{
    count := N
    count_pos := hN
    count_bound := hNbound
    L := K
    dim := fun b => Fintype.card (M.PositivePolynomialDownsetIndex (J b))
    model := E
    multi := R
    complexity := fun b => (F b).restrictBound_complexity (coordinateSplitBound s i b)
      (coordinateSplitBound_le s i b) (hzero b) (hE b)
    dimension_bound := hdim
    orbit := fun b => (F b).filtration.restrictBoundRealOrbit (coordinateSplitBound s i b)
      (hzero b) (M.filtration.positivePolynomialDownsetOrbit (J b) (hJ b) h)
    test := tests
    test_norm := ?_
    test_complexity := ?_
    test_orbit := ?_
    approximation := ?_ }⟩
  · intro b j
    cases b
    · exact hAnorm j
    · exact hBnorm j
  · intro b j
    cases b
    · exact hA j
    · exact hB' j
  · intro b j
    cases b
    · exact hAg j
    · exact hBg j
  · intro x
    change ‖T.eval x - ∑ j, (A j).eval x * (B' j).eval x‖ ≤ epsilon
    have heval : T.observable (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g)) =
        T.eval x := by
      change T.observable (QuotientGroup.mk
        ((D.filtration.totalDegreeMultifiltration σ).realification.polynomialOrbitEval x
          (D.filtration.realTotalDegreeOrbit T.orbit))) = _
      rw [D.filtration.realTotalDegreeOrbit_eval]
      rfl
    simpa only [heval] using herr x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateErrorReduction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

theorem exists_coordinate_error_reduction (σ : Type) [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (s : ℕ) : ∃ C : ℕ, 2 ≤ C ∧ CoordinateErrorReductionStatement σ s C := by
  obtain ⟨a, _, hsplit⟩ := exists_coordinate_niltest_splitting σ s 2
  obtain ⟨b, _, hfreeze⟩ := NativeCoordinateSplit.exists_second_expansion_budget σ s
  obtain ⟨C, hC, hbudget⟩ := exists_coordinate_reduction_budget a b
  refine ⟨C, hC, ?_⟩
  intro i L _ _ _ _ _ _ d D p T hp hT G X H hH S z n f hS hf hcorr
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  let U := T.conjugate.expNormalize p
  let epsilon := Real.exp (-(3 * p + 1))
  have hscale : 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [hp0, sq_nonneg p]
  obtain ⟨R⟩ := hsplit i U (T.conjugate.expNormalize_complexity hT)
    (T.conjugate.expNormalize_norm hT) epsilon (Real.exp_pos _) hscale
  let sample (h : G) (x : X) := Function.update (z h) i (n h x)
  let f₀ (h : G) (x : X) := (Real.exp (-p) : ℂ) * f h x
  have hf₀ : ∀ h ∈ H, ∀ x ∈ S h, ‖f₀ h x‖ ≤ 1 :=
    fun h hh x hx => exp_scaled_norm_le_one (hf h hh x hx)
  have hc₀ : ∀ h ∈ H, Real.exp (-(3 * p)) ≤
      ‖𝔼 x ∈ S h, f₀ h x * star (U.eval (sample h x))‖ := by
    intro h hh
    have hc := finite_double_normalization (S h) (f h) (fun x => T.eval (sample h x)) p (hcorr h hh)
    simpa only [f₀, U, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
      RationalFilteredNilmanifold.Niltest.eval_conjugate, star_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj, mul_assoc, mul_left_comm, mul_comm] using hc
  have hepsilon : epsilon ≤ Real.exp (-(3 * p)) / 2 := by
    simpa only [epsilon, show -(3 * p + 1) = -(3 * p) - 1 by ring] using
      exp_sub_one_le_half_exp (-(3 * p))
  obtain ⟨j, Q, hQH, hQ, hsize, hterm⟩ := R.exists_fixed_correlating_term
    H hH S hS sample f₀ (Real.exp_pos _) hepsilon hf₀ hc₀
  let weight (x : ℤ) := star (R.firstFactor j x)
  have hweight (x : ℤ) : ‖weight x‖ ≤ 1 := by
    simpa only [weight, norm_star] using R.firstFactor_norm j x
  have hfirst (h : G) (x : X) : (R.test false j).eval (sample h x) = R.firstFactor j (n h x) := by
    simpa only [sample, Function.update_self] using R.first_eval_firstFactor j (sample h x)
  have hsmall : Real.exp (-(3 * p + (p + a) ^ a + 1)) ≤
      Real.exp (-(3 * p)) / (2 * Real.exp ((p + a) ^ a)) := by
    calc
      _ = Real.exp (-(3 * p + (p + a) ^ a) - 1) := by congr 1; ring
      _ ≤ Real.exp (-(3 * p + (p + a) ^ a)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by
        rw [show -(3 * p + (p + a) ^ a) = -(3 * p) - (p + a) ^ a by ring, Real.exp_sub]
        ring
  refine ⟨weight, Q, hweight, hQH, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp0).1)) (Nat.cast_nonneg H.card)).trans hsize
  · intro h hh
    let v (x : ℤ) := star ((R.test true j).eval (Function.update (z h) i x))
    obtain ⟨E, _⟩ := hfreeze R j (z h)
    refine ⟨v, ?_, ⟨E.conjugate.mono (hbudget p hp0).2.1⟩, ?_⟩
    · intro x
      simpa only [v, norm_star] using ((R.test true j).norm_eval_le (Function.update (z h) i x)).trans
        (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
    · have hc : Real.exp (-(3 * p)) / (2 * Real.exp ((p + a) ^ a)) ≤
          ‖𝔼 x ∈ S h, ((Real.exp (-p) : ℂ) * f h x) * (weight (n h x) * v (n h x))‖ := by
        simpa only [f₀, hfirst, weight, v, sample, star_mul,
          mul_assoc, mul_left_comm, mul_comm] using hterm h hh
      have hout := finite_remove_normalization (S h) (f h)
        (fun x => weight (n h x) * v (n h x)) hp0 hc
      have hthreshold := (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp0).2.2)).trans
        (hsmall.trans hout)
      simpa only [mul_assoc] using hthreshold

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_weighted_multilinear_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
            (fun _ : Unit => fun x => multiplicativeDerivative f h x * star
              ((V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) * weight x))) := by
  obtain ⟨a, _, hmulti⟩ := exists_fixed_multilinearized_correlation s
  obtain ⟨c, _, hsplit⟩ := exists_split_global_error s
  let X : Polynomial ℕ := Polynomial.X
  let Q₀ := (X + Polynomial.C a) ^ a
  let B₀ := 2 * X + 3 * Q₀ + 3
  let R₀ := (B₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * X + 4 * Q₀ + R₀ + 4)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  let b := 2 * p + 3 * q + 3
  let R := (b + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 2 ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hpb : p ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hqb : q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hcb : p + 2 * q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpoly : 4 * p + 4 * q + R + 4 ≤ (p + C) ^ C := by
    simpa [X, Q₀, B₀, R₀, q, b, R, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hRC : R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hdenseC : 3 * p + 2 * q + R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  obtain ⟨V, hdim, hsymm, E, j, k, z, i, H, hsub, hH, hdense, hcorr⟩ := hmulti W
  let T := (E.selectedExpansion j k).test z
  let m (h x : ZMod N) :=
    V.eval k (fun l => correlationInput (h.val : ℤ) (x.val : ℤ) l.1) *
      W.family.evalCyclic N i h x
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    dsimp only [m]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hinput (h n : ℤ) : correlationInput h n = ![h, n] := by
    funext t
    fin_cases t <;> rfl
  have hcor' (h : ZMod N) (hh : h ∈ H) : Real.exp (-b) ≤
      ‖𝔼 x, multiplicativeDerivative f h x * star
        (m h x * (W.selectedWitness ⟨h, hsub hh⟩).test.evalCyclic N (fun _ => x) *
          T.eval ![(h.val : ℤ), (x.val : ℤ)])‖ := by
    obtain ⟨hh', _, hc⟩ := hcorr h hh
    apply (Real.exp_le_exp.mpr (neg_le_neg hcb)).trans
    simpa only [m, T, hinput] using hc
  obtain ⟨weight, S, hweight, hSH, hS, hsize, hnew⟩ := hsplit W T b hb hpb
    (((E.selectedExpansion j k).complexity z).mono hqb) H hsub hH m hm hf hcor'
  have htotal : Real.exp (-(3 * p + 2 * q + R)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) := by
    calc
      _ = Real.exp (-R) * (Real.exp (-(3 * p + 2 * q)) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-R) * (H.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  refine ⟨V.mono hqC, hdim, hsymm, k, i, weight, S, hweight, hSH.trans hsub, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdenseC))
      (Nat.cast_nonneg _)).trans htotal
  · intro h hh
    obtain ⟨Z⟩ := hnew h hh
    exact ⟨Z.mono hRC⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_multilinear_quadruples (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨a, _, hweighted⟩ := exists_weighted_multilinear_correlation s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (13 * (X + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hQbudget : 13 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hQbudget]
  obtain ⟨V, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, hdense, hcorr⟩ := hweighted W hf
  let f₀ (x : ZMod N) := f x * star (weight x)
  let m (h x : ZMod N) := V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
    W.family.evalCyclic N i h x
  have hf₀ (x : ZMod N) : ‖f₀ x‖ ≤ 1 := by
    simp only [f₀, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    simp only [m, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hc (h : H) : Nonempty (NativeVectorCorrelation (s - 1) N q (nativeCrossResidual f₀ f m h.val)) := by
    obtain ⟨R⟩ := hcorr h.val h.property
    refine ⟨{ R with correlation := ?_ }⟩
    simpa only [nativeCrossResidual, f₀, m, multiplicativeDerivative, star_mul,
      mul_assoc, mul_left_comm, mul_comm] using R.correlation
  let U : NativeCrossWitnesses (s - 1) N q f₀ f m H := fun h => Classical.choice (hc h)
  obtain ⟨Q, hQ, hsize, hquad⟩ := U.exists_quadruples_budget hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, ?_, U.mono hqC,
    Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQbudget))
      (by positivity)).trans hsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hcor⟩ := hquad t ht
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2
    exact (Real.exp_le_exp.mpr (neg_le_neg hQbudget)).trans hcor

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_integer_multilinear_quadruples (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          CyclicShortShiftSet H ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => W.multilinearFactor V k i h x.val) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, ∃ (h₁ : t.2.1 ∈ H) (h₂ : t.2.1 - t.1 ∈ H)
                (h₃ : t.2.2 ∈ H) (h₄ : t.2.2 - t.1 ∈ H),
                -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0 ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 ∧
                ∃ (branch : Bool) (c len : ℕ), 0 < len ∧ c + len ≤ N ∧
                  2 * ((len : ℤ) - 1) < N ∧
                  Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
                    fourPointProduct
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1, h₁⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.1 - t.1, h₂⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2, h₃⟩)
                      (U.integerProduct (W.multilinearFactor V k i) ⟨t.2.2 - t.1, h₄⟩)
                      (cyclicBranchOffset t.1 branch) n‖ ∧
                  Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N := by
  obtain ⟨a, _, hmulti⟩ := exists_multilinear_quadruples s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (17 * (X + Polynomial.C a) ^ a + 20)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 17 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hHC : q + 1 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hQC : 13 * (q + 1) + 2 ≤ (p + C) ^ C := by linarith only [hq, hcost]
  have hIC : 13 * (q + 1) + 2 + 4 * q + 5 ≤ (p + C) ^ C := by linarith only [hcost]
  obtain ⟨V, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, hdense, U, _⟩ := hmulti W hf
  let M := W.multilinearFactor V k i
  have hm (h x : ZMod N) : ‖M h x.val‖ ≤ 1 := by
    dsimp only [M, NativeCorrelationStructure.multilinearFactor]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hf₀ (x : ZMod N) : ‖f x * star (weight x)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  obtain ⟨S, hSH, hS, hshort, hSsize, Q, hQ, hQsize, hquad⟩ :=
    U.exists_short_quadruples hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, k, i, weight, S, hweight,
    fun x hx => hsub (hSH hx), hS, hshort, ?_, (U.restrict hSH).mono hqC, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hHC))
      (Nat.cast_nonneg _)).trans hSsize
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQC))
      (by positivity)).trans hQsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hrel, hc⟩ := hquad t ht
    obtain ⟨branch, c, len, hlen, hN, hlenShort, hcor, hvol⟩ :=
      U.exists_integer_quadruple_interval_budget M (fun _ _ => rfl) hm
        t.1 t.2.1 t.2.2 (hSH h₁) (hSH h₂) (hSH h₃) (hSH h₄) hc
    refine ⟨h₁, h₂, h₃, h₄, hrel, ?_, branch, c, len, hlen, hN, hlenShort, ?_, ?_⟩
    · change Real.exp (-((p + C) ^ C)) ≤
        additiveQuadrupleCorrelation (U.restrict hSH).extension t.1 t.2.1 t.2.2
      rw [U.restrict_quadruple hSH t.1 t.2.1 t.2.2 h₁ h₂ h₃ h₄]
      exact (Real.exp_le_exp.mpr (neg_le_neg hQC)).trans hc
    · change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n ∈ Finset.Ico (c : ℤ) (c + len),
        fourPointProduct (U.integerProduct M ⟨t.2.1, hSH h₁⟩)
          (U.integerProduct M ⟨t.2.1 - t.1, hSH h₂⟩)
          (U.integerProduct M ⟨t.2.2, hSH h₃⟩)
          (U.integerProduct M ⟨t.2.2 - t.1, hSH h₄⟩) (cyclicBranchOffset t.1 branch) n‖
      exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hcor
    · exact (Real.exp_le_exp.mpr (neg_le_neg hIC)).trans hvol

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3

theorem exists_native_multilinear_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeMultilinearIntervalFamily W ((p + C) ^ C)) := by
  obtain ⟨C, hC, hquad⟩ := exists_integer_multilinear_quadruples s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  obtain ⟨V, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, hshort,
    hHsize, U, Q, hQ, hQsize, hinterval⟩ := hquad W hf
  classical
  have hdata (t : Q) := hinterval t.val t.property
  choose h₁ h₂ h₃ h₄ hrel hcyclic branch c len hlen hN hlenShort hcor hvol using hdata
  exact ⟨{
    mixed := V
    mixed_dim := hdim
    mixed_symmetric := hsymm
    coordinate := k
    rankCoordinate := i
    weight := weight
    weight_norm := hweight
    shifts := H
    shifts_subset := hsub
    shifts_nonempty := hH
    shifts_short := hshort
    shifts_density := hHsize
    lower := U
    quadruples := Q
    quadruples_nonempty := hQ
    quadruples_density := hQsize
    interval := fun t => {
      first_mem := h₁ t
      second_mem := h₂ t
      third_mem := h₃ t
      fourth_mem := h₄ t
      integer_relation := hrel t
      cyclic_correlation := hcyclic t
      branch := branch t
      start := c t
      length := len t
      length_pos := hlen t
      endpoint_le := hN t
      length_short := hlenShort t
      correlation := hcor t
      length_ratio := hvol t } }⟩

end Erdos3

end

section

namespace Erdos3.NativeReducedIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
  {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K)

noncomputable def localLower (t : R.retained) (n : ℤ) : ℂ :=
  B.lowerProduct t.val n *
    D.translationLower R.code.translations (t.val.val.2.1 - t.val.val.1).val
      (t.val.val.2.2 - t.val.val.1).val (B.delta t.val) (R.lowerChoice t) n

noncomputable def localExpansion (t : R.retained) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (intervalErrorBudget K)
      (fun x => R.localLower t (x ())) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  have hbase := intervalErrorBaseBudget_bounds hK
  have hfirst : mixedErrorBudget (q + 2) ≤ intervalErrorBaseBudget K :=
    (mixedErrorBudget_mono (by linarith) (by linarith [R.base_budget])).trans hbase.2.2
  have hsecond : mixedErrorPairBudget P ≤ intervalErrorBaseBudget K :=
    R.lower_budget.trans hbase.2.1
  exact ((B.lowerProductExpansion t.val).mono hfirst).mul
    ((D.translationLowerExpansion R.code.translations (t.val.val.2.1 - t.val.val.1).val
      (t.val.val.2.2 - t.val.val.1).val (B.delta t.val) (R.lowerChoice t)).mono hsecond) hbase.1

theorem rank_correlation (t : R.retained) :
    Real.exp (-K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
      B.rankProduct t.val n * D.globalError (fun _ => B.coordinate) R.code (B.sample t.val n) *
        R.localLower t n‖ := by
  simpa only [localLower, NativeMultilinearIntervalFamily.residual,
    mul_assoc, mul_left_comm, mul_comm] using R.correlation t

end Erdos3.NativeReducedIntervalFamily

end

section

namespace Erdos3

namespace NativeReducedIntervalFamily

variable {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
  {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K)

theorem localLower_norm (t : R.retained) (n : ℤ) :
    ‖R.localLower t n‖ ≤ Real.exp (2 * intervalErrorBudget K) :=
  (R.localExpansion t).norm_eval_le (fun _ => n)

theorem scalar_norm (t : R.retained) (n : ℤ) :
    ‖B.rankProduct t.val n * R.localLower t n‖ ≤ Real.exp (2 * intervalErrorBudget K) := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (B.rankProduct_norm t.val n) (R.localLower_norm t n)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end NativeReducedIntervalFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedRepresentative_grid
    (R : (pi (I.productModels D.index)).filtration.RealPolynomialSymbolGroup (fun _ : Unit => 1))
    (hR : (pi (I.productModels D.index)).filtration.SymbolRationalGrid
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) D.denominator R)
    (α : Unit →₀ ℕ) :
    (fun j => (W.fourRankBasis.baseChange ℝ).repr (D.projectedRepresentative R α) j) ∈
      realDenominatorGrid D.projectedDenominator := by
  unfold projectedDenominator projectedRepresentative
  have hgrid := (pi (I.productModels D.index)).filtration.realSymbolRepresentative_original_grid
    D.adapted.basis D.adapted.weight D.adapted.layers (pi (I.productModels D.index)).basis
    (fun _ : Unit => 1) D.denominator R hR α
  have hp := I.real_rankProjection_grid D.index
    (matrixDenominator (fun i j => (pi (I.productModels D.index)).basis.repr (D.adapted.basis j) i) *
      D.denominator)
    (coefficients ((pi (I.productModels D.index)).filtration.realSymbolRepresentative
      D.adapted.basis D.adapted.weight D.adapted.layers (fun _ => 1) R.coord) α) hgrid
  convert hp using 2

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankOrbitCoefficientCorrections
namespace OAI

section

namespace Erdos3.NativeRankInterval.SunflowerWitness

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem exists_bounded_coefficient_corrections (hs : 1 ≤ s) (hP : 0 ≤ P) :
    ∃ E R : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ,
      (∀ α j, |(W.fourRankBasis.baseChange ℝ).repr (E α).val j| ≤
        Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α) ∧
      (∀ α, (fun j => (W.fourRankBasis.baseChange ℝ).repr (R α).val j) ∈
        realDenominatorGrid D.projectedDenominator) ∧
      ∀ α, W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
          (D.projectedOrbitCoefficient α - E α - R α) ∈
        (I.refilteredHorizontalImage D.index D.subalgebra
          (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ := by
  obtain ⟨E, R, hE, hR, hres⟩ := D.exists_projected_corrections hs
  refine ⟨D.projectedRepresentativeLayer E, D.projectedRepresentativeLayer R, ?_, ?_, ?_⟩
  · intro α j
    exact D.projectedRepresentative_slow hP E hE α j
  · intro α
    exact D.projectedRepresentative_grid R hR α
  · intro α
    let f := W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
    have hinner := (map_sub f (D.projectedOrbitCoefficient α) (D.projectedRepresentativeLayer E α)).trans
      (congrArg₂ (fun x y => x - y) (D.projectedOrbitCoefficient_horizontal α)
        (D.projectedRepresentative_horizontal E α))
    have heq := (map_sub f (D.projectedOrbitCoefficient α - D.projectedRepresentativeLayer E α)
      (D.projectedRepresentativeLayer R α)).trans
        (congrArg₂ (fun x y => x - y) hinner (D.projectedRepresentative_horizontal R α))
    exact (congrArg (fun v => v ∈ (I.refilteredHorizontalImage D.index D.subalgebra
      (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ) heq).mpr (hres α)

end Erdos3.NativeRankInterval.SunflowerWitness

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_bounded_coefficient_corrections (D : R.CommonData P) (hs : 1 ≤ s) (hP : 0 ≤ P)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ,
      (∀ α j, |(W.fourRankBasis.baseChange ℝ).repr (E α).val j| ≤
        Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α) ∧
      (∀ α, (fun j => (W.fourRankBasis.baseChange ℝ).repr (Q α).val j) ∈
        realDenominatorGrid V.projectedDenominator) ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
            (V.projectedOrbitCoefficient α - E α - Q α) ∈
          (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩).baseChange ℝ := by
  intro I V
  obtain ⟨E, Q, hE, hQ, hres⟩ := V.exists_bounded_coefficient_corrections hs hP
  refine ⟨E, Q, hE, hQ, ?_⟩
  intro α hα
  exact (congrArg (fun U => _ ∈ U.baseChange ℝ)
    (D.horizontalImage_eq t ht ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).mp
    (hres α)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonNativeCoordinateCorrections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (d : Fin (s + 1)) (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))

noncomputable def realCoordinateSpace : Submodule ℝ ((Σ _ : Fin 4, κ) → ℝ) :=
  ((D.coordinateSpace d f).baseChange ℝ).map
    (DegreeRankLieFiltration.realFourCoordinateEquiv (ι := κ)).toLinearMap

theorem realCoordinateSpace_eq_image :
    D.realCoordinateSpace d f =
      ((D.horizontal d).baseChange ℝ).map (W.rank.filtration.realFourHorizontalCoordinates d.val f) :=
  (W.rank.filtration.realFourHorizontalCoordinates_image d.val f (D.horizontal d)).symm

theorem realCoordinateSpace_mem
    (x : (W.rank.filtration.fourHorizontalLayer d.val).baseChange ℝ)
    (hx : W.rank.filtration.realFourHorizontalMap d.val x ∈ (D.horizontal d).baseChange ℝ) :
    W.rank.filtration.realFourAmbientCoordinates d.val f x.val ∈ D.realCoordinateSpace d f := by
  rw [D.realCoordinateSpace_eq_image, ← W.rank.filtration.realFourHorizontalCoordinates_map d.val f x]
  exact ⟨_, hx, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_coordinate_corrections (D : R.CommonData P) (hs : 1 ≤ s) (hP : 0 ≤ P)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : (Σ _ : Fin 4, κ) → ℝ,
      (∀ j, |E j| ≤ ((W.dim : ℝ) + 1) * (K + 1) *
        (Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α)) ∧
      Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * V.projectedDenominator) ∧
      W.rank.filtration.realFourAmbientCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
          (V.projectedOrbitCoefficient α).val - E - Q ∈
        D.realCoordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f := by
  intro I V
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_bounded_coefficient_corrections hs hP t ht
  let φ := W.rank.filtration.realFourAmbientCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
  refine ⟨φ (E α).val, φ (Q α).val, ?_, ?_, ?_⟩
  · intro j
    have hscale := monomialScale_pos (fun _ : Unit => (I.length : ℝ))
      (fun _ => by exact_mod_cast I.length_pos) α
    have hbound := W.rank.filtration.realFourAmbientCoordinates_bound
      (Finsupp.weight (fun _ : Unit => 1) α) f W.model.basis hf (E α).val
      (div_nonneg (Real.exp_pos _).le hscale.le) (hE α) j.1 j.2
    simpa only [Fintype.card_fin] using hbound
  · exact W.rank.filtration.realFourAmbientCoordinates_grid
      (Finsupp.weight (fun _ : Unit => 1) α) f W.model.basis V.projectedDenominator (Q α).val (hQ α)
  · have h := D.realCoordinateSpace_mem
      ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
      (V.projectedOrbitCoefficient α - E α - Q α) (hres α hα)
    change φ ((V.projectedOrbitCoefficient α).val - (E α).val - (Q α).val) ∈ _ at h
    simpa only [map_sub] using h

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_anchor_representative_corrections
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (n : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) :
    ∃ E Q : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ,
      (∀ α, Finsupp.weight (fun _ : Unit => 1) α ≤ s →
        ‖(W.model.basis.baseChange ℝ).equivFun (E α).val‖ ≤
          Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α) ∧
      (∀ α, (W.model.basis.baseChange ℝ).equivFun (Q α).val ∈ realDenominatorGrid n) ∧
      ∀ α (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        W.horizontalCoefficient hs c τ hG α h₀ -
            W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) (E α) -
            W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) (Q α) ∈
          (fourFirstProjection (D.horizontal
            ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ := by
  let t := (A.anchors12.2 - h₀, A.anchors12.2, A.anchors12.1)
  have ht : t ∈ D.quadruples := (A.relations h₀ hh₀).1
  let I := R.interval ⟨t, D.subset ht⟩
  let V : I.SunflowerWitness P := D.witness t ht
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_bounded_coefficient_corrections hs hP t ht
  refine ⟨fun α => W.rank.filtration.realFourLayerComponent _ 0 (E α),
    fun α => W.rank.filtration.realFourLayerComponent _ 0 (Q α), ?_, ?_, ?_⟩
  · intro α hα
    have he := W.rank.filtration.realFourLayerComponent_norm_bound
      (Finsupp.weight (fun _ : Unit => 1) α) W.model.basis 0 (E α)
      (div_nonneg (Real.exp_nonneg _) (monomialScale_pos _
        (fun _ => by exact_mod_cast I.length_pos) α).le) (hE α)
    have hb := I.norm_bound_on_modulus hp α hα (Real.exp_nonneg ((P + 3) ^ 2))
      ((W.model.basis.baseChange ℝ).equivFun
        (W.rank.filtration.realFourLayerComponent _ 0 (E α)).val) he
    rwa [← Real.exp_add] at hb
  · intro α
    have hg := W.rank.filtration.realFourLayerComponent_grid
      (Finsupp.weight (fun _ : Unit => 1) α) W.model.basis 0 (Q α)
      V.projectedDenominator (hQ α)
    simpa only [Basis.equivFun_apply] using
      realDenominatorGrid_subset_of_dvd V.projectedDenominator_pos (hdenom t ht) hg
  · intro α hα
    have hm := real_firstProjection_mem
      (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩) (hres α hα)
    have hfirst : rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) 0) = h₀ := by
      simp [t, rankQuadrupleParameters]
    let φ := ((LinearMap.proj (0 : Fin 4)).baseChange ℝ).comp
      (W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α))
    have heq : φ (V.projectedOrbitCoefficient α - E α - Q α) =
        φ (V.projectedOrbitCoefficient α) - φ (E α) - φ (Q α) := by
      exact (map_sub φ (V.projectedOrbitCoefficient α - E α) (Q α)).trans
        (congrArg₂ (· - ·) (map_sub φ (V.projectedOrbitCoefficient α) (E α)) rfl)
    change φ (V.projectedOrbitCoefficient α - E α - Q α) ∈ _ at hm
    rw [heq] at hm
    change (LinearMap.proj (0 : Fin 4)).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap _ (V.projectedOrbitCoefficient α)) -
      (LinearMap.proj (0 : Fin 4)).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap _ (E α)) -
      (LinearMap.proj (0 : Fin 4)).baseChange ℝ
        (W.rank.filtration.realFourHorizontalMap _ (Q α)) ∈ _ at hm
    rw [V.projectedOrbitCoefficient_native_component hs c τ hG α 0, hfirst,
      W.rank.filtration.realFourLayerComponent_horizontal,
      W.rank.filtration.realFourLayerComponent_horizontal] at hm
    exact hm

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation.CommonData

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem native_scaled_correction
    (D : R.CommonData P) (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let β := W.nativeCoefficientCoordinates hs c τ hG α f
    ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
      ‖E‖ ≤ ((W.dim : ℝ) + 1) * (K + 1) *
        (Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α) ∧
      Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l) ∧
      rankCoordinateTuple β t - E - Q ∈ realFourCoordinateSpan
        (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f) := by
  intro β
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_coordinate_corrections hs hP t ht α hα f hf
  let I := R.interval ⟨t, D.subset ht⟩
  let M : ℝ := ((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hnorm : ‖E‖ ≤ M / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hM
      (monomialScale_pos _ (fun _ => hlength) α).le)).mpr
    intro j
    simpa only [Real.norm_eq_abs, M, mul_div_assoc] using hE j
  refine ⟨E, Q, ?_, ?_, ?_⟩
  · have h := I.norm_bound_on_modulus hp α hα hM E hnorm
    simpa only [M, Real.exp_add, mul_div_assoc, mul_assoc] using h
  · change Q ∈ realDenominatorGrid
      (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * (D.witness t ht).projectedDenominator) at hQ
    simpa only [hdenom t ht] using hQ
  · have hcoeff : W.rank.filtration.realFourAmbientCoordinates
        (Finsupp.weight (fun _ : Unit => 1) α) f ((D.witness t ht).projectedOrbitCoefficient α).val =
        rankCoordinateTuple β t := by
      funext j
      exact (D.witness t ht).projectedOrbitCoefficient_native_coordinates hs c τ hG α f j.1 j.2
    rw [hcoeff] at hres
    exact hres

end NativeRankRelation.CommonData

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {ι κ ν : Type*} [Fintype ι] [Fintype ν] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_native_sparse_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) (hα₀ : α ≠ 0)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    {K : ℕ} (hf : ∀ i j, RationalHeightLE
      (f.repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).mkQ (W.model.basis j)) i) K)
    (v : ν → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) =
      D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f)
    {JH : ℕ} (hJH : 1 ≤ JH) (hvH : ∀ a k i, RationalHeightLE (v a k i) JH)
    {z : ℝ} (hz : 0 ≤ z) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ z)
    (hcols : (Fintype.card ν : ℝ) ≤ z) (hJHz : (JH : ℝ) ≤ Real.exp z)
    (hlz : ((matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l : ℕ) : ℝ) ≤ Real.exp z)
    (hslow : 2 * (((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) ≤ Real.exp z)
    (hN : Real.exp (separationBudget z) ≤ N) :
    let β := W.nativeCoefficientCoordinates hs c τ hG α f
    let J := D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (2 * (z + ((z + 2) ^ 3 + (z + 2) ^ 36))) ∧
      matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l ∣ m ∧
      ∀ h ∈ A.shifts, ∃ e₁₂ q₁₂ e₁₃ q₁₃ : ι → ℝ,
        ‖e₁₂‖ ≤ (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
          monomialScale (fun _ : Unit => (N : ℝ)) α ∧
        ‖e₁₃‖ ≤ (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
          monomialScale (fun _ : Unit => (N : ℝ)) α ∧
        q₁₂ ∈ realDenominatorGrid m ∧ q₁₃ ∈ realDenominatorGrid m ∧
        β h - β h₀ - e₁₂ - q₁₂ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) ∧
        β h - β h₀ - e₁₃ - q₁₃ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) := by
  intro β J
  let M : ℝ := ((W.dim : ℝ) + 1) * (K + 1) * Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)
  have hcorrect (t) (ht : t ∈ D.quadruples) : ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
      ‖E‖ ≤ M / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
      Q ∈ realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix W.model.basis f) * l) ∧
      rankCoordinateTuple β t - E - Q ∈ realFourCoordinateSpan J := by
    obtain ⟨E, Q, hE, hQ, hres⟩ := D.native_scaled_correction hs hp hP c τ hG l hdenom α hα f hf t ht
    exact ⟨E, Q, by simpa only [M, mul_div_assoc] using hE, hQ, hres⟩
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_rank_sparse_family A.shifts h₀ hh₀ J v hv hJH
    (Nat.mul_pos (matrixDenominator_pos _) hl) hvH hz hfour hcols hJHz hlz
    (fun _ : Unit => (N : ℝ)) (fun _ => hN)
  refine ⟨m, hm, hmp, hlm, ?_⟩
  exact hsolve α hα₀ β A.anchors12.1 A.anchors12.2 A.anchors13.1 A.anchors13.2 M hslow
    (fun h hh => hcorrect _ (A.relations h hh).1)
    (fun h hh => hcorrect _ (A.relations h hh).2)

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRealDependentProjection
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation.CommonData

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem real_dependent_coordinateSpace_eq (D : R.CommonData P) (d : Fin (s + 1))
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) :
    realRationalCoordinateSpan (fourDependentProjection (D.coordinateSpace d f)) =
      ((fourDependentProjection (D.horizontal d)).baseChange ℝ).map
        (W.rank.filtration.realHigherHorizontalCoordinates d.val f) := by
  rw [D.coordinateSpace_dependent]
  exact (W.rank.filtration.realHigherHorizontalCoordinates_image d.val f
    (fourDependentProjection (D.horizontal d))).symm

theorem exists_real_dependent_remainder (D : R.CommonData P) (d : Fin (s + 1))
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))
    (x y : ℝ ⊗[ℚ] W.rank.filtration.HigherHorizontal d.val) (e u : ι → ℝ)
    (hmem : W.rank.filtration.realHigherHorizontalCoordinates d.val f x -
        W.rank.filtration.realHigherHorizontalCoordinates d.val f y - e - u ∈
      realRationalCoordinateSpan (fourDependentProjection (D.coordinateSpace d f))) :
    ∃ z ∈ (fourDependentProjection (D.horizontal d)).baseChange ℝ,
      W.rank.filtration.realHigherHorizontalCoordinates d.val f (x - y - z) = e + u := by
  rw [D.real_dependent_coordinateSpace_eq d f] at hmem
  obtain ⟨z, hz, hcoord⟩ := hmem
  refine ⟨z, hz, ?_⟩
  rw [map_sub, map_sub, hcoord]
  abel

theorem exists_native_dependent_remainder (D : R.CommonData P) (hs : 1 ≤ s)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    (h h₀ : ZMod N) (e u : ι → ℝ)
    (hmem : W.nativeCoefficientCoordinates hs c τ hG α f h -
        W.nativeCoefficientCoordinates hs c τ hG α f h₀ - e - u ∈
      realRationalCoordinateSpan (fourDependentProjection
        (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f))) :
    ∃ z ∈ (fourDependentProjection
        (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ,
      W.rank.filtration.realHigherHorizontalCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
        (W.horizontalCoefficient hs c τ hG α h - W.horizontalCoefficient hs c τ hG α h₀ - z) = e + u := by
  apply D.exists_real_dependent_remainder
    ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
    (W.horizontalCoefficient hs c τ hG α h) (W.horizontalCoefficient hs c τ hG α h₀) e u
  simpa only [W.nativeCoefficientCoordinates_eq_real hs c τ hG α f] using hmem

end NativeRankRelation.CommonData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
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

theorem exists_coefficient_space_bases (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) (hd : 1 ≤ d.val) :
    ∃ c : Basis (Fin (finrank ℚ (D.commonCoefficientSpace d))) ℚ (D.commonCoefficientSpace d),
      (∀ i j, rationalLogHeight (W.model.basis.repr (c i : W.L) j) ≤ coefficientSpaceBasisBudget P) ∧
      ∃ e : Basis (Fin (finrank ℚ (D.dependentCoefficientSpace d))) ℚ (D.dependentCoefficientSpace d),
        ∀ i j, rationalLogHeight (W.model.basis.repr (e i : W.L) j) ≤ coefficientSpaceBasisBudget P := by
  classical
  let : FiniteDimensional ℚ W.L := W.model.basis.finiteDimensional_of_finite
  have hR := W.complexity.mono W.rank hbP
  have hdim : (W.dim : ℝ) ≤ P := hR.1.1
  obtain ⟨m, hm, f, hf, v, hv, hvH⟩ := D.exists_bounded_coordinate_generators hP hbP d hd
  let J := D.coordinateSpace d f
  let a := coefficientSpaceInputBudget P
  have hhor := horizontalCoordinateBudget_nonneg hP
  have hpow : 0 ≤ (P + 3) ^ 7 := by positivity
  have hPa : P ≤ a := by dsimp only [a, coefficientSpaceInputBudget]; linarith
  have h4Pa : 4 * P ≤ a := by dsimp only [a, coefficientSpaceInputBudget]; linarith
  have hhora : horizontalCoordinateBudget P ≤ a := by
    dsimp only [a, coefficientSpaceInputBudget]; linarith
  have hpowa : (P + 3) ^ 7 ≤ a := by dsimp only [a, coefficientSpaceInputBudget]; linarith
  have ha : 0 ≤ a := hP.trans hPa
  have hma : (m : ℝ) ≤ a := (Nat.cast_le.mpr hm).trans (hdim.trans hPa)
  have hcols : Fintype.card (Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim))) = 4 * W.dim := by simp
  have hcolsa : (Fintype.card (Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim))) : ℝ) ≤ a := by
    rw [hcols, Nat.cast_mul, Nat.cast_ofNat]
    exact (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)).trans h4Pa
  obtain ⟨eD, heD⟩ := exists_dependent_coordinate_basis J v hv ha
    (by simpa only [Fintype.card_fin] using hma) hcolsa
    (fun i k j => (hvH i k j).trans hhora)
  have hdepdim : finrank ℚ (fourDependentProjection J) ≤ m := by
    simpa using (fourDependentProjection J).finrank_le
  let a₁ := W.rank.basis d ⟨1, by omega⟩
  let u : Fin (finrank ℚ (W.rank.filtration.layer d.val 1)) → W.L := fun i => a₁ i
  have hu : Submodule.span ℚ (Set.range u) = W.rank.filtration.layer d.val 1 :=
    span_submodule_basis _ a₁
  have hudim : finrank ℚ (W.rank.filtration.layer d.val 1) ≤ W.dim := by
    simpa only [finrank_eq_card_basis W.model.basis, Fintype.card_fin] using
      (W.rank.filtration.layer d.val 1).finrank_le
  have huH (i) (j) : rationalLogHeight (W.model.basis.repr (u i) j) ≤ P :=
    hR.2 d ⟨1, by omega⟩ i j
  let T := W.rank.filtration.ambientHorizontalCoordinates d.val f
  have hTu (i) (j) : rationalLogHeight ((Pi.basisFun ℚ (Fin m)).repr (T (u i)) j) ≤
      (a + 2) ^ 4 := by
    change rationalLogHeight (f.repr ((W.rank.filtration.layer d.val 2).mkQ (u i)) j) ≤ _
    exact linearMap_coordinate_logHeight W.model.basis f
      (W.rank.filtration.layer d.val 2).mkQ ha
      (by simpa only [Fintype.card_fin] using hdim.trans hPa)
      (fun k l => (hf l k).trans hpowa) (u i) (fun k => (huH i k).trans hPa) j
  let Q := a + (a + 2) ^ 4 + dependentCoordinateBudget a
  have hdep := dependentCoordinateBudget_nonneg ha
  have hpower : 0 ≤ (a + 2) ^ 4 := by positivity
  have haQ : a ≤ Q := by dsimp only [Q]; linarith
  have hpQ : (a + 2) ^ 4 ≤ Q := by dsimp only [Q]; linarith
  have hdQ : dependentCoordinateBudget a ≤ Q := by dsimp only [Q]; linarith
  have hQ : 0 ≤ Q := ha.trans haQ
  have huQ : (Fintype.card (Fin (finrank ℚ (W.rank.filtration.layer d.val 1))) : ℝ) ≤ Q := by
    simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hudim).trans (hdim.trans (hPa.trans haQ))
  have hv₀ : Submodule.span ℚ (Set.range (fun i => v i 0)) = fourFirstProjection J := by
    change _ = (D.coordinateSpace d f).map (LinearMap.proj 0)
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hdepSpan : Submodule.span ℚ (Set.range (fun i => (eD i : Fin m → ℚ))) =
      fourDependentProjection J := by
    change Submodule.span ℚ (Set.range ((fourDependentProjection J).subtype ∘ eD)) = _
    rw [Set.range_comp, ← Submodule.map_span, eD.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hc := exists_preimage_basis_logHeight W.model.basis (Pi.basisFun ℚ (Fin m))
    (W.rank.filtration.layer d.val 1) (fourFirstProjection J) T u (fun i => v i 0)
    hu hv₀ hQ (by simpa only [Fintype.card_fin] using hma.trans haQ) huQ (hcolsa.trans haQ)
    (fun i j => (huH i j).trans (hPa.trans haQ))
    (by simpa only [Pi.basisFun_repr] using fun i j => (hvH i 0 j).trans (hhora.trans haQ))
    (fun i j => (hTu i j).trans hpQ)
  have he := exists_preimage_basis_logHeight W.model.basis (Pi.basisFun ℚ (Fin m))
    (W.rank.filtration.layer d.val 1) (fourDependentProjection J) T u (fun i => (eD i : Fin m → ℚ))
    hu hdepSpan hQ (by simpa only [Fintype.card_fin] using hma.trans haQ) huQ
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hdepdim).trans (hma.trans haQ))
    (fun i j => (huH i j).trans (hPa.trans haQ))
    (by simpa only [Pi.basisFun_repr] using fun i j => (heD i j).trans hdQ)
    (fun i j => (hTu i j).trans hpQ)
  have hcspace : D.commonCoefficientSpace d =
      W.rank.filtration.layer d.val 1 ⊓ (fourFirstProjection J).comap T := by
    unfold commonCoefficientSpace
    rw [W.rank.filtration.horizontalPreimage_coordinates d.val f,
      ← D.coordinateSpace_first d f]
  have hespace : D.dependentCoefficientSpace d =
      W.rank.filtration.layer d.val 1 ⊓ (fourDependentProjection J).comap T := by
    unfold dependentCoefficientSpace
    rw [W.rank.filtration.horizontalPreimage_coordinates d.val f,
      ← D.coordinateSpace_dependent d f]
  rw [← hcspace] at hc
  rw [← hespace] at he
  obtain ⟨c, hc⟩ := hc
  obtain ⟨e, he⟩ := he
  exact ⟨c, hc, e, he⟩

end NativeRankRelation.CommonData
end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

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

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.freeEvaluation_commonFreeLift (d : Fin s)
    (x : D.commonCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.freeEvaluation D (B.commonFreeLift D d x) = x.val := by
  have h : (B.freeEvaluation D).toLinearMap.comp (B.commonFreeLift D d) =
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).subtype := by
    apply (B.common d).ext
    intro i
    change B.freeEvaluation D ((B.common d).constr ℚ _ (B.common d i)) = _
    rw [Basis.constr_basis]
    exact B.freeEvaluation_generator D (Sum.inl ⟨d, i⟩)
  exact LinearMap.congr_fun h x

theorem CoefficientBases.freeEvaluation_dependentFreeLift (d : Fin s)
    (x : D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩) :
    B.freeEvaluation D (B.dependentFreeLift D d x) = x.val := by
  have h : (B.freeEvaluation D).toLinearMap.comp (B.dependentFreeLift D d) =
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).subtype := by
    apply (B.dependent d).ext
    intro i
    change B.freeEvaluation D ((B.dependent d).constr ℚ _ (B.dependent d i)) = _
    rw [Basis.constr_basis]
    exact B.freeEvaluation_generator D (Sum.inr ⟨d, i⟩)
  exact LinearMap.congr_fun h x

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.realEvaluation_commonFreeLift (d : Fin s)
    (x : (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    realificationLieHom (B.freeEvaluation D) (B.realCommonFreeLift D d x) = x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realCommonFreeLift_baseChange, realificationSubmoduleEquiv_coe]
  change (B.freeEvaluation D).toLinearMap.baseChange ℝ
    ((B.commonFreeLift D d).baseChange ℝ v) = _
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    change a ⊗ₜ[ℚ] B.freeEvaluation D (B.commonFreeLift D d v) = a ⊗ₜ[ℚ] v.val
    rw [B.freeEvaluation_commonFreeLift]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem CoefficientBases.realEvaluation_dependentFreeLift (d : Fin s)
    (x : (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    realificationLieHom (B.freeEvaluation D) (B.realDependentFreeLift D d x) = x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [B.realDependentFreeLift_baseChange, realificationSubmoduleEquiv_coe]
  change (B.freeEvaluation D).toLinearMap.baseChange ℝ
    ((B.dependentFreeLift D d).baseChange ℝ v) = _
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    change a ⊗ₜ[ℚ] B.freeEvaluation D (B.dependentFreeLift D d v) = a ⊗ₜ[ℚ] v.val
    rw [B.freeEvaluation_dependentFreeLift]
  | add v w hv hw => simp only [map_add, hv, hw]

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def dependentWordLayer (d k l : ℕ) : Submodule ℚ D.CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra.markedLayer D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent d k l

noncomputable def dependentWordIdeal (d k l : ℕ) : LieIdeal ℚ D.CoefficientFreeLieAlgebra :=
  FreeDegreeRankLieAlgebra.markedLayerIdeal D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent d k l

theorem commonFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.commonFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 0 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact markedLieSpan_leaf D.coefficientFreeGenerator D.coefficientWeight
    D.coefficientIsDependent (Sum.inl ⟨d, i⟩)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonAnchorPolynomialCorrections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_anchor_polynomial_corrections
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (n : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) :
    let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
    ∃ E Q : W.rank.filtration.realification.associatedDegree.adaptedLieSubalgebra (fun _ : Unit => 1),
      coefficients E.val 0 = 0 ∧ coefficients Q.val 0 = 0 ∧
      CoefficientBound (W.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) E.val ∧
      CoefficientGrid (W.model.basis.baseChange ℝ) n Q.val ∧
      ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
        ∃ e u : (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 1).baseChange ℝ,
          coefficients E.val (α d) = e.val ∧ coefficients Q.val (α d) = u.val ∧
          W.horizontalCoefficient hs c τ hG (α d) h₀ -
              W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) e -
              W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) u ∈
            (fourFirstProjection (D.horizontal
              ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  intro α
  obtain ⟨e, u, he, hu, hres⟩ := A.exists_anchor_representative_corrections h₀ hh₀ hs hp hP c τ hG n hdenom
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  let E := positiveUnivariate (fun d => (e (α d)).val)
  let Q := positiveUnivariate (fun d => (u (α d)).val)
  refine ⟨⟨E, W.rank.filtration.positiveUnivariate_horizontal_mem (fun d => e (α d))⟩,
    ⟨Q, W.rank.filtration.positiveUnivariate_horizontal_mem (fun d => u (α d))⟩,
    positiveUnivariate_zero _, positiveUnivariate_zero _, ?_, ?_, ?_⟩
  · exact positiveUnivariate_coefficientBound (W.model.basis.baseChange ℝ)
      (fun d => (e (α d)).val) (fun _ : Unit => (N : ℝ))
      (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_nonneg _) (fun d => he (α d) (hd d))
  · exact positiveUnivariate_coefficientGrid (W.model.basis.baseChange ℝ)
      (fun d => (u (α d)).val) n (fun d => hu (α d))
  · intro d hd'
    exact ⟨e (α d), u (α d), positiveUnivariate_coefficient _ d,
      positiveUnivariate_coefficient _ d, hres (α d) hd'⟩

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeFreePolynomialLifts
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.exists_commonFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : D.coefficientFreeRealFiltration.PolynomialOrbit (fun _ : Unit => 1),
      D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.commonFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.coefficientFreeFiltration.associatedDegree.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  let v (d : Fin s) := B.realCommonFreeLift D d
    ⟨coefficients g.log (Finsupp.single () (d.val + 1)), hcoeff d⟩
  have hvspan (d : Fin s) : v d ∈ (D.commonFreeSpan d).baseChange ℝ :=
    B.realCommonFreeLift_mem D d _
  have hv (d : Fin s) : v d ∈ D.coefficientFreeRealFiltration.layer (d.val + 1) := by
    change v d ∈ (D.coefficientFreeFiltration.layer (d.val + 1) 0).baseChange ℝ
    rw [D.coefficientFreeFiltration.rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_layer d) (hvspan d)
  let π := (realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ
  have hπ (d : Fin s) : π (v d) = coefficients g.log (Finsupp.single () (d.val + 1)) :=
    B.realEvaluation_commonFreeLift D d _
  obtain ⟨u, hu, hu0, humap, hueval⟩ :=
    D.coefficientFreeRealFiltration.exists_positiveUnivariate_orbit_lift
      W.model.filtration.realification π g hg v hv hπ
  refine ⟨u, hu0, ?_, humap, ?_⟩
  · intro d
    rw [hu, positiveUnivariate_coefficient]
    exact hvspan d
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact hueval x

theorem CoefficientBases.exists_dependentFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : D.coefficientFreeRealFiltration.PolynomialOrbit (fun _ : Unit => 1),
      D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.dependentFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.coefficientFreeFiltration.associatedDegree.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  let v (d : Fin s) := B.realDependentFreeLift D d
    ⟨coefficients g.log (Finsupp.single () (d.val + 1)), hcoeff d⟩
  have hvspan (d : Fin s) : v d ∈ (D.dependentFreeSpan d).baseChange ℝ :=
    B.realDependentFreeLift_mem D d _
  have hv (d : Fin s) : v d ∈ D.coefficientFreeRealFiltration.layer (d.val + 1) := by
    change v d ∈ (D.coefficientFreeFiltration.layer (d.val + 1) 0).baseChange ℝ
    rw [D.coefficientFreeFiltration.rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_layer d) (hvspan d)
  let π := (realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ
  have hπ (d : Fin s) : π (v d) = coefficients g.log (Finsupp.single () (d.val + 1)) :=
    B.realEvaluation_dependentFreeLift D d _
  obtain ⟨u, hu, hu0, humap, hueval⟩ :=
    D.coefficientFreeRealFiltration.exists_positiveUnivariate_orbit_lift
      W.model.filtration.realification π g hg v hv hπ
  refine ⟨u, hu0, ?_, humap, ?_⟩
  · intro d
    rw [hu, positiveUnivariate_coefficient]
    exact hvspan d
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact hueval x

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (F : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : F.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.exists_native_commonFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : F.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.commonFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, realificationMap
        (hnil := F.filtration.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  obtain ⟨u, hu0, huc, humap, hueval⟩ := B.exists_commonFreePolynomialOrbit D g hg hcoeff
  let hF := D.coefficientFreeRealFiltration_eq_native F T hT
  let u' := D.coefficientFreeRealFiltration.orbitEquivOfEq hF (fun _ : Unit => 1) u
  have hlog : u'.log = u.log :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_log hF _ u
  have heval (x : Unit → ℤ) :
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u' =
        D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_eval hF _ u x
  refine ⟨u', (heval 0).trans hu0, ?_, ?_, ?_⟩
  · simpa only [hlog] using huc
  · simpa only [hlog] using humap
  · intro x
    rw [heval]
    exact hueval x

theorem CoefficientBases.exists_native_dependentFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : F.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.dependentFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, realificationMap
        (hnil := F.filtration.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  obtain ⟨u, hu0, huc, humap, hueval⟩ := B.exists_dependentFreePolynomialOrbit D g hg hcoeff
  let hF := D.coefficientFreeRealFiltration_eq_native F T hT
  let u' := D.coefficientFreeRealFiltration.orbitEquivOfEq hF (fun _ : Unit => 1) u
  have hlog : u'.log = u.log :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_log hF _ u
  have heval (x : Unit → ℤ) :
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u' =
        D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_eval hF _ u x
  refine ⟨u', (heval 0).trans hu0, ?_, ?_, ?_⟩
  · simpa only [hlog] using huc
  · simpa only [hlog] using humap
  · intro x
    rw [heval]
    exact hueval x

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFreeFamily
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

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

theorem exists_coefficient_bases (hP : 0 ≤ P) (hbP : b ≤ P) :
    Nonempty (D.CoefficientBases (coefficientSpaceBasisBudget P)) := by
  classical
  choose c hc e he using fun d : Fin s =>
    D.exists_coefficient_space_bases hP hbP
      ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ (Nat.succ_pos d.val)
  exact ⟨⟨c, e, hc, he⟩⟩

theorem exists_controlled_coefficient_bases :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s r N : ℕ} [NeZero N] {b p q P : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P), 0 ≤ P → b ≤ P → Nonempty (D.CoefficientBases ((P + C) ^ C)) := by
  obtain ⟨C, hC, hbound⟩ := coefficientSpaceBasisBudget_bound
  refine ⟨C, hC, ?_⟩
  intro s r N _ b p q P W out H R D hP hbP
  obtain ⟨B⟩ := D.exists_coefficient_bases hP hbP
  exact ⟨B.mono D (hbound P hP)⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_common_free_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M)
      (E : RationalFilteredNilmanifold W.L s W.dim) (S : E.DegreeRankStructure r),
      S.filtration = W.rank.filtration → E.basis = W.model.basis →
      0 ≤ M → S.ComplexityLE M → ∀ (I : Type*) [Fintype I]
      (U : E.UnitVerticalObservable (S.realSubgroup s r) I M),
      ∃ F : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
          (finrank ℚ D.CoefficientFreeLieAlgebra),
        ∃ T : F.DegreeRankStructure r,
          T.filtration = D.coefficientFreeFiltration ∧
          T.ComplexityLE ((M + C) ^ C) ∧ IsCentralLieBasis F.basis ∧
          Nonempty (FreeCoordinateFrame F.basis ((M + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (E.basis.repr (B.freeEvaluation D (F.basis j)) i) ≤ (M + C) ^ C) ∧
          F.lattice ≤ E.lattice.comap (mapOfSteps
            (hL := F.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 F.basis
           ∃ V : F.UnitVerticalObservable (T.realSubgroup s r) I ((M + C) ^ C),
             V.frequency = U.frequency.comp (B.freeEvaluation D).toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.observable i (QuotientGroup.mk (realificationMap
                 (hnil := F.filtration.lowerCentralSeries_eq_bot)
                 (hM := E.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D) x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_free_unit_observable s
  let K₀ : Polynomial ℕ := Polynomial.C (2 * s + 1) * Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M W out H R D B E S hS hE hM hcomplex I _ U
  let K := ((2 * s + 1 : ℕ) : ℝ) * M + 1
  have hcoef : (1 : ℝ) ≤ (2 * s + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * s + 1 by omega)
  have hMK : M ≤ K := by dsimp only [K]; nlinarith
  have hK : 0 ≤ K := hM.trans hMK
  have hdim : (W.dim : ℝ) ≤ M := hcomplex.1.1
  have hcard : (Fintype.card D.CoefficientAlphabet : ℝ) ≤ K := by
    calc
      _ ≤ (2 : ℝ) * s * W.dim := by exact_mod_cast D.coefficientAlphabet_card
      _ ≤ (2 : ℝ) * s * M := mul_le_mul_of_nonneg_left hdim (by positivity)
      _ ≤ K := by dsimp only [K]; push_cast; nlinarith
  have hbound : (K + a) ^ a ≤ (M + C) ^ C := by
    simpa [K₀, K, Polynomial.eval₂_pow] using hbudget M hM
  have hgen (x : D.CoefficientAlphabet) :
      B.generator D x ∈ S.filtration.layer (D.coefficientWeight x) 0 := by
    rw [hS]
    exact B.generator_mem_layer D x
  have hheight (x : D.CoefficientAlphabet) (i : Fin W.dim) :
      rationalLogHeight (E.basis.repr (B.generator D x) i) ≤ K := by
    rw [hE]
    exact (B.generator_height D x i).trans hMK
  obtain ⟨F, T, hT, hTc, hcentral, ⟨frame⟩, hmatrix, hlattice, hV⟩ :=
    hfree D.CoefficientAlphabet W.L I r W.dim W.rank.filtration.rank_le_degree E S
      D.coefficientWeight D.coefficientWeight_pos (B.generator D) hgen K hK hcard
      (hcomplex.mono S hMK) hheight (U.mono hMK)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 F.basis
  obtain ⟨V, hfreq, hobs⟩ := hV
  have heval : FreeDegreeRankLieAlgebra.lift S.filtration D.coefficientWeight
      D.coefficientWeight_pos (B.generator D) hgen = B.freeEvaluation D := by
    apply FreeDegreeRankLieAlgebra.hom_ext
    intro x
    exact (FreeDegreeRankLieAlgebra.lift_of _ _ _ _ _ x).trans
      (B.freeEvaluation_generator D x).symm
  rw [heval] at hmatrix hlattice hfreq hobs
  refine ⟨F, T, hT, hTc.mono T hbound, hcentral,
    ⟨frame.mono hbound⟩, (fun i j => (hmatrix i j).trans hbound), hlattice, ?_⟩
  exact ⟨V.mono hbound, hfreq, hobs⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentIntegralModel
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

abbrev DependentQuotient := D.CoefficientFreeLieAlgebra ⧸ D.dependentWordIdeal 0 2 0

noncomputable def dependentQuotientMap : D.CoefficientFreeLieAlgebra →ₗ⁅ℚ⁆ D.DependentQuotient :=
  lieQuotientMap (D.dependentWordIdeal 0 2 0)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end


