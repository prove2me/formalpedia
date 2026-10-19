-- Prove2me | Definitions.Def_OAIE3v2B205
-- name    : OAIE3v2B205
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:13:07.667066+00:00
-- url     : https://prove2.me/theorems/95f50781-9553-4fdc-aee5-e8ab6848e271
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 209 of 311
-- statement:
--   Definitions bundle 209 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B179`, `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B182`, `OAIE3v2B185`, `OAIE3v2B187`, `OAIE3v2B188` of this split.
--
--   Modules: `Estimates/CubeSignalAlgebra.lean`, `Estimates/MixedFrozenMiddleRows.lean`, `Estimates/NativeIteratedDifferencing.lean`, `Estimates/NativeMixedCubeResiduals.lean`, `Estimates/NativeResidualMultiplier.lean`, `Estimates/NativeRetainedTargetCubeIntervals.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/PrescribedInvariantUnit.lean`, `Estimates/ShiftedVerticalExpansion.lean`, `Estimates/UnitVerticalMeanRowCorrelation.lean`, `Fourier/NativeMixedFourierProfiles.lean`, `Lattices/MultidegreeIntegerTranslation.lean`, `Lattices/NativeIntegerDivision.lean`, `Lattices/NativeIntegerEquivalenceFiniteFamily.lean`, `Lattices/NativeIntegerHalving.lean`, `Linear/NativeCoefficientKernel.lean`, `Polynomial/CubicResidualPhase.lean`, `Polynomial/NativeZeroDegreeCorrelation.lean`, `Polynomial/PositiveDegreeCyclicDifference.lean`, `Polynomial/StepOneScalarPhase.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B179
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B182
import Definitions.Def_OAIE3v2B185
import Definitions.Def_OAIE3v2B187
import Definitions.Def_OAIE3v2B188

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3

namespace NativeMixedCorrelation

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  (W : NativeMixedCorrelation s N p f)

noncomputable def mono (hpq : p ≤ q) : NativeMixedCorrelation s N q f where
  shifts := W.shifts
  nonempty := W.nonempty
  density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg _)).trans W.density
  mixed := W.mixed.mono hpq
  correlation h hh := by
    obtain ⟨V⟩ := W.correlation h hh
    exact ⟨V.mono hpq⟩

end NativeMixedCorrelation

end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation s N p f)

noncomputable def residualWitness (h : {h // h ∈ M.shifts}) :
    NativeVectorCorrelation (s - 1) N p (nativeMixedResidual f M.mixed h.val) :=
  Classical.choice (M.correlation h.val h.property)

noncomputable def normalizedResidualRow (h n : ZMod N) : ℂ :=
  if hh : h ∈ M.shifts then
    multiplicativeDerivative f h n *
      star (((M.residualWitness ⟨h, hh⟩).test.expNormalize p).evalCyclic N (fun _ => n))
  else 0

theorem normalizedResidualRow_norm (hf : ∀ n, ‖f n‖ ≤ 1) (h n : ZMod N) :
    ‖M.normalizedResidualRow h n‖ ≤ 1 := by
  classical
  by_cases hh : h ∈ M.shifts
  · rw [normalizedResidualRow, dif_pos hh, norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      (multiplicativeDerivative_norm_le_one f hf h n)).trans
    apply (((M.residualWitness ⟨h, hh⟩).test.expNormalize p).norm_eval_le _).trans
    exact_mod_cast (M.residualWitness ⟨h, hh⟩).test.expNormalize_norm
      (M.residualWitness ⟨h, hh⟩).complexity
  · simp only [normalizedResidualRow, dif_neg hh, norm_zero, zero_le_one]

theorem normalizedResidualRow_correlation (h : ZMod N) (hh : h ∈ M.shifts) :
    Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
      star (M.mixed.evalCyclic N (M.residualWitness ⟨h, hh⟩).coordinate (correlationInput h n))‖ := by
  classical
  let V := M.residualWitness ⟨h, hh⟩
  have heval (n : ZMod N) : (V.test.expNormalize p).evalCyclic N (fun _ => n) =
      (Real.exp (-p) : ℂ) * V.test.evalCyclic N (fun _ => n) := rfl
  have hmean : (𝔼 n : ZMod N, M.normalizedResidualRow h n *
      star (M.mixed.evalCyclic N V.coordinate (correlationInput h n))) =
      (Real.exp (-p) : ℂ) * (𝔼 n : ZMod N,
        nativeMixedResidual f M.mixed h V.coordinate n * star (V.test.evalCyclic N (fun _ => n))) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    rw [normalizedResidualRow, dif_pos hh]
    change (multiplicativeDerivative f h n * star ((V.test.expNormalize p).evalCyclic N (fun _ => n))) *
      star (M.mixed.evalCyclic N V.coordinate (correlationInput h n)) = _
    rw [heval, star_mul]
    simp only [nativeMixedResidual, Complex.star_def, Complex.conj_ofReal]
    ring
  change Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
    star (M.mixed.evalCyclic N V.coordinate (correlationInput h n))‖
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left V.correlation (Real.exp_nonneg _)

theorem exists_fixed_normalized_residual_coordinate :
    ∃ out : Fin M.mixed.outputDim, ∃ H : Finset (ZMod N), H ⊆ M.shifts ∧ H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
        star (M.mixed.evalCyclic N out (correlationInput h n))‖ := by
  classical
  let rel := fun (h : ZMod N) (_ : Unit) (out : Fin M.mixed.outputDim) =>
    Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
      star (M.mixed.evalCyclic N out (correlationInput h n))‖
  have hc : ∀ h ∈ M.shifts, ∀ z : Unit, ∃ out, rel h z out := by
    intro h hh _
    exact ⟨(M.residualWitness ⟨h, hh⟩).coordinate, M.normalizedResidualRow_correlation h hh⟩
  have hcount : (Fintype.card (Fin M.mixed.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using M.mixed.output_bound
  obtain ⟨out, H, hsub, hH, hsize, hcorr⟩ :=
    exists_large_fixed_choices M.shifts M.nonempty rel hc hcount
  have hsize' : Real.exp (-p) * (M.shifts.card : ℝ) ≤ (H.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize
  have hdensity : Real.exp (-p) * N ≤ (M.shifts.card : ℝ) := by
    simpa only [ZMod.card] using M.density
  refine ⟨out (), H, hsub, hH, ?_, fun h hh => hcorr h hh ()⟩
  calc
    _ = Real.exp (-p) * (Real.exp (-p) * N) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-p) * (M.shifts.card : ℝ) :=
      mul_le_mul_of_nonneg_left hdensity (Real.exp_nonneg _)
    _ ≤ _ := hsize'

end Erdos3.NativeMixedCorrelation

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation s N p f)

noncomputable def residualMultiplier (h : ZMod N) (x : Unit → ℤ) : ℂ :=
  if hh : h ∈ M.shifts then ((M.residualWitness ⟨h, hh⟩).test.expNormalize p).eval x else 0

theorem residualMultiplier_norm (h : ZMod N) (x : Unit → ℤ) :
    ‖M.residualMultiplier h x‖ ≤ 1 := by
  classical
  by_cases hh : h ∈ M.shifts
  · rw [residualMultiplier, dif_pos hh]
    apply (((M.residualWitness ⟨h, hh⟩).test.expNormalize p).norm_eval_le x).trans
    exact_mod_cast (M.residualWitness ⟨h, hh⟩).test.expNormalize_norm
      (M.residualWitness ⟨h, hh⟩).complexity
  · simp only [residualMultiplier, dif_neg hh, norm_zero, zero_le_one]

theorem normalizedResidualRow_factor (h n : ZMod N) :
    M.normalizedResidualRow h n =
      multiplicativeDerivative f h n * star (M.residualMultiplier h (fun _ => (n.val : ℤ))) := by
  classical
  by_cases hh : h ∈ M.shifts
  · simp only [normalizedResidualRow, residualMultiplier, dif_pos hh]
    rfl
  · simp only [normalizedResidualRow, residualMultiplier, dif_neg hh, star_zero, mul_zero]

theorem residualMultiplier_expansion (h : ZMod N) :
    Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) p (M.residualMultiplier h)) := by
  classical
  by_cases hh : h ∈ M.shifts
  · let V := M.residualWitness ⟨h, hh⟩
    refine ⟨NativeIntegerExpansion.ofTest (V.test.expNormalize p)
      (V.test.expNormalize_complexity V.complexity) ?_⟩
    intro x
    simp only [residualMultiplier, dif_pos hh]
    rfl
  · obtain ⟨h₀, hh₀⟩ := M.nonempty
    let V := M.residualWitness ⟨h₀, hh₀⟩
    refine ⟨NativeIntegerExpansion.ofTest (V.test.scaleComplex 0)
      (V.test.scaleComplex_complexity (by simp) V.complexity) ?_⟩
    intro x
    simp only [residualMultiplier, dif_neg hh,
      RationalFilteredNilmanifold.Niltest.scaleComplex_eval, zero_mul]

end Erdos3.NativeMixedCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedVerticalExpansion
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_uniform_two_shift_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
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
      (p : ℝ), 0 ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE p →
      ∃ (n : ℕ) (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s n),
        Q.GeometryComplexityLE (squareGeometryBudget p) ∧
        ∀ (χ : D.RealGroup → CircleFourier.Circle),
          (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
            T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ a b : σ → ℤ, ∃ S : Q.Niltest w,
          S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
          ∀ x : σ → ℤ, S.eval x = T.eval (x + a) * star (T.eval (x + b)) := by
  obtain ⟨a, _, hnorm⟩ := exists_bounded_realified_square_orbit (s + 1)
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp w hw T hT
  obtain ⟨e, ω, hF, N, hN, hin, hout, _, hgeom, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  refine ⟨_, _, hgeom, ?_⟩
  intro χ hvert h k
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hT.1 w hw (h - k) T.orbit
  obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
  obtain ⟨S, _, _, hSB, hS, hSval⟩ := hconstruct ε q χ hvert A hA (hALip ε hε)
  have hval (x : σ → ℤ) : S.eval x = T.eval (x + (h - k)) * star (T.eval x) := by
    exact (hSval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice ε γ
      (D.filtration.realification.polynomialOrbitEval w (fun i => x i + (h - k) i) T.orbit)
      (D.filtration.realification.polynomialOrbitEval w x T.orbit) hγ T.observable
      (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) (hq x).1 (hq x).2)
  refine ⟨S.translate hw k, hSB, hS.mono (hbudget p hp), ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_translate, hval]
  congr 2
  abel

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_shifted_product_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
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
      {p : ℝ} (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      {w : σ → ℕ} (g : D.filtration.realification.PolynomialOrbit w),
      0 ≤ p → D.GeometryComplexityLE p → (∀ k, 0 < w k) → ∀ (i j : I) (a b : σ → ℤ),
      ∃ (n : Fin 4 → ℕ)
        (Q : ∀ k, RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s (n k))
        (S : ∀ k, (Q k).Niltest w),
        (∀ k, (S k).normBound = 4) ∧ (∀ k, (S k).ComplexityLE ((p + C) ^ C)) ∧
        ∀ x, V.observable i (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w (x + a) g)) *
          star (V.observable j (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w (x + b) g))) =
          ∑ k, polarizationWeight k * (S k).eval x := by
  obtain ⟨A, _, hsquare⟩ := exists_uniform_two_shift_square s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + 5 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ d D _ _ _ _ _ _ _ _ p V w g hp hD hw i j a b
  have hbound : (p + 5 + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  let T : Fin 4 → D.Niltest w := fun k =>
    V.combinationNiltest g i j (polarizationPhase k) (polarizationPhase_norm k).le
  have hparts : ∀ k, ∃ (n : ℕ)
      (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)) s n) (S : Q.Niltest w),
      S.normBound = 4 ∧ S.ComplexityLE ((p + C) ^ C) ∧
      ∀ x, S.eval x = (T k).eval (x + a) * star ((T k).eval (x + b)) := by
    intro k
    obtain ⟨n, Q, _, hconstruct⟩ := hsquare D (p + 5) (by linarith) w hw (T k)
      (V.combinationNiltest_complexity g i j _ _ hp hD)
    obtain ⟨S, hSn, hSc, hSe⟩ := hconstruct
      (fun z => ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle))
      (fun z hz x => V.coordinateCombination_vertical i j (polarizationPhase k) z hz x) a b
    refine ⟨n, Q, S, ?_, hSc.mono hbound, hSe⟩
    calc
      S.normBound = (T k).normBound ^ 2 := hSn
      _ = 4 := by norm_num [T, combinationNiltest]
  choose n Q S hSn hSc hSe using hparts
  refine ⟨n, Q, S, hSn, hSc, ?_⟩
  intro x
  refine (complex_mixed_polarization _
    (V.observable j (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w (x + a) g)))
    (V.observable i (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w (x + b) g))) _).trans ?_
  apply Finset.sum_congr rfl
  intro k _
  rw [hSe k x]
  rfl

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MultidegreeIntegerTranslation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_integer_translation_equivalence_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p →
      ∀ a b : σ → ℤ,
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun i x => V.observable i (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) (x + a) g)))
        (fun i x => V.observable i (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval (fun _ : σ => 1) (x + b) g))) := by
  obtain ⟨A, _, hexpand⟩ := exists_shifted_product_expansion s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + X + 4)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ d D p V g hp hD hI a b
  let r := (p + A) ^ A
  let q := r + p + 4
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hrq : r ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hbound : q ≤ (p + C) ^ C := by
    simpa [q, r, X, Polynomial.eval₂_pow] using hbudget p hp
  have hd := hI.trans (Real.exp_le_exp.mpr (hpq.trans hbound))
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ D.filtration.squareLieSubalgebra)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1))) :=
    realification_moduleTopology_t2 (Module.finBasis ℚ (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))
  refine ⟨hd, hd, ?_⟩
  intro i j
  obtain ⟨n, Q, S, _, hSc, hSe⟩ := hexpand D V g hp hD (fun _ => Nat.zero_lt_one) i j a b
  have hcard : (Fintype.card (Fin 4) : ℝ) ≤ Real.exp q := by
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    have h4 : 4 ≤ q := by dsimp [q]; linarith
    linarith [Real.add_one_le_exp q]
  have hcost : (∑ k, ‖polarizationWeight k‖) ≤ Real.exp q := by
    rw [polarizationWeight_cost]
    exact Real.one_le_exp hq
  exact ⟨(NativeIntegerExpansion.ofFamily Q S polarizationWeight hcard
    (fun k => (hSc k).mono hrq) hcost hSe).mono hbound⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_multidegree_integer_translation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] (bound : σ → ℕ),
      (∑ i, bound i) = s + 1 → ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (a b : σ → ℤ), NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun i x => W.eval i (x + a)) (fun i x => W.eval i (x + b)) := by
  obtain ⟨C, hC, htranslate⟩ := UnitVerticalObservable.exists_integer_translation_equivalence_budget s
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hdegree p W a b
  rw [← hdegree] at htranslate
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let U : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (∑ i, bound i)) (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (W.multi.realSubgroup_top.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (W.multi.realSubgroup_top.symm ▸ hz) hL }
  have hI : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model U (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hI a b
  have heval (i : Fin W.outputDim) (x : σ → ℤ) :
      U.observable i (QuotientGroup.mk
        (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (W.multi.orbitToOrdinary W.orbit))) = W.eval i x := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  simpa only [heval] using E

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedInvariantUnit
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct NNReal BigOperators

theorem exists_native_unit_vertical_completion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ eta : L →ₗ[ℚ] ℚ,
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        T.observable (z • x) =
          character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ y : D.Space, Real.exp (-p) ≤ ‖T.observable y‖ →
      ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ v : Fin (n + 1) → D.Space → ℂ,
        (∀ x, v 0 x = T.observable x / 2) ∧
        (∀ x, ∑ i, ‖v i x‖ ^ 2 = 1) ∧
        (∀ i x, ‖v i x‖ ≤ 1) ∧
        (letI := D.metricSpace; ∀ i, LipschitzWith K (v i)) ∧
        ∀ i z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          v i (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * v i x := by
  obtain ⟨a, _, hfamily⟩ := exists_native_unit_vertical_family s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + Polynomial.C a) ^ a + 1)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT hnorm eta hvertical y hy
  let := D.metricSpace
  let P := (p + a) ^ a
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have htotal : p + P + 1 ≤ (p + C) ^ C := by
    simpa [X, P, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨n, hn, hnc, K, hK, v, hvunit, hvnorm, hvLip, hvphase⟩ :=
    hfamily D T hp hT hnorm eta hvertical y hy
  let f (x : D.Space) := T.observable x / 2
  have htwoNorm : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  have hf (x : D.Space) : ‖f x‖ ≤ 1 / 2 := by
    have hn' : (T.normBound : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hnorm
    dsimp [f]
    rw [norm_div, htwoNorm]
    exact div_le_div_of_nonneg_right ((T.norm_le x).trans hn') (by norm_num)
  have hfLip : LipschitzWith T.lipBound f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (T.observable x / 2) (T.observable y / 2) ≤ _
    rw [dist_eq_norm, ← sub_div, norm_div, htwoNorm]
    have h := T.lipschitz.dist_le_mul x y
    rw [dist_eq_norm] at h
    linarith [norm_nonneg (T.observable x - T.observable y)]
  obtain ⟨u, hu0, huunit, hunorm, huLip, huphase⟩ :=
    exists_complex_unit_completion f v hf hfLip hvunit hvnorm hvLip
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hcount : (n : ℝ) + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith [Real.one_le_exp hP]
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hsum : ((T.lipBound + K : ℝ≥0) : ℝ) ≤ Real.exp (p + P + 1) := by
    have hTlip : (T.lipBound : ℝ) ≤ Real.exp p := by
      linarith [Niltest.observable_budget hT, T.normBound.coe_nonneg]
    have ht := hTlip.trans (Real.exp_le_exp.mpr (show p ≤ p + P by linarith))
    have hk := hK.trans (Real.exp_le_exp.mpr (show (p + a) ^ a ≤ p + P by dsimp [P]; linarith))
    calc
      _ ≤ 2 * Real.exp (p + P) := by push_cast; linarith
      _ ≤ Real.exp 1 * Real.exp (p + P) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨n, hn, hcount.trans (Real.exp_le_exp.mpr (by linarith)),
    T.lipBound + K, hsum.trans (Real.exp_le_exp.mpr htotal), u, hu0, huunit, hunorm, huLip, ?_⟩
  intro i z hz x
  apply huphase (z • x) x _ (norm_character _) ?_ (fun j => hvphase j z hz x) i
  dsimp [f]
  rw [hvertical z hz]
  ring

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerHalving
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

theorem exists_fin_prod_budget (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
      (f : Fin n → (σ → ℤ) → ℂ), 0 ≤ p →
      (∀ i, Nonempty (NativeIntegerExpansion w s p (f i))) →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) (fun x => ∏ i, f i x)) := by
  induction n with
  | zero =>
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Polynomial.X + 2)
    refine ⟨C, hC, ?_⟩
    intro σ w s p f hp _
    have hcost : p + 2 ≤ (p + C) ^ C := by simpa using hbudget p hp
    exact ⟨by simpa using (constOne w s (by linarith : 2 ≤ p + 2)).mono hcost⟩
  | succ n ih =>
    obtain ⟨A, _, hprod⟩ := ih
    obtain ⟨B, _, hmul⟩ := exists_mul_budget
    let X : Polynomial ℕ := Polynomial.X
    let T := X + (X + Polynomial.C A) ^ A
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
    refine ⟨C, hC, ?_⟩
    intro σ w s p f hp hf
    let t := p + (p + A) ^ A
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
    have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
    obtain ⟨tail⟩ := hprod (fun i => f i.succ) hp (fun i => hf i.succ)
    obtain ⟨H⟩ := hmul ht ((Classical.choice (hf 0)).mono hpt) (tail.mono hAt)
    have hcost : (t + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
    exact ⟨by simpa only [Fin.prod_univ_succ] using H.mono hcost⟩

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_pairParityIndicator_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ r : Fin 2 → ZMod 2,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (C : ℝ) (pairParityIndicator r)) := by
  obtain ⟨A, hA, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  refine ⟨(4 + A) ^ A + 2, by omega, ?_⟩
  intro r
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  obtain ⟨E0⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 0 (r 0) (by norm_num : (0 : ℝ) ≤ 2) htwo
  obtain ⟨E1⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 1 (r 1) (by norm_num : (0 : ℝ) ≤ 2) htwo
  obtain ⟨E⟩ := hmul (by norm_num : (0 : ℝ) ≤ 2 + 2) E0 E1
  have hb : ((2 : ℝ) + 2 + A) ^ A ≤ (((4 + A) ^ A + 2 : ℕ) : ℝ) := by
    push_cast
    norm_num
  have heq : (fun x => (if (x 0 : ZMod 2) = r 0 then (1 : ℂ) else 0) *
      (if (x 1 : ZMod 2) = r 1 then 1 else 0)) = pairParityIndicator r := by
    funext x
    exact (pairParityIndicator_product r x).symm
  rw [heq] at E
  exact ⟨E.mono hb⟩

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem exists_tensor_power_budget (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p f g →
      NativeIntegerVectorEquivalence s ((p + C) ^ C) (tensorVector f n) (tensorVector g n) := by
  obtain ⟨A, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C n * X)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s p f g hp E
  have hsum : (p + A) ^ A + n * p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by
    have hn : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
    linarith
  have hnp : (n : ℝ) * p ≤ (p + C) ^ C := by
    have ha : 0 ≤ (p + A) ^ A := by positivity
    linarith
  have hI : (Fintype.card (Fin n → I) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) E.left_dimension n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  have hJ : (Fintype.card (Fin n → J) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) E.right_dimension n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  refine ⟨hI, hJ, ?_⟩
  intro a b
  obtain ⟨F⟩ := hprod (fun k x => f (a k) x * star (g (b k) x)) hp
    (fun k => E.expansion (a k) (b k))
  have heq : (fun x => ∏ k, f (a k) x * star (g (b k) x)) =
      (fun x => tensorVector f n a x * star (tensorVector g n b x)) := by
    funext x
    simp only [tensorVector, Finset.prod_mul_distrib, star_prod]
  exact ⟨heq ▸ F.mono hcost⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

theorem exists_halving_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} {f : (Fin 2 → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 p f →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (fun x => f (fun i => x i / 2))) := by
  obtain ⟨A, hA, hparity⟩ := exists_pairParityIndicator_expansion
  obtain ⟨B, _, hmul⟩ := exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A + 2 + Polynomial.C B) ^ B + 2)
  refine ⟨C, hC, ?_⟩
  intro p f hp E
  classical
  let t : ℝ := p + A + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) A; linarith
  have hAt : (A : ℝ) ≤ t := by dsimp [t]; linarith
  let P (r : Fin 2 → ZMod 2) := halvingPolynomial (fun i => ((r i).val : ℤ))
  have hP (r : Fin 2 → ZMod 2) (i : Fin 2) :
      P r i ∈ weightedSupportLE (fun _ : Fin 2 => 1) 1 := halvingPolynomial_support _ i
  let F (r : Fin 2 → ZMod 2) := E.substitutedValue (P r) (hP r)
  have hF (r : Fin 2 → ZMod 2) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((t + B) ^ B) (fun x => pairParityIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hparity r)).mono hAt)
      ((E.substituteExpansion (P r) (hP r)).mono hpt)
  have hc : (Fintype.card (Fin 2 → ZMod 2) : ℝ) ≤ Real.exp 2 := by
    norm_num only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hh := Real.add_one_le_exp (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hcost : (∑ _ : Fin 2 → ZMod 2, ‖(1 : ℂ)‖) ≤ Real.exp 2 := by simpa using hc
  let S := weightedSum (fun r => Classical.choice (hF r)) (fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 2) hc hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod 2, (1 : ℂ) * (pairParityIndicator r x * F r x)) =
      (fun x => f (fun i => x i / 2)) := by
    funext x
    let r : Fin 2 → ZMod 2 := fun i => (x i : ZMod 2)
    rw [Finset.sum_eq_single r]
    · simp only [pairParityIndicator, r, ite_true, one_mul]
      apply E.substitutedValue_eq (P r) (hP r) x (fun i => x i / 2)
      exact halvingPolynomial_eval _ x (fun i => (ZMod.val_intCast (x i)).symm)
    · intro a _ ha
      have hne : (fun i => (x i : ZMod 2)) ≠ a := fun h => ha h.symm
      simp only [pairParityIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  have hb : (t + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [t, X, Polynomial.eval₂_pow] using hbudget p hp
  rw [heq] at S
  exact ⟨S.mono hb⟩

end Erdos3.NativeIntegerExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerEquivalenceFiniteFamily
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem exists_fin_product_budget (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      (f : Fin n → I → (σ → ℤ) → ℂ) (g : Fin n → J → (σ → ℤ) → ℂ),
      0 ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p → (Fintype.card J : ℝ) ≤ Real.exp p →
      (∀ i, NativeIntegerVectorEquivalence s p (f i) (g i)) →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun a : Fin n → I => fun x => ∏ i, f i (a i) x)
        (fun b : Fin n → J => fun x => ∏ i, g i (b i) x) := by
  obtain ⟨A, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C n * X)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s p f g hp hI hJ E
  have hsum : (p + A) ^ A + n * p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by
    have hn : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
    linarith
  have hnp : (n : ℝ) * p ≤ (p + C) ^ C := by
    have ha : 0 ≤ (p + A) ^ A := by positivity
    linarith
  have hIn : (Fintype.card (Fin n → I) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) hI n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  have hJn : (Fintype.card (Fin n → J) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) hJ n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  refine ⟨hIn, hJn, ?_⟩
  intro a b
  obtain ⟨F⟩ := hprod (σ := σ) (w := fun _ : σ => 1) (s := s)
    (fun k x => f k (a k) x * star (g k (b k) x)) hp
    (fun k => (E k).expansion (a k) (b k))
  have heq : (fun x => ∏ k, f k (a k) x * star (g k (b k) x)) =
      (fun x => (∏ k, f k (a k) x) * star (∏ k, g k (b k) x)) := by
    funext x
    simp only [Finset.prod_mul_distrib, star_prod]
  exact ⟨heq ▸ F.mono hcost⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem exists_finite_product_budget (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      (f : ι → I → (σ → ℤ) → ℂ) (g : ι → J → (σ → ℤ) → ℂ),
      0 ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p → (Fintype.card J : ℝ) ≤ Real.exp p →
      (∀ i, NativeIntegerVectorEquivalence s p (f i) (g i)) →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun a : ι → I => fun x => ∏ i, f i (a i) x)
        (fun b : ι → J => fun x => ∏ i, g i (b i) x) := by
  obtain ⟨C, hC, hprod⟩ := exists_fin_product_budget (Fintype.card ι)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s p f g hp hI hJ E
  classical
  let e := (Fintype.equivFin ι).symm
  have F := hprod (fun j => f (e j)) (fun j => g (e j)) hp hI hJ (fun j => E (e j))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using F.left_dimension
  · simpa only [Fintype.card_fun, Fintype.card_fin] using F.right_dimension
  · intro a b
    have h := F.expansion (fun j => a (e j)) (fun j => b (e j))
    have hf (x : σ → ℤ) : (∏ j, f (e j) (a (e j)) x) = ∏ i, f i (a i) x :=
      e.prod_comp (fun i => f i (a i) x)
    have hg (x : σ → ℤ) : (∏ j, g (e j) (b (e j)) x) = ∏ i, g i (b i) x :=
      e.prod_comp (fun i => g i (b i) x)
    simpa only [hf, hg] using h

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeSignalAlgebra
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

theorem mixedCubeWithShift_unit {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : (Fin d → Bool) → ℤ) (x : Fin (d + 2) → ℤ) :
    ∑ a, ‖M.mixedCubeWithShift c a x‖ ^ 2 = 1 := by
  simp only [mixedCubeWithShift, norm_prod, ← Finset.prod_pow, conjugationPower_norm]
  rw [← Fintype.prod_sum (fun ω (i : Fin M.outputDim) =>
    ‖M.eval i (mixedCubeInput ω x + ![0, c ω])‖ ^ 2)]
  simp only [M.unit_eval, Finset.prod_const_one]

theorem exists_mixed_cube_translation (s d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
      (c : (Fin d → Bool) → ℤ),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (M.mixedCubeWithShift c) (M.mixedCubeWithShift 0) := by
  obtain ⟨A, _, htranslate⟩ := exists_multidegree_integer_translation s
  obtain ⟨B, _, hprod⟩ := NativeIntegerVectorEquivalence.exists_finite_product_budget (Fin d → Bool)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let U := X + P
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p M c
  have hp : 0 ≤ p := (Nat.cast_nonneg M.dim).trans M.complexity.1.1
  let q := (p + A) ^ A
  let u := p + q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := add_nonneg hp hq
  have hpu : p ≤ u := le_add_of_nonneg_right hq
  have hqu : q ≤ u := le_add_of_nonneg_left hp
  have hcost : (u + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, P, U, q, u, Polynomial.eval₂_pow] using hbudget p hp
  have hdegree : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
    rw [Fin.sum_univ_two]
    change 1 + s = s + 1
    omega
  let F (ω : Fin d → Bool) : Fin 2 → ((Fin (d + 2) → ℤ) →+ ℤ) := fun i =>
    { toFun := fun x => mixedCubeInput ω x i
      map_zero' := by
        fin_cases i <;> simp [mixedCubeInput, correlationInput, cubeShift]
        rfl
      map_add' := by
        intro x y
        fin_cases i
        · rfl
        · change x 1 + y 1 + cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
            (x 1 + cubeShift (fun j => x j.succ.succ) ω) +
              (y 1 + cubeShift (fun j => y j.succ.succ) ω)
          have hs : cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
              cubeShift (fun j => x j.succ.succ) ω + cubeShift (fun j => y j.succ.succ) ω := by
            simp only [cubeShift, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp
          rw [hs]
          ring }
  have hzero : (![0, 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> rfl
  have E (ω : Fin d → Bool) : NativeIntegerVectorEquivalence s u
      (fun i x => M.eval i (mixedCubeInput ω x + ![0, c ω]))
      (fun i x => M.eval i (mixedCubeInput ω x + ![0, 0])) := by
    have T := ((htranslate (mixedCorrelationDegree s) hdegree M ![0, c ω] 0).linearPullbackHom (F ω)).mono hqu
    change NativeIntegerVectorEquivalence s u
      (fun i x => M.eval i (mixedCubeInput ω x + ![0, c ω]))
      (fun i x => M.eval i (mixedCubeInput ω x + 0)) at T
    simpa only [hzero] using T
  have hdim : (Fintype.card (Fin M.outputDim) : ℝ) ≤ Real.exp u := by
    simpa only [Fintype.card_fin] using M.output_bound.trans (Real.exp_le_exp.mpr hpu)
  exact (hprod _ _ hu hdim hdim (fun ω => (E ω).conjugationPower (booleanWeight ω))).mono hcost

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem NativeIntegerVectorEquivalence.exists_mixed_cube_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      {f : I → (Fin 2 → ℤ) → ℂ} {g : J → (Fin 2 → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p f g →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (mixedCubeObservable (d := d) f) (mixedCubeObservable (d := d) g) := by
  obtain ⟨C, hC, hprod⟩ := NativeIntegerVectorEquivalence.exists_finite_product_budget (Fin d → Bool)
  refine ⟨C, hC, ?_⟩
  intro I J _ _ s p f g hp E
  have H (ω : Fin d → Bool) : NativeIntegerVectorEquivalence s p
      (fun i x => f i (mixedCubeInput ω x)) (fun j x => g j (mixedCubeInput ω x)) :=
    E.linearPullbackHom (mixedCubeInputHom ω)
  exact hprod _ _ hp E.left_dimension E.right_dimension
    (fun ω => (H ω).conjugationPower (booleanWeight ω))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_unit_vertical_mean_row_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ H X L : Type*}
      [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ}
      (T : D.Niltest w) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ (sample : H → X → σ → ℤ) (f : H → X → ℂ), (∀ h x, ‖f h x‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 x, f h x * star (T.eval (sample h x))‖) →
      ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
          (Fin (n + 1)) ((p + C) ^ C),
        D.GeometryComplexityLE ((p + C) ^ C) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 x, f h x * star ((V.test T.orbit 0).eval (sample h x))‖) := by
  obtain ⟨A, _, hmode⟩ := Niltest.exists_unit_bounded_vertical_mean_row
  obtain ⟨B, _, hcomplete⟩ := exists_native_unit_vertical_completion s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B + 1)
  refine ⟨C, hC, ?_⟩
  intro σ H Y L _ _ _ _ _ _ _ _ _ _ d D w T p hp hT sample f hf hcorr
  let q := (p + A) ^ A
  let r := (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r + 1 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨η, U, hU, hUnorm, horbit, hheight, hchar, hint, hcorrU⟩ :=
    hmode D T hp hT sample f hf hcorr
  obtain ⟨h, x, hx⟩ := exists_large_value_of_mean_row_correlation f
    (fun h x => U.eval (sample h x)) hf hcorrU
  let y : D.Space := QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w (sample h x) U.orbit)
  obtain ⟨n, hn, hncard, K, hK, v, hv0, hvunit, hvnorm, hvLip, hvchar⟩ :=
    hcomplete D U hq hU hUnorm η hchar y hx
  let V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
      (Fin (n + 1)) ((p + C) ^ C) :=
    { observable := v
      unit := hvunit
      norm := hvnorm
      lipBound := K
      lip_bound := hK.trans (Real.exp_le_exp.mpr hrC)
      lipschitz := hvLip
      frequency := η
      height := fun i => (hheight i).trans hqC
      vertical := hvchar
      integral := hint }
  have hscalar (z : σ → ℤ) : (V.test T.orbit 0).eval z = U.eval z / 2 := by
    rw [UnitVerticalObservable.test_eval]
    change v 0 _ = U.eval z / 2
    rw [hv0]
    unfold Niltest.eval
    rw [horbit]
  have hmean : (𝔼 h, ‖𝔼 x, f h x * star ((V.test T.orbit 0).eval (sample h x))‖) =
      (𝔼 h, ‖𝔼 x, f h x * star (U.eval (sample h x))‖) / 2 := by
    simp only [hscalar, star_div₀, star_ofNat, ← mul_div_assoc, ← Finset.expect_div,
      norm_div]
    norm_num
  refine ⟨n, hn, hncard.trans (Real.exp_le_exp.mpr hrC), V,
    hU.1.mono D hqC, ?_⟩
  rw [hmean]
  have hhalf : Real.exp (-(q + 1)) ≤ Real.exp (-q) / 2 := by
    simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-q)
  exact (Real.exp_le_exp.mpr (by linarith)).trans
    (hhalf.trans (div_le_div_of_nonneg_right hcorrU (by norm_num)))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PositiveDegreeCyclicDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_smoothedSecondDifference_expansion_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      ∀ (N : ℕ) (δ : ℝ≥0), 0 < δ → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p (integerSecondDifference u v k)) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p (integerSecondDifference u v (k - N))) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + e + C) ^ C)
        (smoothedSecondDifference N δ u v k)) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 6) ^ 2 + 7
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + Polynomial.C A) ^ A + R + 2)
  refine ⟨C, hC, ?_⟩
  intro p e hp he N δ hδ hinv u v k ⟨E0⟩ ⟨E1⟩
  let r := p + e + (p + e + 6) ^ 2 + 7
  let t := (r + A) ^ A + r
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + e + 6)]
  have her : raisedNiltestBudget (e + 4) ≤ r := by
    have hsq : (e + 6) ^ 2 ≤ (p + e + 6) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    dsimp [raisedNiltestBudget, r]
    nlinarith
  have hrt : r ≤ t := le_add_of_nonneg_left (by positivity)
  have hmt : (r + A) ^ A ≤ t := le_add_of_nonneg_right hr
  have htC : t + 2 ≤ (p + e + C) ^ C := by
    simpa [X, R, r, t, Polynomial.eval₂_pow] using hbudget (p + e) (by linarith)
  obtain ⟨EC⟩ := exists_fixed_shift_smoothCyclicCarry_expansion N δ hδ he hinv k
  obtain ⟨EM0⟩ := hmul hr ((EC.raiseStep hs (by linarith)).mono her) (E0.mono hpr)
  obtain ⟨EM1⟩ := hmul hr ((EC.raiseStep hs (by linarith)).mono her) (E1.mono hpr)
  let w (x : Fin 2 → ℤ) := (smoothCyclicCarry N δ ![k, x 1] : ℂ)
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![integerSecondDifference u v k,
    (fun x => w x * integerSecondDifference u v (k - N) x),
    (fun x => w x * integerSecondDifference u v k x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s t (fs j)) := by
    fin_cases j
    · exact ⟨E0.mono (hpr.trans hrt)⟩
    · exact ⟨EM1.mono hmt⟩
    · exact ⟨EM0.mono hmt⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono htC
  have heq : (fun x => ∑ j, cs j * fs j x) = smoothedSecondDifference N δ u v k := by
    funext x
    simp [cs, fs, w, Fin.sum_univ_succ, smoothedSecondDifference]
    ring
  exact ⟨heq ▸ E⟩

theorem exists_cyclicSecondDifference_approximation_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (u v : (Fin 2 → ℤ) → ℂ), (∀ x, ‖u x‖ ≤ 1) → (∀ x, ‖v x‖ ≤ 1) →
      (∀ k : ℤ, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p
        (integerSecondDifference u v k))) →
      ∀ k : ZMod N, ∃ K : (Fin 2 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + e + C) ^ C) K) ∧
        ∀ h : ℤ, (𝔼 n : ZMod N,
          ‖cyclicSecondDifference u v k h n - K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hexpand⟩ := exists_smoothedSecondDifference_expansion_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 16 + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p e hp he N _ hN u v hu hv hmodel k
  let δ : ℝ≥0 := ⟨Real.exp (-(e + 16)), (Real.exp_pos _).le⟩
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp (e + 16) := by
    change (Real.exp (-(e + 16)))⁻¹ ≤ Real.exp (e + 16)
    rw [← Real.exp_neg, neg_neg]
  have hbudget' : (p + (e + 16) + A) ^ A ≤ (p + e + C) ^ C := by
    have hb := hbudget (p + e) (by linarith)
    simpa [X, Polynomial.eval₂_pow, add_assoc] using hb
  obtain ⟨E⟩ := hexpand hp (by linarith : 0 ≤ e + 16) N δ hδ hinv u v k.val
    (hmodel k.val) (hmodel ((k.val : ℤ) - N))
  refine ⟨smoothedSecondDifference N δ u v k.val, ⟨E.mono hbudget'⟩, ?_⟩
  intro h
  apply (smoothedSecondDifference_mean_error δ hδ u v hu hv k h).trans
  have hNinv : 1 / (N : ℝ) ≤ Real.exp (-(e + 16)) := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (e + 16)) hN
    simpa only [one_div, ← Real.exp_neg] using hh
  have htwo : 2 / (N : ℝ) ≤ 2 * Real.exp (-(e + 16)) := by
    calc
      _ = 2 * (1 / (N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNinv (by norm_num)
  calc
    12 * (δ : ℝ) + 2 / N ≤ 14 * Real.exp (-(e + 16)) := by
      change 12 * Real.exp (-(e + 16)) + 2 / (N : ℝ) ≤ 14 * Real.exp (-(e + 16))
      linarith only [htwo]
    _ ≤ Real.exp 16 * Real.exp (-(e + 16)) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (16 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (-e) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerDivision
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_pairResidueIndicator_expansion (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ r : Fin 2 → ZMod d,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s (C : ℝ) (pairResidueIndicator r)) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let D := d + 2 + (d + 4) ^ 2 + 3
  refine ⟨(D + A) ^ A + 2, by omega, ?_⟩
  intro r
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  obtain ⟨E0⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 0 (r 0) (Nat.cast_nonneg d) hd
  obtain ⟨E1⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 1 (r 1) (Nat.cast_nonneg d) hd
  have hraise : raisedNiltestBudget ((d : ℝ) + 2) = (D : ℝ) := by
    dsimp [D, raisedNiltestBudget]
    push_cast
    ring
  have F0 : NativeIntegerExpansion (fun _ : Fin 2 => 1) s D
      (fun x => if (x 0 : ZMod d) = r 0 then 1 else 0) := by
    simpa only [hraise] using E0.raiseStep hs (by positivity)
  have F1 : NativeIntegerExpansion (fun _ : Fin 2 => 1) s D
      (fun x => if (x 1 : ZMod d) = r 1 then 1 else 0) := by
    simpa only [hraise] using E1.raiseStep hs (by positivity)
  obtain ⟨F⟩ := hmul (Nat.cast_nonneg D) F0 F1
  have hb : ((D : ℝ) + A) ^ A ≤ (((D + A) ^ A + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  have heq : (fun x => (if (x 0 : ZMod d) = r 0 then (1 : ℂ) else 0) *
      (if (x 1 : ZMod d) = r 1 then 1 else 0)) = pairResidueIndicator r := by
    funext x
    exact (pairResidueIndicator_product r x).symm
  rw [heq] at F
  exact ⟨F.mono hb⟩

theorem NativeIntegerExpansion.exists_division_expansion (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} {f : (Fin 2 → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion (fun _ : Fin 2 => 1) s p f →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + C) ^ C)
        (fun x => f (fun i => x i / (d : ℤ)))) := by
  obtain ⟨A, _, hresidue⟩ := exists_pairResidueIndicator_expansion d s hs
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A + 2 + Polynomial.C B) ^ B + Polynomial.C (d ^ 2))
  refine ⟨C, hC, ?_⟩
  intro p f hp E
  classical
  let t : ℝ := p + A + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) A; linarith
  have hAt : (A : ℝ) ≤ t := by dsimp [t]; linarith
  let P (r : Fin 2 → ZMod d) := divisionPolynomial d (fun i => ((r i).val : ℤ))
  have hP (r : Fin 2 → ZMod d) (i : Fin 2) :
      P r i ∈ weightedSupportLE (fun _ : Fin 2 => 1) 1 := divisionPolynomial_support d _ i
  let F (r : Fin 2 → ZMod d) := E.substitutedValue (P r) (hP r)
  have hF (r : Fin 2 → ZMod d) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s
      ((t + B) ^ B) (fun x => pairResidueIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hAt)
      ((E.substituteExpansion (P r) (hP r)).mono hpt)
  have hcost : (∑ _ : Fin 2 → ZMod d, ‖(1 : ℂ)‖) ≤ Real.exp ((d : ℝ) ^ 2) := by
    simpa using card_pairResidue_le_exp d
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hF r)) (fun _ => 1)
    (sq_nonneg (d : ℝ)) (card_pairResidue_le_exp d) hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod d, (1 : ℂ) * (pairResidueIndicator r x * F r x)) =
      (fun x => f (fun i => x i / (d : ℤ))) := by
    funext x
    let r : Fin 2 → ZMod d := fun i => (x i : ZMod d)
    rw [Finset.sum_eq_single r]
    · simp only [pairResidueIndicator, r, ite_true, one_mul]
      apply E.substitutedValue_eq (P r) (hP r) x (fun i => x i / (d : ℤ))
      exact divisionPolynomial_eval d _ x (fun i => (ZMod.val_intCast (x i)).symm)
    · intro a _ ha
      have hne : (fun i => (x i : ZMod d)) ≠ a := fun h => ha h.symm
      simp only [pairResidueIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  have hb : (t + B) ^ B + (d : ℝ) ^ 2 ≤ (p + C) ^ C := by
    simpa [t, X, Polynomial.eval₂_pow] using hbudget p hp
  rw [heq] at S
  exact ⟨S.mono hb⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

variable {A κ : Type*} {s r : ℕ} {b : ℝ} (W : NativeDegreeRankFamily s r A b)

theorem logCoefficient_mem_rank_one (α : Unit →₀ ℕ) (a : A) :
    coefficients (W.orbit a).log α ∈
      (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ := by
  have h := W.rank.filtration.polynomialOrbit_coefficient_mem_rank_one (fun _ : Unit => 1) α
    (W.rank.orbitEquiv (fun _ : Unit => 1) (W.orbit a))
  exact (congrArg (fun z => coefficients z α ∈
    (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ)
    (W.rank.orbitEquiv_log (fun _ : Unit => 1) (W.orbit a))).mp h

theorem horizontalCoefficient_real_log (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i})) (α : Unit →₀ ℕ) (a : A)
    (v : (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ)
    (hv : v.val = coefficients (W.orbit a).log α) :
    W.horizontalCoefficient hs c τ hG α a =
      W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) v := by
  apply W.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs c τ hG
    (fun _ : Unit => 1) α (W.rank.orbitEquiv (fun _ : Unit => 1) (W.orbit a)) v
  exact hv.trans (congrArg (fun z => coefficients z α)
    (W.rank.orbitEquiv_log (fun _ : Unit => 1) (W.orbit a))).symm

end NativeDegreeRankFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {n : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)

theorem mixedPairComponent_complexity (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2)) :
    (W.mixedPairComponent out v).ComplexityLE (p + 4) := W.component_complexity out

end NativeMultidegreeNilcharacter

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

namespace NativeSampleCorrelation

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

include V in
theorem mixedPairBudget_six_le : 6 ≤ mixedPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  unfold mixedPairBudget raisedNiltestBudget
  nlinarith [sq_nonneg (p + q + 2)]

end NativeSampleCorrelation
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedFrozenMiddleRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem mixedMiddleTensor_norm (b : MixedMiddleCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.mixedMiddleTensor b x‖ ≤ 1 := by
  rw [mixedMiddleTensor, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeIteratedDifferencing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_cyclic_second_difference_models_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p e : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Fin 2 => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (i j : I) (k : ZMod N), ∃ K : (Fin 2 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + e + C) ^ C) K) ∧
        ∀ h : ℤ, (𝔼 n : ZMod N,
          ‖cyclicSecondDifference (V.test g i).eval (V.test g j).eval k h n -
            K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, htranslate⟩ := exists_integer_translation_equivalence_budget s
  obtain ⟨B, _, happrox⟩ := exists_cyclicSecondDifference_approximation_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d D p e V g hp hD hI he N _ hN i j k
  let r := (p + A) ^ A
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hmodels (t : ℤ) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r
      (integerSecondDifference (V.test g i).eval (V.test g j).eval t)) := by
    have E := (htranslate D V g hp hD hI 0 ![0, t]).expansion i j
    change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r
      (fun x => (V.test g i).eval (x + 0) * star ((V.test g j).eval (x + ![0, t])))) at E
    have hshift (x : Fin 2 → ℤ) : x + ![0, t] = ![x 0, x 1 + t] := by
      funext a
      fin_cases a <;> simp
    change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r
      (fun x => (V.test g i).eval x * star ((V.test g j).eval ![x 0, x 1 + t])))
    simpa only [add_zero, hshift] using E
  have hcost : (r + e + B) ^ B ≤ (p + e + C) ^ C := by
    have hbase : r ≤ (p + e + A) ^ A := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hb : ((p + e + A) ^ A + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget (p + e) (by linarith)
    exact (pow_le_pow_left₀ (by positivity) (by linarith) B).trans hb
  obtain ⟨K, ⟨E⟩, herr⟩ := happrox hr he hN (V.test g i).eval (V.test g j).eval
    (fun x => (V.test g i).norm_eval_le x) (fun x => (V.test g j).norm_eval_le x) hmodels k
  exact ⟨K, ⟨E.mono hcost⟩, herr⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_differenced_scalar_expansions (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (T : D.Niltest (fun _ : Unit => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 n, f n * star (T.evalCyclic N (fun _ => n))‖ →
      ∃ K : ZMod N → (Unit → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + C) ^ C) (K k))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k : ZMod N, ‖𝔼 n : ZMod N,
          multiplicativeDerivative f k n * star (K k (fun _ => (n.val : ℤ)))‖) := by
  obtain ⟨A, _, hunit⟩ := RationalFilteredNilmanifold.exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, hcyclic⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_cyclic_second_difference_models_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * Q + 2 + Polynomial.C B) ^ B + 3 * Q + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f hf hcorr
  classical
  let projection : Unit → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let U := T.linearPullbackHom projection
  have hU (n : ZMod N) : U.eval ![0, (n.val : ℤ)] = T.evalCyclic N (fun _ => n) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
    rfl
  let q := (p + A) ^ A
  let e := 2 * q + 2
  let r := (3 * q + 2 + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : r + 3 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have heC : e ≤ (p + C) ^ C := by dsimp [e]; linarith
  have hN' : Real.exp (e + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by dsimp [e]; linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D U hp hT
    (fun (_ : Unit) (n : ZMod N) => ![0, (n.val : ℤ)]) (fun _ => f) (fun _ => hf)
    (by simpa only [hU, Fintype.expect_const] using hcorr)
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r K) ∧
      (𝔼 n : ZMod N, ‖cyclicSecondDifference (V.test U.orbit 0).eval
        (V.test U.orbit 0).eval k 0 n - K ![0, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
    obtain ⟨K, hK, herr⟩ := hcyclic D V U.orbit hq hD hcard he hN' 0 0 k
    have hbudgeteq : ((p + A) ^ A + e + B) ^ B = r := by
      change (q + e + B) ^ B = (3 * q + 2 + B) ^ B
      congr 1
      dsimp [e]
      ring
    exact ⟨K, by simpa only [hbudgeteq] using hK, herr 0⟩
  choose K hK herror using hmodels
  let embedding : Fin 2 → ((Unit → ℤ) →+ ℤ) := fun j =>
    if j = 0 then 0 else
      { toFun := fun x => x (), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hemb (x : Unit → ℤ) : (fun j => embedding j x) = ![0, x ()] := by
    funext j
    fin_cases j <;> simp [embedding]
  let g (n : ZMod N) := (V.test U.orbit 0).eval ![0, (n.val : ℤ)]
  have hc : Real.exp (-q) ≤ ‖𝔼 n : ZMod N, f n * star (g n)‖ := by
    simpa only [Fintype.expect_const] using hVcorr
  have hd := mean_row_correlation_sq_le_approximated_derivatives
    (fun _ : Unit => f) (fun _ : Unit => g)
    (fun k _ n => K k ![0, (n.val : ℤ)]) (fun _ => hf)
    (ε := Real.exp (-e)) (by
      intro k _
      simpa only [g, multiplicativeDerivative, cyclicSecondDifference] using herror k)
  simp only [Fintype.expect_const] at hd
  have hlarge : Real.exp (-(2 * q)) ≤
      (𝔼 k : ZMod N, ‖𝔼 n : ZMod N,
        multiplicativeDerivative f k n * star (K k ![0, (n.val : ℤ)])‖) + Real.exp (-e) := by
    have hsq := (pow_le_pow_left₀ (Real.exp_nonneg (-q)) hc 2).trans hd
    have hexp : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rwa [hexp] at hsq
  have htwo : 2 * Real.exp (-e) ≤ Real.exp (-(2 * q)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-e) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
  refine ⟨fun k x => K k ![0, x ()], ?_, ?_⟩
  · intro k
    have E := ((Classical.choice (hK k)).linearPullbackHom embedding).mono hrC
    simpa only [hemb] using (show Nonempty _ from ⟨E⟩)
  · apply (Real.exp_le_exp.mpr (neg_le_neg heC)).trans
    linarith

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_many_native_derivative_correlations (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      Nonempty (NativeVectorCorrelation (s + 1) N p (fun _ : Unit => f)) →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∀ h ∈ H, Nonempty (NativeVectorCorrelation s N ((p + C) ^ C)
          (fun _ : Unit => multiplicativeDerivative f h)) := by
  obtain ⟨A, _, hdifference⟩ := exists_differenced_scalar_expansions s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * Q + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf ⟨V⟩
  classical
  let q := (p + A) ^ A
  let t := 3 * q + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htotal : 4 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by dsimp [t]; linarith
  have htqC : t + q ≤ (p + C) ^ C := by dsimp [t]; linarith
  obtain ⟨K, hK, hmean⟩ := hdifference V.model V.test hp V.complexity
    ((Real.exp_le_exp.mpr hqC).trans hN) f hf V.correlation
  let c (k : ZMod N) := ‖𝔼 n : ZMod N,
    multiplicativeDerivative f k n * star (K k (fun _ => (n.val : ℤ)))‖
  let z (k : ZMod N) := Real.exp (-(2 * q)) * c k
  have hcap (k : ZMod N) : c k ≤ Real.exp (2 * q) := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (multiplicativeDerivative_norm_le_one f hf k n)).trans
        ((Classical.choice (hK k)).norm_eval_le _)
  have hzcap (k : ZMod N) : z k ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * q)) * Real.exp (2 * q) :=
        mul_le_mul_of_nonneg_left (hcap k) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * q)) ≤ 𝔼 k, z k := by
    change Real.exp (-(3 * q)) ≤ 𝔼 k, Real.exp (-(2 * q)) * c k
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * q)) = Real.exp (-(2 * q)) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmean (Real.exp_nonneg _)
  obtain ⟨H, hHsize, hHcorr⟩ :=
    exists_dense_level_set z (Real.exp_nonneg (-(3 * q))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * q)) / 2 := by
    apply (Real.exp_le_exp.mpr (by dsimp [t]; linarith : -t ≤ -(3 * q) - 1)).trans
    exact exp_sub_one_le_half_exp (-(3 * q))
  have hdense : Real.exp (-t) * N ≤ (H.card : ℝ) := by
    simpa only [ZMod.card] using
      (mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg (Fintype.card (ZMod N)))).trans hHsize
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hH : H.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le (by positivity : 0 < Real.exp (-t) * (N : ℝ)) hdense
  refine ⟨H, hH, (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg htC)) (Nat.cast_nonneg N)).trans hdense, ?_⟩
  intro k hk
  have hzle : z k ≤ c k := mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hc : Real.exp (-t) ≤ c k := hhalf.trans ((hHcorr k hk).trans hzle)
  let E := Classical.choice (hK k)
  obtain ⟨i, hi⟩ := E.select_sample_correlation Finset.univ (fun (n : ZMod N) (_ : Unit) => (n.val : ℤ))
    (multiplicativeDerivative f k) hc
  exact ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono hqC
    coordinate := ()
    correlation := (Real.exp_le_exp.mpr (neg_le_neg htqC)).trans hi }⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_iterated_native_derivative_correlations (k d : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeVectorCorrelation (k + d) N p (fun _ : Unit => f)) →
      ∃ Q : Finset (Fin d → ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ d ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, Nonempty (NativeVectorCorrelation k N ((p + C) ^ C)
          (fun _ : Unit => cubeProduct f (List.ofFn u))) := by
  induction d with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    intro N _ p hp _ f _ ⟨V⟩
    classical
    have hq : 0 ≤ (p + 2) ^ 2 := sq_nonneg _
    have hpq : p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    refine ⟨Finset.univ, Finset.univ_nonempty, ?_, ?_⟩
    · simpa using (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hq))
    · intro u _
      have hfun : (fun _ : Unit => cubeProduct f (List.ofFn u)) = (fun _ : Unit => f) := by
        funext _ x
        simp only [List.ofFn_zero, cubeProduct_nil]
      rw [hfun]
      exact ⟨V.mono hpq⟩
  | succ d ih =>
    obtain ⟨a, _, hstep⟩ := exists_many_native_derivative_correlations (k + d) (by omega)
    obtain ⟨b, _, hiter⟩ := ih
    let X : Polynomial ℕ := Polynomial.X
    let P := (X + Polynomial.C a) ^ a
    let R := (P + Polynomial.C b) ^ b
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
    refine ⟨C, hC, ?_⟩
    intro N _ p hp hN f hf hc
    classical
    let q := (p + a) ^ a
    let r := (q + b) ^ b
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hsum : q + r ≤ (p + C) ^ C := by
      simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
    have hqC : q ≤ (p + C) ^ C := by linarith
    have hrC : r ≤ (p + C) ^ C := by linarith
    obtain ⟨H, hH, hHdense, hHcorr⟩ := hstep hp ((Real.exp_le_exp.mpr hqC).trans hN)
      f hf (by simpa only [Nat.add_assoc] using hc)
    have hdata (h : H) := hiter hq ((Real.exp_le_exp.mpr hrC).trans hN)
      (multiplicativeDerivative f h.val) (multiplicativeDerivative_norm_le_one f hf h.val)
      (hHcorr h.val h.property)
    choose K _hK hKdense hKcorr using hdata
    obtain ⟨Q, hQdense, hQmem⟩ := dense_tuple_fibers d H K (Real.exp_nonneg (-r))
      (by simpa only [ZMod.card] using hHdense)
      (fun h => by simpa only [ZMod.card] using hKdense h)
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    have hQ : Q.Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast lt_of_lt_of_le
        (by positivity : 0 < Real.exp (-q) * Real.exp (-r) * (Fintype.card (ZMod N) : ℝ) ^ (d + 1)) hQdense
    refine ⟨Q, hQ, ?_, ?_⟩
    · have heq : Real.exp (-(q + r)) = Real.exp (-q) * Real.exp (-r) := by rw [neg_add, Real.exp_add]
      have hsmall := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hsum)) (pow_nonneg (Nat.cast_nonneg N) (d + 1))
      rw [heq] at hsmall
      exact hsmall.trans (by simpa only [ZMod.card] using hQdense)
    · intro u hu
      obtain ⟨h, hh, htail⟩ := (hQmem u).mp hu
      have hlist : List.ofFn u = h.val :: List.ofFn (Fin.tail u) := by
        rw [List.ofFn_succ, ← hh]
        rfl
      obtain ⟨V⟩ := hKcorr h (Fin.tail u) htail
      have hfun : (fun _ : Unit => cubeProduct f (List.ofFn u)) =
          (fun _ : Unit => cubeProduct (multiplicativeDerivative f h.val)
            (List.ofFn (Fin.tail u))) := by
        funext _ x
        rw [hlist, cubeProduct_cons_eq_derivative]
      rw [hfun]
      exact ⟨V.mono hrC⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeZeroDegreeCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

theorem exists_fixed_quadratic_coordinate {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeMixedCorrelation 1 N p f) :
    ∃ i : Fin W.mixed.outputDim, ∃ H ⊆ W.shifts, H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Real.exp (-(2 * p)) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star (W.mixed.evalCyclic N i (correlationInput h x))‖ := by
  obtain ⟨i, H, hsub, hH, hdense, hcorr⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    W.shifts W.nonempty (nativeMixedResidual f W.mixed)
    (by simpa only [Fintype.card_fin] using W.mixed.output_bound) W.correlation
  refine ⟨i, H, hsub, hH, ?_, ?_⟩
  · have hW : Real.exp (-p) * N ≤ (W.shifts.card : ℝ) := by
      simpa only [ZMod.card] using W.density
    calc
      Real.exp (-(2 * p)) * N = Real.exp (-p) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-p) * W.shifts.card := mul_le_mul_of_nonneg_left hW (Real.exp_nonneg _)
      _ ≤ H.card := hdense
  · intro h hh
    obtain ⟨V⟩ := hcorr h hh
    exact V.mean_correlation_of_degree_zero

end NativeMixedCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.StepOneScalarPhase
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_stepOne_row_phase_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d N : ℕ} [NeZero N]
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : Fin 2 => 1), T.ComplexityLE p →
      ∀ F : ZMod N → ZMod N → ℂ, (∀ h n, ‖F h n‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ α β : ℝ, Real.exp (-((p + C) ^ C)) ≤
        (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n *
          star (character ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))‖) := by
  obtain ⟨A, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (2 * X + 2 + Polynomial.C A) ^ A + (2 * X + 2) + 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp T hT F hF hmass
  let r := 2 * p + 2
  let δ := Real.exp (-(p + 2))
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hδ : 0 < δ := Real.exp_pos _
  have hδr : δ⁻¹ ≤ Real.exp r := by
    dsimp [δ]
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (by dsimp [r]; linarith)
  obtain ⟨J, inst, η, U, hcard, _, hU, hchar, _, _, _, herr⟩ :=
    T.exists_controlled_vertical_decomposition hr (hT.mono hpr) δ hδ hδr
  let := inst
  have hrow (h : ZMod N) :
      ‖𝔼 n : ZMod N, F h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖ ≤
        (∑ j : J, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖) + δ := by
    apply (norm_correlation_partition_bound (F h)
      (fun n => T.eval ![(h.val : ℤ), (n.val : ℤ)])
      (fun j n => (U j).eval ![(h.val : ℤ), (n.val : ℤ)]) (hF h)).trans
    apply add_le_add le_rfl
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    simpa only [norm_sub_rev] using herr ![(h.val : ℤ), (n.val : ℤ)]
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hrow h)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm, Fintype.expect_const] at hm
  have htwo : 2 * δ ≤ Real.exp (-p) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hs : δ ≤ ∑ j : J, (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    linarith
  obtain ⟨j, hj⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ))
    (fun j => 𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖)
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hs)
  let θ (k : Fin 2) := realifyFunctional (η j) (VectorPolynomial.coefficients (U j).orbit.log (Finsupp.single k 1))
  let γ := realifyFunctional (η j) (VectorPolynomial.coefficients (U j).orbit.log 0)
  let a := (U j).observable (QuotientGroup.mk (1 : D.RealGroup)) * character (γ : CircleFourier.Circle)
  let P (h n : ZMod N) := character ((((h.val : ℝ) * θ 0 + (n.val : ℝ) * θ 1) : ℝ) : CircleFourier.Circle)
  have heval (h n : ZMod N) : (U j).eval ![(h.val : ℤ), (n.val : ℤ)] = a * P h n := by
    rw [D.stepOne_niltest_eval_affine (U j) (η j) (hchar j)]
    simp only [a, P, γ, θ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Int.cast_natCast, AddCircle.coe_add, character_add]
    ring
  have ha : ‖a‖ ≤ Real.exp r := by
    dsimp [a]
    rw [norm_mul, norm_character, mul_one]
    apply ((U j).norm_le _).trans
    have h := (U j).observable_budget (hU j).1
    have hl := (U j).lipBound.coe_nonneg
    linarith
  have hmean (h : ZMod N) :
      (𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])) =
        star a * (𝔼 n : ZMod N, F h n * star (P h n)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    rw [heval, star_mul]
    ring
  have hupper : (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖) ≤
      Real.exp r * (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := by
    simp only [hmean, norm_mul, norm_star, ← Finset.mul_expect]
    exact mul_le_mul_of_nonneg_right ha (Finset.expect_nonneg (fun _ _ => norm_nonneg _))
  have hchosen : Real.exp (-(p + 2 + verticalDecompositionBudget r)) ≤
      Real.exp r * (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := by
    have hexp : δ / Real.exp (verticalDecompositionBudget r) = Real.exp (-(p + 2 + verticalDecompositionBudget r)) := by
      dsimp [δ]
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [hexp] at hj
    exact hj.trans hupper
  have hlower : Real.exp (-(p + verticalDecompositionBudget r + r + 2)) ≤
      (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos r)).mp
    calc
      Real.exp r * Real.exp (-(p + verticalDecompositionBudget r + r + 2)) =
          Real.exp (-(p + 2 + verticalDecompositionBudget r)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp r * (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := hchosen
  have hcost : p + verticalDecompositionBudget r + r + 2 ≤ (p + C) ^ C := by
    have hh : p + (r + A) ^ A + r + 2 ≤ (p + C) ^ C := by
      simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
    linarith [hvertical r hr]
  exact ⟨θ 0, θ 1, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hlower⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_stepOne_scalar_phase_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d N : ℕ} [NeZero N]
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : Unit => 1), T.ComplexityLE p →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 n, f n * star (T.evalCyclic N (fun _ => n))‖ →
      ∃ β : ℝ, Real.exp (-((p + C) ^ C)) ≤
        ‖𝔼 n : ZMod N, f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))‖ := by
  obtain ⟨C, hC, hphase⟩ := exists_stepOne_row_phase_budget
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp T hT f hf hcorr
  let projection : Unit → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let U := T.linearPullbackHom projection
  have hU (h n : ZMod N) : U.eval ![(h.val : ℤ), (n.val : ℤ)] =
      T.evalCyclic N (fun _ => n) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
    rfl
  have hmass : Real.exp (-p) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, f n * star (U.eval ![(h.val : ℤ), (n.val : ℤ)])‖ := by
    simpa only [hU, Fintype.expect_const] using hcorr
  obtain ⟨α, β, hresult⟩ := hphase D hp U hT (fun _ n => f n) (fun _ => hf) hmass
  have hrow (h : ZMod N) :
      ‖𝔼 n : ZMod N, f n * star (character
        ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))‖ =
      ‖𝔼 n : ZMod N, f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))‖ := by
    have heq : (𝔼 n : ZMod N, f n * star (character
        ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))) =
        star (character (((h.val : ℝ) * α : ℝ) : CircleFourier.Circle)) *
          (𝔼 n : ZMod N, f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      simp only [AddCircle.coe_add, character_add, star_mul]
      ring
    rw [heq, norm_mul, norm_star, norm_character, one_mul]
  exact ⟨β, by simpa only [hrow, Fintype.expect_const] using hresult⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CubicResidualPhase
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

namespace NativeMixedCorrelation

theorem exists_fixed_residual_coordinate {s N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeMixedCorrelation s N p f) :
    ∃ i : Fin W.mixed.outputDim, ∃ H ⊆ W.shifts, H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p
        (fun _ : Unit => nativeMixedResidual f W.mixed h i)) := by
  obtain ⟨i, H, hsub, hH, hdense, hcorr⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    W.shifts W.nonempty (nativeMixedResidual f W.mixed)
    (by simpa only [Fintype.card_fin] using W.mixed.output_bound) W.correlation
  refine ⟨i, H, hsub, hH, ?_, hcorr⟩
  have hW : Real.exp (-p) * N ≤ (W.shifts.card : ℝ) := by
    simpa only [ZMod.card] using W.density
  calc
    Real.exp (-(2 * p)) * N = Real.exp (-p) * (Real.exp (-p) * N) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-p) * W.shifts.card := mul_le_mul_of_nonneg_left hW (Real.exp_nonneg _)
    _ ≤ H.card := hdense

end NativeMixedCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedCubeResiduals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem nativeMixedResidual_norm_le_one {s N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (h : ZMod N) (i : Fin M.outputDim) (x : ZMod N) :
    ‖nativeMixedResidual f M h i x‖ ≤ 1 := by
  rw [nativeMixedResidual, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (multiplicativeDerivative_norm_le_one f hf h x)).trans (M.norm_eval _ _)

noncomputable def nativeMixedCubeResidual {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
    (i : Fin M.outputDim) (u : Fin (d + 1) → ZMod N) : ZMod N → ℂ :=
  cubeProduct (nativeMixedResidual f M (u 0) i) (List.ofFn (Fin.tail u))

theorem nativeMixedCubeResidual_norm_le_one {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
    (i : Fin M.outputDim) (u : Fin (d + 1) → ZMod N) (x : ZMod N) :
    ‖nativeMixedCubeResidual f M i u x‖ ≤ 1 :=
  cubeProduct_norm_le_one _ (nativeMixedResidual_norm_le_one f hf M (u 0) i) _ x

theorem nativeMixedCubeResidual_eq {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
    (i : Fin M.outputDim) (u : Fin (d + 1) → ZMod N) (x : ZMod N) :
    nativeMixedCubeResidual f M i u x =
      cubeProduct f (List.ofFn u) x *
        star (cubeProduct (fun y => M.evalCyclic N i (correlationInput (u 0) y))
          (List.ofFn (Fin.tail u)) x) := by
  change cubeProduct (fun y => multiplicativeDerivative f (u 0) y *
    star (M.evalCyclic N i (correlationInput (u 0) y))) (List.ofFn (Fin.tail u)) x = _
  rw [cubeProduct_mul, cubeProduct_star, List.ofFn_succ, cubeProduct_cons_eq_derivative]
  rfl

namespace NativeMixedCorrelation

theorem exists_degree_one_cube_residuals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim, ∃ Q : Finset (Fin (d + 1) → ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 1) ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, u 0 ∈ M.shifts ∧
          Nonempty (NativeVectorCorrelation 1 N ((p + C) ^ C)
            (fun _ : Unit => nativeMixedCubeResidual f M.mixed i u)) := by
  obtain ⟨a, _, hiter⟩ := exists_iterated_native_derivative_correlations 1 d (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + P)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  classical
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsum : 2 * p + q ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨i, H, hsub, hH, hHdense, hHcorr⟩ := M.exists_fixed_residual_coordinate
  have hdata (h : H) := hiter hp ((Real.exp_le_exp.mpr hqC).trans hN)
    (nativeMixedResidual f M.mixed h.val i)
    (nativeMixedResidual_norm_le_one f hf M.mixed h.val i)
    (by simpa only [show d + 2 - 1 = 1 + d by omega] using hHcorr h.val h.property)
  choose K _hK hKdense hKcorr using hdata
  obtain ⟨Q, hQdense, hQmem⟩ := dense_tuple_fibers d H K (Real.exp_nonneg (-q))
    (by simpa only [ZMod.card] using hHdense)
    (fun h => by simpa only [ZMod.card] using hKdense h)
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le
      (by positivity : 0 < Real.exp (-(2 * p)) * Real.exp (-q) *
        (Fintype.card (ZMod N) : ℝ) ^ (d + 1)) hQdense
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · have heq : Real.exp (-(2 * p + q)) = Real.exp (-(2 * p)) * Real.exp (-q) := by
      rw [neg_add, Real.exp_add]
    have hsmall := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsum))
      (pow_nonneg (Nat.cast_nonneg N) (d + 1))
    rw [heq] at hsmall
    exact hsmall.trans (by simpa only [ZMod.card] using hQdense)
  · intro u hu
    obtain ⟨h, hh, htail⟩ := (hQmem u).mp hu
    refine ⟨hsub (hh ▸ h.property), ?_⟩
    obtain ⟨V⟩ := hKcorr h (Fin.tail u) htail
    change Nonempty (NativeVectorCorrelation 1 N ((p + C) ^ C)
      (fun _ : Unit => cubeProduct (nativeMixedResidual f M.mixed (u 0) i)
        (List.ofFn (Fin.tail u))))
    rw [← hh]
    exact ⟨V.mono hqC⟩

end NativeMixedCorrelation
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NativeMixedFourierProfiles
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_fourier_of_stepOne_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ {g : (Unit → ℤ) → ℂ} (_E : NativeIntegerExpansion (fun _ : Unit => 1) 1 p g)
        (f : ZMod N → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 n : ZMod N, f n * star (g (fun _ => (n.val : ℤ)))‖ →
      ∃ χ : AddChar (ZMod N) ℂ, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff f χ‖ := by
  obtain ⟨A, _, hphase⟩ := exists_stepOne_scalar_phase_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * (2 * X + Polynomial.C A) ^ A + 16)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp g E f hf hc
  obtain ⟨i, hi⟩ := E.select_sample_correlation Finset.univ
    (fun n : ZMod N => fun _ => (n.val : ℤ)) f hc
  obtain ⟨β, hβ⟩ := hphase (E.model i) (by positivity : 0 ≤ 2 * p) (E.test i)
    ((E.complexity i).mono (by linarith)) f hf (by
      change Real.exp (-(2 * p)) ≤
        ‖𝔼 n : ZMod N, f n * star ((E.test i).eval (fun _ => (n.val : ℤ)))‖
      simpa only [two_mul] using hi)
  let t := (2 * p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  obtain ⟨χ, hχ⟩ := exists_fourier_of_real_linear_phase f hf β
    (Real.exp_pos (-t)) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) hβ
  have hsmall : Real.exp (-(2 * t + 16)) ≤ Real.exp (-t) ^ 2 / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    calc
      _ ≤ Real.exp (-(2 * t + 16)) * Real.exp 16 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (16 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; norm_num
  have hcost : 2 * t + 16 ≤ (p + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨χ, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hsmall.trans hχ)⟩

end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_cube_residual_fourier_profiles (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim, ∃ Q : Finset (Fin (d + 1) → ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 1) ≤ (Q.card : ℝ) ∧
        ∃ χ : (Fin (d + 1) → ZMod N) → AddChar (ZMod N) ℂ,
          ∀ u ∈ Q, u 0 ∈ M.shifts ∧ Real.exp (-((p + C) ^ C)) ≤
            ‖finiteFourierCoeff (nativeMixedCubeResidual f M.mixed i u) (χ u)‖ := by
  obtain ⟨a, _, hresidual⟩ := exists_degree_one_cube_residuals d
  obtain ⟨b, _, hfourier⟩ := exists_fourier_of_stepOne_expansion
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  classical
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hresidual hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  have hchar (u : Fin (d + 1) → ZMod N) (hu : u ∈ Q) :
      ∃ χ : AddChar (ZMod N) ℂ, Real.exp (-r) ≤
        ‖finiteFourierCoeff (nativeMixedCubeResidual f M.mixed i u) χ‖ := by
    obtain ⟨V⟩ := (hcorr u hu).2
    let E := NativeIntegerExpansion.ofTest V.test V.complexity (fun _ => rfl)
    exact hfourier hq E (nativeMixedCubeResidual f M.mixed i u)
      (nativeMixedCubeResidual_norm_le_one f hf M.mixed i u) V.correlation
  let χ (u : Fin (d + 1) → ZMod N) : AddChar (ZMod N) ℂ :=
    if hu : u ∈ Q then Classical.choose (hchar u hu) else 1
  refine ⟨i, Q, hQ, ?_, χ, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro u hu
    refine ⟨(hcorr u hu).1, ?_⟩
    dsimp only [χ]
    rw [dif_pos hu]
    exact (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (Classical.choose_spec (hchar u hu))

end Erdos3.NativeMixedCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_derivative_correlation_mul_addChar {G : Type*} [AddCommGroup G] [Fintype G]
    (f u : G → ℂ) (χ : AddChar G ℂ) (h : G) :
    ‖finiteCorrelation Finset.univ f (multiplicativeDerivative (fun x => u x * χ x) h)‖ =
      ‖finiteCorrelation Finset.univ f (multiplicativeDerivative u h)‖ := by
  have hcancel (x : G) : χ x * star (χ x) = 1 := by
    change χ x * (starRingEnd ℂ) (χ x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, AddChar.norm_apply]
    norm_num
  have hder (x : G) : multiplicativeDerivative (fun y => u y * χ y) h x =
      star (χ h) * multiplicativeDerivative u h x := by
    simp only [multiplicativeDerivative, AddChar.map_add_eq_mul, star_mul]
    calc
      _ = (χ x * star (χ x)) * (star (χ h) * (u x * star (u (x + h)))) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have heq : finiteCorrelation Finset.univ f (multiplicativeDerivative (fun x => u x * χ x) h) =
      χ h * finiteCorrelation Finset.univ f (multiplicativeDerivative u h) := by
    unfold finiteCorrelation
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    rw [hder, star_mul, star_star]
    ring
  rw [heq, norm_mul, AddChar.norm_apply, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

theorem exists_full_difference_correlation (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, u.1 0 ∈ M.shifts ∧ Real.exp (-((p + C) ^ C)) ≤
          ‖finiteCorrelation Finset.univ
            (cubeProduct f (u.2 :: List.ofFn u.1))
            (cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u.1 0) x))
              (u.2 :: List.ofFn (Fin.tail u.1)))‖ := by
  obtain ⟨a, _, hfourier⟩ := exists_cube_residual_fourier_profiles d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  classical
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 3 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨i, H, _hH, hdense, χ, hcorr⟩ := hfourier hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  let F (u : Fin (d + 1) → ZMod N) := cubeProduct f (List.ofFn u)
  let V (u : Fin (d + 1) → ZMod N) :=
    cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u 0) x))
      (List.ofFn (Fin.tail u))
  let G (u : Fin (d + 1) → ZMod N) (x : ZMod N) := V u x * χ u x
  have hF (u : Fin (d + 1) → ZMod N) (x : ZMod N) : ‖F u x‖ ≤ 1 :=
    cubeProduct_norm_le_one f hf _ x
  have hV (u : Fin (d + 1) → ZMod N) (x : ZMod N) : ‖V u x‖ ≤ 1 :=
    cubeProduct_norm_le_one _ (fun _ => M.mixed.norm_eval i _) _ x
  have hG (u : Fin (d + 1) → ZMod N) (x : ZMod N) : ‖G u x‖ ≤ 1 := by
    dsimp only [G]
    rw [norm_mul, AddChar.norm_apply, mul_one]
    exact hV u x
  have hc (u : Fin (d + 1) → ZMod N) (hu : u ∈ H) :
      Real.exp (-q) ≤ ‖finiteCorrelation Finset.univ (F u) (G u)‖ := by
    have heq (x : ZMod N) : nativeMixedCubeResidual f M.mixed i u x * star (χ u x) =
        F u x * star (G u x) := by
      rw [nativeMixedCubeResidual_eq]
      dsimp only [F, G, V]
      rw [star_mul]
      ring
    simpa only [finiteFourierCoeff, finiteCorrelation, heq] using (hcorr u hu).2
  obtain ⟨Q, hQ, hQsize, hQcorr⟩ := exists_many_family_derivative_correlations F G H hF hG
    (Real.exp_pos (-q)) (Real.exp_pos (-q))
    (by simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow] using hdense) hc
  have hprod : Real.exp (-q) * Real.exp (-q) ^ 2 = Real.exp (-(3 * q)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) * Real.exp (-q) ^ 2 / 2 := by
    rw [hprod]
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -(3 * q) - 1)).trans
      (exp_sub_one_le_half_exp (-(3 * q)))
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · have hsize : Real.exp (-q) * Real.exp (-q) ^ 2 / 2 * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) := by
      convert hQsize using 1
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
      simp only [pow_succ]
      ring
    exact (mul_le_mul_of_nonneg_right hsmall (pow_nonneg (Nat.cast_nonneg N) _)).trans hsize
  · intro u hu
    obtain ⟨hbase, hder⟩ := hQcorr u hu
    refine ⟨(hcorr u.1 hbase).1, ?_⟩
    have h := hsmall.trans hder
    change Real.exp (-((p + C) ^ C)) ≤
      ‖finiteCorrelation Finset.univ (multiplicativeDerivative (F u.1) u.2)
        (multiplicativeDerivative (fun x => V u.1 x * χ u.1 x) u.2)‖ at h
    rw [norm_derivative_correlation_mul_addChar] at h
    have hFder : multiplicativeDerivative (F u.1) u.2 =
        cubeProduct f (u.2 :: List.ofFn u.1) := by
      funext x
      exact (cubeProduct_cons f u.2 (List.ofFn u.1) x).symm
    have hVder : multiplicativeDerivative (V u.1) u.2 =
        cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u.1 0) x))
          (u.2 :: List.ofFn (Fin.tail u.1)) := by
      funext x
      exact (cubeProduct_cons _ u.2 (List.ofFn (Fin.tail u.1)) x).symm
    rw [hFder, hVder] at h
    exact h

end NativeMixedCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

theorem exists_cube_carry_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧
          ∃ (b : (Fin (d + 1) → Bool) → Fin (d + 2)) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
                  star (M.mixed.mixedCubeWithShift (cubeCarryShift (d + 1) N b)
                    (fun _ => i) (mixedDifferencePoint t n))‖ := by
  obtain ⟨A, _, hdifference⟩ := exists_full_difference_correlation d
  let L : ℕ := 2 * (2 ^ (d + 1) + 8)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Polynomial.C L)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  let q := (p + A) ^ A
  have htotal : q + L ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have hLpos : (0 : ℝ) < L := by dsimp [L]; positivity
  have hLexp : (L : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp (L : ℝ)]
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) / (2 * ((2 : ℝ) ^ (d + 1) + 8)) := by
    have hden : (2 * ((2 : ℝ) ^ (d + 1) + 8)) = L := by simp [L]
    rw [hden]
    apply (le_div_iff₀ hLpos).mpr
    calc
      _ ≤ Real.exp (-((p + C) ^ C)) * Real.exp L :=
        mul_le_mul_of_nonneg_left hLexp (Real.exp_nonneg _)
      _ = Real.exp (-((p + C) ^ C) + L) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hdifference hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    refine ⟨(hcorr t ht).1, ?_⟩
    let R (z : ℤ) := M.mixed.eval i (correlationInput ((t.1 0).val : ℤ) z)
    let g := cubeProduct f (t.2 :: List.ofFn t.1)
    have hg : ∀ x, ‖g x‖ ≤ 1 := cubeProduct_norm_le_one f hf _
    have hR : (fun n : ZMod N => R n.val) =
        (fun x => M.mixed.evalCyclic N i (correlationInput (t.1 0) x)) := by
      funext x
      apply congrArg (M.mixed.eval i)
      funext j
      fin_cases j <;> rfl
    have hc : Real.exp (-q) ≤ ‖finiteCorrelation Finset.univ g
        (cubeProduct (fun n : ZMod N => R n.val) (List.ofFn (mixedDifferenceShifts t)))‖ := by
      rw [hR]
      simpa only [mixedDifferenceShifts, List.ofFn_cons] using (hcorr t ht).2
    obtain ⟨b, a, len, hlen, hend, hshort, hcor, hvol⟩ :=
      exists_cyclic_cube_product_interval g R (mixedDifferenceShifts t) (Real.exp_pos (-q))
        hg (fun _ => M.mixed.norm_eval i _) hc
    refine ⟨b, a, len, hlen, hend, hshort, hsmall.trans hvol, ?_⟩
    simpa only [finiteCorrelation, mixedDifferencePoint, M.mixed.mixedCubeWithShift_diagonal]
      using hsmall.trans hcor

end NativeMixedCorrelation
end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_cube_unwrapped_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ E : ∀ b : (Fin (d + 1) → Bool) → Fin (d + 2),
        NativeIntegerVectorEquivalence (d + 2) r
          (M.mixed.mixedCubeWithShift (cubeCarryShift (d + 1) N b))
          (M.mixed.mixedCubeWithShift 0),
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧
          ∃ (b : (Fin (d + 1) → Bool) → Fin (d + 2)) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            ∃ v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim,
            ∃ l : Fin ((E b).selectedExpansion (fun _ => i) v).count,
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
                    star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) *
                    star ((((E b).selectedExpansion (fun _ => i) v).test l).eval (mixedDifferencePoint t n))‖ := by
  obtain ⟨A, _, hinterval⟩ := exists_cube_carry_intervals d
  obtain ⟨B, _, htranslate⟩ := NativeMultidegreeNilcharacter.exists_mixed_cube_translation (d + 2) (d + 1)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let R := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + 2 * R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  let q := (p + A) ^ A
  let r := (p + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + 2 * r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  let E (b : (Fin (d + 1) → Bool) → Fin (d + 2)) := htranslate M.mixed (cubeCarryShift (d + 1) N b)
  refine ⟨r, hr, hrC, E, i, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hshift, b, a, len, hlen, hend, hshort, hvol, hcor⟩ := hcorr t ht
    obtain ⟨v, l, hc⟩ := (E b).transfer_sample_correlation
      (Finset.Ico (a : ℤ) (a + len)) (mixedDifferencePoint t) (fun _ => i)
      (fun n => cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N))
      (fun n _ => M.mixed.mixedCubeWithShift_unit 0 _) hcor
    exact ⟨hshift, b, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      v, l, (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hc⟩

end Erdos3.NativeMixedCorrelation

end

end OAI
end


