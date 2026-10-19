-- Prove2me | Definitions.Def_OAIE3v2B256
-- name    : OAIE3v2B256
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:36:09.117828+00:00
-- url     : https://prove2.me/theorems/4059ca37-bf1c-4e79-b74c-22706624cd98
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 262 of 311
-- statement:
--   Definitions bundle 262 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B248`, `OAIE3v2B249`, `OAIE3v2B250`, `OAIE3v2B251` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidateTaggedSourceEvaluation.lean`, `Estimates/AllocatedZeroLayerFixedCenterExcess.lean`, `Estimates/FreeCoefficientCorrectionControl.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/SharedFreeCorrelatedFactorization.lean`, `Estimates/SharedFreeLowerFactorization.lean`, `Geometry/AllocatedExternalCandidateRefilteredSupportedStep.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Lattices/NativeCorrelatedAffineExistence.lean`, `Linear/SharedFreeCommonProjection.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/LocalPhaseMarkedObservable.lean`, `Polynomial/SharedFreeCommonPolynomialCorrections.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B249
import Definitions.Def_OAIE3v2B250
import Definitions.Def_OAIE3v2B251

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ) (u : Fin t → ℝ)

theorem realAffineMarkedBase_eval (j : Fin s) (a : Fin t → ℚ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ
        (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j)) =
            (x j).val + ∑ i, a i • (y j i).val := by
  exact (realMarkedPolynomialLift_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j) a).trans
      (realAffinePolynomial_eval (x j).val (fun i => (y j i).val) a)

theorem realAffineMarkedSlope_eval (j : Fin s) (a : Fin t → ℚ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ
        (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y u j)) =
            ∑ i, u i • (y j i).val := by
  apply (realMarkedPolynomialLift_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y u j) a).trans
  change (eval a).baseChange ℝ ((monomialLinearMap 0).baseChange ℝ (∑ i, u i • (y j i).val)) = _
  rw [realMonomial_eval, Finsupp.prod_zero_index, one_smul]

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)

theorem realAffineMarkedSlope_zero (j : Fin s) : D.realAffineMarkedSlope t y 0 j = 0 := by
  apply Subtype.ext
  change (monomialLinearMap (0 : Fin t →₀ ℕ)).baseChange ℝ
    (∑ i, (0 : ℝ) • (y j i).val) = 0
  simp

theorem realAffineMarkedBase_shift_eval (a : Fin t → ℝ) (j : Fin s) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (realMarkedAffineShift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t a
          (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
            D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j))) =
      (x j).val + ∑ i, a i • (y j i).val := by
  apply realMarkedAffineShift_eval_affine
  intro b
  simpa only [← Rat.cast_smul_eq_qsmul ℝ] using D.realAffineMarkedBase_eval t x y j b

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeCommonProjection
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

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

theorem exists_shared_free_common_projection
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    ∃ (m : Fin s → ℕ) (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
      ∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp Λ ∧
        γ d ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ d + e d + q d ∧
        ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤ Real.exp Λ / (N : ℝ) ^ (d.val + 1) ∧
        (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (m d) := by
  intro Λ
  classical
  let z := 8 * sharedRefinementInputBudget s P' + 1
  let A₀ := sharedFreeEquationInputBudget s Q P'
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hbudget := (sharedFreeAffineConstant_spec s).2 Q P' hQ hQP' hP' 0
    (by simpa only [Nat.cast_zero] using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg s)) hP')
  have hcut := sharedFreeRecoveryThreshold_spec s hQ hP' N
    ((Real.exp_le_exp.mpr hbudget.1).trans hN)
  have hb := sharedFreeEquationInputBudget_bounds s hQ hP'
  have hA₀ : 0 ≤ A₀ := hb.1
  have hcoeff := sharedFreeRecoveryThreshold_coefficient_bounds s hQ hP'
  have hAΛ : A₀ ≤ Λ :=
    (le_power_budget hb.1 (by decide : 1 ≤ 4)).trans (hcoeff.1.trans hbudget.1)
  have hnum : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤ Real.exp Λ := by
    have hfac : 1 ≤ 2 * Real.exp ((A₀ + 2) ^ 3) := by
      have h := Real.one_le_exp_iff.mpr (show 0 ≤ (A₀ + 2) ^ 3 by positivity)
      linarith
    calc
      _ ≤ 2 * (Real.exp ((A₀ + 2) ^ 3) *
          (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) := by
        have h := mul_le_mul_of_nonneg_right hfac
          (show 0 ≤ Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) by positivity)
        simpa only [one_mul, mul_assoc] using h
      _ ≤ _ := hcoeff.2.trans (Real.exp_le_exp.mpr hbudget.1)
  obtain ⟨D₁, _hsub, _hspaces, hcorr⟩ :=
    D.exists_controlled_shared_free_refinement E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hcut.1
  obtain ⟨t, ht⟩ := D₁.nonempty
  choose m hm hmb hcorr using hcorr
  have hdenom (d : Fin s) : (m d : ℝ) ≤ Real.exp Λ :=
    (hmb d).trans (Real.exp_le_exp.mpr (hb.2.2.2.trans hAΛ))
  let π := (LinearMap.proj (0 : Fin 4) :
    (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] D.CoefficientFreeLieAlgebra).baseChange ℝ
  have hcommon (d : Fin s) : ∃ γ e q : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra,
      γ ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
      coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ + e + q ∧
      ‖(E.basis.baseChange ℝ).equivFun e‖ ≤ Real.exp Λ / (N : ℝ) ^ (d.val + 1) ∧
      (E.basis.baseChange ℝ).equivFun q ∈ realDenominatorGrid (m d) := by
    obtain ⟨A, S, hA, hS, hmem⟩ := hcorr d t ht
    let K := fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
    let u := coefficients (v (rankQuadrupleParameters t 1)).log (Finsupp.single () (d.val + 1))
    let γ := coefficients ξ.log (Finsupp.single () (d.val + 1)) - π A - π S
    have hhead : π ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm
        (sharedLogCoefficientTuple E.filtration ξ v (Finsupp.single () (d.val + 1)) t)) =
          coefficients ξ.log (Finsupp.single () (d.val + 1)) + u := by
      dsimp only [π]
      rw [real_four_projection, LinearEquiv.apply_symm_apply]
      rfl
    have hproj : π ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm
        (sharedLogCoefficientTuple E.filtration ξ v (Finsupp.single () (d.val + 1)) t) - A - S) ∈
          (K.map (LinearMap.proj 0)).baseChange ℝ := by
      rw [realification_map]
      exact ⟨_, hmem, rfl⟩
    rw [map_sub, map_sub, hhead] at hproj
    have hu : u ∈ (K.map (LinearMap.proj 0)).baseChange ℝ :=
      Submodule.baseChange_mono ℝ (dependent_le_refined_firstProjection _ _ _) (hv _ d)
    refine ⟨γ, π A, π S, ?_, ?_, ?_, ?_⟩
    · have h := ((K.map (LinearMap.proj 0)).baseChange ℝ).sub_mem hproj hu
      convert h using 1
      dsimp [γ]
      abel
    · dsimp [γ]
      abel
    · have hA' : ‖((Pi.basis (fun _ : Fin 4 => E.basis)).baseChange ℝ).equivFun A‖ ≤
          (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) / (N : ℝ) ^ (d.val + 1) := by
        simpa only [monomialScale, Finsupp.prod_single_index, pow_zero] using hA
      exact (real_four_projection_norm_le E.basis A 0).trans
        (hA'.trans (div_le_div_of_nonneg_right hnum (by positivity)))
    · exact real_four_projection_grid E.basis S 0 (m d) hS
  choose γ e q hγ heq he hq using hcommon
  exact ⟨m, γ, e, q, fun d => ⟨hm d, hdenom d, hγ d, heq d, he d, hq d⟩⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

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

theorem exists_shared_free_filtered_common
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let L := sharedFreeCommonCorrectionBudget s Q P'
    ∃ (m : Fin s → ℕ) (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
      ∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp L ∧
        γ d ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        γ d ∈ (D.coefficientFreeSpan d).baseChange ℝ ∧
        e d ∈ (D.coefficientFreeSpan d).baseChange ℝ ∧
        q d ∈ (D.coefficientFreeSpan d).baseChange ℝ ∧
        coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ d + e d + q d ∧
        ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤ Real.exp L / (N : ℝ) ^ (d.val + 1) ∧
        (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (m d) := by
  intro L
  classical
  obtain ⟨l, γ, e, q, hdata⟩ :=
    D.exists_shared_free_common_projection E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let A := Q + P' + Λ
  let t := A + 1
  let C := (t + 2) ^ 3 + (t + 2) ^ 18
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hΛ : 0 ≤ Λ := pow_nonneg (add_nonneg hP' (Nat.cast_nonneg _)) _
  have hA : 0 ≤ A := add_nonneg (add_nonneg hQ hP') hΛ
  have hQA : Q ≤ A := (le_add_of_nonneg_right hP').trans (le_add_of_nonneg_right hΛ)
  have hPA : P' ≤ A := (le_add_of_nonneg_left hQ).trans (le_add_of_nonneg_right hΛ)
  have hΛA : Λ ≤ A := le_add_of_nonneg_left (add_nonneg hQ hP')
  have hprojectors (d : Fin s) :
      ∃ (P : (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) →ₗ[ℝ]
          (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) (m : ℕ),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
        (∀ x, P x ∈ (D.coefficientFreeSpan d).baseChange ℝ) ∧
        (∀ x ∈ (D.coefficientFreeSpan d).baseChange ℝ, P x = x) ∧
        (∀ x, ‖(E.basis.baseChange ℝ).equivFun (P x)‖ ≤
          Real.exp C * ‖(E.basis.baseChange ℝ).equivFun x‖) ∧
        ∀ x, (E.basis.baseChange ℝ).equivFun x ∈ realDenominatorGrid (l d) →
          (E.basis.baseChange ℝ).equivFun (P x) ∈ realDenominatorGrid m := by
    exact D.exists_coefficientFreeSpan_projector E.basis F (by omega) d
      (l d) (hdata d).1 hA hQA ((hT.1.1.trans hQP').trans hPA)
      ((hdata d).2.1.trans (Real.exp_le_exp.mpr hΛA))
  choose P m hm hmb hPU hPfix hPnorm hPgrid using hprojectors
  have ht : 0 ≤ t := add_nonneg hA zero_le_one
  have h18 : (t + 2) ^ 18 ≤ (t + 2) ^ 36 := pow_le_pow_right₀ (by linarith only [ht]) (by decide)
  have hL : L = (t + 2) ^ 3 + (t + 2) ^ 36 + Λ := rfl
  have hCL : C + Λ ≤ L := add_le_add (add_le_add (le_refl ((t + 2) ^ 3)) h18) (le_refl Λ)
  refine ⟨m, γ, (fun d => P d (e d)), (fun d => P d (q d)), ?_⟩
  intro d
  obtain ⟨_hl, _hlb, hγ, heq, herr, hgrid⟩ := hdata d
  have hγC : γ d ∈ (D.coefficientFreeSpan d).baseChange ℝ :=
    Submodule.baseChange_mono ℝ
      (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan d) _) hγ
  have hξC : coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.coefficientFreeSpan d).baseChange ℝ :=
    Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_coefficientFreeSpan d) (hξ d)
  have hsum : e d + q d ∈ (D.coefficientFreeSpan d).baseChange ℝ := by
    have hh : e d + q d = coefficients ξ.log (Finsupp.single () (d.val + 1)) - γ d := by
      rw [heq]
      abel
    rw [hh]
    exact ((D.coefficientFreeSpan d).baseChange ℝ).sub_mem hξC hγC
  have hsumfix := hPfix d (e d + q d) hsum
  rw [map_add] at hsumfix
  refine ⟨hm d, (hmb d).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hΛ)),
    hγ, hγC, hPU d _, hPU d _, ?_, ?_, hPgrid d _ hgrid⟩
  · calc
      _ = γ d + (e d + q d) := by rw [heq, add_assoc]
      _ = γ d + (P d (e d) + P d (q d)) := by rw [hsumfix]
      _ = _ := (add_assoc _ _ _).symm
  · calc
      _ ≤ Real.exp C * ‖(E.basis.baseChange ℝ).equivFun (e d)‖ := hPnorm d _
      _ ≤ Real.exp C * (Real.exp Λ / (N : ℝ) ^ (d.val + 1)) :=
        mul_le_mul_of_nonneg_left herr (Real.exp_pos _).le
      _ = Real.exp (C + Λ) / (N : ℝ) ^ (d.val + 1) := by rw [← mul_div_assoc, ← Real.exp_add]
      _ ≤ _ := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hCL) (pow_nonneg (Nat.cast_nonneg N) _)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeCoefficientCorrectionControl
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : E.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

theorem exists_native_freeCoefficient_corrections
    (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hγ : ∀ d, γ d ∈ (D.coefficientFreeSpan d).baseChange ℝ)
    (he : ∀ d, e d ∈ (D.coefficientFreeSpan d).baseChange ℝ)
    (hq : ∀ d, q d ∈ (D.coefficientFreeSpan d).baseChange ℝ)
    (l : Fin s → ℕ) (hl : ∀ d, 0 < l d) {L : ℝ}
    (hlb : ∀ d, (l d : ℝ) ≤ Real.exp L)
    (herr : ∀ d, ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤
      Real.exp L / (N : ℝ) ^ (d.val + 1))
    (hgrid : ∀ d, (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (l d)) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * L) ∧ (∀ d, l d ∣ m) ∧
      ∃ Γ ε ρ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
        Γ.log = positiveUnivariate γ ∧ ε.log = positiveUnivariate e ∧
        ρ.log = positiveUnivariate q ∧
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
        CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
          (Real.exp L) ε.log ∧
        CoefficientGrid (E.basis.baseChange ℝ) m ρ.log := by
  classical
  obtain ⟨Γ, hΓ, hΓ0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hT γ hγ
  obtain ⟨ε, hε, hε0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hT e he
  obtain ⟨ρ, hρ, hρ0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hT q hq
  let m := ∏ d, l d
  have hm : 0 < m := Finset.prod_pos (fun d _ => hl d)
  have hdiv (d : Fin s) : l d ∣ m := Finset.dvd_prod_of_mem l (Finset.mem_univ d)
  have hmb : (m : ℝ) ≤ Real.exp ((s : ℝ) * L) := by
    change ((∏ d, l d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _d : Fin s, Real.exp L :=
        Finset.prod_le_prod (fun d _ => Nat.cast_nonneg (l d)) (fun d _ => hlb d)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
  refine ⟨m, hm, hmb, hdiv, Γ, ε, ρ, hΓ, hε, hρ, hΓ0, hε0, hρ0, ?_, ?_⟩
  · rw [hε]
    apply positiveUnivariate_coefficientBound (E.basis.baseChange ℝ) e
      (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_pos L).le
    intro d
    simpa only [monomialScale, Finsupp.prod_single_index, pow_zero] using herr d
  · rw [hρ]
    apply positiveUnivariate_coefficientGrid
    intro d
    exact realDenominatorGrid_subset_of_dvd (hl d) (hdiv d) (hgrid d)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SharedFreeCommonPolynomialCorrections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

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

theorem exists_shared_free_common_polynomial_corrections
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let L := sharedFreeCommonCorrectionBudget s Q P'
    ∃ (m : ℕ) (Γ ε ρ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * L) ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
      CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ)) (Real.exp L) ε.log ∧
      CoefficientGrid (E.basis.baseChange ℝ) m ρ.log ∧
      ∀ d : Fin s,
        coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
          ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        coefficients ξ.log (Finsupp.single () (d.val + 1)) =
          coefficients Γ.log (Finsupp.single () (d.val + 1)) +
          coefficients ε.log (Finsupp.single () (d.val + 1)) +
          coefficients ρ.log (Finsupp.single () (d.val + 1)) := by
  intro L
  obtain ⟨l, γ, e, q, hdata⟩ := D.exists_shared_free_filtered_common E T hbQ hT F V g hg D'
    hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  obtain ⟨m, hm, hmb, _hdiv, Γ, ε, ρ, hΓ, hε, hρ, hΓ0, hε0, hρ0, hbound, hgrid⟩ :=
    D.exists_native_freeCoefficient_corrections E T hTfil γ e q
      (fun d => (hdata d).2.2.2.1)
      (fun d => (hdata d).2.2.2.2.1)
      (fun d => (hdata d).2.2.2.2.2.1)
      l (fun d => (hdata d).1) (fun d => (hdata d).2.1)
      (fun d => (hdata d).2.2.2.2.2.2.2.1)
      (fun d => (hdata d).2.2.2.2.2.2.2.2)
  refine ⟨m, Γ, ε, ρ, hm, hmb, hΓ0, hε0, hρ0, hbound, hgrid, ?_⟩
  intro d
  rw [hΓ, hε, hρ, positiveUnivariate_coefficient, positiveUnivariate_coefficient,
    positiveUnivariate_coefficient]
  exact ⟨(hdata d).2.2.1, (hdata d).2.2.2.2.2.2.1⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeLowerFactorization
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

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

theorem exists_shared_free_full_orbit_factorization
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let Lc := sharedFreeCommonCorrectionBudget s Q P'
    let Lv := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : ℕ) (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * (Lc + Lv)) ∧
          E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
          (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
            ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
          ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
            (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
            ∃ ε A K U ρ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
              A.log = Γ.log + positiveUnivariate (fun d => α d + ∑ j, (x j : ℝ) • β j d) ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 A = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 K = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
              CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                (Real.exp Lc + Real.exp Lv) ε.log ∧
              CoefficientGrid (E.basis.baseChange ℝ) m ρ.log ∧
              ε * A * K * U * ρ = g h ∧
              ∀ d : Fin s,
                coefficients K.log (Finsupp.single () (d.val + 1)) ∈
                  (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
                coefficients U.log (Finsupp.single () (d.val + 1)) ∈
                  (fourPetalSpace (D.dependentFreeSpan d)
                    (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ := by
  intro B Λ Lc Lv
  classical
  obtain ⟨mc, Γ, εc, ρc, hmc, hmcb, hΓ0, hεc0, hρc0, hεc, hρc, hcommon⟩ :=
    D.exists_shared_free_common_polynomial_corrections E T hbQ hT F V g hg D'
      hTfil hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  obtain ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, mv, α, β,
      hrank, hproper, hmv, hmvb, hα, hβ, hfamily⟩ :=
    D.exists_shared_free_affine_orbit_family E T hbQ hT F V g hg D'
      hTfil hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let m := mc * mv
  have hm : 0 < m := Nat.mul_pos hmc hmv
  have hmcdiv : mc ∣ m := ⟨mv, rfl⟩
  have hmvdiv : mv ∣ m := ⟨mc, Nat.mul_comm _ _⟩
  have hmb : (m : ℝ) ≤ Real.exp ((s : ℝ) * (Lc + Lv)) := by
    change ((mc * mv : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((s : ℝ) * Lc) * Real.exp ((s : ℝ) * Lv) :=
        mul_le_mul hmcb hmvb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hρcM : CoefficientGrid (E.basis.baseChange ℝ) m ρc.log :=
    fun a => realDenominatorGrid_subset_of_dvd hmc hmcdiv (hρc a)
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
    hrank, hproper, hm, hmb, hΓ0, (fun d => (hcommon d).1), hα, hβ, ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, Av, εv, ρv, U, hAv, hAv0, hεv0, hρv0, hU0,
      hεv, hρv, hdependent⟩ := hfamily h hh
  let ε := εc.logSum εv
  let ρ := ρc.logSum ρv
  let A := Γ.logSum Av
  have hε0 := εc.logSum_normalized εv hεc0 hεv0
  have hρ0 := ρc.logSum_normalized ρv hρc0 hρv0
  have hA0 := Γ.logSum_normalized Av hΓ0 hAv0
  have hρvM : CoefficientGrid (E.basis.baseChange ℝ) m ρv.log :=
    fun a => realDenominatorGrid_subset_of_dvd hmv hmvdiv (hρv a)
  have hcoeff (d : Fin s) : coefficients (g h).log (Finsupp.single () (d.val + 1)) -
      (coefficients ε.log (Finsupp.single () (d.val + 1)) +
        coefficients A.log (Finsupp.single () (d.val + 1)) +
        coefficients U.log (Finsupp.single () (d.val + 1)) +
        coefficients ρ.log (Finsupp.single () (d.val + 1))) ∈
      (T.filtration.layer (Finsupp.weight (fun _ : Unit => 1)
        (Finsupp.single () (d.val + 1))) 2).baseChange ℝ := by
    have hp := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two (by omega)
      (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) ξ (v h)
    rw [← hsplit h, (hcommon d).2, (hdependent d).2] at hp
    convert hp using 1
    simp only [ε, ρ, A, NilpotentLieFiltration.PolynomialOrbit.logSum_log,
      map_add, Finsupp.add_apply]
    abel
  obtain ⟨K, hK0, hprod, hK⟩ := T.exists_polynomialOrbit_factorization_rank_two (by omega)
    (fun _ : Unit => 1) (fun d : Fin s => Finsupp.single () (d.val + 1))
    (g h) ε A U ρ (hg h) hε0 hA0 hU0 hρ0 hcoeff
  refine ⟨x, hx, hspace, ε, A, K, U, ρ, ?_, hε0, hA0, hK0, hU0, hρ0,
    CoefficientBound.add _ _ hεc hεv, CoefficientGrid.add _ _ hρcM hρvM, hprod, ?_⟩
  · exact congrArg (fun z => Γ.log + z) hAv
  · intro d
    exact ⟨by simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hK d,
      (hdependent d).1⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_lower_factored_family {τ : Type*}
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (A K U : τ → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A t) = 1)
    (hK0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K t) = 1)
    (hU0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U t) = 1)
    (hA : ∀ t (d : Fin s), coefficients (A t).log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ t (d : Fin s), coefficients (K t).log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ t (d : Fin s), coefficients (U t).log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
        (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
      ∃ Tm : M.DegreeRankStructure (r + 1),
        Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
        Tm.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧
        M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
          (fun t (i : Fin W.family.outputDim × Fin W.family.outputDim) x =>
            V.observable i.1 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t * K t * U t))) *
            star (V.observable i.2 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t)))))
          (sharedFreeLowerComparisonBudget s Q P') := by
  intro S
  obtain ⟨J, _, M, Tm, hTm, hTmc, hZ⟩ :=
    B₀.exists_uniform_lower_comparison_model D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP'
  refine ⟨M, Tm, hTm, hTmc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hobs, huniform⟩ := hZ
  apply huniform.realizeFamily
  intro t
  obtain ⟨u, hu0, _, hu⟩ := D.exists_native_factored_comparison_orbit E T hbQ hT V g hg D'
    hTfil (by omega) (A t) (K t) (U t) (hA0 t) (hK0 t) (hU0 t) (hA t) (hK t) (hU t)
    J M Tm hTm
  refine ⟨u, hu0, ?_⟩
  intro i x
  exact SubspaceFreeLift.native_pair_observable_eval E T S J
    (D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil)
    M Tm V Z hobs ![A t * K t * U t, A t] u hu i x

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_shared_free_lower_factorization
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let Lc := sharedFreeCommonCorrectionBudget s Q P'
    let Lv := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : ℕ) (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * (Lc + Lv)) ∧
          E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
          (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
            ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
          ∃ (x : {h // h ∈ J} → Fin r₀ → ℤ)
            (ε A K U ρ : {h // h ∈ J} →
              E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ h : {h // h ∈ J},
              (∀ j, |x h j| ≤ (R₀ j : ℤ)) ∧ h.val = h₀ + η (x h) ∧
              (A h).log = Γ.log + positiveUnivariate
                (fun d => α d + ∑ j, (x h j : ℝ) • β j d) ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (ε h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (ρ h) = 1 ∧
              CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                (Real.exp Lc + Real.exp Lv) (ε h).log ∧
              CoefficientGrid (E.basis.baseChange ℝ) m (ρ h).log ∧
              ε h * A h * K h * U h * ρ h = g h.val ∧
              ∀ d : Fin s,
                coefficients (K h).log (Finsupp.single () (d.val + 1)) ∈
                  (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
                coefficients (U h).log (Finsupp.single () (d.val + 1)) ∈
                  (fourPetalSpace (D.dependentFreeSpan d)
                    (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) ∧
            (∃ M₀ : ℕ, 0 < M₀ ∧
              (M₀ : ℝ) ≤ Real.exp ((P' + sharedFreeFactorFreezingConstant s) ^
                sharedFreeFactorFreezingConstant s) ∧
              (∀ (h : {h // h ∈ J}) (y z : Unit → ℤ),
                (∀ j, (M₀ : ℤ) ∣ y j - z j) →
                ((QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) y (ρ h)) : E.Space) =
                  QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) z (ρ h))) ∧
                ((QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) y (ρ h))⁻¹ : E.Space) =
                  QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) z (ρ h))⁻¹)) ∧
              ∀ (h : {h // h ∈ J}) i (y z : Unit → ℤ) (δ : ℝ), 0 ≤ δ →
                (∀ j, |(y j : ℝ)| ≤ N) → (∀ j, |(z j : ℝ)| ≤ N) →
                (∀ j, |(y j : ℝ) - z j| ≤ (N : ℝ) * δ) →
                (∀ j, (M₀ : ℤ) ∣ y j - z j) →
                ‖V.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y (g h.val))) -
                  V.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (ε h) *
                     E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y
                       (A h * K h * U h) *
                     E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (ρ h)))‖ ≤
                  Real.exp ((P' + sharedFreeFactorFreezingConstant s) ^
                    sharedFreeFactorFreezingConstant s) * δ) ∧
            let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
            ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
              ∃ Tm : M.DegreeRankStructure (r + 1),
                Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                Tm.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧
                M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                  (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) y =>
                    V.observable i.1 (QuotientGroup.mk
                      (E.filtration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) y (A h * K h * U h))) *
                    star (V.observable i.2 (QuotientGroup.mk
                      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y (A h)))))
                  (sharedFreeLowerComparisonBudget s Q P') := by
  intro B Λ Lc Lv
  classical
  obtain ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
      hrank, hproper, hm, hmb, hΓ0, hΓ, hα, hβ, hfamily⟩ :=
    D.exists_shared_free_full_orbit_factorization E T hbQ hT F V g hg D'
      hTfil hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  choose x hx hspace ε A K U ρ hAl hε0 hA0 hK0 hU0 hρ0 hε hρ hprod hKU using
    (fun h : {h // h ∈ J} => hfamily h.val h.property)
  have hAc : ∀ (h : {h // h ∈ J}) (d : Fin s),
      coefficients (A h).log (Finsupp.single () (d.val + 1)) ∈
        ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ := by
    intro h d
    rw [hAl h]
    exact affine_refined_coefficient_mem D.coefficientFreeSpan D.dependentFreeSpan
      (fun d : Fin s => D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
      Γ.log α β (fun j => (x h j : ℝ)) hΓ (fun d => (hα d).1) (fun j d => (hβ j d).1) d
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
    hrank, hproper, hm, hmb, hΓ0, hΓ, hα, hβ, x, ε, A, K, U, ρ, ?_, ?_, ?_⟩
  · intro h
    exact ⟨hx h, hspace h, hAl h, hε0 h, hA0 h, hK0 h, hU0 h, hρ0 h,
      hε h, hρ h, hprod h, hKU h⟩
  · have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
    obtain ⟨M₀, hM₀, hM₀b, hperiod, hfreeze⟩ :=
      (RationalFilteredNilmanifold.exists_sharedFreeFactorFreezing.{0} s).choose_spec.2
        E hQ hQP' hP' hT.1 m hm hmb
    refine ⟨M₀, hM₀, hM₀b, (fun h y z hres => hperiod (ρ h) (hρ h) y z hres), ?_⟩
    intro h i y z δ hδ hy hz hyz hres
    exact hfreeze (V.observable i) V.lipBound (V.norm i) (V.lipschitz i) V.lip_bound
      (ε h) (A h * K h * U h) (ρ h) (g h.val)
      (by simpa only [mul_assoc] using hprod h) (N : ℝ)
      (by exact_mod_cast NeZero.pos N) (hε h) (hρ h) y z δ hδ hy hz hyz hres
  · exact B₀.exists_lower_factored_family D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' A K U hA0 hK0 hU0 hAc
      (fun h d => (hKU h d).1) (fun h d => (hKU h d).2)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeCorrelatedFactorization
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_correlated_lower_factorization
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (Hsource : Finset (ZMod N)) (hsource : Hsource.Nonempty)
    (hsourceDense : Real.exp (-Q) * Fintype.card (ZMod N) ≤ (Hsource.card : ℝ))
    (hHsource : H' ⊆ Hsource)
    (hcorr : ∀ h ∈ Hsource, Nonempty (NativeVectorCorrelation (s - 1) N Q
      (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h)))))))
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (sharedFreeCorrelationBudget s hs P') ≤ (N : ℝ)) :
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let Lv := sharedFreePetalLiftBudget s Q P'
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-(Λ + C)) * H'.card ≤ (J.card : ℝ) ∧
      ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
        (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
        (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
        (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
        (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
          ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
        (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
        (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
        ∃ (x : {h // h ∈ J} → Fin r₀ → ℤ)
          (A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
          (∀ h : {h // h ∈ J},
            (∀ j, |x h j| ≤ (R₀ j : ℤ)) ∧ h.val = h₀ + η (x h) ∧
            (A h).log = Γ.log + positiveUnivariate (fun d => α d + ∑ j, (x h j : ℝ) • β j d) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            ∀ d : Fin s,
              coefficients (K h).log (Finsupp.single () (d.val + 1)) ∈
                (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (d.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan d)
                  (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                    (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) ∧
          ∃ Δ : Subgroup E.filtration.Group, Δ ≤ E.lattice ∧
            (Δ.subgroupOf E.lattice).Characteristic ∧ (Δ.subgroupOf E.lattice).Normal ∧
            (Δ.subgroupOf E.lattice).FiniteIndex ∧ (Δ.relIndex E.lattice : ℝ) ≤ Real.exp C ∧
            ∃ (l : ℕ) (hl : 0 < l)
              (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates E.basis Δ)
              (hout : bchSubgroupCoordinates E.basis Δ ⊆ denominatorGrid l),
              (T.withLattice Δ l hl hin hout).ComplexityLE C ∧
              ∃ V₁ : (E.withLattice Δ l hl hin hout).UnitVerticalObservable
                  ((T.withLattice Δ l hl hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) C,
                V₁.frequency = V.frequency ∧
                (∀ h : {h // h ∈ J}, Nonempty (NativeVectorCorrelation (s - 1) N C
                  (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (fun _ => (z.val : ℤ)) (A h * K h * U h))))))) ∧
                ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                    (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
                  ∃ Tm : M.DegreeRankStructure (r + 1),
                    Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                    Tm.ComplexityLE ((Qc + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
                    M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                      (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) z =>
                        V₁.observable i.1 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval
                            (fun _ : Unit => 1) z (A h * K h * U h))) *
                        star (V₁.observable i.2 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (A h)))))
                      (nativeLowerPairModelBudget s Qc) := by
  intro Λ C Qc Lv S
  classical
  let P₀ := sharedFreeCorrelationInput s P'
  have hQ0 : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  obtain ⟨hP₀, hQP₀, hΛP₀, hdenP₀, hslowP₀, hperiodP₀⟩ :=
    sharedFreeCorrelationInput_bounds s hQ0 hQP' hP'
  have hP₀C : P₀ ≤ C := sharedFreeCorrelationInput_le_budget s hs hP'
  have hC0 : 0 ≤ C := (show 0 ≤ P₀ by linarith).trans hP₀C
  obtain ⟨D₁, _, _, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
      hrank, hproper, hm, hmb, hΓ0, hΓ, hα, hβ, x, ε, A, K, U, ρ, hdata, hperiod, _⟩ :=
    B₀.exists_shared_free_lower_factorization D E T hbQ hT F V g hg D'
      hTfil hfreq hs hp' hP' hQP' hpp' ξ v hsplit hξ hv
      ((Real.exp_le_exp.mpr (hΛP₀.trans hP₀C)).trans hN)
  obtain ⟨M₀, hM₀, hM₀b, hperiod, _⟩ := hperiod
  let X := W.replaceRank E T hbQ hT V g hg Hsource hsource hsourceDense hcorr
  let ε' (h : ZMod N) := if hh : h ∈ J then ε ⟨h, hh⟩ else 1
  let a' (h : ZMod N) := if hh : h ∈ J then A ⟨h, hh⟩ * K ⟨h, hh⟩ * U ⟨h, hh⟩ else 1
  let ρ' (h : ZMod N) := if hh : h ∈ J then ρ ⟨h, hh⟩ else 1
  have hprod' (h : ZMod N) (hh : h ∈ J) : ε' h * a' h * ρ' h = X.family.orbit h := by
    rcases hdata ⟨h, hh⟩ with ⟨_, _, _, _, _, _, _, _, _, _, hprod, _⟩
    change ε' h * a' h * ρ' h = g h
    simp only [ε', a', ρ', dif_pos hh]
    simpa only [mul_assoc] using hprod
  have hε' (h : ZMod N) (hh : h ∈ J) :
      CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P₀ + 2) ^ 1)) (ε' h).log := by
    rcases hdata ⟨h, hh⟩ with ⟨_, _, _, _, _, _, _, _, hε, _, _, _⟩
    simp only [ε', dif_pos hh]
    exact CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) hε hslowP₀
  have hρ' (h : ZMod N) (hh : h ∈ J) : CoefficientGrid (E.basis.baseChange ℝ) m (ρ' h).log := by
    rcases hdata ⟨h, hh⟩ with ⟨_, _, _, _, _, _, _, _, _, hρ, _, _⟩
    simpa only [ρ', dif_pos hh] using hρ
  have hperiod' (h : ZMod N) (hh : h ∈ J) (z z' : Unit → ℤ)
      (hres : ∀ j, (M₀ : ℤ) ∣ z j - z' j) :
      (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) z (ρ' h)) : E.Space) =
      QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) z' (ρ' h)) := by
    simpa only [ρ', dif_pos hh] using (hperiod ⟨h, hh⟩ z z' hres).1
  obtain ⟨Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
      hRank, J₂, hsub, hJ₂, hdense, V₁, hfreq₁, hcorr₁⟩ :=
    (exists_shared_factor_correlations s hs).choose_spec.2 X hf hP₀ hQP₀ m M₀ hm
      (hmb.trans (Real.exp_le_exp.mpr hdenP₀)) hM₀
      (hM₀b.trans (Real.exp_le_exp.mpr hperiodP₀)) J
      (fun h hh => hHsource (hJH hh)) hJ ε' a' ρ' hprod' hε' hρ' hperiod' hN
  let lift (h : {h // h ∈ J₂}) : {h // h ∈ J} := ⟨h.val, hsub h.property⟩
  refine ⟨J₂, (fun h hh => hJH (hsub hh)), hJ₂, ?_, r₀, R₀, η, h₀, Γ, α, β,
    hrank, hproper, hΓ0, hΓ, hα, hβ, (fun h => x (lift h)), (fun h => A (lift h)),
    (fun h => K (lift h)), (fun h => U (lift h)), ?_, Δ, hΔ, hchar, hnormal, hfinite,
    hindex, l, hl, hin, hout, hRank, V₁, hfreq₁, ?_, ?_⟩
  · calc
      _ = Real.exp (-C) * (Real.exp (-Λ) * H'.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-C) * J.card := mul_le_mul_of_nonneg_left hcard (Real.exp_pos _).le
      _ ≤ _ := hdense
  · intro h
    rcases hdata (lift h) with ⟨hx, hs, hA, _, hA0, hK0, hU0, _, _, _, _, hKU⟩
    exact ⟨hx, hs, hA, hA0, hK0, hU0, hKU⟩
  · intro h
    have hc := hcorr₁ h.val h.property
    change Nonempty (NativeVectorCorrelation (s - 1) N C
      (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (z.val : ℤ)) (a' h.val)))))) at hc
    have ha : a' h.val = A (lift h) * K (lift h) * U (lift h) := by
      simp only [a', dif_pos (hsub h.property), lift]
    rw [ha] at hc
    exact hc
  · apply B₀.exists_covered_factored_family D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' Δ l hl hin hout hC0 hRank V₁ hfreq₁
      (fun h => A (lift h)) (fun h => K (lift h)) (fun h => U (lift h))
    · intro h
      rcases hdata (lift h) with ⟨_, _, _, _, hA0, _, _, _, _, _, _, _⟩
      exact hA0
    · intro h
      rcases hdata (lift h) with ⟨_, _, _, _, _, hK0, _, _, _, _, _, _⟩
      exact hK0
    · intro h
      rcases hdata (lift h) with ⟨_, _, _, _, _, _, hU0, _, _, _, _, _⟩
      exact hU0
    · intro h d
      rcases hdata (lift h) with ⟨_, _, hA, _, _, _, _, _, _, _, _, _⟩
      rw [hA]
      exact affine_refined_coefficient_mem D.coefficientFreeSpan D.dependentFreeSpan
        (fun d : Fin s => D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
        Γ.log α β (fun j => (x (lift h) j : ℝ)) hΓ (fun d => (hα d).1) (fun j d => (hβ j d).1) d
    · intro h d
      rcases hdata (lift h) with ⟨_, _, _, _, _, _, _, _, _, _, _, hKU⟩
      exact (hKU d).1
    · intro h d
      rcases hdata (lift h) with ⟨_, _, _, _, _, _, _, _, _, _, _, hKU⟩
      exact (hKU d).2

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeCorrelatedAffineExistence
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.has_correlated_affine_comparison
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (Hsource : Finset (ZMod N)) (hsource : Hsource.Nonempty)
    (hsourceDense : Real.exp (-Q) * Fintype.card (ZMod N) ≤ (Hsource.card : ℝ))
    (hHsource : H' ⊆ Hsource)
    (hcorr : ∀ h ∈ Hsource, Nonempty (NativeVectorCorrelation (s - 1) N Q
      (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h)))))))
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (sharedFreeCorrelationBudget s hs P') ≤ (N : ℝ)) :
    D.CorrelatedAffineComparison E T hbQ hT V g hg D' hs := by
  exact B₀.exists_correlated_lower_factorization D E T hbQ hT F V g hg D'
    hTfil hfreq hs hp' hP' hQP' hpp' hf Hsource hsource hsourceDense hHsource hcorr
    ξ v hsplit hξ hv hN

end Erdos3.NativeRankRelation.CommonData

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

theorem majorPhasePlateauSignal_eq_phase
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) (b : Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
    (hb : ∀ i, |MvPolynomial.eval (fun x => (u x : ℝ))
      (lowTaggedPolynomial J k poly i) - c i - (b i : ℝ)| ≤ 1 / 8) :
    majorPhasePlateauSignal J k poly c P u =
      (Real.fourierChar (MvPolynomial.eval (fun i => ((Sum.elim u b i : ℤ) : ℝ)) P) : ℂ) := by
  unfold majorPhasePlateauSignal majorPhaseSample
  rw [majorPhaseNearestLift_eq_of_close J k poly c u b hb]
  rw [majorPhasePlateauKernel_one _ hb]
  simp only [Complex.ofReal_one, one_mul, mul_one]

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost shortCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

noncomputable def axisSlice : ResidueBoxSlice
    (fun i : {i // keep i} => A.sides i.val) C.step :=
  C.slice.comap (C.keptInclusion keep hkeep)

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

include A in

theorem trimMargin_proper (x : X) : 2 * spatialTrimMargin τ N x < N x := by
  obtain ⟨base, hbase⟩ := A.bases_nonempty
  obtain ⟨a, ha, _⟩ := Finset.mem_image.mp hbase
  have hx := (mem_integerBox _ _).mp ha x
  omega

end AllocatedExternalCandidateSampler

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedSourceEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

@[simp] theorem withKeep_siteValue
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep)
    (site : A.Site) :
    (candidate.withKeep keep hkeep).siteValue site = candidate.siteValue site := by
  cases hkeep
  rfl

end AllocatedExternalLocalCandidate

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

include A in
omit [∀ layer, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J layer)) (euclideanSubspace (U layer)))] in
theorem integerBox_nonempty : (integerBox N).Nonempty := by
  refine ⟨0, (mem_integerBox N _).mpr ?_⟩
  intro x
  change (0 : ℤ) ≤ 0 ∧ (0 : ℤ) < (N x : ℤ)
  exact ⟨le_rfl, by exact_mod_cast A.size_pos x⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end


