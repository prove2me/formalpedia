-- Prove2me | Definitions.Def_OAIE3v2B304
-- name    : OAIE3v2B304
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:00:53.614171+00:00
-- url     : https://prove2.me/theorems/e2f4dbc2-d0d1-47e4-9372-ca88d24be6b0
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 271 of 311
-- statement:
--   Definitions bundle 271 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B257`, `OAIE3v2B263` of this split.
--
--   Modules: `Estimates/AllocatedZeroLayerFixedCenterExcess.lean`, `Estimates/CommonInducedCorrelation.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/MixedPairComparison.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Sampling/AllocatedExternalCandidateActualShearForecastScore.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B257
import Definitions.Def_OAIE3v2B263

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

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

theorem commonAffineMarkedLift_eval (a : Fin t → ℚ) (h n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ
        (D.commonAffineMarkedLift t x y u h n) =
          ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
            ((x j).val + ∑ i, ((a i : ℝ) + (h : ℝ) * u i) • (y j i).val) := by
  simp only [commonAffineMarkedLift, map_sum, LinearMap.map_smul_of_tower, map_add]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  calc
    _ = ((x j).val + ∑ i, a i • (y j i).val) + (h : ℚ) • (∑ i, u i • (y j i).val) :=
      congrArg₂ (fun z z' : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => z + (h : ℚ) • z')
        (D.realAffineMarkedBase_eval t x y j a) (D.realAffineMarkedSlope_eval t y u j a)
    _ = _ := by
      simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum,
        ← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_intCast, smul_smul, add_assoc]

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonInducedCorrelation
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem localPhaseMarkedOrbit_induced_value
    {s r N d e k : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
    (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (hs : 1 ≤ s)
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    (hmap : ∀ z : E.RealGroup, z ∈ E.realLattice →
      (⟨(D.markedDependentEvaluation t 0).baseChange ℝ z.coord⟩ : Q.RealGroup) ∈ Q.realLattice)
    (hdir : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice)
    (V : Q.Space → ℂ) (G : E.Space → ℂ)
    (hG : ∀ z : E.RealGroup,
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) z.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk z) = markedLocalCoefficientValue D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t m hm E (D.dependentWordIdeal 0 2 0) le_rfl Q hmap V z)
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) (n : ℤ) :
    G (QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m))) =
      V (QuotientGroup.mk (⟨D.dependentQuotientMap.toLinearMap.baseChange ℝ
        (∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
          ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val))⟩ : Q.RealGroup)) := by
  let φ := normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t m
  let g : E.RealGroup := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m)
  let γ : E.RealGroup := D.scaledLocalAffineCorrectingElement t u c h₀ m h
  let ε : E.RealGroup := D.localPhaseMarkedSmallElement t u c h₀ m h
  let z : E.RealGroup :=
    ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩
  have hγ : γ ∈ E.realLattice := D.scaledLocalAffineCorrectingElement_mem_realLattice
    t u c h₀ m E hdir h
  have hcoset : (QuotientGroup.mk g : E.Space) = QuotientGroup.mk (ε * z) := by
    calc
      _ = QuotientGroup.mk (g * γ⁻¹) :=
        (quotient_mk_mul_mem E.realLattice g ⟨γ⁻¹, E.realLattice.inv_mem hγ⟩).symm
      _ = _ := congrArg QuotientGroup.mk (D.localPhaseMarkedOrbit_lift_factorization t x y u c h₀ m hs h n)
  have hz : torusPhaseLinear φ z.coord = 0 := normalizedMarkedPhase_real_pure
    D.coefficientFreeFiltration D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    t m z.coord (D.localPhaseMarkedLift_pure t x y u c h₀ m h n)
  have hε : ε = realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t
        ((m : ℝ) • (fun i => -affineCyclicTorusLocalLift u c h₀ h i)) := by
    change realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t _ = _
    apply congrArg (realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t)
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_neg, neg_mul]
  change G (QuotientGroup.mk g) = _
  rw [hcoset, hε]
  apply (induced_marked_observable_scaled_parameter D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer hm E (D.dependentWordIdeal 0 2 0) le_rfl Q hmap V G hG
    (fun i => -affineCyclicTorusLocalLift u c h₀ h i)
    (fun i => by simpa only [abs_neg] using hsmall i) z hz).trans
  exact congrArg (fun a => V (QuotientGroup.mk (⟨a⟩ : Q.RealGroup)))
    (D.localPhaseMarkedLift_base_projection t x y u c h₀ m hm h n)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N d e k l : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (hs : 1 ≤ s)
  (M : RationalFilteredNilmanifold
    (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s l)
  (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
  (hφ : E.lattice ≤ Q.lattice.comap (mapOfSteps
    (hL := E.filtration.lowerCentralSeries_eq_bot) (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
  (hmap : ∀ z : M.RealGroup, z ∈ M.realLattice →
    (⟨(D.markedDependentEvaluation t 0).baseChange ℝ z.coord⟩ : Q.RealGroup) ∈ Q.realLattice)
  (hdir : ∀ a : Fin t → ℤ,
    (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
        M.filtration.Group) ∈ M.lattice)

include hs hdir

theorem induced_local_value_eq_nativeSpaceMap (V : Q.Space → ℂ) (G : M.Space → ℂ)
    (hG : ∀ z : M.RealGroup,
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) z.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk z) = markedLocalCoefficientValue D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t m hm M (D.dependentWordIdeal 0 2 0) le_rfl Q hmap V z)
    (a : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4)
    (ha : a.log = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) (n : ℤ) :
    G (QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m))) =
      V (E.nativeSpaceMap Q D.dependentQuotientMap hφ (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => n) a))) := by
  apply (D.localPhaseMarkedOrbit_induced_value t x y u c h₀ m hm hs M Q hmap hdir V G hG h hsmall n).trans
  have hcoord : (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => n) a).coord =
      ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
        ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
    rw [E.filtration.realification.polynomialOrbitEval_coord, ha]
    simp only [positiveUnivariate, map_sum, eval_monomial, Finsupp.prod_single_index, pow_zero]
  rw [nativeSpaceMap_mk]
  apply congrArg (fun z : Q.RealGroup => V (QuotientGroup.mk z))
  apply NilpotentLieBCHGroup.ext
  change _ = D.dependentQuotientMap.toLinearMap.baseChange ℝ _
  rw [hcoord]

variable [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
  [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]

theorem exists_local_induced_comparison_correlation {A I J : Type*} [Fintype I] [Fintype J]
    {degree : ℕ} {z q₁ q₂ qV : ℝ} {S : Subgroup E.RealGroup} {T : Subgroup Q.RealGroup}
    (V : E.UnitVerticalObservable S I qV) (U : Q.UnitVerticalObservable T J qV)
    (G : J → M.Space → ℂ)
    (hG : ∀ j (z : M.RealGroup),
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) z.coord i| ≤ 1 / 4) →
      G j (QuotientGroup.mk z) = markedLocalCoefficientValue D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t m hm M (D.dependentWordIdeal 0 2 0) le_rfl Q hmap (U.observable j) z)
    (a v : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4)
    (ha : a.log = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val))
    (f : A → ZMod N → ℂ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp q₁) (hJ : (Fintype.card J : ℝ) ≤ Real.exp q₂)
    (B : NativeVectorCorrelation degree N z (fun ai : A × I => fun n =>
      f ai.1 n * star (V.observable ai.2 (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) v))))) :
    Nonempty (NativeVectorCorrelation degree N (z + q₁ + q₂)
      (fun ij : A × ((I × I) × (I × J)) => fun n =>
        f ij.1 n * star (G ij.2.2.2 (QuotientGroup.mk
          ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
            (correlationInput (h.val : ℤ) (n.val : ℤ)) (D.localPhaseMarkedOrbit t x y u c h₀ m)))) *
        star (V.observable ij.2.1.1 (QuotientGroup.mk
            (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) v)) *
          star (V.observable ij.2.1.2 (QuotientGroup.mk
            (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a)))) *
        star (mapDifferenceObservable V U D.dependentQuotientMap hφ ij.2.2 (QuotientGroup.mk
          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a))))) := by
  have hvalue (j : J) (n : ZMod N) := D.induced_local_value_eq_nativeSpaceMap
    t x y u c h₀ m hm hs M E Q hφ hmap hdir (U.observable j) (G j) (hG j) a h hsmall ha (n.val : ℤ)
  have htwo := exists_native_two_unit_comparison f
    (fun i n => V.observable i (QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) v)))
    (fun i n => V.observable i (QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a)))
    (fun j n => U.observable j (E.nativeSpaceMap Q D.dependentQuotientMap hφ (QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a))))
    (fun n => V.unit _) (fun n => U.unit _) hq₁ hq₂ hI hJ B
  simpa only [hvalue, mapDifferenceObservable] using htwo

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem hasCommonInducedCorrelationFamily_of_model
    {τ K I J : Type*} [Fintype I] [Fintype J]
    {s k r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (f : τ → K → ZMod N → ℂ) (B C : ℝ) (hs : 1 ≤ s)
    (hZ : 0 ≤ Z) (hI : (Fintype.card I : ℝ) ≤ Real.exp Z)
    (hJ : (Fintype.card J : ℝ) ≤ Real.exp Z)
    (hsmall : ∀ z i, |affineCyclicTorusLocalLift u c h₀ (h z) i| ≤ 1 / 4)
    (ha : ∀ z, (a z).log = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ (h z) i • (y j i).val))
    (hcorr : ∀ z, Nonempty (NativeVectorCorrelation degree N Z (fun ij : K × I => fun n =>
      f z ij.1 n * star (V.observable ij.2 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (n.val : ℤ)) (v z)))))))
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp B)
    (d : ℕ) (hdim : d ≤ n * (s + 1) * (t + 1) ^ s + t)
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (M : E.MultidegreeStructure (mixedCorrelationDegree s))
    (hMF : M.filtration = D.markedQuotientMultidegree t) (hM : M.ComplexityLE B)
    (hmap : ∀ z : E.RealGroup, z ∈ E.realLattice →
      (⟨(D.markedDependentEvaluation t 0).baseChange ℝ z.coord⟩ : Q.RealGroup) ∈ Q.realLattice)
    (hlat : ∀ b : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (b i : ℚ))⟩ : E.filtration.Group) ∈ E.lattice)
    (hobs :
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
      letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
          IsModuleTopology.topologicalAddGroup ℝ _
      letI := realification_moduleTopology_t2 E.basis
      letI := E.metricSpace
      ∃ G : J → E.Space → ℂ, (∀ j z, ‖G j z‖ ≤ 2) ∧
        (∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) ∧
        ∀ j (g : E.RealGroup),
          (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t m) g.coord i| ≤ 1 / 4) →
          G j (QuotientGroup.mk g) = markedLocalCoefficientValue
            D.coefficientFreeFiltration D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
            D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t m hm E
            (D.dependentWordIdeal 0 2 0) le_rfl Q hmap (U.observable j) g)
    (hBC : B ≤ C) (hthree : Z + Z + Z ≤ C) :
    D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ x y u c h₀ h a v f C := by
  unfold HasCommonInducedCorrelationFamily
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hBC), d, hdim, E, M, hMF,
    hM.mono M hBC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := E.metricSpace
  obtain ⟨G, hGn, hGL, hGe⟩ := hobs
  refine ⟨G, hGn, ?_, ?_⟩
  · intro j
    exact (hGL j).weaken (show (⟨Real.exp B, Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp C, Real.exp_nonneg _⟩ from Real.exp_le_exp.mpr hBC)
  · intro z
    refine Nonempty.map (fun Cz => NativeVectorCorrelation.mono Cz hthree) ?_
    exact D.exists_local_induced_comparison_correlation
      (d := d) (e := e) (k := k) (l := n) (A := K) (I := I) (J := J)
      (degree := degree) (z := Z) (q₁ := Z) (q₂ := Z) (qV := Z) (S := S) (T := T)
      t x y u c h₀ m hm hs E A Q hφ hmap hlat
      V U G hGe (a z) (v z) (h z) (hsmall z) (ha z) (f z) hZ hZ hI hJ
      (Classical.choice (hcorr z))

theorem exists_common_induced_correlation_family (s k : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {τ K I J : Type*} [Fintype I] [Fintype J]
      {r N n e degree : ℕ} [NeZero N] {b p q P Z : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (t : ℕ)
      (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (_hFA : D.coefficientFreeFiltration.associatedDegree = A.filtration)
      (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
      [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
      {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
      (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T J Z)
      (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
        (hL := A.filtration.lowerCentralSeries_eq_bot) (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap)),
      0 ≤ Z → A.GeometryComplexityLE Z → Q.GeometryComplexityLE Z → (t : ℝ) ≤ Z →
      (∀ i j, rationalLogHeight (A.basis.repr (D.coefficientFreeGenerator i) j) ≤ Z) →
      (∀ i j, rationalLogHeight (Q.basis.repr (D.dependentQuotientMap (A.basis j)) i) ≤ Z) →
      (Fintype.card I : ℝ) ≤ Real.exp Z → (Fintype.card J : ℝ) ≤ Real.exp Z →
      ∀ (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
        (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
        (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
        (∀ z i, |affineCyclicTorusLocalLift u c h₀ (h z) i| ≤ 1 / 4) →
        (∀ z, (a z).log = positiveUnivariate (fun j => (x j).val +
          ∑ i, affineCyclicTorusLocalLift u c h₀ (h z) i • (y j i).val)) →
        ∀ f : τ → K → ZMod N → ℂ,
          (∀ z, Nonempty (NativeVectorCorrelation degree N Z (fun ij : K × I => fun n =>
            f z ij.1 n * star (V.observable ij.2 (QuotientGroup.mk
              (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) (v z))))))) →
          D.HasCommonInducedCorrelationFamily (degree := degree) t A Q V U hφ
            x y u c h₀ h a v f ((Z + C) ^ C) := by
  obtain ⟨B, _, hmodel⟩ := exists_native_induced_marked_model s k hs
  let P₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * Polynomial.X + P₀)
  refine ⟨C, hC, ?_⟩
  intro τ K I J _ _ r N n e degree _ b p q P Z W out H R D t A hFA Q _ _ _ _ _ _ _ _ S T V U hφ
    hZ hA hQ ht hgen hproj hI hJ x y u c h₀ h a v hsmall ha f hcorr
  let Q₀ := (Z + B) ^ B
  have hQ₀ : 0 ≤ Q₀ := by dsimp [Q₀]; positivity
  have htotal : 3 * Z + Q₀ ≤ (Z + C) ^ C := by
    simpa [P₀, Q₀, Polynomial.eval₂_pow] using hbudget Z hZ
  have hQC : Q₀ ≤ (Z + C) ^ C := by linarith
  have hthree : Z + Z + Z ≤ (Z + C) ^ C := by linarith
  let := Q.metricSpace
  obtain ⟨m, hm, hmp, d, hdim, E, M, hMF, hM, hmap, hint, hlat, hobs⟩ :=
    hmodel D.coefficientFreeFiltration A hFA D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
      D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer (D.dependentWordIdeal 0 2 0) le_rfl Q U.observable
      hZ hA ht hgen hQ hproj U.norm
      (fun j => (U.lipschitz j).weaken (show U.lipBound ≤ ⟨Real.exp Z, Real.exp_nonneg _⟩ from U.lip_bound))
  exact D.hasCommonInducedCorrelationFamily_of_model t A Q V U hφ x y u c h₀ h a v f
    Q₀ ((Z + C) ^ C) hs hZ hI hJ hsmall ha hcorr m hm hmp d hdim E M hMF hM hmap hlat hobs hQC hthree

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {τ K I : Type} [Fintype I] {s r N n degree : ℕ} [NeZero N]
  {b p q P Z : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
  {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
  (D : R.CommonData P) (t : ℕ)
  (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : A.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z)
  (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
  (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (f : τ → K → ZMod N → ℂ)

theorem exists_covered_induced_correlation_family (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {τ K I : Type} [Fintype I]
      {r N n degree : ℕ} [NeZero N] {b p q P Q₀ Z : ℝ}
      {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (J : D.CoefficientBases Q₀) (t : ℕ)
      (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : A.DegreeRankStructure (r + 1))
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z),
      T.filtration = D.coefficientFreeFiltration →
      V.frequency = J.freeFrequency D →
      0 ≤ Z → T.ComplexityLE Z → (t : ℝ) ≤ Z →
      (∀ i j, rationalLogHeight (A.basis.repr (D.coefficientFreeGenerator i) j) ≤ Z) →
      (Fintype.card I : ℝ) ≤ Real.exp Z →
      ∀ (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
        (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
        (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
        (∀ z i, |affineCyclicTorusLocalLift u c h₀ (h z) i| ≤ 1 / 4) →
        (∀ z, (a z).log = positiveUnivariate (fun j => (x j).val +
          ∑ i, affineCyclicTorusLocalLift u c h₀ (h z) i • (y j i).val)) →
        (∀ z, A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (a z) = 1) →
        ∀ f : τ → K → ZMod N → ℂ,
          (∀ z, Nonempty (NativeVectorCorrelation degree N Z (fun ij : K × I => fun w =>
            f z ij.1 w * star (V.observable ij.2 (QuotientGroup.mk
              (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                (fun _ => (w.val : ℤ)) (v z))))))) →
          D.HasCoveredInducedCorrelationFamily (degree := degree)
            t A T V x y u c h₀ h a v f ((Z + C) ^ C) := by
  obtain ⟨a₀, _, hcover⟩ := exists_covered_dependentQuotient_comparison s
  obtain ⟨b₀, _, hinduce⟩ := exists_common_induced_correlation_family s s hs
  let Y₀ : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a₀) ^ a₀
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Y₀ + (Y₀ + Polynomial.C b₀) ^ b₀)
  refine ⟨C, hC, ?_⟩
  intro τ K I _ r N n degree _ b p q P Q₀ Z W out H R D J t A T _ _ _ _ V
    hTF hV hZ hT ht hgen hI x y u c h₀ h a v hsmall ha ha0 f hcorr
  let B := (Z + a₀) ^ a₀
  let Y := Z + B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hY : 0 ≤ Y := add_nonneg hZ hB
  have hZY : Z ≤ Y := le_add_of_nonneg_right hB
  have hBY : B ≤ Y := le_add_of_nonneg_left hZ
  have htotal : Y + (Y + b₀) ^ b₀ ≤ (Z + C) ^ C := by
    simpa [Y₀, Y, B, Polynomial.eval₂_pow] using hbudget Z hZ
  have hYC : Y ≤ (Z + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans htotal
  have hBC : B ≤ (Z + C) ^ C := hBY.trans hYC
  have hindC : (Y + b₀) ^ b₀ ≤ (Z + C) ^ C := (le_add_of_nonneg_left hY).trans htotal
  obtain ⟨e, he, Q, S, hSF, hS, _, _, hproj, Λ, hΛ, _, _, _, _,
    m, hm, hin, hout, hT₀, hφ, V₀, hVfreq, _, hVobs, hcoeff⟩ :=
    hcover D J A T V hTF hZ hT hgen hV 1 (by decide) (by simpa using Real.one_le_exp hZ)
  let A₀ := A.withLattice Λ m hm hin hout
  let T₀ := T.withLattice Λ m hm hin hout
  refine ⟨Λ, hΛ, m, hm, hin, hout, hT₀.mono T₀ hBC, e, he, Q, S, hSF,
    hS.mono S hBC, hφ, V₀.mono hBC, hVfreq, hVobs, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨k, hk, hkB, U, _, _, hcomparison⟩ := hcoeff
  refine ⟨k, hk, hkB.trans (Real.exp_le_exp.mpr hBC), U.mono hBC, ?_, ?_⟩
  · have hFA : D.coefficientFreeFiltration.associatedDegree = A₀.filtration := by
      rw [← hTF]
      exact T.associated
    have hcorrY (z : τ) : Nonempty (NativeVectorCorrelation degree N Y
        (fun ij : K × I => fun w => f z ij.1 w *
          star ((V₀.mono hBY).observable ij.2 (QuotientGroup.mk
            (A₀.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (w.val : ℤ)) (v z)))))) := by
      obtain ⟨Bz⟩ := hcorr z
      have hvalue (i : I) (w : ZMod N) :
          (V₀.mono hBY).observable i (QuotientGroup.mk
            (A₀.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (w.val : ℤ)) (v z))) =
          V.observable i (QuotientGroup.mk
            (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (w.val : ℤ)) (v z))) := hVobs i _
      simpa only [hvalue] using
        (show Nonempty (NativeVectorCorrelation degree N Y _) from ⟨Bz.mono hZY⟩)
    have hfamily := hinduce D t A₀ hFA Q (V₀.mono hBY) (U.mono hBY) hφ
      hY (hT₀.1.mono A₀ hBY) (hS.1.mono Q hBY) (ht.trans hZY)
      (fun i j => (hgen i j).trans hZY) (fun i j => (hproj i j).trans hBY)
      (hI.trans (Real.exp_le_exp.mpr hZY))
      (by simpa only [Fintype.card_fin] using hkB.trans (Real.exp_le_exp.mpr hBY))
      x y u c h₀ h a v hsmall ha f hcorrY
    exact HasCommonInducedCorrelationFamily.mono D t A₀ Q (V₀.mono hBY) (U.mono hBY)
      hφ x y u c h₀ h a v f hfamily hindC
  · apply ((hcomparison Unit (fun _ => 1)).mono hBC).realizeFamily
    intro z
    exact ⟨a z, ha0 z, fun _ _ => rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

def CorrelatedLocalMarkedFamily (hs : 2 ≤ s) : Prop :=
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let B := P' + Λ + C
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-((B + 4) ^ 7)) * N ≤ (J.card : ℝ) ∧
      ∃ t : ℕ, (t : ℝ) ≤ Λ ∧ ∃ (h₀ : ZMod N) (u c : Fin t → ℝ)
        (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ),
        (∀ i, u i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * u i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound t (Real.exp (-B)) + 1 / 16) ∧
        ∃ A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          (∀ h : {h // h ∈ J},
            (∀ i, |affineCyclicTorusLocalLift u c h₀ h.val i| ≤ 1 / 16) ∧
            (A h).log = positiveUnivariate (fun j => (x j).val +
              ∑ i, affineCyclicTorusLocalLift u c h₀ h.val i • (y j i).val) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            (∀ j : Fin s,
              coefficients (K h).log (Finsupp.single () (j.val + 1)) ∈
                (T.filtration.layer (j.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (j.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan j)
                  (fourRefinedRelation (D.coefficientFreeSpan j) (D.dependentFreeSpan j)
                    (D'.coefficientFourSpace ⟨j.val + 1, by omega⟩))).baseChange ℝ) ∧
            ∀ n : ℤ,
              (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
                D.coefficientWeight D.coefficientIsDependent t
                  (fun i => (-affineCyclicTorusCarry u c h₀ h.val i : ℤ))).baseChange ℝ
                    (D.localAffineMarkedLift t x y u c h₀ h.val n) =
                      (E.filtration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => n) (A h)).coord) ∧
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
                      (nativeLowerPairModelBudget s Qc)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def localCoveredInducedBudget (s : ℕ) (hs : 2 ≤ s) (q p : ℝ) : ℝ :=
  let Z := q + (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
    sharedFreeCorrelationBudget s hs p + 2
  let C := (NativeRankRelation.CommonData.exists_covered_induced_correlation_family s (by omega)).choose
  (Z + C) ^ C

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def NativeCorrelationStructure.HasLocalMarkedFamily
    {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s (r + 1) N p f) (hs : 2 ≤ s) (C : ℕ) : Prop :=
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  ∃ (A : ℝ) (hpA : p ≤ A), A ≤ Z ∧
  ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
    H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧ p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
    ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
      (B : D.CoefficientBases A)
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
        (finrank ℚ D.CoefficientFreeLieAlgebra))
      (T : E.DegreeRankStructure (r + 1)) (hT : T.ComplexityLE A),
      T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
      Nonempty (FreeCoordinateFrame E.basis A) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 E.basis
       ∃ V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) A,
         V.frequency = B.freeFrequency D ∧
         ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
           (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
           (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
             (D.commonFreeSpan d).baseChange ℝ) ∧
           ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
             (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
               (fun _ : Unit => 1) 0 (v h) = 1),
             (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
               (D.dependentFreeSpan d).baseChange ℝ) ∧
             (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                (fun h => by rw [map_mul, hξ, hv h, one_mul])
              ∃ (out' : Fin U.outputDim) (H' : Finset (ZMod N)) (q' : ℝ),
                H' ⊆ W.shifts ∧ H'.Nonempty ∧ CyclicShortShiftSet H' ∧
                Real.exp (-Z) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                A ≤ q' ∧ q' ≤ Z ∧
                ∃ (R' : NativeRankRelation U out' H' q' q') (D' : R'.CommonData Z),
                  D.CorrelatedLocalMarkedFamily E T hpA hT V (fun h => ξ * v h)
                    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs ∧
                  (Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
                    sharedFreeCorrelationBudget s hs Z + 4) ^ 7 ≤ (p + C) ^ C ∧
                  ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
                    nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
                  nativeLowerPairModelBudget s
                    (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
                    (p + C) ^ C))

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def NativeCorrelationStructure.HasLocalInducedFamily
    {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s (r + 1) N p f) (hs : 2 ≤ s) (C : ℕ) : Prop :=
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  ∃ (A : ℝ) (hpA : p ≤ A), A ≤ Z ∧
  ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
    H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧ p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
    ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
      (B : D.CoefficientBases A)
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
        (finrank ℚ D.CoefficientFreeLieAlgebra))
      (T : E.DegreeRankStructure (r + 1)) (hT : T.ComplexityLE A),
      T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
      Nonempty (FreeCoordinateFrame E.basis A) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 E.basis
       ∃ V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) A,
         V.frequency = B.freeFrequency D ∧
         ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
           (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
           (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
             (D.commonFreeSpan d).baseChange ℝ) ∧
           ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
             (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
               (fun _ : Unit => 1) 0 (v h) = 1),
             (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
               (D.dependentFreeSpan d).baseChange ℝ) ∧
             (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                (fun h => by rw [map_mul, hξ, hv h, one_mul])
              ∃ (out' : Fin U.outputDim) (H' : Finset (ZMod N)) (q' : ℝ),
                H' ⊆ W.shifts ∧ H'.Nonempty ∧ CyclicShortShiftSet H' ∧
                Real.exp (-Z) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                A ≤ q' ∧ q' ≤ Z ∧
                ∃ (R' : NativeRankRelation U out' H' q' q') (D' : R'.CommonData Z),
                  D.CorrelatedLocalInducedFamily E T hpA hT V (fun h => ξ * v h)
                    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs
                    (localCoveredInducedBudget s hs A Z) ∧
                  localCoveredInducedBudget s hs A Z ≤ (p + C) ^ C ∧
                  (Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
                    sharedFreeCorrelationBudget s hs Z + 4) ^ 7 ≤ (p + C) ^ C ∧
                  ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
                    nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
                  nativeLowerPairModelBudget s
                    (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
                    (p + C) ^ C))

end Erdos3

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

def NativeDetection (degree : ℕ) (pSlice pTest pNative α : ℝ) : Prop :=
  ∀ {Tests : A.Path → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) degree (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset A.Site)
    (origin : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ),
    (∀ z j, 0 < step z j) →
    (∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j)) →
    (∀ z j, IsDenseCommonStrideBox A.sides pSlice ((slices z j).image Subtype.val)) →
    (∀ z j, (Vdetect z j).ComplexityLE pTest) →
    (∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1) →
    SampledSliceNativeDetection J N A.integerBox_nonempty poly A.law A.physical slices
      (fun z j t => star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val)))
      degree pNative α

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

local instance instNonemptySite_4 : Nonempty A.Site := A.site_nonempty

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end


