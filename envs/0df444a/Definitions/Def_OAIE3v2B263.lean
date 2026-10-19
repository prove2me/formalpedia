-- Prove2me | Definitions.Def_OAIE3v2B263
-- name    : OAIE3v2B263
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:48:20.655397+00:00
-- url     : https://prove2.me/theorems/8d99c01e-138d-4130-ba37-7e810aaa8d7c
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 270 of 311
-- statement:
--   Definitions bundle 270 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B255`, `OAIE3v2B256` of this split.
--
--   Modules: `Estimates/MixedPairComparison.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Polynomial/LocalPhaseMarkedObservable.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B255
import Definitions.Def_OAIE3v2B256

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

theorem commonAffineMarkedOrbit_eval (h n : ℤ) :
    ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval (correlationInput h n)
      (D.commonAffineMarkedOrbit t x y u)).coord =
        (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.commonAffineMarkedLift t x y u h n) := by
  have he := realMarkedAffineMixedOrbit_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t 1 (D.realAffineMarkedBase t x y) (D.realAffineMarkedSlope t y u) h n
  apply he.trans
  simp only [commonAffineMarkedLift, map_sum, LinearMap.map_smul_of_tower, map_add]
  rfl

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
namespace OAI

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
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

theorem localPhaseMarkedOrbit_eval (h : ZMod N) (n : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) =
        (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
          (correlationInput (h.val : ℤ) n)
          (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0) *
        realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t
            (fun i => -(m : ℝ) * (((h.val : ℝ) - h₀.val) * u i - c i)) := by
  let E := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n)
  let g := D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0
  let a₀ : Fin t → ℝ := fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)
  let a₁ : Fin t → ℝ := fun i => -(m : ℝ) * u i
  let phase : (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
    realMarkedParameterOrbit D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t a₀ a₁
  have hm : E (D.localPhaseMarkedOrbit t x y u c h₀ m) = E g * E phase := E.map_mul g phase
  apply hm.trans
  apply congrArg (fun z : (D.markedQuotientMultidegree t).realification.Group => E g * z)
  apply (realMarkedParameterOrbit_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t a₀ a₁ (h.val : ℤ) n).trans
  apply congrArg (realMarkedParameterElement D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t)
  funext i
  simp only [a₀, a₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_natCast]
  ring

theorem localPhaseMarkedOrbit_right_normalization (h : ZMod N) (n : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) *
        (D.scaledLocalAffineCorrectingElement t u c h₀ m h)⁻¹ =
      (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n)
        (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0) *
          D.localPhaseMarkedSmallElement t u c h₀ m h := by
  let par : (Fin t → ℝ) → (D.markedQuotientMultidegree t).realification.Group :=
    realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t
  let a : Fin t → ℝ := fun i => -(m : ℝ) * (((h.val : ℝ) - h₀.val) * u i - c i)
  let b : Fin t → ℝ := fun i => -(m : ℝ) * (affineCyclicTorusCarry u c h₀ h i : ℝ)
  let g := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n)
    (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)
  have hi : (par b)⁻¹ = par (-b) :=
    realMarkedParameterElement_inv D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t b
  have hab : par a * par (-b) = D.localPhaseMarkedSmallElement t u c h₀ m h := by
    apply (realMarkedParameterElement_mul D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t a (-b)).trans
    apply congrArg par
    funext i
    simp only [a, b, Pi.add_apply, Pi.neg_apply, affineCyclicTorusLocalLift_eq_sub_carry]
    ring
  calc
    _ = (g * par a) * (par b)⁻¹ :=
      congrArg₂ (fun z w : (D.markedQuotientMultidegree t).realification.Group => z * w⁻¹)
        (D.localPhaseMarkedOrbit_eval t x y u c h₀ m h n)
        (D.scaledLocalAffineCorrectingElement_eq_parameter t u c h₀ m h)
    _ = (g * par a) * par (-b) := congrArg (fun z => (g * par a) * z) hi
    _ = g * (par a * par (-b)) := mul_assoc _ _ _
    _ = _ := congrArg (g * ·) hab

end Erdos3.NativeRankRelation.CommonData

end

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

theorem commonAffineMarkedLift_shift_eval (a : Fin t → ℝ) (h n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (realMarkedAffineShift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t a (D.commonAffineMarkedLift t x y 0 h n)) =
      ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) • ((x j).val + ∑ i, a i • (y j i).val) := by
  have hz (j : Fin s) :
      realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y 0 j) = 0 := by
    rw [D.realAffineMarkedSlope_zero t y j]
    exact (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1).map_zero
  simp only [commonAffineMarkedLift, hz, smul_zero, add_zero,
    map_sum, LinearMap.map_smul_of_tower]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
    (D.realAffineMarkedBase_shift_eval t x y a j)

variable (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

theorem localPhaseMarkedLift_eval (hm : 0 < m) (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n) =
      ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
        ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  apply (D.commonAffineMarkedLift_shift_eval t x (fun j i => (m : ℝ)⁻¹ • y j i)
    (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i) h.val n).trans
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  apply congrArg ((x j).val + ·)
  apply Finset.sum_congr rfl
  intro i _
  change ((m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i) •
    ((m : ℝ)⁻¹ • (y j i).val) = _
  rw [smul_smul]
  apply congrArg (fun z : ℝ => z • (y j i).val)
  field_simp [hm0]

theorem localPhaseMarkedLift_conjugation (hs : 1 ≤ s) (h : ZMod N) (n : ℤ) :
    conjugationCoord (D.localPhaseMarkedSmallElement t u c h₀ m h)⁻¹
      (((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n)
        (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)).coord) =
      (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
          (D.localPhaseMarkedLift t x y u c h₀ m h n) := by
  apply (congrArg (fun z => conjugationCoord z _)
    (D.localPhaseMarkedSmallElement_inv t u c h₀ m h)).trans
  apply (congrArg (conjugationCoord _)
    (D.commonAffineMarkedOrbit_eval t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n)).trans
  exact realMarkedAffineShift_conjugation D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t hs
      (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)
      (D.commonAffineMarkedLift t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n)

theorem localPhaseMarkedOrbit_lift_factorization (hs : 1 ≤ s) (h : ZMod N) (n : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) *
        (D.scaledLocalAffineCorrectingElement t u c h₀ m h)⁻¹ =
      D.localPhaseMarkedSmallElement t u c h₀ m h *
        ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩ := by
  let ε := D.localPhaseMarkedSmallElement t u c h₀ m h
  let g := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n)
    (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)
  have hg : ε⁻¹ * g * ε =
      ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
          (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩ := by
    apply NilpotentLieBCHGroup.ext
    simpa only [conjugationCoord, inv_inv] using D.localPhaseMarkedLift_conjugation t x y u c h₀ m hs h n
  apply (D.localPhaseMarkedOrbit_right_normalization t x y u c h₀ m h n).trans
  calc
    g * ε = ε * (ε⁻¹ * g * ε) := by simp only [mul_assoc, mul_inv_cancel_left]
    _ = _ := congrArg (ε * ·) hg

end Erdos3.NativeRankRelation.CommonData

end

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
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P) (t : ℕ)

theorem localPhaseMarkedLift_base_projection
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (h : ZMod N) (n : ℤ) :
    (D.markedDependentEvaluation t 0).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.localPhaseMarkedLift t x y u c h₀ m h n)) =
      D.dependentQuotientMap.toLinearMap.baseChange ℝ
        (∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
          ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) :=
  (D.markedDependentEvaluation_real_map t 0 _).trans
    (congrArg (D.dependentQuotientMap.toLinearMap.baseChange ℝ)
      (D.localPhaseMarkedLift_eval t x y u c h₀ m hm h n))

theorem commonAffineMarkedLift_phase
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u : Fin t → ℝ) (h n : ℤ) :
    (markedShiftPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t).toLinearMap.baseChange ℝ
        (D.commonAffineMarkedLift t x y u h n) = 0 := by
  simp only [commonAffineMarkedLift, map_sum, LinearMap.map_smul_of_tower, map_add]
  apply Finset.sum_eq_zero
  intro j _
  have hb := realMarkedPolynomialLift_phase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (by omega) (D.realAffineMarkedBase t x y j)
  have hs := realMarkedPolynomialLift_phase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (by omega) (D.realAffineMarkedSlope t y u j)
  apply (congrArg₂ (fun a b : ℝ ⊗[ℚ] RationalTorus.Algebra t =>
    (n : ℚ) ^ (j.val + 1) • (a + (h : ℚ) • b)) hb hs).trans
  simp only [smul_zero, add_zero]

theorem localPhaseMarkedLift_pure
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (h : ZMod N) (n : ℤ) :
    (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n) ∈
      (markedQuotientPolynomialAlgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t).toSubmodule.baseChange ℝ := by
  change _ ∈ (LinearMap.ker (markedQuotientPhase D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t).toLinearMap).baseChange ℝ
  rw [realification_ker, LinearMap.mem_ker]
  apply (markedQuotientPhase_real_map D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t _).trans
  apply (realMarkedAffineShift_phase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t _ _).trans
  exact D.commonAffineMarkedLift_phase t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n

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

def CorrelatedLocalInducedFamily (hs : 2 ≤ s) (Bound : ℝ) : Prop :=
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
                (∃ hCZ : C ≤ Q + Λ + C + 2,
                  D.HasCoveredInducedCorrelationFamily (degree := s - 1)
                    t (E.withLattice Δ l hl hin hout) (T.withLattice Δ l hl hin hout)
                    (V₁.mono hCZ) x y u c h₀ (fun h : {h // h ∈ J} => h.val)
                    A (fun h => A h * K h * U h)
                    (fun h i z => multiplicativeDerivative f h.val z *
                      star (W.mixed.evalCyclic N i (correlationInput h.val z))) Bound) ∧
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

end OAI
end


