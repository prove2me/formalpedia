-- Prove2me | Definitions.Def_OAIE3v2B225
-- name    : OAIE3v2B225
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:39:06.139991+00:00
-- url     : https://prove2.me/theorems/018ca2c6-8f76-4836-ac7f-eed5ddaa845f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 230 of 311
-- statement:
--   Definitions bundle 230 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B202`, `OAIE3v2B204`, `OAIE3v2B205`, `OAIE3v2B206`, `OAIE3v2B207` of this split.
--
--   Modules: `Estimates/AntisymmetricPairVerticalModel.lean`, `Estimates/CoveredQuotientCorrelation.lean`, `Estimates/DiagonalWrapComparison.lean`, `Estimates/MixedPairFrozenEquivalence.lean`, `Estimates/MixedPairPartitionPrecision.lean`, `Estimates/MixedPairStepDrop.lean`, `Estimates/MixedPreciseSampledExchange.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/MixedRootCyclicComparison.lean`, `Estimates/MixedRootLosses.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/NativeMixedReflectionBridge.lean`, `Estimates/NativeRetainedTargetCubeIntervals.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/QuadraticAntisymmetricCorrelation.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/QuarticRootExchange.lean`, `Estimates/TensorSquarePairComparison.lean`, `Estimates/UnitVerticalCyclicDifference.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Geometry/AntisymmetricPairCoordinateTest.lean`, `Geometry/MixedPairCoordinateTest.lean`, `Linear/BinaryLowerRankFamily.lean`, `Linear/LowerRankObservableDifference.lean`, `Linear/MixedPairPartitionKernel.lean`, `Linear/NativeRankFamilyConstruction.lean`, `Nilpotent/MixedPrimitiveNiltest.lean`, `Nilpotent/NativeMixedPairNiltest.lean`, `Polynomial/DegreeRankNativeInverseModels.lean`, `Polynomial/MixedPairPolynomial.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B202
import Definitions.Def_OAIE3v2B204
import Definitions.Def_OAIE3v2B205
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B207

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TensorSquarePairComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_integer_translation_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (a b : Fin 2 → ℤ),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun i x => W.eval i (x + a)) (fun i x => W.eval i (x + b)) := by
  obtain ⟨C, hC, htranslate⟩ :=
    UnitVerticalObservable.exists_integer_translation_equivalence_budget 1
  refine ⟨C, hC, ?_⟩
  intro p W a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have htop : W.multi.realSubgroup (mixedCorrelationDegree 1) =
      W.model.filtration.realification.subgroup 2 := by
    have hsum : (∑ i, mixedCorrelationDegree 1 i) = 2 := by decide
    simpa only [hsum] using W.multi.realSubgroup_top
  let V : W.model.UnitVerticalObservable (W.model.filtration.realification.subgroup 2)
      (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (htop.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (htop.symm ▸ hz) hL }
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model V (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hdim a b
  refine ⟨E.left_dimension, E.right_dimension, ?_⟩
  intro i j
  obtain ⟨F⟩ := E.expansion i j
  have heq (k : Fin W.outputDim) (x : Fin 2 → ℤ) :
      V.observable k (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
        (fun _ : Fin 2 => 1) x (W.multi.orbitToOrdinary W.orbit))) = W.eval k x := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  have hf : (fun x => V.observable i (QuotientGroup.mk
      (W.model.filtration.realification.polynomialOrbitEval (fun _ : Fin 2 => 1)
        (x + a) (W.multi.orbitToOrdinary W.orbit))) *
      star (V.observable j (QuotientGroup.mk
        (W.model.filtration.realification.polynomialOrbitEval (fun _ : Fin 2 => 1)
          (x + b) (W.multi.orbitToOrdinary W.orbit))))) =
      (fun x => W.eval i (x + a) * star (W.eval j (x + b))) := by
    funext x
    rw [heq, heq]
  exact ⟨hf ▸ F⟩

theorem exists_half_dilation_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (W.rationalDilation (1 / 2)).eval (fun j x => W.eval j (fun i => x i / 2)) := by
  obtain ⟨A, _, hshift⟩ := exists_quadratic_integer_translation_equivalence
  obtain ⟨B, _, hparity⟩ := exists_pairParityIndicator_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + Polynomial.C B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C D) ^ D + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let V := W.rationalDilation (1 / 2)
  let t : ℝ := (p + A) ^ A + B + p + 2
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hat : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hbt : (B : ℝ) ≤ t := by dsimp [t]; linarith
  have hbound : (t + D) ^ D + t + 2 ≤ (p + C) ^ C := by
    simpa [T, t, X, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (t + D) ^ D := by positivity
  have hpc : p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpc)
  refine ⟨hdim, hdim, ?_⟩
  intro i j
  let F (r : Fin 2 → ZMod 2) (x : Fin 2 → ℤ) :=
    V.eval i x * star (V.eval j (fun k => x k - ((r k).val : ℤ)))
  have hF (r : Fin 2 → ZMod 2) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t (F r)) := by
    obtain ⟨E⟩ := (hshift V 0 (fun k => -((r k).val : ℤ))).expansion i j
    have heq : (fun x => V.eval i (x + 0) * star (V.eval j (x + fun k => -((r k).val : ℤ)))) = F r := by
      funext x
      simp only [F, add_zero, sub_eq_add_neg]
      rfl
    rw [heq] at E
    exact ⟨E.mono hat⟩
  have hterm (r : Fin 2 → ZMod 2) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((t + D) ^ D) (fun x => pairParityIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hparity r)).mono hbt) (Classical.choice (hF r))
  have hc : (Fintype.card (Fin 2 → ZMod 2) : ℝ) ≤ Real.exp 2 := by
    norm_num only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hh := Real.add_one_le_exp (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hcost : (∑ _ : Fin 2 → ZMod 2, ‖(1 : ℂ)‖) ≤ Real.exp 2 := by simpa using hc
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hterm r)) (fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 2) hc hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod 2, (1 : ℂ) * (pairParityIndicator r x * F r x)) =
      (fun x => V.eval i x * star (W.eval j (fun k => x k / 2))) := by
    funext x
    let r : Fin 2 → ZMod 2 := fun k => (x k : ZMod 2)
    rw [Finset.sum_eq_single r]
    · simp only [pairParityIndicator, r, ite_true, one_mul, F]
      rw [show V.eval j (fun k => x k - ((x k : ZMod 2).val : ℤ)) =
        W.eval j (fun k => x k / 2) from W.half_dilation_integer_representative x j]
    · intro a _ ha
      have hne : (fun k => (x k : ZMod 2)) ≠ a := fun h => ha h.symm
      simp only [pairParityIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  rw [heq] at S
  exact ⟨S.mono (by linarith)⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem exists_halfDilationExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
        (W.halfDilationExchangeCorrection G a b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_half_dilation_equivalence
  obtain ⟨B, _, hhalf⟩ := NativeIntegerExpansion.exists_halving_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B + X + 2
  let U := (T + Polynomial.C D) ^ D + T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((U + Polynomial.C D) ^ D + 2 * T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + (v + B) ^ B + v + 2
  let u := (t + D) ^ D + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpt : p ≤ t := by
    have hA : 0 ≤ (v + A) ^ A := by positivity
    have hB : 0 ≤ (v + B) ^ B := by positivity
    dsimp [t, v]
    dsimp [v] at hA hB
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    have hB : 0 ≤ (v + B) ^ B := by positivity
    linarith
  have hBt : (q + B) ^ B ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show q + B ≤ v + B by dsimp [v]; linarith) B).trans
    dsimp [t]
    have hA : 0 ≤ (v + A) ^ A := by positivity
    linarith
  have htu : t ≤ u := by
    have hh : 0 ≤ (t + D) ^ D := by positivity
    dsimp [u]
    linarith
  have hprod : (t + D) ^ D ≤ u := by dsimp [u]; linarith
  have hbound : (u + D) ^ D + (2 * t + 2) ≤ (p + q + C) ^ C := by
    simpa [T, U, X, t, u, v, Polynomial.eval₂_pow, add_assoc] using hbudget v hv
  let V := W.rationalDilation (1 / 2)
  let Amap : Fin 2 → ((Fin 2 → ℤ) →+ ℤ) :=
    fun k => { toFun := fun x => x k.rev, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hterm (ij : Fin W.outputDim × Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((u + D) ^ D)
        (fun x => (star (V.eval a x * star (W.eval ij.1 (fun k => x k / 2))) *
          (V.eval b (fun k => x k.rev) * star (W.eval ij.2 (fun k => x k.rev / 2)))) *
          G ij.1 ij.2 (fun k => x k / 2))) := by
    obtain ⟨E⟩ := (hcompare W).expansion a ij.1
    obtain ⟨F⟩ := (hcompare W).expansion b ij.2
    obtain ⟨H⟩ := hhalf hq (Classical.choice (hG ij.1 ij.2))
    obtain ⟨K⟩ := hmul ht (E.conjugate.mono hAt) ((F.linearPullbackHom Amap).mono hAt)
    exact hmul hu (K.mono hprod) (H.mono (hBt.trans htu))
  have hc : (Fintype.card (Fin W.outputDim × Fin W.outputDim) : ℝ) ≤ Real.exp (2 * t + 2) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul W.output_bound W.output_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcost : (∑ _ : Fin W.outputDim × Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp (2 * t + 2) := by
    simpa using hc
  let S := NativeIntegerExpansion.weightedSum (fun ij => Classical.choice (hterm ij)) (fun _ => 1)
    (by linarith : 0 ≤ 2 * t + 2) hc hcost
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => W.halfDilationExchangeCorrection G a b x)
  simpa only [one_mul, halfDilationExchangeCorrection, V] using S.mono hbound

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem exists_explicit_half_root_exchange_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G i j))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
        ((W.rationalDilation (1 / 2)).tensorSquareExchangeCorrection
          (W.halfDilationExchangeCorrection G) a b)) := by
  obtain ⟨A, _, hhalf⟩ := exists_halfDilationExchangeCorrection_expansion
  obtain ⟨B, _, hsquare⟩ := exists_tensorSquareExchangeCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hsquare (W.rationalDilation (1 / 2)) (by positivity : 0 ≤ (p + q + A) ^ A)
    (W.halfDilationExchangeCorrection G) (hhalf W hq G hG) a b
  have hbound : ((p + q + A) ^ A + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalWrapComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem exists_diagonalWrapCoefficient_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ)
      (j k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (W.diagonalWrapCoefficient N j k)) := by
  obtain ⟨C, hC, htranslate⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_integer_translation_equivalence_budget 1
  refine ⟨C, hC, ?_⟩
  intro p W N j k
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have htop : W.multi.realSubgroup (mixedCorrelationDegree 1) =
      W.model.filtration.realification.subgroup 2 := by
    have hsum : (∑ i, mixedCorrelationDegree 1 i) = 2 := by decide
    simpa only [hsum] using W.multi.realSubgroup_top
  let V : W.model.UnitVerticalObservable (W.model.filtration.realification.subgroup 2)
      (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (htop.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (htop.symm ▸ hz) hL }
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model V (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hdim
    0 (fun _ => -(N : ℤ))
  let A : Fin 2 → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1 + x 0, map_zero' := by simp,
      map_add' := fun x y => by simp only [Pi.add_apply]; ring }
  obtain ⟨F⟩ := E.expansion k j
  have H := F.linearPullbackHom A
  have heval (i : Fin W.outputDim) (x : Fin 2 → ℤ) (c : ℤ) :
      V.observable i (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
        (fun _ : Fin 2 => 1) ((fun l => A l x) + fun _ => c) (W.multi.orbitToOrdinary W.orbit))) =
      W.eval i (fun _ => x 1 + x 0 + c) := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  have heq : (W.diagonalWrapCoefficient N j k) =
      (fun x => V.observable k (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
          (fun _ : Fin 2 => 1) ((fun l => A l x) + 0) (W.multi.orbitToOrdinary W.orbit))) *
        star (V.observable j (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
          (fun _ : Fin 2 => 1) ((fun l => A l x) + fun _ => -(N : ℤ))
          (W.multi.orbitToOrdinary W.orbit))))) := by
    funext x
    rw [show (0 : Fin 2 → ℤ) = (fun _ => 0) from rfl, heval, heval]
    simp only [diagonalWrapCoefficient, add_zero, sub_eq_add_neg]
  exact ⟨heq.symm ▸ H⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem exists_cyclicDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ F : (Fin W.outputDim × Fin W.outputDim) →
          (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (F a b))) →
        ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + e + C) ^ C) (W.cyclicDiagonalCorrection N δ F a b)) := by
  obtain ⟨A, _, hwrap⟩ := exists_diagonalWrapCoefficient_expansion
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + 6
  let T := (R + Polynomial.C B) ^ B + X + R + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv F hF a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  let r := (v + A) ^ A + v + 6
  let t := (r + B) ^ B + v + r + 2
  let d := (t + B) ^ B + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have har : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; linarith
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have her : e + 4 ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have hrt : r ≤ t := by
    have : 0 ≤ (r + B) ^ B := by positivity
    dsimp [t]
    linarith
  have hwt : (r + B) ^ B + p ≤ t := by dsimp [t, v]; linarith
  have htd : t ≤ d := le_add_of_nonneg_left (by positivity)
  have hpd : (t + B) ^ B ≤ d := le_add_of_nonneg_right ht
  have hcost : d + 2 ≤ (p + q + e + C) ^ C := by
    simpa [X, R, T, r, t, d, v, Polynomial.eval₂_pow] using hbudget v hv
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _k : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterms (k : Fin W.outputDim) := hmul hr
    ((Classical.choice (hwrap W N a.2 k)).mono har) ((Classical.choice (hF (a.1, k) b)).mono hqr)
  have EW : NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t
      (W.wrappedDiagonalCorrection N F a b) := by
    have E := (NativeIntegerExpansion.weightedSum (fun k => Classical.choice (hterms k))
      (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hwt
    change NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t
      (fun x => ∑ k, W.diagonalWrapCoefficient N a.2 k x * F (a.1, k) b x)
    simpa only [one_mul] using E
  let w := fun x => (smoothCyclicCarry N δ x : ℂ)
  have EC := (Classical.choice (exists_smoothCyclicCarry_expansion N δ hδ he hinv)).mono (her.trans hrt)
  have E₀ := (Classical.choice (hF a b)).mono (hqr.trans (hrt.trans htd))
  have E₁ := (Classical.choice (hmul ht EC EW)).mono hpd
  have E₂ := (Classical.choice (hmul ht EC ((Classical.choice (hF a b)).mono (hqr.trans hrt)))).mono hpd
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![F a b,
    (fun x => w x * W.wrappedDiagonalCorrection N F a b x), (fun x => w x * F a b x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 d (fs j)) := by
    fin_cases j
    · exact ⟨E₀⟩
    · exact ⟨E₁⟩
    · exact ⟨E₂⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono hcost
  have heq : (fun x => ∑ j, cs j * fs j x) = W.cyclicDiagonalCorrection N δ F a b := by
    funext x
    simp [cs, fs, Fin.sum_univ_succ, w, cyclicDiagonalCorrection]
    ring
  exact ⟨heq ▸ E⟩

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BinaryLowerRankFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

universe u v t

theorem uniform_lower_rank_family {L : Type u} {I : Type v} {σ : Type t}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (R : D.DegreeRankStructure (r + 1)) {p : ℝ}
    (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
    (w : σ → ℕ) (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    (hzero : ∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = 0) :
    let C := (exists_lower_rank_family.{u, v, t} s).choose
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
        ∃ U : Q.DegreeRankStructure r,
          ∃ hQF : Q.filtration = D.filtration.quotientLie
              (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal,
            U.filtration = R.filtration.quotientRank r
              (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
            Q.lattice = D.lattice.map (D.filtration.quotientStepHom
              (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal) ∧
            U.ComplexityLE ((p + C) ^ C) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
               IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 Q.basis
             ∃ S : I → Q.Niltest w,
               (∀ i, (S i).normBound = 1) ∧
               (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
               (∀ y : Q.Space, ∑ i, ‖(S i).observable y‖ ^ 2 = 1) ∧
               (∀ i x, (S i).observable (QuotientGroup.mk
                 (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                   (hM := Q.filtration.lowerCentralSeries_eq_bot)
                   (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
                 V.observable i (QuotientGroup.mk x)) ∧
               ∀ (g : D.filtration.realification.PolynomialOrbit w) i x,
                 ((S i).withOrbit (R.rankQuotientOrbit Q hQF g)).eval x =
                   V.observable i
                     (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g))) := by
  dsimp only
  obtain ⟨n, hn, Q, U, hQF, hUF, hQL, hUc, hS⟩ :=
    (exists_lower_rank_family.{u, v, t} s).choose_spec.2 D R V
      (1 : D.filtration.realification.PolynomialOrbit w) hp hR hzero
  refine ⟨n, hn, Q, U, hQF, hUF, hQL, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨S, _, hSn, hSc, hSu, hSp, _⟩ := hS
  refine ⟨S, hSn, hSc, hSu, hSp, ?_⟩
  intro g i x
  rw [Niltest.withOrbit_eval, R.rankQuotientOrbit_eval Q hQF]
  exact hSp i _

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

universe u v t

theorem UnitVerticalObservable.hasUniformLowerRankUnitFamily
    {L : Type u} {I : Type v} {σ : Type t}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (R : D.DegreeRankStructure (r + 1)) {p : ℝ}
    (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
    (w : σ → ℕ) (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    (hzero : ∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = 0) :
    let C := (UnitVerticalObservable.exists_lower_rank_family.{u, v, t} s).choose
    D.HasUniformLowerRankUnitFamily R V.observable w ((p + C) ^ C) := by
  obtain ⟨n, hn, Q, U, hQF, _, _, hUc, hK⟩ :=
    UnitVerticalObservable.uniform_lower_rank_family D R V w hp hR hzero
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, _, hKe⟩ := hK
  refine ⟨K, hKn, hKc, hKu, R.rankQuotientOrbit Q hQF, ?_, hKe⟩
  intro g hg
  rw [R.rankQuotientOrbit_eval Q hQF, hg]
  exact map_one _

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem HasUniformLowerRankUnitFamily.realizeFamily {L I σ τ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {v : I → D.Space → ℂ} {w : σ → ℕ} {p : ℝ}
    (h : D.HasUniformLowerRankUnitFamily R v w p)
    (f : τ → I → (σ → ℤ) → ℂ)
    (hf : ∀ t, ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.filtration.realification.polynomialOrbitEval w 0 g = 1 ∧
      ∀ i x, v i (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval w x g)) = f t i x) :
    D.HasLowerRankOrbitFamily R w f p := by
  classical
  choose b hb0 hb using hf
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, hKe⟩ := hK
  exact ⟨K, hKn, hKc, hKu, (fun t => a (b t)),
    (fun t => ha0 (b t) (hb0 t)),
    fun t i x => (hKe (b t) i x).trans (hb t i x)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LowerRankObservableDifference
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

namespace UnitVerticalObservable

universe u v w t

theorem exists_uniform_lower_rank_difference_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type u} {I : Type v} {J : Type w} {σ : Type t}
      [LieRing L] [LieAlgebra ℚ L]
      [Fintype I] [Fintype J]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {r d : ℕ} (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure (r + 1)) {p : ℝ}
      (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
      (U : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) J p),
      0 ≤ p → R.ComplexityLE p →
      (∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = U.frequency x) →
      ∀ w : σ → ℕ,
        HasUniformLowerRankUnitFamily D R (V.differenceObservable U) w ((p + C) ^ C) := by
  let a := (exists_lower_rank_family.{u, max v w, t} s).choose
  let P : Polynomial ℕ := (Polynomial.X + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L I J σ _ _ _ _ _ _ _ _ r d D R p V U hp hR hfreq w
  have hb : (p + 2 + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have h := hasUniformLowerRankUnitFamily D R (rankDifference R V U hfreq) w
    (by linarith) (hR.mono R (by linarith)) (fun _ _ => rfl)
  exact h.mono hb

end UnitVerticalObservable
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredQuotientCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {L M I J : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [Fintype I] [Fintype J] {s t d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {D : RationalFilteredNilmanifold L s d} {E : RationalFilteredNilmanifold M t e}
  {T : Subgroup D.RealGroup} {S : Subgroup E.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p) (U : E.UnitVerticalObservable S J p)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
    (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))

theorem exists_uniform_lower_rank_map_difference (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M I J σ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] [Fintype I] [Fintype J]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {r d e : ℕ} (D : RationalFilteredNilmanifold L s d)
      (E : RationalFilteredNilmanifold M s e)
      (R : D.DegreeRankStructure (r + 1)) (S : E.DegreeRankStructure (r + 1))
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : D.lattice ≤ E.lattice.comap (mapOfSteps
        (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
      {p : ℝ} (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
      (U : E.UnitVerticalObservable (S.realSubgroup s (r + 1)) J p),
      0 ≤ p → R.ComplexityLE p → S.ComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (∀ x ∈ R.filtration.layer s (r + 1), φ x ∈ S.filtration.layer s (r + 1)) →
      (∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = U.frequency (φ x)) →
      ∀ w : σ → ℕ,
        HasUniformLowerRankUnitFamily D R (mapDifferenceObservable V U φ hφ) w ((p + C) ^ C) := by
  obtain ⟨a, _, hdescent⟩ := UnitVerticalObservable.exists_uniform_lower_rank_difference_family s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + (X + 3) ^ 2 + (X + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L M I J σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r d e D E R S φ hφ p V U hp hR hS hentries htop hfreq w
  let q := p + (p + 3) ^ 2 + (p + 2) ^ 4
  have hpq : p ≤ q := by
    dsimp only [q]
    linarith [sq_nonneg (p + 3), show 0 ≤ (p + 2) ^ 4 from by positivity]
  have hq : 0 ≤ q := hp.trans hpq
  have hb : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hreal : R.realSubgroup s (r + 1) ≤ (S.realSubgroup s (r + 1)).comap
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
    intro z hz
    change realificationLieHom φ z.coord ∈ (S.filtration.layer s (r + 1)).baseChange ℝ
    have hmap : (R.filtration.layer s (r + 1)).map φ.toLinearMap ≤
        S.filtration.layer s (r + 1) := by
      rintro y ⟨x, hx, rfl⟩
      exact htop x hx
    have h := Submodule.baseChange_mono ℝ hmap
    rw [realification_map] at h
    exact h ⟨z.coord, hz, rfl⟩
  let U' := U.controlledPullback φ hφ (R.realSubgroup s (r + 1)) hreal hp hR.1 hS.1 hentries
  have heq : ∀ x ∈ R.filtration.layer s (r + 1), (V.mono hpq).frequency x = U'.frequency x := hfreq
  have h := hdescent D R (V.mono hpq) U' hq (hR.mono R hpq) heq w
  exact h.mono hb

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

noncomputable def NativeVerticalDerivativeData.mono {s N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {B : NativeCommonDerivativeModels s N p f}
    (V : NativeVerticalDerivativeData B) (hpq : p ≤ q) :
    NativeVerticalDerivativeData (B.mono hpq) where
  normalized := V.normalized
  frequency := V.frequency
  height i := (V.height i).trans hpq
  vertical := V.vertical
  integral := V.integral

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticAntisymmetricCorrelation
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_reflected_factor_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z : ℤ),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (correlationInput (x 0) (z - x 0 - x 1)))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (correlationInput (x 0) (z - x 0)) *
            star (W.eval k.2 (correlationInput (x 0) (x 1)))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence (mixedCorrelationDegree 1)
  refine ⟨C, hC, ?_⟩
  intro p W z
  let A : Option (Fin 2) → Fin 2 → ℤ := fun j => match j with
    | none => ![0, 1]
    | some i => if i = 0 then ![1, 0] else ![-1, -1]
  let b : Option (Fin 2) → ℤ := fun j => match j with
    | none => 0
    | some i => if i = 0 then 0 else z
  have hinput (x : Fin 2 → ℤ) : integerAffineMap A b x =
      coordinatePairInput (1 : Fin 2) (z - x 0 - x 1) (x 1) (x 0) := by
    funext j
    cases j with
    | none => simp [integerAffineMap, A, b, coordinatePairInput, Fin.sum_univ_two]
    | some i =>
      fin_cases i
      · simp [integerAffineMap, A, b, coordinatePairInput, coordinateConstantInput,
          Fin.sum_univ_two]
      · simp [integerAffineMap, A, b, coordinatePairInput, coordinateConstantInput,
          Fin.sum_univ_two]
        ring
  have hcoordinate (a n : ℤ) : coordinateConstantInput (1 : Fin 2) a n =
      correlationInput n a := by
    funext i
    fin_cases i <;> rfl
  have hdegree : (∑ i, mixedCorrelationDegree 1 i) - 1 = 1 := by
    rw [Fin.sum_univ_two]
    rfl
  have E := (hadd W (1 : Fin 2) rfl).affinePullback A b
  have E' : NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
      (fun k (x : Fin 2 → ℤ) => W.eval k (correlationInput (x 0) (z - x 0)))
      (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval k.1 (correlationInput (x 0) (z - x 0 - x 1)) *
          W.eval k.2 (correlationInput (x 0) (x 1))) := by
    simpa only [hdegree, coordinateSumVector, coordinateTensorVector, hinput,
      coordinatePairInput_sum, coordinatePairInput_left, coordinatePairInput_right,
      sub_add_cancel, hcoordinate] using E
  refine ⟨E'.left_dimension, E'.right_dimension, ?_⟩
  intro i k
  obtain ⟨R⟩ := E'.symm.expansion (i, k.2) k.1
  have heq : (fun x : Fin 2 → ℤ =>
      (W.eval i (correlationInput (x 0) (z - x 0 - x 1)) *
        W.eval k.2 (correlationInput (x 0) (x 1))) *
          star (W.eval k.1 (correlationInput (x 0) (z - x 0)))) =
      (fun x => W.eval i (correlationInput (x 0) (z - x 0 - x 1)) *
        star (W.eval k.1 (correlationInput (x 0) (z - x 0)) *
          star (W.eval k.2 (correlationInput (x 0) (x 1))))) := by
    funext x
    simp only [star_mul, star_star]
    ring
  exact ⟨heq ▸ R⟩

theorem exists_reflected_pair_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z : ℤ),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x : Fin 2 → ℤ =>
          W.eval k.1 (correlationInput (x 0) (z - x 0 - x 1)) *
            star (W.eval k.2 (correlationInput (x 1) (z - x 0 - x 1))))
        (fun k : (Fin W.outputDim × Fin W.outputDim) ×
            (Fin W.outputDim × Fin W.outputDim) => fun x =>
          W.eval k.1.1 (correlationInput (x 0) (z - x 0)) *
            star (W.eval k.2.1 (correlationInput (x 1) (z - x 1))) *
            star (W.eval k.1.2 (correlationInput (x 0) (x 1))) *
            W.eval k.2.2 (correlationInput (x 1) (x 0))) := by
  obtain ⟨a, _, hfactor⟩ := exists_reflected_factor_equivalence
  obtain ⟨b, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W z
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have E := hfactor W z
  have F := (E.coordinatePullback (![1, 0] : Fin 2 → Fin 2)).conjugate
  have R := htensor hq E F
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hsub (x : Fin 2 → ℤ) : z - x 1 - x 0 = z - x 0 - x 1 := by abel
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hsub, star_mul, star_star,
    mul_assoc, mul_comm, mul_left_comm] using R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

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

theorem pairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.pairComparisonTests a b k).ComplexityLE (antisymmetricPairBudget p q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
      (V.antisymmetricPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact V.antisymmetricPairTests_complexity (some 0)
    · exact V.antisymmetricPairTests_complexity (some 1)

end NativeSampleCorrelation

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

theorem pairCoordinateTests_complexity (k : Fin 2) (out : Fin W.outputDim) (l : Option (Fin 2)) :
    (V.pairCoordinateTests k out l).ComplexityLE (antisymmetricPairBudget p q) := by
  have htwo : 2 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (2 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  cases l with
  | none => exact Niltest.oneOnOrbit_complexity _ htwo (V.antisymmetricPairTests_complexity none).1
  | some l =>
    fin_cases k <;> fin_cases l
    · exact V.antisymmetricPairTests_complexity (some 0)
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.antisymmetricPairTests_complexity (some 1)).1
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.antisymmetricPairTests_complexity (some 0)).1
    · exact V.antisymmetricPairTests_complexity (some 1)

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

noncomputable def pairCoordinateNiltest (k : Fin 2) (out : Fin W.outputDim) :
    (pi V.antisymmetricPairModels).Niltest (fun _ : Fin 2 => 1) :=
  piNiltest V.antisymmetricPairModels (V.pairCoordinateTests k out)
    ((by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
    (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
    (V.pairCoordinateTests_complexity k out)

theorem pairCoordinateNiltest_complexity (k : Fin 2) (out : Fin W.outputDim) :
    (V.pairCoordinateNiltest k out).ComplexityLE
      (productNiltestBudget (antisymmetricPairBudget p q)) :=
  piNiltest_complexity V.antisymmetricPairModels (V.pairCoordinateTests k out) _ _ _

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPairVerticalModel
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

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

theorem pairFrozenEquivalence_at {b : ℝ} (h : R.HasPairFrozenReduction b)
    (x : Fin 2 → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ (N : ℝ)) :
    NativeIntegerVectorEquivalence 1 b
      (R.pairFrozenVector 0 (R.slowValue x) (R.rationalValue x))
      (R.pairFrozenVector 1 (R.slowValue x) (R.rationalValue x)) := by
  obtain ⟨u, _hu, _hub, ⟨m, hm, hmb, hrat, hslow⟩, hequiv⟩ := h
  exact hequiv m hm hmb (R.slowValue x) (R.rationalValue x) (hslow x hx) (hrat x)

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuarticRootExchange
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped BigOperators

theorem exists_sampled_rational_division_equivalence (d s : ℕ) [NeZero d] (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] (bound : σ → ℕ),
      (∑ k, bound k) = s + 1 → ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter bound p) (ρ : σ → Fin 2),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) => (W.rationalDilation ((d : ℚ)⁻¹)).eval j (fun k => x (ρ k)))
        (fun j x => W.eval j (fun k => x (ρ k) / (d : ℤ))) := by
  obtain ⟨A, _, hshift⟩ := exists_multidegree_integer_translation s
  obtain ⟨B, _, hresidue⟩ := exists_pairResidueIndicator_expansion d s hs
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + Polynomial.C B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C D) ^ D + T + Polynomial.C (d ^ 2))
  refine ⟨C, hC, ?_⟩
  intro σ _ bound hdegree p W ρ
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let V := W.rationalDilation ((d : ℚ)⁻¹)
  let t : ℝ := (p + A) ^ A + B + p + 2
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hat : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hbt : (B : ℝ) ≤ t := by dsimp [t]; linarith
  have hbound : (t + D) ^ D + t + (d : ℝ) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (t + D) ^ D := by positivity
  have hpc : p ≤ (p + C) ^ C := by
    have hpt : p ≤ t := by dsimp [t]; linarith
    linarith [sq_nonneg (d : ℝ)]
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpc)
  refine ⟨hdim, hdim, ?_⟩
  intro i j
  let inp (x : Fin 2 → ℤ) : σ → ℤ := fun k => x (ρ k)
  have hinput (x : Fin 2 → ℤ) : (fun k => x (ρ k)) = inp x := rfl
  let F (r : Fin 2 → ZMod d) (x : Fin 2 → ℤ) :=
    V.eval i (inp x) * star (V.eval j (inp (fun k => x k - ((r k).val : ℤ))))
  have hF (r : Fin 2 → ZMod d) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s t (F r)) := by
    obtain ⟨E⟩ := ((hshift bound hdegree V 0 (fun k => -((r (ρ k)).val : ℤ))).coordinatePullback ρ).expansion i j
    have hr (x : Fin 2 → ℤ) :
        (fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ)) =
          inp (fun k => x k - ((r k).val : ℤ)) := by
      calc
        _ = (fun k => x (ρ k) - ((r (ρ k)).val : ℤ)) := by
          funext k
          simp only [Pi.add_apply, sub_eq_add_neg]
        _ = _ := hinput (fun k => x k - ((r k).val : ℤ))
    have heq : (fun x : Fin 2 → ℤ => V.eval i ((fun k => x (ρ k)) + 0) *
        star (V.eval j ((fun k => x (ρ k)) + (fun k => -((r (ρ k)).val : ℤ))))) = F r := by
      funext x
      rw [add_zero, hr, hinput]
    exact ⟨heq ▸ E.mono hat⟩
  have hterm (r : Fin 2 → ZMod d) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s
      ((t + D) ^ D) (fun x => pairResidueIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hbt) (Classical.choice (hF r))
  have hcoeff : (∑ _ : Fin 2 → ZMod d, ‖(1 : ℂ)‖) ≤ Real.exp ((d : ℝ) ^ 2) := by
    simpa using card_pairResidue_le_exp d
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hterm r)) (fun _ => 1)
    (sq_nonneg (d : ℝ)) (card_pairResidue_le_exp d) hcoeff
  have hrep (x : Fin 2 → ℤ) :
      V.eval j (inp (fun k => x k - ((x k : ZMod d).val : ℤ))) =
        W.eval j (inp (fun k => x k / (d : ℤ))) := by
    exact division_dilation_integer_representative d W (inp x) j
  have heq : (fun x => ∑ r : Fin 2 → ZMod d, (1 : ℂ) * (pairResidueIndicator r x * F r x)) =
      (fun x => V.eval i (inp x) * star (W.eval j (inp (fun k => x k / (d : ℤ))))) := by
    funext x
    let r : Fin 2 → ZMod d := fun k => (x k : ZMod d)
    rw [Finset.sum_eq_single r]
    · simp only [pairResidueIndicator, r, ite_true, one_mul, F, hrep]
    · intro z _ hz
      have hne : (fun k => (x k : ZMod d)) ≠ z := fun h => hz h.symm
      simp only [pairResidueIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  rw [heq] at S
  exact ⟨S.mono (by linarith)⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_reflected_factor_equivalence (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p) (c : ℤ),
      NativeIntegerVectorEquivalence (n + 1) ((p + C) ^ C)
        (fun i (x : Fin (n + 2) → ℤ) => W.eval i
          (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)))
        (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval a.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
            star (W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ)))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence
    (fun _ : MixedReplicatedIndex (n + 1) => 1)
  refine ⟨C, hC, ?_⟩
  intro p W c
  have hdegree : (∑ _ : MixedReplicatedIndex (n + 1), 1) - 1 = n + 1 := by
    have hc : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 := replicatedMixed_card (n + 1)
    simp only [Finset.sum_const, Finset.card_univ, hc, smul_eq_mul, mul_one]
    omega
  have E := (hadd W (mixedReplica 0) rfl).affinePullbackHom
    (mixedReflectionLinear n) (mixedReflectionOffset n c)
  have hinput (x : Fin (n + 2) → ℤ) :
      (fun j => mixedReflectionOffset n c j + mixedReflectionLinear n j x) =
        mixedReflectionAffineInput n c x := rfl
  have E' : NativeIntegerVectorEquivalence (n + 1) ((p + C) ^ C)
      (fun i (x : Fin (n + 2) → ℤ) => W.eval i
        (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)))
      (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval a.1 (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
          W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))) := by
    simpa only [hdegree, coordinateSumVector, coordinateTensorVector,
      hinput, mixedReflectionInput_sum,
      mixedReflectionInput_left, mixedReflectionInput_right] using E
  refine ⟨E'.left_dimension, E'.right_dimension, ?_⟩
  intro i a
  obtain ⟨R⟩ := E'.symm.expansion (i, a.2) a.1
  have heq :
      (fun x : Fin (n + 2) → ℤ =>
        (W.eval i (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
          W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))) *
            star (W.eval a.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)))) =
      (fun x => W.eval i (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
        star (W.eval a.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
          star (W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))))) := by
    funext x
    simp only [star_mul, star_star]
    ring
  exact ⟨heq ▸ R⟩

theorem exists_mixed_reflected_pair_equivalence (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p) (c : ℤ),
      NativeIntegerVectorEquivalence (n + 1) ((p + C) ^ C)
        (W.mixedReflectionSource c) (W.mixedReflectionTarget c) := by
  obtain ⟨a, _, hfactor⟩ := exists_mixed_reflected_factor_equivalence n
  obtain ⟨b, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have E := hfactor W c
  have F := (E.coordinatePullback (mixedExchangeCoordinate n)).conjugate
  have R := htensor hq E F
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have h0 : mixedExchangeCoordinate n 0 = 1 := rfl
  have h1 : mixedExchangeCoordinate n 1 = 0 := rfl
  have ht (i : Fin n) : mixedExchangeCoordinate n i.succ.succ = i.succ.succ := rfl
  have hsub (x : Fin (n + 2) → ℤ) : c - x 1 - x 0 = c - x 0 - x 1 := by abel
  unfold mixedReflectionSource mixedReflectionTarget
  simpa only [h0, h1, ht, hsub, star_mul, star_star, mul_assoc, mul_comm, mul_left_comm]
    using R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem exists_mixedDiagonalWrapCoefficient_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p) (N : ℕ)
      (j k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + C) ^ C)
        (W.mixedDiagonalWrapCoefficient N j k)) := by
  obtain ⟨C, hC, htranslate⟩ := exists_multidegree_integer_translation (s + 2)
  refine ⟨C, hC, ?_⟩
  intro p W N j k
  let A : MixedReplicatedIndex (s + 2) → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1 + x 0, map_zero' := by simp,
      map_add' := fun x y => by simp only [Pi.add_apply]; ring }
  obtain ⟨F⟩ := (htranslate (fun _ : MixedReplicatedIndex (s + 2) => 1) (mixedReplicated_totalDegree (s + 1)) W 0 (fun _ => -(N : ℤ))).expansion k j
  have H := F.linearPullbackHom A
  have heq : (fun x : Fin 2 → ℤ => W.eval k ((fun l => A l x) + 0) *
      star (W.eval j ((fun l => A l x) + fun _ => -(N : ℤ)))) =
      W.mixedDiagonalWrapCoefficient N j k := by
    funext x
    simp only [add_zero, mixedDiagonalWrapCoefficient, sub_eq_add_neg]
    rfl
  exact ⟨heq ▸ H⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_rational_division_equivalence (d D : ℕ) [NeZero D] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)
      (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) =>
          (W.rationalDilation ((D : ℚ)⁻¹)).eval j (mixedSampledInput π x))
        (fun j x => W.eval j (mixedSampledInput π (fun k => x k / (D : ℤ)))) := by
  obtain ⟨C, hC, h⟩ := exists_sampled_rational_division_equivalence D (d + 2) (by omega)
  refine ⟨C, hC, ?_⟩
  intro p W π
  simpa only [← mixedSampledInput_coordinates] using
    h (fun _ : MixedReplicatedIndex (d + 2) => 1) (mixedReplicated_totalDegree (d + 1)) W
      (fun j => π (mixedInputCoordinate (d + 1) j))

end Erdos3.NativeMultidegreeNilcharacter

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

theorem mixedPairTests_complexity (k : Option (Fin 2)) :
    (V.mixedPairTests k).ComplexityLE (mixedPairBudget p q) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have hr : 0 ≤ raisedNiltestBudget (p + q) := hpq.trans (le_raisedNiltestBudget _)
  cases k with
  | none =>
    exact (V.test.raiseStep_complexity (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1) hpq
      (V.complexity.mono (le_add_of_nonneg_left hp))).mono
        (by unfold mixedPairBudget; linarith)
  | some k =>
    have hcost : p + 4 ≤ mixedPairBudget p q := by
      unfold mixedPairBudget
      linarith
    fin_cases k
    · exact (W.mixedPairComponent_complexity i id).mono hcost
    · exact (W.mixedPairComponent_complexity j (mixedExchangeCoordinate n)).mono hcost

end NativeSampleCorrelation
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

noncomputable def mixedPairNiltest : (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels V.mixedPairTests
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    V.mixedPairTests_complexity

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairStepDrop
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

structure NativeMixedPairFactorization {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
    {i j : Fin W.outputDim}
    (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
      Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))) (r : ℝ) where
  [topology : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  basis : Basis (Fin (finrank ℚ V.MixedPairAlgebra)) ℚ V.MixedPairAlgebra
  weight : Fin (finrank ℚ V.MixedPairAlgebra) → ℕ
  adapted : ∀ k, (pi V.mixedPairModels).filtration.layer k =
    Submodule.span ℚ (basis '' {l | k ≤ weight l})
  height : ∀ a b, rationalLogHeight ((pi V.mixedPairModels).basis.repr (basis a) b) ≤ r
  factorization : (pi V.mixedPairModels).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency V.mixedPairFrequencies) (fun _ : Fin (n + 2) => (N : ℝ))
    (V.mixedPairNiltest.symbol basis weight adapted) r

end Erdos3

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

theorem mixedPairPolynomial_eq_test : V.mixedPairPolynomial =
    ⟨⟨V.mixedPairNiltest.orbit.log, V.mixedPairNiltest.orbit.property⟩⟩ := rfl

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

theorem mixedOriginalPairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.mixedOriginalPairComparisonTests a b k).ComplexityLE (mixedPairBudget (tensorPowerBudget m p) q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
      (V.mixedPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact (W.mixedPairComponent_complexity a id).mono V.mixedOriginalPairComparison_component_cost
    · exact (W.mixedPairComponent_complexity b (mixedExchangeCoordinate n)).mono V.mixedOriginalPairComparison_component_cost

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

noncomputable def mixedOriginalPairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels (V.mixedOriginalPairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget (tensorPowerBudget m p) q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    (V.mixedOriginalPairComparisonTests_complexity a b)

theorem mixedOriginalPairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.mixedPairModels).RealGroup)
    (hz : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (pi V.mixedPairModels).Space) :
    (V.mixedOriginalPairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.mixedOriginalPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.mixedOriginalPairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.mixedPairModels (V.mixedOriginalPairComparisonTests a b)
    V.mixedOriginalPairFrequencies _ _ _ (V.mixedOriginalPairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} [NeZero m] {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixed_original_pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.mixedPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (pi V.mixedPairModels).Space) :
    (V.mixedOriginalPairComparisonNiltest a b).observable (z • x) =
      (V.mixedOriginalPairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1) :=
    (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.mixedOriginalPairComparisonNiltest_vertical a b z htop,
    V.mixedOriginalPairFrequency_real, R.mixed_original_pair_top_agreement z.coord hz,
    sub_self]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

namespace NativeUnitVerticalData

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} {V : NativeVerticalDerivativeData B}
  (U : NativeUnitVerticalData B V q)

noncomputable def mono {p' q' : ℝ} (hp : p ≤ p') (hq : q ≤ q') :
    NativeUnitVerticalData (B.mono hp) (V.mono hp) q' where
  tailDim := U.tailDim
  dimension := U.dimension.trans (Real.exp_le_exp.mpr hq)
  observable := U.observable
  lipBound := U.lipBound
  lip_bound := U.lip_bound.trans (Real.exp_le_exp.mpr hq)
  unit := U.unit
  norm := U.norm
  lipschitz := U.lipschitz
  scalar := U.scalar
  vertical := U.vertical

end NativeUnitVerticalData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankNativeInverseModels
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeDegreeRankDerivativeData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) (r : ℕ) (q : ℝ) where
  vertical : NativeVerticalDerivativeData B
  unit : NativeUnitVerticalData B vertical q
  rank : B.model.DegreeRankStructure r
  complexity : rank.ComplexityLE q

namespace NativeDegreeRankDerivativeData

variable {s N r : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

noncomputable def mono {p' q' : ℝ} (hp : p ≤ p') (hq : q ≤ q') :
    NativeDegreeRankDerivativeData (B.mono hp) r q' where
  vertical := W.vertical.mono hp
  unit := W.unit.mono hp hq
  rank := W.rank
  complexity := W.complexity.mono W.rank hq

theorem rank_vertical (i : Fin (W.unit.tailDim + 1)) (z : B.model.RealGroup)
    (hz : z ∈ W.rank.realSubgroup s r) (x : B.model.Space) :
    W.unit.observable i (z • x) =
      CircleFourier.character ((realifyFunctional W.vertical.frequency z.coord : ℝ) :
        CircleFourier.Circle) * W.unit.observable i x :=
  W.unit.vertical i z (W.rank.realSubgroup_le_degree s r hz) x

theorem rank_integral (z : B.model.RealGroup) (hz : z ∈ W.rank.realSubgroup s r)
    (hΓ : z ∈ B.model.realLattice) : ∃ n : ℤ, realifyFunctional W.vertical.frequency z.coord = n :=
  W.vertical.integral z (W.rank.realSubgroup_le_degree s r hz) hΓ

end NativeDegreeRankDerivativeData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankFamilyConstruction
namespace OAI

section

namespace Erdos3.NativeDegreeRankDerivativeData

open scoped BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

noncomputable def toFamily (hpq : p ≤ q) : NativeDegreeRankFamily s r (ZMod N) q where
  L := B.L
  dim := B.dim
  model := B.model
  rank := W.rank
  complexity := W.complexity
  orbit h := (B.test h).orbit
  normalized := W.vertical.normalized
  outputDim := W.unit.tailDim + 1
  output_pos := by omega
  output_bound := by simpa only [Nat.cast_add, Nat.cast_one] using W.unit.dimension
  vertical := {
    observable := W.unit.observable
    unit := W.unit.unit
    norm := W.unit.norm
    lipBound := W.unit.lipBound
    lip_bound := W.unit.lip_bound
    lipschitz := W.unit.lipschitz
    frequency := W.vertical.frequency
    height := fun i => (W.vertical.height i).trans hpq
    vertical := W.rank_vertical
    integral := W.rank_integral
  }

theorem toFamily_evalCyclic (hpq : p ≤ q) (i : Fin (W.unit.tailDim + 1)) (h x : ZMod N) :
    (W.toFamily hpq).evalCyclic N i h x = (W.unit.test i h).evalCyclic N (fun _ => x) := rfl

end Erdos3.NativeDegreeRankDerivativeData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals
namespace OAI

section

namespace Erdos3.NativeMixedCorrelation

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_fixed_target_cube_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ (M : NativeMixedCorrelation (d + 2) N p f) (η : J → (Fin 2 → ℤ) → ℂ),
      (∀ x, ∑ j, ‖η j x‖ ^ 2 = 1) → NativeIntegerVectorEquivalence (d + 2) p M.mixed.eval η →
      HasFixedTargetCubeIntervals f M η ((p + C) ^ C) := by
  obtain ⟨A, _, hinterval⟩ := exists_cube_unwrapped_intervals d
  obtain ⟨B, _, hcube⟩ := NativeIntegerVectorEquivalence.exists_mixed_cube_budget (d + 1)
  let L : ℕ := (d + 2) ^ (2 ^ (d + 1))
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let U := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2 * U + Polynomial.C L)
  refine ⟨C, hC, ?_⟩
  intro J _ N _ p hp hN f hf M η hη Ediag
  classical
  let q := (p + A) ^ A
  let u := (p + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have htotal : 3 * q + 2 * u + L ≤ (p + C) ^ C := by
    simpa [X, P, U, q, u, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by linarith
  have htransfer : q + 2 * u ≤ (p + C) ^ C := by linarith
  obtain ⟨r, hr, hrq, E, i, Q, hQ, hdense, hcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  have F : NativeIntegerVectorEquivalence (d + 2) u (M.mixed.mixedCubeWithShift 0)
      (mixedCubeObservable (d := d + 1) η) := by
    rw [M.mixed.mixedCubeWithShift_zero_eq]
    exact hcube hp Ediag
  let K := Σ b : (Fin (d + 1) → Bool) → Fin (d + 2),
    Σ v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim,
      Fin ((E b).selectedExpansion (fun _ => i) v).count ×
        (Σ w : (Fin (d + 1) → Bool) → J, Fin (F.selectedExpansion v w).count)
  let R (t : (Fin (d + 1) → ZMod N) × ZMod N) (_ : Unit) (c : K) : Prop :=
    t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
      0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-(q + 2 * u)) ≤
        ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
          cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
            star (mixedCubeObservable η c.2.2.2.1 (mixedDifferencePoint t n)) *
            star ((((E c.1).selectedExpansion (fun _ => i) c.2.1).test c.2.2.1).eval (mixedDifferencePoint t n)) *
            star (((F.selectedExpansion c.2.1 c.2.2.2.1).test c.2.2.2.2).eval (mixedDifferencePoint t n))‖
  have hchoice : ∀ t ∈ Q, ∀ j, ∃ c, R t j c := by
    intro t ht _
    obtain ⟨hshift, b, a, len, hlen, hend, hshort, hvol, v, l, hcor⟩ := hcorr t ht
    let D (n : ℤ) := cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N)
    let T (n : ℤ) := (((E b).selectedExpansion (fun _ => i) v).test l).eval (mixedDifferencePoint t n)
    have hc : Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        (D n * star (T n)) * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n))‖ := by
      have hswap (n : ℤ) : D n * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) * star (T n) =
          (D n * star (T n)) * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) :=
        mul_right_comm _ _ _
      change Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        D n * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) * star (T n)‖ at hcor
      simpa only [hswap] using hcor
    obtain ⟨w, z, hw⟩ := F.transfer_sample_correlation (Finset.Ico (a : ℤ) (a + len))
      (mixedDifferencePoint t) v (fun n => D n * star (T n))
      (fun n _ => mixedCubeObservable_unit η hη _) hc
    have horder (n : ℤ) :
        (D n * star (T n)) * star (mixedCubeObservable η w (mixedDifferencePoint t n)) *
          star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n)) =
        D n * star (mixedCubeObservable η w (mixedDifferencePoint t n)) * star (T n) *
          star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n)) :=
      congrArg (fun c : ℂ => c * star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n)))
        (mul_right_comm _ _ _)
    simp only [horder] at hw
    exact ⟨⟨b, v, l, w, z⟩, hshift, a, len, hlen, hend, hshort, hvol, hw⟩
  have hinner (b : (Fin (d + 1) → Bool) → Fin (d + 2)) :=
    (E b).selectedChainedChoice_card_bound F (fun _ => i)
  have hcount : (Fintype.card K : ℝ) ≤ Real.exp (2 * q + 2 * u + L) := by
    change (Fintype.card (Σ b : (Fin (d + 1) → Bool) → Fin (d + 2),
      Σ v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim,
        Fin ((E b).selectedExpansion (fun _ => i) v).count ×
          (Σ w : (Fin (d + 1) → Bool) → J, Fin (F.selectedExpansion v w).count)) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _b : (Fin (d + 1) → Bool) → Fin (d + 2), Real.exp (2 * r + 2 * u) :=
        Finset.sum_le_sum (fun b _ => hinner b)
      _ = (L : ℝ) * Real.exp (2 * r + 2 * u) := by simp [L]
      _ ≤ Real.exp L * Real.exp (2 * r + 2 * u) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (L : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (L + (2 * r + 2 * u)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨c, S, _, hS, hSdense, hfixed⟩ := exists_large_fixed_choices Q hQ R hchoice hcount
  have hsize : Real.exp (-(2 * q + 2 * u + L)) * (Q.card : ℝ) ≤ (S.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSdense
  refine ⟨r, u, hr, hrq.trans hqC, hu, huC, E, F, i, (c ()).1, (c ()).2.1,
    (c ()).2.2.1, (c ()).2.2.2.1, (c ()).2.2.2.2, S, hS, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(3 * q + 2 * u + L)) * (N : ℝ) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (by positivity)
      _ = Real.exp (-(2 * q + 2 * u + L)) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(2 * q + 2 * u + L)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hfixed t ht ()
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg htransfer)).trans hc⟩

end Erdos3.NativeMixedCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedPairCoordinateTest
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

variable {n m : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

theorem mixedPairCoordinateTests_complexity (k : Fin 2) (out : Fin W.outputDim) (l : Option (Fin 2)) :
    (V.mixedPairCoordinateTests k out l).ComplexityLE (mixedPairBudget (tensorPowerBudget m p) q) := by
  have htwo : 2 ≤ mixedPairBudget (tensorPowerBudget m p) q :=
    (by norm_num : (2 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  cases l with
  | none => exact Niltest.oneOnOrbit_complexity _ htwo (V.mixedPairTests_complexity none).1
  | some l =>
    fin_cases k <;> fin_cases l
    · exact (W.mixedPairComponent_complexity out id).mono V.mixedOriginalPairComparison_component_cost
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.mixedPairTests_complexity (some 1)).1
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.mixedPairTests_complexity (some 0)).1
    · exact (W.mixedPairComponent_complexity out (mixedExchangeCoordinate n)).mono V.mixedOriginalPairComparison_component_cost

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

noncomputable def mixedPairCoordinateNiltest (k : Fin 2) (out : Fin W.outputDim) :
    (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels (V.mixedPairCoordinateTests k out)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget (tensorPowerBudget m p) q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    (V.mixedPairCoordinateTests_complexity k out)

theorem mixedPairCoordinateNiltest_complexity (k : Fin 2) (out : Fin W.outputDim) :
    (V.mixedPairCoordinateNiltest k out).ComplexityLE
      (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) :=
  piNiltest_complexity V.mixedPairModels (V.mixedPairCoordinateTests k out) _ _ _

theorem mixedPairCoordinateNiltest_observable (k : Fin 2) (out : Fin W.outputDim)
    (x : (pi V.mixedPairModels).Space) :
    (V.mixedPairCoordinateNiltest k out).observable x =
      W.vertical.observable out (productProjection V.mixedPairModels (some k) x) := by
  change (∏ l, (V.mixedPairCoordinateTests k out l).observable
    (productProjection V.mixedPairModels l x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * (W.vertical.observable out
      (productProjection V.mixedPairModels (some 0) x) * 1) = _
    simp only [one_mul, mul_one]
    rfl
  · change 1 * (1 * W.vertical.observable out
      (productProjection V.mixedPairModels (some 1) x)) = _
    simp only [one_mul]
    rfl

theorem mixedPairCoordinateNiltest_orbit (k : Fin 2) (out : Fin W.outputDim) :
    (V.mixedPairCoordinateNiltest k out).orbit = V.mixedPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun l => (V.mixedPairModels l).filtration))
  funext l
  cases l with
  | none => rfl
  | some l => fin_cases k <;> fin_cases l <;> rfl

theorem mixedPairCoordinateNiltest_eval (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) :
    (V.mixedPairCoordinateNiltest k out).eval x =
      W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k))
        (fun j => x j.succ.succ)) := by
  rw [mixedPairCoordinateNiltest, piNiltest_eval, Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * ((W.mixedPairComponent out id).eval x * 1) = _
    rw [one_mul, mul_one, W.mixedPairComponent_eval]
    rfl
  · change 1 * (1 * (W.mixedPairComponent out (mixedExchangeCoordinate n)).eval x) = _
    rw [one_mul, one_mul, W.mixedPairComponent_eval]
    rfl

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairPartitionPrecision
namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

def HasMixedPairLocalApproximation (b : ℝ) : Prop :=
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
    ∀ y : Fin (n + 2) → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
      ∀ (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) -
          R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤ Real.exp b * δ

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixedPairFrozenVector_diagonal (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) :
    W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) =
      R.mixedPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x := by
  have hpoly : V.mixedPairPolynomial =
      ⟨⟨(V.mixedPairCoordinateNiltest k out).orbit.log,
        (V.mixedPairCoordinateNiltest k out).orbit.property⟩⟩ := by
    rw [V.mixedPairCoordinateNiltest_orbit]
    exact V.mixedPairPolynomial_eq_test
  calc
    _ = (V.mixedPairCoordinateNiltest k out).eval x :=
      (V.mixedPairCoordinateNiltest_eval k out x).symm
    _ = _ := (R.eval_niltest (V.mixedPairCoordinateNiltest k out) hpoly x).trans
      (V.mixedPairCoordinateNiltest_observable k out _)

theorem mixedPairFrozenVector_error (k : Fin 2) (out : Fin W.outputDim) (x y : Fin (n + 2) → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) : (pi V.mixedPairModels).Space) =
      QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi V.mixedPairModels).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi V.mixedPairModels).basis.baseChange ℝ)
    ‖W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) -
        R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
  let D := pi V.mixedPairModels
  let T := V.mixedPairCoordinateNiltest k out
  let b := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin (n + 2) => 1) (fun i => (x i : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq T.observable (R.slowValue x) b
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left T.observable T.lipschitz
    (R.slowValue x) (R.slowValue y) b (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (T.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) := by
    have h := T.observable_budget (V.mixedPairCoordinateNiltest_complexity k out)
    linarith [T.normBound.coe_nonneg]
  have hraw : ‖R.mixedPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x -
      R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
    simpa only [T, V.mixedPairCoordinateNiltest_observable, mixedPairFrozenVector, frozenMiddleValue, b] using
      hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)
  simpa only [← R.mixedPairFrozenVector_diagonal k out x] using hraw

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

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

theorem hasMixedPairFrozenEquivalence_mono {u a b : ℝ}
    (h : R.HasMixedPairFrozenEquivalence u a) (hab : a ≤ b) : R.HasMixedPairFrozenEquivalence u b := by
  intro den hm hmb left right hleft hright
  exact (h den hm hmb left right hleft hright).mono hab

def HasMixedPairFrozenReduction (b : ℝ) : Prop :=
  ∃ u : ℝ, 0 ≤ u ∧ u ≤ b ∧ R.HasOuterValueControl u ∧ R.HasMixedPairFrozenEquivalence u b

theorem mixedPairFrozenEquivalence_at {b : ℝ} (h : R.HasMixedPairFrozenReduction b)
    (x : Fin (n + 2) → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ (N : ℝ)) :
    NativeIntegerVectorEquivalence (n + 1) b
      (R.mixedPairFrozenVector 0 (R.slowValue x) (R.rationalValue x))
      (R.mixedPairFrozenVector 1 (R.slowValue x) (R.rationalValue x)) := by
  obtain ⟨u, _hu, _hub, ⟨den, hm, hmb, hrat, hslow⟩, hequiv⟩ := h
  exact hequiv den hm hmb (R.slowValue x) (R.rationalValue x) (hslow x hx) (hrat x)

end NativePolynomialOrbitFactors

end Erdos3

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

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem mixedPairAnchoredVector_norm (y : Fin (n + 2) → ℤ) (k : Fin 2)
    (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ‖R.mixedPairAnchoredVector y k out x‖ ≤ 1 :=
  W.vertical.norm out _

end NativePolynomialOrbitFactors

end Erdos3

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

section Data

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}

attribute [local instance] NativeMixedPairPartition.finite

noncomputable def NativeMixedPairPartition.mono
    {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r} {a b ε δ : ℝ}
    (P : NativeMixedPairPartition R a ε) (hab : a ≤ b) (hεδ : ε ≤ δ) : NativeMixedPairPartition R b δ :=
  { P with
    card_bound := P.card_bound.trans (Real.exp_le_exp.mpr hab)
    positive := fun j => (P.positive j).mono le_rfl hab
    equivalence := fun j => (P.equivalence j).mono hab
    weighted_approximation := fun k out => (P.weighted_approximation k out).trans hεδ }

end Data

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MixedPairPartitionKernel
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

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}

namespace NativeMixedPairPartition

attribute [local instance] NativeMixedPairPartition.finite

variable {b ε : ℝ}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}
  (P : NativeMixedPairPartition R b ε)

noncomputable def cellWeight (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) : ℝ :=
  ∏ l, P.weight (a l) (x l)

theorem cellWeight_nonneg (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) : 0 ≤ P.cellWeight a x :=
  Finset.prod_nonneg (fun l _ => ((P.positive (a l)).unit_interval (x l)).1)

theorem cellWeight_total (x : Fin (n + 2) → ZMod N) : ∑ a, P.cellWeight a x = 1 :=
  sum_productPartitionWeight (fun _ : Fin (n + 2) => P.weight) (fun _ => P.total) x

noncomputable def cellVector (a : Fin (n + 2) → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ZMod N) : ℂ :=
  R.mixedPairAnchoredVector (fun l => ((P.anchor a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))

theorem cellVector_norm (a : Fin (n + 2) → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ZMod N) : ‖P.cellVector a k out x‖ ≤ 1 :=
  R.mixedPairAnchoredVector_norm _ _ _ _

end NativeMixedPairPartition
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

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}

structure NativeMixedPointwisePartition
    (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r) (b δ β : ℝ) where
  partition : NativeMixedPairPartition R b (δ + 2 * ((n + 2 : ℕ) : ℝ) * β)
  error_nonneg : 0 ≤ δ
  density_nonneg : 0 ≤ β
  bad : Finset (ZMod N)
  bad_density : (bad.card : ℝ) / N ≤ β
  pointwise : ∀ a x, (∀ l, x l ∉ bad) → 0 < partition.cellWeight a x →
    ∀ (k : Fin 2) (out : Fin W.outputDim),
      ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) - partition.cellVector a k out x‖ ≤ δ

namespace NativeMixedPointwisePartition

attribute [local instance] NativeMixedPairPartition.finite

variable {b δ β : ℝ} (P : NativeMixedPointwisePartition R b δ β)

noncomputable def mono {b' δ' β' : ℝ} (hb : b ≤ b') (hδ : δ ≤ δ') (hβ : β ≤ β') :
    NativeMixedPointwisePartition R b' δ' β' where
  partition := P.partition.mono hb (add_le_add hδ
    (mul_le_mul_of_nonneg_left hβ (by positivity)))
  error_nonneg := P.error_nonneg.trans hδ
  density_nonneg := P.density_nonneg.trans hβ
  bad := P.bad
  bad_density := P.bad_density.trans hβ
  pointwise := fun a x hx hax k out => (P.pointwise a x hx hax k out).trans hδ

theorem sampled_error {X : Type*} [Fintype X] [Nonempty X]
    (sample : X → Fin (n + 2) → ZMod N) (E : Finset X)
    (hE : ∀ x, x ∉ E → ∀ l, sample x l ∉ P.bad) (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x, ∑ a, P.partition.cellWeight a (sample x) *
      ‖W.eval out (mixedSlotInput ((sample x (![0, 1] k)).val : ℤ) ((sample x (![1, 0] k)).val : ℤ) (fun l => ((sample x l.succ.succ).val : ℤ))) - P.partition.cellVector a k out (sample x)‖) ≤
      δ + 2 * (E.card : ℝ) / Fintype.card X := by
  exact weighted_partition_mean_error E
    (fun a x => P.partition.cellWeight a (sample x))
    (fun a x => P.partition.cellVector a k out (sample x)) _ P.error_nonneg
    (fun a x => P.partition.cellWeight_nonneg a (sample x))
    (fun x => P.partition.cellWeight_total (sample x))
    (fun a x => P.partition.cellVector_norm a k out (sample x))
    (fun x => W.norm_eval out _) (fun a x hx hax => P.pointwise a (sample x) (hE x hx) hax k out)

end NativeMixedPointwisePartition
end Erdos3

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
  NativeMixedPairPartition.finite

namespace NativeMixedPointwisePartition

variable {n m : ℕ} {p q r b δ β : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}
  (P : NativeMixedPointwisePartition R b δ β)

theorem weighted_two_variable_error (π : Fin (n + 2) → Fin 2)
    (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
      ‖W.eval out (mixedSlotInput ((x (π (![0, 1] k))).val : ℤ) ((x (π (![1, 0] k))).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) -
        P.partition.cellVector a k out (fun l => x (π l))‖) ≤ δ + 4 * β := by
  let E := coordinateExceptional (ι := Fin 2) P.bad
  have h := P.sampled_error (fun x l => x (π l)) E
    (fun x hx l => (not_mem_coordinateExceptional P.bad x).mp hx (π l)) k out
  have hd : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * β := by
    have hD := coordinateExceptional_density_le (ι := Fin 2) P.bad
    simp only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] at hD
    exact hD.trans (mul_le_mul_of_nonneg_left P.bad_density (by norm_num))
  rw [mul_div_assoc] at h
  linarith

theorem weighted_two_variable_exchange_error (π : Fin (n + 2) → Fin 2) (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
      ‖W.eval out₀ (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
          star (W.eval out₁ (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
        P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
          star (P.partition.cellVector a 1 out₁ (fun l => x (π l)))‖) ≤ 2 * (δ + 4 * β) := by
  let err := fun (k : Fin 2) (out : Fin W.outputDim) (a : Fin (n + 2) → P.partition.I)
      (x : Fin 2 → ZMod N) =>
    ‖W.eval out (mixedSlotInput ((x (π (![0, 1] k))).val : ℤ) ((x (π (![1, 0] k))).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) -
      P.partition.cellVector a k out (fun l => x (π l))‖
  have hbound (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err k out a x) ≤
        δ + 4 * β := P.weighted_two_variable_error π k out
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
        (err 0 out₀ a x + err 1 out₁ a x) := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (P.partition.cellWeight_nonneg _ _)
      exact norm_mul_star_sub_mul_star_le_of_le_one (W.norm_eval out₁ _)
        (P.partition.cellVector_norm a 0 out₀ _)
    _ = (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err 0 out₀ a x) +
        (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err 1 out₁ a x) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.expect_add_distrib]
    _ ≤ _ := by linarith [hbound 0 out₀, hbound 1 out₁]

theorem two_variable_exchange_approximation (π : Fin (n + 2) → Fin 2) (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out₀ (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
          star (W.eval out₁ (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
        ∑ a, (P.partition.cellWeight a (fun l => x (π l)) : ℂ) *
          (P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
            star (P.partition.cellVector a 1 out₁ (fun l => x (π l))))‖) ≤ 2 * (δ + 4 * β) := by
  apply le_trans _ (P.weighted_two_variable_exchange_error π out₀ out₁)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (fun l => x (π l)))
    (fun a => P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
      star (P.partition.cellVector a 1 out₁ (fun l => x (π l)))) _
    (fun a => P.partition.cellWeight_nonneg a _) (P.partition.cellWeight_total _))

end NativeMixedPointwisePartition
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootLosses
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem exists_divisionMixedExchangeCorrection_expansion (s d : ℕ) [NeZero d] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (W.divisionMixedExchangeCorrection d G π a b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_mixed_rational_division_equivalence s d
  obtain ⟨B, _, hdivision⟩ := NativeIntegerExpansion.exists_division_expansion d (s + 2) (by omega)
  obtain ⟨D, _, hcontract⟩ := exists_native_cross_contraction
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + q + A) ^ A + (p + q + B) ^ B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hBt : (q + B) ^ B ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    exact pow_le_pow_left₀ (by positivity) (by linarith) B
  have hF (i j : Fin W.outputDim) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) t
      (fun x => G π i j (fun k => x k / (d : ℤ)))) :=
    ⟨(Classical.choice (hdivision hq (Classical.choice (hG π i j)))).mono hBt⟩
  have H := hcontract (fun i j x => G π i j (fun k => x k / (d : ℤ))) ht
    ((hcompare W π).mono hAt) ((hcompare W (mixedSwapSample π)).mono hAt) hF a b
  have hcost : (t + D) ^ D ≤ (p + q + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨(Classical.choice H).mono hcost⟩

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

theorem exists_division_mixed_last_slots_equivalence (d D : ℕ) [NeZero D] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin (d + 2))) (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => (W.rationalDilation ((D : ℚ)⁻¹)).eval i (mixedSampledInput π x))
        (fun i x => (W.rationalDilation ((D : ℚ)⁻¹)).eval i
          (mixedSampledInput (mixedPermuteSample e π) x)) := by
  obtain ⟨A, _, hcompare⟩ := exists_mixed_rational_division_equivalence d D
  obtain ⟨B, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have heq : (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π (fun k => x k / (D : ℤ)))) =
      (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) (fun k => x k / (D : ℤ)))) := by
    funext i x
    symm
    change W.eval i (mixedReplicatedInput (x (π 0) / (D : ℤ)) (fun j => x (π (e j).succ) / (D : ℤ))) =
      W.eval i (mixedReplicatedInput (x (π 0) / (D : ℤ)) (fun j => x (π j.succ) / (D : ℤ)))
    exact W.mixed_permutation_eval hsymm e i (x (π 0) / (D : ℤ)) (fun j => x (π j.succ) / (D : ℤ))
  have F : NativeIntegerVectorEquivalence (d + 2) ((p + A) ^ A)
      (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π (fun k => x k / (D : ℤ))))
      (fun i x => (W.rationalDilation ((D : ℚ)⁻¹)).eval i
        (mixedSampledInput (mixedPermuteSample e π) x)) := by
    rw [heq]
    exact (hcompare W (mixedPermuteSample e π)).symm
  have H := htrans hu (hcompare W π) F (fun x => W.unit_eval _)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

theorem exists_division_mixed_tensor_last_slots_equivalence (d D n : ℕ) [NeZero D] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin (d + 2))) (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => ((W.rationalDilation ((D : ℚ)⁻¹)).tensorPower n).eval i (mixedSampledInput π x))
        (fun i x => ((W.rationalDilation ((D : ℚ)⁻¹)).tensorPower n).eval i (mixedSampledInput (mixedPermuteSample e π) x)) := by
  obtain ⟨A, _, hdivision⟩ := exists_division_mixed_last_slots_equivalence d D
  obtain ⟨B, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_power_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have H := htensor hu (hdivision W hsymm e π)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have E := H.mono hcost
  have hdim : (Fintype.card (Fin ((W.rationalDilation ((D : ℚ)⁻¹)).tensorPower n).outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [Fintype.card_fin]
    change ((W.outputDim ^ n : ℕ) : ℝ) ≤ _
    have h := E.left_dimension
    simp only [Fintype.card_fun, Fintype.card_fin] at h
    change ((W.outputDim ^ n : ℕ) : ℝ) ≤ _ at h
    exact h
  apply E.of_coordinate_maps _ _ (tensorIndexEquiv W.outputDim n).symm
    (tensorIndexEquiv W.outputDim n).symm _ _ hdim hdim (le_refl _)
  · intro i x
    exact (W.rationalDilation ((D : ℚ)⁻¹)).tensorPower_eval n i (mixedSampledInput π x)
  · intro i x
    exact (W.rationalDilation ((D : ℚ)⁻¹)).tensorPower_eval n i
      (mixedSampledInput (mixedPermuteSample e π) x)

theorem exists_mixed_root_last_slots_equivalence (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval i x) →
      ∀ (e : Equiv.Perm (Fin (d + 2))) (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun i (x : Fin 2 → ℤ) => W.mixedIntegrationRoot.eval i (mixedSampledInput π x))
        (fun i x => W.mixedIntegrationRoot.eval i (mixedSampledInput (mixedPermuteSample e π) x)) := by
  obtain ⟨C, hC, h⟩ := exists_division_mixed_tensor_last_slots_equivalence d (d + 3) ((d + 3) ^ (d + 2))
  refine ⟨C, hC, ?_⟩
  intro p W hsymm e π
  exact h W hsymm e π

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem exists_mixedTensorExchangeCorrection_expansion (s n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((q + C) ^ C)
        (W.mixedTensorExchangeCorrection n G π a b)) := by
  obtain ⟨C, hC, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  exact hprod _ hq (fun _ => hG _ _ _)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem exists_mixedRootExchangeCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      ∀ G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      ∀ π a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (W.mixedRootExchangeCorrection G π a b)) := by
  obtain ⟨A, _, hdivision⟩ := exists_divisionMixedExchangeCorrection_expansion s (s + 3)
  obtain ⟨B, _, htensor⟩ := exists_mixedTensorExchangeCorrection_expansion s ((s + 3) ^ (s + 2))
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG π a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := htensor (W.rationalDilation (((s + 3 : ℕ) : ℚ)⁻¹)) (by positivity : 0 ≤ (p + q + A) ^ A)
    (W.divisionMixedExchangeCorrection (s + 3) G) (hdivision W hq G hG) π a b
  have hcost : ((p + q + A) ^ A + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  exact ⟨E.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_corner_product_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (G : (Fin (s + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ),
      0 ≤ q → 0 ≤ r →
      (∀ π i j, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (G π i j))) →
      (∀ (e : Equiv.Perm (Fin (s + 2))) (π : Fin (s + 3) → Fin 2), NativeIntegerVectorEquivalence (s + 2) r
        (fun i (x : Fin 2 → ℤ) => W.eval i (mixedSampledInput π x))
        (fun i x => W.eval i (mixedSampledInput (mixedPermuteSample e π) x))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((q + r + C) ^ C)
        (W.mixedCornerExchangeProduct G a b)) := by
  obtain ⟨A, _, hfactor⟩ := exists_mixed_corner_exchange_expansion s
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget (mixedCornerCount s)
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r W G hq hr hG hperm a b
  let e : Fin (mixedCornerCount s) ≃ MixedNonconstantCorner s := (Fintype.equivFinOfCardEq (mixedNonconstantCorner_card_eq s)).symm
  obtain ⟨F⟩ := hprod (fun k => W.mixedCornerExchangeFactor G a b (e k))
    (by positivity : 0 ≤ (q + r + A) ^ A)
    (fun k => hfactor W G hq hr hG hperm a b (e k))
  have hcost : ((q + r + A) ^ A + B) ^ B ≤ (q + r + C) ^ C := by
    simpa [X, T, Polynomial.eval₂_pow] using hbudget (q + r) (add_nonneg hq hr)
  have heq : (fun x => star (∏ k : Fin (mixedCornerCount s), W.mixedCornerExchangeFactor G a b (e k) x)) =
      W.mixedCornerExchangeProduct G a b := by
    funext x
    exact congrArg star (e.prod_comp (fun v => W.mixedCornerExchangeFactor G a b v x))
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRootCyclicComparison
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

theorem exists_mixedCyclicDiagonalCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ F : (Fin W.outputDim × Fin W.outputDim) →
          (MixedNonconstantCorner s → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (F a b))) →
        ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2)
          ((p + q + e + C) ^ C) (W.mixedCyclicDiagonalCorrection N δ F a b)) := by
  obtain ⟨A, _, hwrap⟩ := exists_mixedDiagonalWrapCoefficient_expansion s
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + (X + 6) ^ 2 + 13
  let T := (R + Polynomial.C B) ^ B + X + R + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv F hF a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  let r := (v + A) ^ A + v + (v + 6) ^ 2 + 13
  let t := (r + B) ^ B + v + r + 2
  let d := (t + B) ^ B + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have har : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; nlinarith [sq_nonneg (v + 6)]
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    have hs : 0 ≤ (v + 6) ^ 2 := sq_nonneg _
    dsimp [r, v] at *
    linarith
  have her : raisedNiltestBudget (e + 4) ≤ r := by
    have hpow : (e + 6) ^ 2 ≤ (v + 6) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) 2
    have hA : 0 ≤ (v + A) ^ A := by positivity
    have hev : e ≤ v := by dsimp [v]; linarith
    dsimp [raisedNiltestBudget, r]
    nlinarith
  have hrt : r ≤ t := by
    have : 0 ≤ (r + B) ^ B := by positivity
    dsimp [t]
    linarith
  have hwt : (r + B) ^ B + p ≤ t := by dsimp [t, v]; linarith
  have htd : t ≤ d := le_add_of_nonneg_left (by positivity)
  have hpd : (t + B) ^ B ≤ d := le_add_of_nonneg_right ht
  have hcost : d + 2 ≤ (p + q + e + C) ^ C := by
    simpa [X, R, T, r, t, d, v, Polynomial.eval₂_pow] using hbudget v hv
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _k : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterms (k : Fin W.outputDim) := hmul hr
    ((Classical.choice (hwrap W N a.2 k)).mono har) ((Classical.choice (hF (a.1, k) b)).mono hqr)
  have EW : NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) t
      (W.mixedWrappedDiagonalCorrection N F a b) := by
    have E := (NativeIntegerExpansion.weightedSum (fun k => Classical.choice (hterms k))
      (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hwt
    change NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) t
      (fun x => ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x)
    simpa only [one_mul] using E
  let w := fun x => (smoothCyclicCarry N δ x : ℂ)
  have EC := ((Classical.choice (exists_smoothCyclicCarry_expansion N δ hδ he hinv)).raiseStep
    (by omega : 1 ≤ s + 2) (by positivity : 0 ≤ e + 4)).mono (her.trans hrt)
  have E₀ := (Classical.choice (hF a b)).mono (hqr.trans (hrt.trans htd))
  have E₁ := (Classical.choice (hmul ht EC EW)).mono hpd
  have E₂ := (Classical.choice (hmul ht EC ((Classical.choice (hF a b)).mono (hqr.trans hrt)))).mono hpd
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![F a b,
    (fun x => w x * W.mixedWrappedDiagonalCorrection N F a b x), (fun x => w x * F a b x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) d (fs j)) := by
    fin_cases j
    · exact ⟨E₀⟩
    · exact ⟨E₁⟩
    · exact ⟨E₂⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono hcost
  have heq : (fun x => ∑ j, cs j * fs j x) = W.mixedCyclicDiagonalCorrection N δ F a b := by
    funext x
    simp [cs, fs, Fin.sum_univ_succ, w, mixedCyclicDiagonalCorrection]
    ring
  exact ⟨heq ▸ E⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

open scoped BigOperators

theorem mixed_original_row_correlation_bound {s : ℕ} {p ε : ℝ} {N : ℕ} [NeZero N]
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
    (i : Fin M.outputDim) (row : ZMod N → ZMod N → ℂ)
    (hrow : ∀ h n, ‖row h n‖ ≤ 1)
    (K : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedMiddleCorner s → Fin W.mixedIntegrationRoot.outputDim) → Fin W.mixedIntegrationRoot.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
          (M.eval i (fun k => ((x k).val : ℤ)) *
            (W.mixedIntegrationRoot.mixedMiddleTensor b (fun k => ((x k).val : ℤ)) *
              W.mixedIntegrationRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
        K a b c (fun k => ((x k).val : ℤ))‖) ≤ ε) :
    (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      row h n * star (M.evalCyclic N i (correlationInput h n))‖) ≤
      (∑ abc : ((Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) ×
          (MixedMiddleCorner s → Fin W.mixedIntegrationRoot.outputDim)) × Fin W.mixedIntegrationRoot.outputDim,
        𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          row h n *
            (W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative abc.1.1 ![h, n] *
              W.mixedIntegrationRoot.mixedMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
                star (K abc.1.1 abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖) +
          (W.mixedIntegrationRoot.outputDim : ℝ) ^ mixedRowCoordinateCount s * ε := by
  let R := W.mixedIntegrationRoot
  let I := (Fin R.outputDim × Fin R.outputDim) × (MixedMiddleCorner s → Fin R.outputDim)
  have hinput (h n : ZMod N) : (fun k => ((![h, n] k).val : ℤ)) = ![(h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  have heval (h n : ZMod N) : M.evalCyclic N i (correlationInput h n) =
      M.eval i ![(h.val : ℤ), (n.val : ℤ)] := by
    unfold evalCyclic
    congr 1
    funext k
    fin_cases k <;> rfl
  have hunit (h n : ZMod N) : ∑ ab : I,
      ‖R.mixedCyclicDiagonalDerivative ab.1 ![h, n] *
        R.mixedMiddleTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)]‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [norm_mul, mul_pow, ← Finset.mul_sum, R.mixedMiddleTensor_unit, mul_one]
    exact R.mixedCyclicDiagonalDerivative_unit _
  have hh := unit_row_correlation_bound row
    (fun h n => M.eval i ![(h.val : ℤ), (n.val : ℤ)])
    (fun ab : I => fun h n => R.mixedCyclicDiagonalDerivative ab.1 ![h, n] *
      R.mixedMiddleTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)])
    (fun c h => R.eval c (fun _ => (h.val : ℤ)))
    (fun ab c h n => K ab.1 ab.2 c ![(h.val : ℤ), (n.val : ℤ)]) hrow hunit
    (fun h => R.unit_eval _) (fun ab h n => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (R.mixedCyclicDiagonalDerivative_norm _ _)
        (norm_nonneg _)).trans (by
          simpa only [one_mul] using R.mixedMiddleTensor_norm _ _))
      (fun c h => R.norm_eval _ _) (ε := ε) (by
      intro ab c
      have he := herr ab.1 ab.2 c
      rw [expect_fin_two] at he
      simpa only [hinput, Matrix.cons_val_zero, mul_assoc, mul_comm, mul_left_comm] using he)
  have hcard : (Fintype.card (I × Fin R.outputDim) : ℝ) =
      (R.outputDim : ℝ) ^ mixedRowCoordinateCount s := mixedRowIndex_card s R.outputDim
  simpa only [heval, hcard] using hh

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

variable {d : ℕ} {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation (d + 2) N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

noncomputable def mixedResidualRowFactor (b : (MixedMiddleCorner d → Fin W.outputDim))
    (h : ZMod N) (x : Unit → ℤ) : ℂ :=
  M.residualMultiplier h x * star (W.mixedMiddleTensor b ![(h.val : ℤ), x ()])

theorem mixedResidualRowFactor_norm (b : (MixedMiddleCorner d → Fin W.outputDim))
    (h : ZMod N) (x : Unit → ℤ) : ‖M.mixedResidualRowFactor W b h x‖ ≤ 1 := by
  rw [mixedResidualRowFactor, norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right (M.residualMultiplier_norm h x)
    (norm_nonneg _)).trans (by
      simpa only [one_mul] using W.mixedMiddleTensor_norm _ _)

end NativeMixedCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.MixedPrimitiveNiltest
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_mixed_diagonal_niltest {d : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p) (i : Fin W.outputDim) :
    ∃ T : W.model.Niltest (fun _ : Unit => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ n : ℤ, T.eval (fun _ => n) = W.eval i (fun _ => n) := by
  obtain ⟨T, hT, hcomplexity, heval⟩ := W.exists_linear_niltest i
    (fun _ => { toFun := fun x : Unit → ℤ => x (), map_zero' := rfl, map_add' := fun _ _ => rfl })
  exact ⟨T, hT, hcomplexity, fun n => heval (fun _ => n)⟩

theorem exists_mixed_primitive_niltest_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p,
      ∀ i : Fin W.outputDim, ∀ g ∈ nativeCyclicFunctions (d + 2) N p,
      (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n) ∈
        nativeCyclicFunctions (d + 3) N ((p + C) ^ C) := by
  obtain ⟨A, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let R := 2 * X + (X + 2) ^ 2 + 7
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp W i g ⟨G⟩
  have hdegree : (∑ _ : MixedReplicatedIndex (d + 2), (1 : ℕ)) = d + 3 := mixedReplicated_totalDegree (d + 1)
  have hraise : d + 2 ≤ ∑ _ : MixedReplicatedIndex (d + 2), (1 : ℕ) := by omega
  obtain ⟨T, hTnorm, hT, hTeval⟩ := W.exists_mixed_diagonal_niltest i
  let r := 2 * p + (p + 2) ^ 2 + 7
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p + 4 ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 2)]
  have hGr : raisedNiltestBudget p ≤ r := by dsimp [raisedNiltestBudget, r]; linarith
  let K : Bool → Type := BoolLieFamily W.L G.L
  let dims : Bool → ℕ := fun b => Bool.rec G.dim W.dim b
  let models : ∀ b, RationalFilteredNilmanifold (K b) (∑ _ : MixedReplicatedIndex (d + 2), 1) (dims b) := fun b => by
    cases b
    · exact G.model.raiseStep hraise
    · exact W.model
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact G.test.raiseStep hraise
    · exact T.conjugate
  have htests : ∀ b, (tests b).ComplexityLE r := by
    intro b
    cases b
    · exact (G.test.raiseStep_complexity hraise hp G.complexity).mono hGr
    · exact hT.mono hpr
  have hcap : ∀ b, (tests b).normBound ≤ 1 := by
    intro b
    cases b
    · exact G.norm
    · exact hTnorm.le
  have hcard : (Fintype.card Bool : ℝ) ≤ r := by
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    linarith
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.unitBoundedPiNiltest models tests hr hcard htests hcap
  have hcost : productNiltestBudget r ≤ (p + C) ^ C := by
    apply (hproduct r hr).trans
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have H : Nonempty (NativeCyclicModel (∑ _ : MixedReplicatedIndex (d + 2), 1) N ((p + C) ^ C)
      (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n)) := by
    refine ⟨{
      L := ∀ b, K b
      dim := _
      model := RationalFilteredNilmanifold.pi models
      test := S
      norm := le_rfl
      complexity := (RationalFilteredNilmanifold.unitBoundedPiNiltest_complexity
        models tests hr hcard htests hcap).mono hcost
      eval := ?_ }⟩
    intro n
    change _ = S.eval (fun _ => (n.val : ℤ))
    rw [RationalFilteredNilmanifold.unitBoundedPiNiltest_eval, Fintype.prod_bool]
    change _ = star (T.eval (fun _ => (n.val : ℤ))) *
      (G.test.raiseStep hraise).eval (fun _ => (n.val : ℤ))
    rw [hTeval, RationalFilteredNilmanifold.Niltest.raiseStep_eval, G.eval n]
    rfl
  change Nonempty (NativeCyclicModel (d + 3) N ((p + C) ^ C) _)
  simpa only [hdegree] using H

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
end


